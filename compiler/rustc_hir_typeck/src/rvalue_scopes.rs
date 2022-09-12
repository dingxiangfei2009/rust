use std::ops::ControlFlow;

use super::FnCtxt;
use hir::def_id::DefId;
use hir::{ExprKind, Node};
use rustc_data_structures::fx::FxHashSet;
use rustc_hir as hir;
use rustc_hir_analysis::astconv::AstConv;
use rustc_middle::middle::region::{RvalueCandidateType, Scope};
use rustc_middle::ty::{
    self, Region, RvalueScopes, Ty, TyCtxt, TypeSuperVisitable, TypeVisitable, TypeVisitor,
};
use smallvec::{smallvec, SmallVec};

struct RegionCollector<'tcx, T> {
    tcx: TyCtxt<'tcx>,
    regions: T,
}
impl<'tcx, T: Extend<Region<'tcx>>> TypeVisitor<'tcx> for RegionCollector<'tcx, T> {
    fn visit_ty(&mut self, t: Ty<'tcx>) -> ControlFlow<Self::BreakTy> {
        match t.kind() {
            ty::Alias(..) => return ControlFlow::Continue(()),
            ty::FnDef(..) | ty::FnPtr(..) | ty::Closure(..) => return ControlFlow::Continue(()),
            ty::Dynamic(_, region, _) | ty::Ref(region, _, _) => {
                return self.visit_region(*region);
            }

            _ => {}
        }
        t.super_visit_with(self)
    }
    fn visit_region(&mut self, region: Region<'tcx>) -> ControlFlow<Self::BreakTy> {
        if let ty::ReEarlyBound(_) | ty::ReFree(_) = *region {
            // pending on stabilizing extend_one
            self.regions.extend(Some(self.tcx.mk_region(*region)))
        }
        ControlFlow::Continue(())
    }
}
impl<'tcx, T: FromIterator<Region<'tcx>> + Extend<Region<'tcx>> + Default>
    RegionCollector<'tcx, T>
{
    fn collect(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> T {
        let mut collector = Self { tcx, regions: T::default() };
        ty.visit_with(&mut collector);
        collector.regions
    }
}

fn choose_extended_arguments<'tcx>(
    tcx: TyCtxt<'tcx>,
    inputs: &[Ty<'tcx>],
    output: Ty<'tcx>,
) -> SmallVec<[bool; 8]> {
    let output_regions: FxHashSet<_> = RegionCollector::collect(tcx, output);
    debug!(?output_regions, "choose_extended_arguments");
    let mut can_be_extended = smallvec![];
    for &arg_ty in inputs {
        let input_regions: Vec<_> = RegionCollector::collect(tcx, arg_ty);
        debug!(?input_regions, "choose_extended_arguments");
        can_be_extended.push(
            !input_regions.is_empty()
                && input_regions.iter().any(|region| output_regions.contains(region)),
        );
    }
    can_be_extended
}

fn is_candidate_for_rvalue_scope_extension(mut expr: &hir::Expr<'_>) -> bool {
    loop {
        match expr.kind {
            ExprKind::AddrOf(..)
            | ExprKind::Path(..)
            | ExprKind::Field(..)
            | ExprKind::Unary(hir::UnOp::Deref, _)
            | ExprKind::Index(..) => return true,
            ExprKind::Block(block, ..) => {
                if let Some(subexpr) = &block.expr {
                    expr = subexpr;
                } else {
                    return false;
                }
            }
            _ => return false,
        }
    }
}

/// Applied to an expression `expr` if `expr` -- or something owned or partially owned by
/// `expr` -- is going to be indirectly referenced by a variable in a let statement. In that
/// case, the "temporary lifetime" or `expr` is extended to be the block enclosing the `let`
/// statement.
///
/// More formally, if `expr` matches the grammar `ET`, record the rvalue scope of the matching
/// `<rvalue>` as `blk_id`:
///
/// ```text
///     ET = *ET
///        | ET[...]
///        | ET.f
///        | (ET)
///        | <rvalue>
/// ```
///
/// Note: ET is intended to match "rvalues or places based on rvalues".
fn record_rvalue_scope_rec<'a, 'tcx>(
    fcx: &FnCtxt<'a, 'tcx>,
    rvalue_scopes: &mut RvalueScopes,
    mut expr: &hir::Expr<'tcx>,
    lifetime: Option<Scope>,
    mut top_call: bool,
) {
    loop {
        // Note: give all the expressions matching `ET` with the
        // extended temporary lifetime, not just the innermost rvalue,
        // because in codegen if we must compile e.g., `*rvalue()`
        // into a temporary, we request the temporary scope of the
        // outer expression.
        // rvalue_scopes.record_rvalue_scope(expr.hir_id.local_id, lifetime);

        match expr.kind {
            ExprKind::AddrOf(_, _, subexpr)
            | ExprKind::Unary(hir::UnOp::Deref, subexpr)
            | ExprKind::Field(subexpr, _)
            | ExprKind::Index(subexpr, _) => {
                top_call = false;
                rvalue_scopes.record_rvalue_scope(expr.hir_id.local_id, lifetime);
                expr = subexpr;
            }
            ExprKind::Call(
                hir::Expr {
                    kind:
                        ExprKind::Path(hir::QPath::Resolved(
                            _,
                            hir::Path {
                                res: hir::def::Res::Def(hir::def::DefKind::Ctor(..), _),
                                ..
                            },
                        )),
                    ..
                },
                args,
            ) => {
                rvalue_scopes.record_rvalue_scope(expr.hir_id.local_id, lifetime);
                for arg in args {
                    record_rvalue_scope_rec(fcx, rvalue_scopes, arg, lifetime, false)
                }
                break;
            }
            ExprKind::Call(callee, args) => {
                let original_callee_ty = fcx.typeck_results.borrow().node_type(callee.hir_id);
                let (inputs, output) = match original_callee_ty.kind() {
                    ty::FnDef(def_id, _subst) => {
                        let fn_sig = fcx.tcx.liberate_late_bound_regions(
                            *def_id,
                            fcx.tcx.fn_sig(def_id).subst_identity(),
                        );
                        (fn_sig.inputs(), fn_sig.output())
                    }
                    ty::Closure(def_id, subst) => {
                        let fn_sig =
                            fcx.tcx.liberate_late_bound_regions(*def_id, subst.as_closure().sig());
                        let [inputs] = fn_sig.inputs() else {
                            span_bug!(expr.span, "expecting function pointer to closure to have exactly one argument")
                        };
                        let ty::Tuple(inputs) = inputs.kind() else {
                            span_bug!(expr.span, "expecting function pointer to closure to have tupled arguments")
                        };
                        (inputs.as_slice(), fn_sig.output())
                    }
                    ty::FnPtr(poly_fn_sig) => {
                        let fn_sig =
                            fcx.tcx.liberate_late_bound_regions(fcx.item_def_id(), *poly_fn_sig);
                        (fn_sig.inputs(), fn_sig.output())
                    }
                    kind => {
                        debug!(?kind, "callee seems not to be of a callable type");
                        break;
                    }
                };
                let extended_args = choose_extended_arguments(fcx.tcx, inputs, output);
                if args.len() != extended_args.len() {
                    debug!(?args, ?extended_args, "mismatching argument length, skipping");
                    break;
                }
                if !top_call {
                    rvalue_scopes.record_rvalue_scope(expr.hir_id.local_id, lifetime)
                }
                debug!(?extended_args, "extended parameter");
                if extended_args.is_empty() || extended_args.iter().all(|&x| !x) {
                    break;
                }
                let filter_args = || {
                    args.into_iter()
                        .zip(&extended_args)
                        .filter_map(|(arg, extended)| extended.then_some(arg))
                };
                if filter_args().any(|arg| !is_candidate_for_rvalue_scope_extension(arg)) {
                    debug!(
                        ?original_callee_ty,
                        ?callee.kind,
                        "one of the argument does not qualify for extended lifetime, skipping"
                    );
                    break;
                }
                for arg in filter_args() {
                    record_rvalue_scope_rec(fcx, rvalue_scopes, arg, lifetime, false)
                }
                break;
            }
            ExprKind::MethodCall(segment, receiver, args, _span) => {
                let Some(def_id) = fcx
                    .typeck_results
                    .borrow()
                    .type_dependent_def_id(expr.hir_id)
                    else {
                        debug!(?segment, "no type-dependent def for method callee");
                        break;
                    };
                debug!(?expr.span, ?def_id, "found method call");
                let fn_sig = fcx
                    .tcx
                    .liberate_late_bound_regions(def_id, fcx.tcx.fn_sig(def_id).subst_identity());
                let extended_args =
                    choose_extended_arguments(fcx.tcx, fn_sig.inputs(), fn_sig.output());
                if args.len() + 1 != extended_args.len() {
                    debug!(?expr.span, "mismatching argument length, skipping");
                    break;
                }
                debug!(?fn_sig, ?extended_args, "extended parameter");
                if !top_call {
                    rvalue_scopes.record_rvalue_scope(expr.hir_id.local_id, lifetime);
                }
                if extended_args.iter().all(|&x| !x) {
                    break;
                }
                if [receiver]
                    .into_iter()
                    .chain(args)
                    .zip(&extended_args)
                    .skip(1)
                    .filter_map(|(arg, extended)| extended.then_some(arg))
                    .any(|arg| !is_candidate_for_rvalue_scope_extension(arg))
                {
                    debug!("one of the argument does not qualify for extended lifetime, skipping");
                    break;
                }
                for arg in [receiver]
                    .into_iter()
                    .chain(args)
                    .zip(extended_args)
                    .filter_map(|(arg, extended)| extended.then_some(arg))
                {
                    record_rvalue_scope_rec(fcx, rvalue_scopes, arg, lifetime, false)
                }
                break;
            }
            _ => {
                rvalue_scopes.record_rvalue_scope(expr.hir_id.local_id, lifetime);
                break;
            }
        }
    }
}

fn record_rvalue_scope<'a, 'tcx>(
    fcx: &FnCtxt<'a, 'tcx>,
    rvalue_scopes: &mut RvalueScopes,
    expr: &hir::Expr<'tcx>,
    candidate: &RvalueCandidateType,
) {
    debug!("resolve_rvalue_scope(expr={expr:?}, candidate={candidate:?})");
    match candidate {
        RvalueCandidateType::Borrow { lifetime, .. }
        | RvalueCandidateType::Pattern { lifetime, .. } => {
            rvalue_scopes.record_rvalue_scope(expr.hir_id.local_id, *lifetime);
            record_rvalue_scope_rec(fcx, rvalue_scopes, expr, *lifetime, false);
        }
        RvalueCandidateType::Call { lifetime, .. } => {
            record_rvalue_scope_rec(fcx, rvalue_scopes, expr, *lifetime, true);
        }
    }
}

pub fn resolve_rvalue_scopes<'a, 'tcx>(fcx: &FnCtxt<'a, 'tcx>, def_id: DefId) -> RvalueScopes {
    let tcx = fcx.tcx;
    let scope_tree = tcx.region_scope_tree(def_id);
    let hir_map = tcx.hir();
    let mut rvalue_scopes = RvalueScopes::new();
    debug!("start resolving rvalue scopes, def_id={def_id:?}");
    debug!("rvalue_scope: rvalue_candidates={:?}", scope_tree.rvalue_candidates);
    for (&hir_id, candidate) in &scope_tree.rvalue_candidates {
        let Some(Node::Expr(expr)) = hir_map.find(hir_id) else {
            bug!("hir node does not exist")
        };
        record_rvalue_scope(fcx, &mut rvalue_scopes, expr, candidate);
    }
    rvalue_scopes
}
