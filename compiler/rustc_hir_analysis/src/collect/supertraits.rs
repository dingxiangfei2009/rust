#![allow(unused)]
use std::assert_matches::assert_matches;

use hir::Node;
use rustc_ast::TraitRefSource;
use rustc_data_structures::fx::{FxHashMap, FxIndexMap, FxIndexSet};
use rustc_data_structures::unord::UnordMap;
use rustc_errors::struct_span_code_err;
use rustc_hir as hir;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, DefIdMap, LOCAL_CRATE, LocalDefId};
use rustc_hir::definitions::DisambiguatorState;
use rustc_middle::ty::print::PrintTraitRefExt as _;
use rustc_middle::ty::{
    self, EarlyBinder, GenericPredicates, ImplTraitInTraitData, Ty, TyCtxt, TypeVisitable,
    TypeVisitableExt, TypeVisitor, Upcast,
};
use rustc_middle::{bug, span_bug};
use rustc_span::sym::rustc_supertrait_in_subtrait_impl;
use rustc_span::{DUMMY_SP, Ident, Span};
use smallvec::SmallVec;
use tracing::{debug, instrument, trace};

use super::item_bounds::explicit_item_bounds_with_filter;
use crate::collect::ItemCtxt;
use crate::constrained_generic_params as cgp;
use crate::delegation::inherit_predicates_for_delegation_item;
use crate::hir_ty_lowering::{HirTyLowerer, PredicateFilter, RegionInferReason};

/// This query collects supertraits that should be implicitly `impl`ed
/// within the context of a subtrait `impl`.
/// In doing so, this subtrait may authorise the compiler to generate `impl`s
/// on marker supertraits.
/// This query also reports this authorisation in the second components.
pub(super) fn supertrait_auto_impls<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_def_id: LocalDefId,
) -> ty::EarlyBinder<'tcx, &'tcx [(ty::Clause<'tcx>, hir::TraitRefSource)]> {
    let Node::Item(item) = tcx.hir_node_by_def_id(trait_def_id) else {
        bug!("trait_def_id {trait_def_id:?} is not an item");
    };
    if !tcx.has_attr(trait_def_id, rustc_supertrait_in_subtrait_impl) {
        return ty::EarlyBinder::bind(&[]);
    }

    let superbounds = match item.kind {
        hir::ItemKind::Trait(_, _, _, _, supertraits, _)
        | hir::ItemKind::TraitAlias(_, _, supertraits) => supertraits,
        _ => span_bug!(item.span, "supertrait_auto_impls invoked on non-trait"),
    };

    let icx = ItemCtxt::new(tcx, trait_def_id);

    let self_param_ty = tcx.types.self_param;
    let mut bounds = vec![];
    icx.lowerer().lower_supertrait_auto_impls(self_param_ty, superbounds, &mut bounds);
    ty::EarlyBinder::bind(&*tcx.arena.alloc_from_iter(bounds))
}

/// This query collects proper, non-marker supertraits in local subtrait `impl` blocks
pub(super) fn supertraits_in_local_subtrait_impls<'tcx>(
    tcx: TyCtxt<'tcx>,
    _: (),
) -> &'tcx (DefIdMap<Vec<LocalDefId>>, DefIdMap<LocalDefId>) {
    let mut supertrait_impls_map = DefIdMap::default();
    let mut supertrait_item_container = DefIdMap::default();
    for (trait_did, impls) in tcx.all_local_trait_impls(()) {
        if impls.is_empty() {
            continue;
        }
        supertraits_in_local_subtrait_impls_inner(
            tcx,
            *trait_did,
            impls,
            &mut supertrait_impls_map,
            &mut supertrait_item_container,
        );
    }
    tcx.arena.alloc((supertrait_impls_map, supertrait_item_container))
}

fn supertraits_in_local_subtrait_impls_inner<'tcx>(
    tcx: TyCtxt<'tcx>,
    subtrait: DefId,
    impls: &[LocalDefId],
    supertrait_impls_map: &mut DefIdMap<Vec<LocalDefId>>,
    supertrait_item_container: &mut DefIdMap<LocalDefId>,
) {
    let supertraits = tcx.supertrait_auto_impls(subtrait);
    if supertraits.skip_binder().is_empty() {
        return;
    }
    let mut supertrait_dids: UnordMap<_, SmallVec<[_; 1]>> = Default::default();
    let mut auto_impls: UnordMap<_, SmallVec<[_; 1]>> = Default::default();
    for (predicate, source) in
        supertraits.skip_binder().iter().filter_map(|(c, s)| c.as_trait_clause().map(|p| (p, *s)))
    {
        match source {
            TraitRefSource::Supertrait => {
                let did = predicate.def_id();
                if tcx.associated_items(did).len() > 0 {
                    supertrait_dids.entry(did).or_default().push(predicate);
                }
            }
            TraitRefSource::SupertraitAutoImpl => {
                auto_impls.entry(predicate.def_id()).or_default().push(predicate);
            }
            TraitRefSource::Any => span_bug!(
                tcx.def_span(subtrait),
                "supertrait_auto_impls query collect a trait predicate {predicate:?} that is not qualified for supertrait",
            ),
        }
    }

    let impls: SmallVec<[_; 4]> = impls
        .iter()
        .filter_map(|&did| {
            let header = tcx.impl_trait_header(did)?;
            let tref = header.trait_ref.instantiate_identity();
            if tref.references_error() { None } else { Some((did, tref, tcx.hir_expect_item(did))) }
        })
        .collect();
    for &(impl_did, subtrait_ref, item) in &impls {
        match item.kind {
            hir::ItemKind::Impl(&hir::Impl {
                polarity: hir::ImplPolarity::Positive,
                safety,
                items: _,
                of_trait: _,
                generics,
                constness: _,
                defaultness: _,
                defaultness_span: _,
                self_ty: subtrait_hir_self_ty,
            }) => {
                let is_safe = matches!(safety, hir::Safety::Safe);
                // FIXME: so far we assume that an item only goes to the first discovered owning supertrait,
                // without checking against the supertrait args, in case they are generic.
                // This is fine for non-generic traits like `Receiver` but it will reject impls unnecessarily
                // when two supertraits of same definition but with different arguments are present.
                let mut mentioned_supertrait_dids: FxIndexMap<_, SmallVec<[_; 4]>> =
                    Default::default();
                let impl_item_refs = tcx.associated_item_def_ids(impl_did);
                for &item_did in impl_item_refs {
                    let assoc_item = tcx.associated_item(item_did);
                    let hir::Node::ImplItem(&hir::ImplItem { owner_id, .. }) =
                        tcx.hir_node_by_def_id(item_did.expect_local())
                    else {
                        bug!()
                    };
                    debug!(?assoc_item);
                    let Some(assoc_item_did) = assoc_item.trait_item_def_id else { continue };
                    if assoc_item_did == subtrait {
                        continue;
                    }
                    let trait_did = tcx.parent(assoc_item_did);
                    debug!("{trait_did:?} owns {assoc_item_did:?}");
                    mentioned_supertrait_dids
                        .entry(trait_did)
                        .or_default()
                        .push((item_did, owner_id));
                }
                if mentioned_supertrait_dids.is_empty() {
                    continue;
                }
                let mut supertrait_refs = FxIndexSet::default();
                let mut marker_supertrait_refs = FxIndexSet::default();
                supertrait_instantiate_rec(
                    tcx,
                    subtrait_ref,
                    &mut supertrait_refs,
                    &mut marker_supertrait_refs,
                );
                debug!(?supertrait_refs);
                debug!(?marker_supertrait_refs);
                debug!(?mentioned_supertrait_dids);
                let self_type = tcx.type_of(impl_did);
                for super_tref in supertrait_refs {
                    let supertrait_did = super_tref.def_id;
                    let supertrait_def = tcx.trait_def(supertrait_did);
                    let Some(impl_items) = mentioned_supertrait_dids.get_mut(&supertrait_did)
                    else {
                        continue;
                    };
                    if supertrait_def.safety.is_unsafe() && is_safe {
                        struct_span_code_err!(
                            tcx.dcx(),
                            tcx.def_span(impl_items[0].0),
                            rustc_errors::E0200,
                            "the trait `{}` requires an `unsafe impl` declaration",
                            super_tref.print_trait_sugared()
                        )
                        .with_span_suggestion_verbose(
                            item.span.shrink_to_lo(),
                            "add `unsafe` to this trait implementation",
                            "unsafe ",
                            rustc_errors::Applicability::MaybeIncorrect,
                        )
                        .emit();
                        continue;
                    }
                    let feed = tcx.create_def(
                        impl_did,
                        None,
                        DefKind::Impl { of_trait: true },
                        None,
                        &mut DisambiguatorState::new(),
                    );
                    feed.defaultness(hir::Defaultness::Final);
                    feed.def_span(tcx.def_span(impl_did));
                    feed.param_env(tcx.param_env(impl_did));
                    feed.generics_of(tcx.generics_of(impl_did).clone());
                    feed.explicit_predicates_of(tcx.explicit_predicates_of(impl_did));
                    feed.type_of(self_type);
                    // This is where it is meant that no items are not binned to the specific supertrait,
                    // in case the supertrait is actually generic.
                    let (collected_items, owners): (SmallVec<[_; 2]>, SmallVec<[_; 2]>) =
                        impl_items.drain(..).unzip();
                    debug!(?owners);
                    let collected_items = tcx.arena.alloc_from_iter(collected_items);
                    feed.associated_item_def_ids(collected_items);
                    feed.feed_hir_item(
                        tcx.arena.alloc(hir::Impl {
                            constness: hir::Constness::NotConst,
                            safety: supertrait_def.safety,
                            polarity: hir::ImplPolarity::Positive,
                            defaultness: hir::Defaultness::Final,
                            defaultness_span: None,
                            generics,
                            of_trait: Some(hir::TraitRef {
                                path: tcx.arena.alloc(hir::Path {
                                    span: tcx.def_span(super_tref.def_id),
                                    res: hir::def::Res::Def(
                                        tcx.def_kind(super_tref.def_id),
                                        super_tref.def_id,
                                    ),
                                    segments: tcx.arena.alloc_from_iter([hir::PathSegment {
                                        ident: todo!(),
                                        hir_id: todo!(),
                                        res: todo!(),
                                        args: todo!(),
                                        infer_args: todo!(),
                                    }]),
                                }),
                                hir_ref_id: todo!(),
                            }),
                            self_ty: subtrait_hir_self_ty,
                            items: tcx.arena.alloc_from_iter(
                                owners.into_iter().map(|owner_id| hir::ImplItemId { owner_id }),
                            ),
                        }),
                        item.span,
                    );
                    feed.impl_trait_header(Some(ty::ImplTraitHeader {
                        trait_ref: ty::EarlyBinder::bind(super_tref),
                        polarity: ty::ImplPolarity::Positive,
                        safety: supertrait_def.safety,
                        constness: hir::Constness::NotConst,
                    }));
                    let supertrait_impl_local_did = feed.def_id();
                    debug!(?supertrait_impl_local_did);
                    for &item in &*collected_items {
                        assert!(
                            supertrait_item_container
                                .insert(item, supertrait_impl_local_did)
                                .is_none()
                        );
                    }
                    supertrait_impls_map
                        .entry(super_tref.def_id)
                        .or_default()
                        .push(supertrait_impl_local_did);
                }
            }
            hir::ItemKind::TraitAlias(_ident, _generics, _generic_bounds) => {
                // FIXME: we would like to account items here
            }
            _ => {}
        }
    }
}

// We have to collect all supertraits in the hierarchy,
// because an item might below to a supertrait deep in the tree.
#[instrument(level = "debug", skip_all, fields(?trait_ref))]
fn supertrait_instantiate_rec<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
    supertrait_refs: &mut FxIndexSet<ty::TraitRef<'tcx>>,
    marker_supertrait_refs: &mut FxIndexSet<ty::TraitRef<'tcx>>,
) {
    for supertrait_clause in tcx.supertrait_auto_impls(trait_ref.def_id).transpose_iter() {
        let source = supertrait_clause.skip_binder().1;
        let clause =
            supertrait_clause.map_bound(|&(clause, _)| clause).instantiate(tcx, trait_ref.args);
        debug!(?clause);
        let Some(predicate) = clause.as_trait_clause() else { continue };
        let did = predicate.def_id();
        let Some(predicate) = predicate.no_bound_vars() else {
            bug!("supertrait clause {clause:?} is not fully instantiated")
        };
        if matches!(predicate.polarity, ty::PredicatePolarity::Negative) {
            continue;
        }
        match source {
            TraitRefSource::Supertrait => {
                if tcx.associated_items(did).len() > 0
                    && supertrait_refs.insert(predicate.trait_ref)
                {
                    supertrait_instantiate_rec(
                        tcx,
                        predicate.trait_ref,
                        supertrait_refs,
                        marker_supertrait_refs,
                    );
                }
            }
            TraitRefSource::SupertraitAutoImpl => {
                if tcx.associated_items(did).len() > 0 {
                    tcx.dcx().emit_err(crate::errors::AutoImplSupertraitIsNotMarker {
                        span: tcx.def_span(trait_ref.def_id),
                        supertrait: tcx.item_name(did),
                    });
                } else if marker_supertrait_refs.insert(predicate.trait_ref) {
                    supertrait_instantiate_rec(
                        tcx,
                        predicate.trait_ref,
                        supertrait_refs,
                        marker_supertrait_refs,
                    );
                }
            }
            TraitRefSource::Any => {}
        }
    }
}
