//! Backend Coroutine Shims and Transformations (`-Zbackend-coroutines`)
//!
//! This module implements the middle-end MIR transformations required when lowering Rust coroutines
//! (`async`, `gen`, `async gen`, and closures/coroutines) to LLVM retcon (`retcon` / `retcon.once`)
//! continuations (`-Zbackend-coroutines`).
//!
//! Under retcon lowering, instead of transforming coroutines into explicit `enum` state machines with
//! integer discriminants, the coroutine state is represented as an aggregate struct containing its
//! captured upvars (`0..upvar_count`) and an internal continuation function pointer (`cont_field_idx`)
//! at struct field index `upvar_count`.
//!
//! To bridge the gap between Rust's high-level trait ABIs (`Coroutine::resume`, `Future::poll`, `Drop::drop`,
//! and `AsyncDrop::async_drop_in_place`) and the low-level LLVM retcon intrinsic (`@llvm.coro.suspend.retcon`),
//! this module synthesizes four primary types of compiler-generated MIR shims across each coroutine:
//!
//! 1. **Ramp Function (`transform_into_ramp_function`)**:
//!    Synthesizes the outer entry point (`Coroutine::resume` or `Future::poll`) that initializes the coroutine
//!    struct, invokes the initial resume continuation (`resume.0`), updates the continuation pointer in
//!    `cont_field_idx`, and returns `Poll::Ready` / `Poll::Pending` (or `CoroutineState`).
//!
//! 2. **Resume Shim (`transform_into_resume_shim`)**:
//!    Synthesizes the ABI-compliant retcon continuation function that corresponds to `.resume.0` stored inside
//!    `cont_field_idx`. It enforces the 5-argument retcon C-ABI (`buffer, is_cleanup, cx, yield_out, ret_out`)
//!    and coordinates state transitions, liveness across `.await` / `yield` points, and early returns upon completion.
//!
//! 3. **Sync Drop Shim (`transform_into_drop_shim`)**:
//!    Synthesizes the synchronous destructor (`Drop::drop(&mut self) -> ()`). It checks whether `cont_field_idx`
//!    is `null` (`0`). If non-null (`coroutine suspended or unresumed`), it enters cleanup mode, invoking the
//!    retcon continuation with `is_cleanup = true` (`or dropping upvars via insert_clean_drop`).
//!
//! 4. **Backend Coroutine Body (`transform_backend_coroutine`)**:
//!    Coordinates the transformation of locals, projection elements, and yield/return terminators across the
//!    coroutine body right before pass execution, mapping local accesses `_N` to aggregate projections `(*_1).field`.
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::{CoroutineDesugaring, CoroutineKind};
use rustc_index::IndexVec;
use rustc_middle::bug;
use rustc_middle::mir::visit::{MutVisitor, PlaceContext};
use rustc_middle::mir::*;
use rustc_middle::ty::{self, CoroutineArgsExt, Ty, TyCtxt};

use crate::patch::MirPatch;

// We need a SELF_ARG locally just like in mod.rs or layout.rs
const SELF_ARG: Local = Local::from_u32(1);

pub(crate) fn transform_backend_coroutine<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    remap: IndexVec<Local, Option<(Ty<'tcx>, VariantIdx, FieldIdx)>>,
    layout: CoroutineLayout<'tcx>,
    coroutine_ty: Ty<'tcx>,
) {
    // Lower locals by mapping them to `_1.N`.
    // Also rewrites Yield value to be `_0` and assigns `_0 = CoroutineState::Yielded(val)`.
    let mut visitor =
        BackendTransformVisitor { tcx, remap, patch: crate::patch::MirPatch::new(body) };
    visitor.visit_body(body);
    visitor.patch.apply(body);

    let coroutine_kind = body.coroutine_kind().unwrap();

    let source_info = SourceInfo::outermost(body.span);
    let args_iter = body.args_iter();
    let is_coro_trait = matches!(coroutine_kind, rustc_hir::CoroutineKind::Coroutine(_));
    let mut prologue_stmts: Vec<Statement<'tcx>> = args_iter
        .filter_map(|local| {
            let (ty, variant_index, idx) = visitor.remap.get(local)?.as_ref()?;
            let lhs = make_field(tcx, *variant_index, *idx, *ty);
            let rhs = if is_coro_trait || local == Local::from_usize(2) {
                Rvalue::Use(Operand::Copy(local.into()), WithRetag::Yes)
            } else {
                let field_idx = if tcx.sess.opts.unstable_opts.backend_coroutines {
                    FieldIdx::from_usize(local.index() - 3)
                } else {
                    FieldIdx::from_usize(local.index() - 2)
                };
                let upvar_place = Place {
                    local: Local::from_u32(1),
                    projection: tcx.mk_place_elems(&[ProjectionElem::Field(field_idx, *ty)]),
                };
                Rvalue::Use(Operand::Copy(upvar_place), WithRetag::No)
            };
            let assign = StatementKind::Assign(Box::new((lhs, rhs)));
            Some(Statement::new(source_info, assign))
        })
        .collect();

    let original_stmts = &mut body.basic_blocks_mut()[START_BLOCK].statements;
    prologue_stmts.append(original_stmts);
    *original_stmts = prologue_stmts;

    // Stash the original body as the Ramp function and Drop shim.
    let mut resume_shim = body.clone();
    resume_shim.mentioned_items = None;
    resume_shim.phase = body.phase;
    let mut drop_shim = body.clone();
    drop_shim.mentioned_items = None;
    drop_shim.phase = body.phase;

    // Update Resume Shim body to act as the continuation function for the retcon coroutine.
    transform_into_resume_shim(tcx, &mut resume_shim, &visitor.remap);
    crate::pass_manager::run_passes_no_validate(
        tcx,
        &mut resume_shim,
        &[&crate::simplify::SimplifyCfg::MakeShim, &crate::mentioned_items::MentionedItems],
        None,
    );

    // Overwrite the original body with the Ramp Function.
    // This allows `Coroutine::resume` trait calls to resolve to the Ramp Function.
    transform_into_ramp_function(tcx, body, coroutine_ty, coroutine_kind);

    body.coroutine.as_mut().unwrap().coroutine_ramp = Some(resume_shim);
    body.coroutine.as_mut().unwrap().coroutine_layout = Some(layout);

    // Create a real drop shim
    transform_into_drop_shim(tcx, &mut drop_shim, coroutine_ty);
    crate::pass_manager::run_passes_no_validate(
        tcx,
        &mut drop_shim,
        &[&crate::simplify::SimplifyCfg::MakeShim, &crate::mentioned_items::MentionedItems],
        None,
    );
    body.coroutine.as_mut().unwrap().coroutine_drop = Some(drop_shim);

    let proxy_shim = super::drop::create_coroutine_drop_shim_proxy_async(tcx, body, coroutine_kind);
    body.coroutine.as_mut().unwrap().coroutine_drop_proxy_async = Some(proxy_shim);
}

struct BackendTransformVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    remap: IndexVec<Local, Option<(Ty<'tcx>, VariantIdx, FieldIdx)>>,
    patch: crate::patch::MirPatch<'tcx>,
}

impl<'tcx> MutVisitor<'tcx> for BackendTransformVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn process_projection_elem(
        &mut self,
        elem: PlaceElem<'tcx>,
        location: Location,
    ) -> Option<PlaceElem<'tcx>> {
        match elem {
            PlaceElem::Index(local) => {
                if let Some(&Some((ty, variant, idx))) = self.remap.get(local) {
                    let field = make_field(self.tcx, variant, idx, ty);
                    self.patch.add_assign(
                        location,
                        Place::from(local),
                        Rvalue::Use(Operand::Copy(field), WithRetag::No),
                    );
                }
                None
            }
            PlaceElem::Field(..)
            | PlaceElem::OpaqueCast(..)
            | PlaceElem::UnwrapUnsafeBinder(..)
            | PlaceElem::Deref
            | PlaceElem::ConstantIndex { .. }
            | PlaceElem::Subslice { .. }
            | PlaceElem::Downcast(..) => None,
        }
    }

    fn visit_local(&mut self, local: &mut Local, _: PlaceContext, _location: Location) {
        assert!(*local == RETURN_PLACE || self.remap.get(*local).unwrap_or(&None).is_none());
    }

    fn visit_place(&mut self, place: &mut Place<'tcx>, _: PlaceContext, location: Location) {
        // Replace a Local in the remap with a coroutine struct access
        if let Some(&Some((ty, variant_index, idx))) = self.remap.get(place.local) {
            crate::coroutine::replace_base(
                place,
                make_field(self.tcx, variant_index, idx, ty),
                self.tcx,
            );
        }
        if let Some(new_projection) = self.process_projection(&place.projection, location) {
            place.projection = self.tcx.mk_place_elems(&new_projection);
        }
    }

    fn visit_statement(&mut self, stmt: &mut Statement<'tcx>, location: Location) {
        // Remove StorageLive and StorageDead statements for remapped locals
        if let StatementKind::StorageLive(l) | StatementKind::StorageDead(l) = stmt.kind
            && self.remap.get(l).unwrap_or(&None).is_some()
        {
            stmt.make_nop(true);
        }
        self.super_statement(stmt, location);
    }

    fn visit_terminator(&mut self, terminator: &mut Terminator<'tcx>, location: Location) {
        // Remove drop(self) from the coroutine body because the Ramp function
        // does not own the coroutine struct (it only operates on a pointer to it).
        // Leaving drop(self) would cause infinite recursion with the Drop Shim.
        if let TerminatorKind::Drop { place, target, .. } = terminator.kind {
            if place.local == SELF_ARG && place.projection.is_empty() {
                terminator.kind = TerminatorKind::Goto { target };
                return;
            }
        }
        self.super_terminator(terminator, location);
    }

    fn visit_basic_block_data(&mut self, block: BasicBlock, data: &mut BasicBlockData<'tcx>) {
        self.super_basic_block_data(block, data);
    }
}

// Create a Place referencing a coroutine struct field
fn make_field<'tcx>(
    tcx: TyCtxt<'tcx>,
    variant_index: VariantIdx,
    idx: FieldIdx,
    ty: Ty<'tcx>,
) -> Place<'tcx> {
    let self_place = Place::from(SELF_ARG);
    let base = tcx.mk_place_downcast_unnamed(self_place, variant_index);
    let mut projection = base.projection.to_vec();
    projection.push(ProjectionElem::Field(idx, ty));

    Place { local: base.local, projection: tcx.mk_place_elems(&projection) }
}

pub(crate) fn transform_into_resume_shim<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    remap: &IndexVec<Local, Option<(Ty<'tcx>, VariantIdx, FieldIdx)>>,
) {
    let span = body.span;
    let old_arg_count = body.arg_count;
    let old_ret_ty = body.return_ty();
    let old_yield_ty = body.yield_ty().unwrap_or(tcx.types.unit);

    let resume_ty =
        if old_arg_count == 2 { body.local_decls[Local::from_usize(2)].ty } else { tcx.types.unit };

    let coroutine_ty = body.local_decls[Local::from_usize(1)].ty;
    let mut_ptr_coro_ty = Ty::new_mut_ptr(tcx, coroutine_ty);

    let const_u8_ptr = Ty::new_mut_ptr(tcx, tcx.types.u8);
    let mut_ptr_resume_ty = Ty::new_mut_ptr(tcx, resume_ty);
    let mut_ptr_yield_ty = Ty::new_mut_ptr(tcx, old_yield_ty);
    let mut_ptr_return_ty = Ty::new_mut_ptr(tcx, old_ret_ty);

    body.var_debug_info.clear();
    for block in body.basic_blocks_mut().iter_mut() {
        for stmt in block.statements.iter_mut() {
            stmt.debuginfos.drop_debuginfo();
        }
        block.after_last_stmt_debuginfos.drop_debuginfo();
    }

    // 1. Ensure local_decls has slots _0..=_6 reserved for the prototype arguments FIRST.
    //    The retcon continuation prototype requires slots _0..=_6:
    //    _0: return place (*mut u8)
    //    _1: buffer (*mut u8)
    //    _2: is_unwind (bool)
    //    _3: resume_arg (*mut ResumeTy)
    //    _4: yield_out (*mut YieldTy)
    //    _5: return_out (*mut ReturnTy)
    //    _6: coro_ptr (*mut Coroutine)
    const NUM_RETCON_PROTOTYPE_LOCALS: usize = 7;
    let orig_len = body.local_decls.len();

    while body.local_decls.len() < NUM_RETCON_PROTOTYPE_LOCALS {
        body.local_decls.push(LocalDecl::new(tcx.types.unit, span));
    }

    // Now any pushed clone is guaranteed to land at index >= NUM_RETCON_PROTOTYPE_LOCALS (>= 7).
    let mut local_rename_map: FxHashMap<Local, Local> = FxHashMap::default();
    for i in 0..std::cmp::min(NUM_RETCON_PROTOTYPE_LOCALS, orig_len) {
        let old_local = Local::from_usize(i);
        let new_local = body.local_decls.push(body.local_decls[old_local].clone());
        local_rename_map.insert(old_local, new_local);
    }

    struct Renamer<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        local_rename_map: &'a FxHashMap<Local, Local>,
    }
    impl<'tcx, 'a> MutVisitor<'tcx> for Renamer<'a, 'tcx> {
        fn tcx(&self) -> TyCtxt<'tcx> {
            self.tcx
        }
        fn visit_local(&mut self, local: &mut Local, _context: PlaceContext, _location: Location) {
            if let Some(&new_local) = self.local_rename_map.get(local) {
                *local = new_local;
            }
        }

        fn visit_terminator(&mut self, terminator: &mut Terminator<'tcx>, location: Location) {
            if let TerminatorKind::Return = terminator.kind {
                self.visit_source_info(&mut terminator.source_info);
                return;
            }
            self.super_terminator(terminator, location);
        }
    }
    Renamer { tcx, local_rename_map: &local_rename_map }.visit_body(body);

    // 2. Define the new retcon continuation arguments
    let retcon_return_place = RETURN_PLACE; // _0
    let retcon_buffer_arg = Local::COROUTINE_ARG_BUFFER; // _1
    let retcon_is_unwind_arg = Local::COROUTINE_ARG_DROP; // _2
    let retcon_resume_ptr_arg = Local::COROUTINE_ARG_RESUME; // _3
    let retcon_yield_ptr_arg = Local::COROUTINE_ARG_YIELD; // _4
    let retcon_return_ptr_arg = Local::COROUTINE_ARG_RETURN; // _5
    let retcon_coro_ptr_arg = Local::from_usize(6); // _6

    body.local_decls[retcon_return_place].ty = const_u8_ptr;
    body.local_decls[retcon_buffer_arg].ty = const_u8_ptr;
    body.local_decls[retcon_is_unwind_arg].ty = tcx.types.bool;
    body.local_decls[retcon_resume_ptr_arg].ty = mut_ptr_resume_ty;
    body.local_decls[retcon_yield_ptr_arg].ty = mut_ptr_yield_ty;
    body.local_decls[retcon_return_ptr_arg].ty = mut_ptr_return_ty;
    body.local_decls[retcon_coro_ptr_arg].ty = mut_ptr_coro_ty;
    body.arg_count = 5;

    let saved_local_1 = *local_rename_map
        .get(&Local::from_usize(1))
        .expect("coroutine body must have self argument _1");
    let saved_local_0 = *local_rename_map
        .get(&Local::from_usize(0))
        .expect("coroutine body must have return place _0");

    let local_is_dropping = body.local_decls.push(LocalDecl::new(tcx.types.bool, span));

    let init_stmts = vec![Statement::new(
        SourceInfo::outermost(span),
        StatementKind::Assign(Box::new((
            Place::from(retcon_coro_ptr_arg),
            Rvalue::Cast(
                CastKind::PtrToPtr,
                Operand::Copy(Place::from(retcon_buffer_arg)),
                mut_ptr_coro_ty,
            ),
        ))),
    )];

    let saved_local_1_ty = body.local_decls[saved_local_1].ty;
    BackendAccessReplacementVisitor {
        tcx,
        saved_local_1,
        local_coro_ptr: retcon_coro_ptr_arg,
        saved_local_1_ty,
    }
    .visit_body(body);

    let source_info = SourceInfo::outermost(span);

    // Collect blocks
    let mut yields = vec![];
    let mut returns = vec![];
    let mut resumes = vec![];
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if let Some(terminator) = &data.terminator {
            match terminator.kind {
                TerminatorKind::Yield { ref value, resume, resume_arg, drop } => {
                    yields.push((bb, value.clone(), resume, resume_arg, drop));
                }
                TerminatorKind::Return => {
                    returns.push(bb);
                }
                TerminatorKind::UnwindResume => {
                    resumes.push(bb);
                }
                _ => {}
            }
        }
    }

    // Constant operand representing `0 as usize`, used to cast into `null` pointers (`0 as *mut u8`)
    // when zeroing continuation function pointers and return places upon coroutine completion.
    let const_zero_operand = Operand::Constant(Box::new(ConstOperand {
        span,
        user_ty: None,
        const_: Const::from_usize(tcx, 0),
    }));

    let args = match coroutine_ty.kind() {
        ty::Coroutine(_, args) => args,
        _ => bug!("expected coroutine type, found {:?}", coroutine_ty),
    };
    let cont_field_idx = FieldIdx::from_usize(args.as_coroutine().upvar_tys().len());

    // Statement assigning `null` (`0`) to `(*_1).field[cont_field_idx]` (`continuation function pointer`).
    // When a retcon coroutine finishes normal execution or completes drop/cleanup (`BB_RETURN / CoroutineDrop`),
    // we set `cont_field_idx` to `null` (`0 as *mut u8`) to mark the state machine as terminated and completed (`Poll::Ready`).
    let zero_cont_ptr_stmt = Statement::new(
        source_info,
        // `((*retcon_coro_ptr_arg).field[cont_field_idx]: *mut u8) = 0 as *mut u8`
        StatementKind::Assign(Box::new((
            Place {
                local: retcon_coro_ptr_arg,
                projection: tcx.mk_place_elems(&[
                    ProjectionElem::Deref,
                    ProjectionElem::Field(cont_field_idx, const_u8_ptr),
                ]),
            },
            Rvalue::Cast(
                rustc_middle::mir::CastKind::PointerWithExposedProvenance,
                const_zero_operand.clone(),
                const_u8_ptr,
            ),
        ))),
    );

    // Statement assigning discriminant `1` (`Returned`) to `(*_1)` (`the coroutine struct place`).
    // Under standard rules (`ty::Coroutine`), variant 0 is `Unresumed` and variant 1 is `Returned`.
    // Even though retcon coroutines (`backend_coroutines`) use `cont_field_idx == null` for dynamic completion checks
    // across shims and drop ladders, keeping `(*_1).discriminant = 1` (`Returned`) synchronized when execution finishes
    // ensures consistency across standard `coroutine_kind` queries and completion state inspection.
    let set_returned_discriminant_stmt = Statement::new(
        source_info,
        StatementKind::SetDiscriminant {
            place: Box::new(tcx.mk_place_deref(Place::from(retcon_coro_ptr_arg))),
            variant_index: rustc_abi::VariantIdx::from_usize(1), // Returned
        },
    );

    let coroutine_drop_bb_normal = body.basic_blocks_mut().push(BasicBlockData::new_stmts(
        vec![
            zero_cont_ptr_stmt.clone(),
            set_returned_discriminant_stmt.clone(),
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(RETURN_PLACE),
                    Rvalue::Cast(
                        rustc_middle::mir::CastKind::PointerWithExposedProvenance,
                        const_zero_operand.clone(),
                        const_u8_ptr,
                    ),
                ))),
            ),
        ],
        Some(Terminator {
            source_info,
            kind: TerminatorKind::CoroutineDrop,
            attributes: Default::default(),
        }),
        false,
    ));

    let coroutine_drop_bb_cleanup = body.basic_blocks_mut().push(BasicBlockData::new_stmts(
        vec![
            zero_cont_ptr_stmt.clone(),
            set_returned_discriminant_stmt.clone(),
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(RETURN_PLACE),
                    Rvalue::Cast(
                        rustc_middle::mir::CastKind::PointerWithExposedProvenance,
                        const_zero_operand.clone(),
                        const_u8_ptr,
                    ),
                ))),
            ),
        ],
        Some(Terminator {
            source_info,
            kind: TerminatorKind::CoroutineDrop,
            attributes: Default::default(),
        }),
        true,
    ));

    // 6. Update Yields
    for (yield_idx, &(bb, ref value, resume, resume_arg, drop)) in yields.iter().enumerate() {
        let source_info = body.basic_blocks[bb].terminator().source_info;

        let assign_yield = StatementKind::Assign(Box::new((
            tcx.mk_place_deref(Place::from(retcon_yield_ptr_arg)),
            Rvalue::Use(value.clone(), rustc_middle::mir::WithRetag::No),
        )));
        body.basic_blocks_mut()[bb].statements.push(Statement::new(source_info, assign_yield));

        // Set discriminant for DWARF DW_TAG_variant_part debugger inspection.
        // LLVM CoroSplitPass handles control flow dispatch independently;
        // this only affects which saved locals debuggers show as in-scope.
        let set_disc = StatementKind::SetDiscriminant {
            place: Box::new(tcx.mk_place_deref(Place::from(retcon_coro_ptr_arg))),
            variant_index: rustc_abi::VariantIdx::from_usize(3 + yield_idx),
        };
        body.basic_blocks_mut()[bb].statements.push(Statement::new(source_info, set_disc));

        let assign_resume_arg = StatementKind::Assign(Box::new((
            resume_arg,
            Rvalue::Use(
                Operand::Move(tcx.mk_place_deref(Place::from(retcon_resume_ptr_arg))),
                rustc_middle::mir::WithRetag::No,
            ),
        )));
        body.basic_blocks_mut()[resume]
            .statements
            .insert(0, Statement::new(source_info, assign_resume_arg));

        let assign_coro_ptr = StatementKind::Assign(Box::new((
            Place::from(retcon_coro_ptr_arg),
            Rvalue::Cast(
                rustc_middle::mir::CastKind::PtrToPtr,
                Operand::Copy(Place::from(retcon_buffer_arg)),
                mut_ptr_coro_ty,
            ),
        )));
        body.basic_blocks_mut()[resume]
            .statements
            .insert(0, Statement::new(source_info, assign_coro_ptr));

        if let Some(old_drop) = drop {
            let true_bool = Operand::Constant(Box::new(ConstOperand {
                span,
                user_ty: None,
                const_: rustc_middle::mir::Const::from_bool(tcx, true),
            }));
            let old_is_cleanup = body.basic_blocks[old_drop].is_cleanup;
            let yield_drop_bb = body.basic_blocks_mut().push(BasicBlockData::new_stmts(
                vec![Statement::new(
                    source_info,
                    StatementKind::Assign(Box::new((
                        Place::from(local_is_dropping),
                        Rvalue::Use(true_bool, rustc_middle::mir::WithRetag::No),
                    ))),
                )],
                Some(Terminator {
                    source_info,
                    kind: TerminatorKind::Goto { target: old_drop },
                    attributes: Default::default(),
                }),
                old_is_cleanup,
            ));
            if let TerminatorKind::Yield { drop: ref mut d, .. } =
                body.basic_blocks_mut()[bb].terminator_mut().kind
            {
                *d = Some(yield_drop_bb);
            }
        }
    }

    // Separate post-yield blocks from pre-yield blocks so that post-yield return blocks
    // are strictly dominated by their yield points. This prevents RPO order inversion
    // and eliminates LLVM CoroSplit frame spilling of continuation arguments across yield points.
    let mut post_yield_blocks =
        rustc_index::bit_set::DenseBitSet::new_empty(body.basic_blocks.len());
    let mut worklist: Vec<BasicBlock> = yields.iter().map(|(_, _, resume, _, _)| *resume).collect();
    while let Some(bb) = worklist.pop() {
        if post_yield_blocks.insert(bb) {
            worklist.extend(body.basic_blocks[bb].terminator().successors());
        }
    }

    let num_orig_blocks = body.basic_blocks.len();
    let mut duplicated = IndexVec::from_elem_n(None, num_orig_blocks);
    for bb in post_yield_blocks.iter() {
        let has_pre_yield_pred = body.basic_blocks.iter_enumerated().any(|(pred, data)| {
            pred.as_usize() < num_orig_blocks
                && !post_yield_blocks.contains(pred)
                && data.terminator().successors().any(|s| s == bb)
        });
        if has_pre_yield_pred {
            let clone_data = body.basic_blocks[bb].clone();
            let clone_bb = body.basic_blocks_mut().push(clone_data);
            duplicated[bb] = Some(clone_bb);
        }
    }

    for bb in (0..num_orig_blocks).map(BasicBlock::from_usize) {
        if post_yield_blocks.contains(bb) || duplicated[bb].is_some() {
            let target_bb = duplicated[bb].unwrap_or(bb);
            body.basic_blocks_mut()[target_bb].terminator_mut().successors_mut(|succ| {
                if let Some(new_succ) = duplicated.get(*succ).copied().flatten() {
                    *succ = new_succ;
                }
            });
        }
    }

    let mut returns = vec![];
    let mut resumes = vec![];
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if let Some(terminator) = &data.terminator {
            match terminator.kind {
                TerminatorKind::Return => returns.push(bb),
                TerminatorKind::UnwindResume => resumes.push(bb),
                _ => {}
            }
        }
    }

    for &bb in &returns {
        let source_info = body.basic_blocks[bb].terminator().source_info;

        let return_place =
            if let Some(&Some((ty, variant_idx, field_idx))) = remap.get(RETURN_PLACE) {
                let base = Place::from(retcon_coro_ptr_arg);
                let deref = tcx.mk_place_deref(base);
                let downcast = tcx.mk_place_downcast_unnamed(deref, variant_idx);
                let mut projection = downcast.projection.to_vec();
                projection.push(ProjectionElem::Field(field_idx, ty));
                Place { local: downcast.local, projection: tcx.mk_place_elems(&projection) }
            } else {
                Place::from(saved_local_0)
            };

        let assign_ret = StatementKind::Assign(Box::new((
            tcx.mk_place_deref(Place::from(retcon_return_ptr_arg)),
            Rvalue::Use(Operand::Move(return_place), rustc_middle::mir::WithRetag::No),
        )));
        body.basic_blocks_mut()[bb].statements.push(Statement::new(source_info, assign_ret));

        let set_disc = StatementKind::SetDiscriminant {
            place: Box::new(tcx.mk_place_deref(Place::from(retcon_coro_ptr_arg))),
            variant_index: rustc_abi::VariantIdx::from_usize(1), // Returned
        };
        body.basic_blocks_mut()[bb].statements.push(Statement::new(source_info, set_disc));

        body.basic_blocks_mut()[bb].terminator_mut().kind =
            TerminatorKind::Goto { target: coroutine_drop_bb_normal };
    }

    for &bb in &resumes {
        let source_info = body.basic_blocks[bb].terminator().source_info;
        let actual_resume_bb = body.basic_blocks_mut().push(BasicBlockData::new_stmts(
            vec![],
            Some(Terminator {
                source_info,
                kind: TerminatorKind::UnwindResume,
                attributes: Default::default(),
            }),
            true,
        ));

        body.basic_blocks_mut()[bb].terminator_mut().kind = TerminatorKind::SwitchInt {
            discr: Operand::Copy(Place::from(retcon_is_unwind_arg)),
            targets: SwitchTargets::new(
                std::iter::once((1, coroutine_drop_bb_cleanup)),
                actual_resume_bb,
            ),
        };
    }

    // SPLIT START_BLOCK
    let old_start_data = std::mem::replace(
        &mut body.basic_blocks_mut()[START_BLOCK],
        BasicBlockData::new(None, false),
    );
    let actual_start_bb = body.basic_blocks_mut().push(old_start_data);

    let false_bool = Operand::Constant(Box::new(ConstOperand {
        span,
        user_ty: None,
        const_: rustc_middle::mir::Const::from_bool(tcx, false),
    }));
    body.basic_blocks_mut()[actual_start_bb].statements.insert(
        0,
        Statement::new(
            source_info,
            StatementKind::Assign(Box::new((
                Place::from(local_is_dropping),
                Rvalue::Use(false_bool, rustc_middle::mir::WithRetag::No),
            ))),
        ),
    );

    let discr_ty = args.as_coroutine().discr_ty(tcx);
    let discr_local = body.local_decls.push(LocalDecl::new(discr_ty, span));
    let proceed_bb = body.basic_blocks_mut().push(BasicBlockData::new_stmts(
        vec![Statement::new(
            source_info,
            StatementKind::Assign(Box::new((
                Place::from(discr_local),
                Rvalue::Discriminant(tcx.mk_place_deref(Place::from(retcon_coro_ptr_arg))),
            ))),
        )],
        Some(Terminator {
            source_info,
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from(discr_local)),
                targets: SwitchTargets::new(
                    std::iter::once((1, coroutine_drop_bb_normal)),
                    actual_start_bb,
                ),
            },
            attributes: Default::default(),
        }),
        false,
    ));

    body.basic_blocks_mut()[START_BLOCK].terminator = Some(Terminator {
        source_info,
        kind: TerminatorKind::SwitchInt {
            discr: Operand::Copy(Place::from(retcon_is_unwind_arg)),
            targets: SwitchTargets::new(std::iter::once((1, coroutine_drop_bb_normal)), proceed_bb),
        },
        attributes: Default::default(),
    });

    // Initialize old arguments from new argument pointers and prepend to BB0 using MirPatch
    let mut prologue = init_stmts;
    if old_arg_count == 2 {
        if let Some(&saved_local_2) = local_rename_map.get(&Local::from_usize(2)) {
            prologue.push(Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(saved_local_2),
                    Rvalue::Use(
                        Operand::Move(tcx.mk_place_deref(Place::from(retcon_resume_ptr_arg))),
                        rustc_middle::mir::WithRetag::No,
                    ),
                ))),
            ));
        }
    }

    let mut patch = MirPatch::new(body);
    let loc = Location { block: START_BLOCK, statement_index: 0 };
    for stmt in prologue.into_iter().rev() {
        patch.add_statement(loc, stmt.kind);
    }
    patch.apply(body);

    crate::deref_separator::deref_finder(tcx, body, false);
}

pub(crate) fn transform_into_ramp_function<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    coroutine_ty: Ty<'tcx>,
    coroutine_kind: CoroutineKind,
) {
    let span = body.span;
    let source_info = SourceInfo::outermost(span);
    let unwind_action = if tcx.sess.panic_strategy().unwinds() {
        UnwindAction::Continue
    } else {
        UnwindAction::Unreachable
    };

    let old_ret_ty = body.return_ty();
    let old_yield_ty = body.yield_ty().unwrap_or(tcx.types.unit);
    let resume_ty = body.local_decls[Local::from_usize(2)].ty;
    // 1. Compute new types
    let (state_adt_ref, state_args, ret_ty) = match coroutine_kind {
        CoroutineKind::Desugared(CoroutineDesugaring::Async, _) => {
            let poll_did = tcx.require_lang_item(rustc_hir::LangItem::Poll, span);
            let adt_ref = tcx.adt_def(poll_did);
            let args = tcx.mk_args(&[old_ret_ty.into()]);
            (adt_ref, args, Ty::new_adt(tcx, adt_ref, args))
        }
        CoroutineKind::Desugared(CoroutineDesugaring::Gen, _) => {
            let option_did = tcx.require_lang_item(rustc_hir::LangItem::Option, span);
            let adt_ref = tcx.adt_def(option_did);
            let args = tcx.mk_args(&[old_yield_ty.into()]);
            (adt_ref, args, Ty::new_adt(tcx, adt_ref, args))
        }
        CoroutineKind::Coroutine(_) => {
            let state_did = tcx.require_lang_item(rustc_hir::LangItem::CoroutineState, span);
            let adt_ref = tcx.adt_def(state_did);
            let args = tcx.mk_args(&[old_yield_ty.into(), old_ret_ty.into()]);
            (adt_ref, args, Ty::new_adt(tcx, adt_ref, args))
        }
        _ => bug!("unsupported coroutine kind for retcon: {:?}", coroutine_kind),
    };

    let ref_coroutine_ty = Ty::new_mut_ref(tcx, tcx.lifetimes.re_erased, coroutine_ty);
    let ty::Coroutine(_def_id, args) = *coroutine_ty.kind() else { unreachable!() };
    let cont_field_idx = FieldIdx::from_usize(args.as_coroutine().upvar_tys().len());
    let pin_did = tcx.require_lang_item(rustc_hir::LangItem::Pin, span);
    let pin_adt_ref = tcx.adt_def(pin_did);
    let pin_args = tcx.mk_args(&[ref_coroutine_ty.into()]);
    let pin_ref_coroutine_ty = Ty::new_adt(tcx, pin_adt_ref, pin_args);

    let maybe_uninit_did = tcx.require_lang_item(rustc_hir::LangItem::MaybeUninit, span);
    let maybe_uninit_adt_ref = tcx.adt_def(maybe_uninit_did);
    let yield_uninit_ty =
        Ty::new_adt(tcx, maybe_uninit_adt_ref, tcx.mk_args(&[old_yield_ty.into()]));
    let return_uninit_ty =
        Ty::new_adt(tcx, maybe_uninit_adt_ref, tcx.mk_args(&[old_ret_ty.into()]));

    let mut_ptr_yield_ty = Ty::new_mut_ptr(tcx, old_yield_ty);
    let mut_ptr_return_ty = Ty::new_mut_ptr(tcx, old_ret_ty);
    let mut_ptr_yield_uninit_ty = Ty::new_mut_ptr(tcx, yield_uninit_ty);
    let mut_ptr_return_uninit_ty = Ty::new_mut_ptr(tcx, return_uninit_ty);
    let const_u8_ptr = Ty::new_mut_ptr(tcx, tcx.types.u8);

    let mut_ptr_resume_ty = Ty::new_mut_ptr(tcx, resume_ty);
    let bool_ty = tcx.types.bool;
    let cont_fn_sig = tcx.mk_fn_sig(
        [const_u8_ptr, bool_ty, mut_ptr_resume_ty, mut_ptr_yield_ty, mut_ptr_return_ty],
        const_u8_ptr,
        rustc_middle::ty::FnSigKind::default().set_safety(rustc_hir::Safety::Unsafe),
    );
    let cont_fn_ptr_ty = Ty::new_fn_ptr(tcx, rustc_middle::ty::Binder::dummy(cont_fn_sig));

    // 2. Setup local declarations
    let mut local_decls = IndexVec::new();
    body.var_debug_info.clear();
    // _0: CoroutineState<YieldTy, ReturnTy>
    let local_ret = local_decls.push(LocalDecl::new(ret_ty, span));
    assert_eq!(local_ret, RETURN_PLACE);
    let arg_self = Local::from_usize(1);
    let arg_resume = Local::from_usize(2);

    // _1: Pin<&mut Coroutine>
    let local_self = local_decls.push(LocalDecl::new(pin_ref_coroutine_ty, span));
    assert_eq!(local_self, arg_self);

    // _2: ResumeTy
    let local_resume = local_decls.push(LocalDecl::new(resume_ty, span));
    assert_eq!(local_resume, arg_resume);

    // Locals for the shim
    let local_mut_coroutine = local_decls.push(LocalDecl::new(ref_coroutine_ty, span));
    let local_cont_ptr = local_decls.push(LocalDecl::new(const_u8_ptr, span));
    let local_yield_uninit = local_decls.push(LocalDecl::new(yield_uninit_ty, span));
    let local_return_uninit = local_decls.push(LocalDecl::new(return_uninit_ty, span));
    let local_mut_yield = local_decls.push(LocalDecl::new(mut_ptr_yield_ty, span));
    let local_mut_return = local_decls.push(LocalDecl::new(mut_ptr_return_ty, span));
    let local_fn_ptr = local_decls.push(LocalDecl::new(cont_fn_ptr_ty, span));
    let local_ret_cont_ptr = local_decls.push(LocalDecl::new(const_u8_ptr, span));
    let local_yield = local_decls.push(LocalDecl::new(old_yield_ty, span));
    let local_return = local_decls.push(LocalDecl::new(old_ret_ty, span));
    let local_mut_yield_uninit = local_decls.push(LocalDecl::new(mut_ptr_yield_uninit_ty, span));
    let local_mut_return_uninit = local_decls.push(LocalDecl::new(mut_ptr_return_uninit_ty, span));

    let local_null_ptr = local_decls.push(LocalDecl::new(const_u8_ptr, span));
    let mut_ptr_coro = Ty::new_mut_ptr(tcx, coroutine_ty);
    let local_mut_coro_ptr_ptr = local_decls.push(LocalDecl::new(mut_ptr_coro, span));
    let local_is_null = local_decls.push(LocalDecl::new(tcx.types.bool, span));
    let local_resume_ptr_uncast =
        local_decls.push(LocalDecl::new(Ty::new_mut_ptr(tcx, resume_ty), span));
    let local_resume_ptr = local_decls.push(LocalDecl::new(mut_ptr_resume_ty, span));

    let local_buffer_ptr = local_decls.push(LocalDecl::new(const_u8_ptr, span));

    // Helper for null pointer
    let null_usize_operand = Operand::Constant(Box::new(ConstOperand {
        span,
        user_ty: None,
        const_: Const::from_usize(tcx, 0),
    }));

    // Helper for false bool
    let false_bool_operand = Operand::Constant(Box::new(ConstOperand {
        span,
        user_ty: None,
        const_: rustc_middle::mir::Const::from_bool(tcx, false),
    }));

    // 3. Basic blocks
    let bb_setup = BasicBlock::from_usize(1);
    let bb_yield = BasicBlock::from_usize(2);
    let bb_yield_ret = BasicBlock::from_usize(3);
    let bb_complete = BasicBlock::from_usize(4);
    let bb_panic = BasicBlock::from_usize(5);
    let bb_return = BasicBlock::from_usize(6);

    let mut basic_blocks = IndexVec::new();

    // BB0: Load continuation pointer and check for null
    let mut bb0_stmts = vec![
        // _local_mut_coroutine = (_arg_self.0: &mut Coroutine)
        Statement::new(
            source_info,
            StatementKind::Assign(Box::new((
                Place::from(local_mut_coroutine),
                Rvalue::Use(
                    Operand::Copy(Place {
                        local: local_self,
                        projection: tcx.mk_place_elems(&[ProjectionElem::Field(
                            FieldIdx::from_usize(0),
                            ref_coroutine_ty,
                        )]),
                    }),
                    rustc_middle::mir::WithRetag::No,
                ),
            ))),
        ),
        // _local_mut_coro_ptr_ptr = &raw mut (*_local_mut_coroutine)
        Statement::new(
            source_info,
            StatementKind::Assign(Box::new((
                Place::from(local_mut_coro_ptr_ptr),
                Rvalue::RawPtr(
                    rustc_middle::mir::RawPtrKind::Mut,
                    Place {
                        local: local_mut_coroutine,
                        projection: tcx.mk_place_elems(&[ProjectionElem::Deref]),
                    },
                ),
            ))),
        ),
        // _local_buffer_ptr = _local_mut_coro_ptr_ptr as *mut u8
        Statement::new(
            source_info,
            StatementKind::Assign(Box::new((
                Place::from(local_buffer_ptr),
                Rvalue::Cast(
                    CastKind::PtrToPtr,
                    Operand::Copy(Place::from(local_mut_coro_ptr_ptr)),
                    const_u8_ptr,
                ),
            ))),
        ),
        // _local_cont_ptr = ((*_local_mut_coroutine).0: *mut u8)
        Statement::new(
            source_info,
            StatementKind::Assign(Box::new((
                Place::from(local_cont_ptr),
                Rvalue::Use(
                    Operand::Copy(Place {
                        local: local_mut_coroutine,
                        projection: tcx.mk_place_elems(&[
                            ProjectionElem::Deref,
                            ProjectionElem::Field(cont_field_idx, const_u8_ptr),
                        ]),
                    }),
                    rustc_middle::mir::WithRetag::No,
                ),
            ))),
        ),
    ];
    bb0_stmts.extend(vec![
        // _local_null_ptr = null
        Statement::new(
            source_info,
            StatementKind::Assign(Box::new((
                Place::from(local_null_ptr),
                Rvalue::Cast(
                    CastKind::PointerWithExposedProvenance,
                    null_usize_operand.clone(),
                    const_u8_ptr,
                ),
            ))),
        ),
        // _local_is_null = _local_cont_ptr == _local_null_ptr
        Statement::new(
            source_info,
            StatementKind::Assign(Box::new((
                Place::from(local_is_null),
                Rvalue::BinaryOp(
                    rustc_middle::mir::BinOp::Eq,
                    Box::new((
                        Operand::Copy(Place::from(local_cont_ptr)),
                        Operand::Copy(Place::from(local_null_ptr)),
                    )),
                ),
            ))),
        ),
    ]);
    let target_on_null = match coroutine_kind {
        // Async: re-poll after Ready returns Ready(()) again (idempotent completion).
        // Gen: re-poll after None returns None again (iterator exhaustion is idempotent).
        CoroutineKind::Desugared(CoroutineDesugaring::Async | CoroutineDesugaring::Gen, _) => {
            bb_complete
        }
        // Coroutine trait: re-poll after completion panics with "coroutine resumed after completion".
        _ => bb_panic,
    };
    basic_blocks.push(BasicBlockData::new_stmts(
        bb0_stmts,
        Some(Terminator {
            source_info,
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Move(Place::from(local_is_null)),
                targets: SwitchTargets::new(std::iter::once((1, target_on_null)), bb_setup),
            },
            attributes: Default::default(),
        }),
        false,
    ));

    // BB_SETUP: Allocate outputs and invoke
    basic_blocks.push(BasicBlockData::new_stmts(
        vec![
            // StorageLive for uninit blocks
            Statement::new(source_info, StatementKind::StorageLive(local_yield_uninit)),
            Statement::new(source_info, StatementKind::StorageLive(local_return_uninit)),
            // _local_mut_yield_uninit = &mut _local_yield_uninit
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_mut_yield_uninit),
                    Rvalue::RawPtr(
                        rustc_middle::mir::RawPtrKind::Mut,
                        Place::from(local_yield_uninit),
                    ),
                ))),
            ),
            // _local_mut_yield = _local_mut_yield_uninit as *mut YieldTy (PtrToPtr)
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_mut_yield),
                    Rvalue::Cast(
                        CastKind::PtrToPtr,
                        Operand::Copy(Place::from(local_mut_yield_uninit)),
                        mut_ptr_yield_ty,
                    ),
                ))),
            ),
            // _local_mut_return_uninit = &mut _local_return_uninit
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_mut_return_uninit),
                    Rvalue::RawPtr(
                        rustc_middle::mir::RawPtrKind::Mut,
                        Place::from(local_return_uninit),
                    ),
                ))),
            ),
            // _local_mut_return = _local_mut_return_uninit as *mut ReturnTy (PtrToPtr)
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_mut_return),
                    Rvalue::Cast(
                        CastKind::PtrToPtr,
                        Operand::Copy(Place::from(local_mut_return_uninit)),
                        mut_ptr_return_ty,
                    ),
                ))),
            ),
            // _local_resume_ptr_uncast = &raw mut _arg_resume
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_resume_ptr_uncast),
                    Rvalue::RawPtr(rustc_middle::mir::RawPtrKind::Mut, Place::from(local_resume)),
                ))),
            ),
            // _local_resume_ptr = _local_resume_ptr_uncast as *mut ResumeTy
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_resume_ptr),
                    Rvalue::Cast(
                        CastKind::PtrToPtr,
                        Operand::Copy(Place::from(local_resume_ptr_uncast)),
                        mut_ptr_resume_ty,
                    ),
                ))),
            ),
            // _local_fn_ptr = _local_cont_ptr as fn(...) -> *mut u8
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_fn_ptr),
                    Rvalue::Cast(
                        CastKind::Transmute,
                        Operand::Copy(Place::from(local_cont_ptr)),
                        cont_fn_ptr_ty,
                    ),
                ))),
            ),
        ],
        Some(Terminator {
            source_info,
            kind: TerminatorKind::Call {
                func: Operand::Copy(Place::from(local_fn_ptr)),
                args: Box::new([
                    rustc_span::Spanned {
                        node: Operand::Copy(Place::from(local_buffer_ptr)),
                        span,
                    },
                    rustc_span::Spanned { node: false_bool_operand.clone(), span },
                    rustc_span::Spanned {
                        node: Operand::Copy(Place::from(local_resume_ptr)),
                        span,
                    },
                    rustc_span::Spanned { node: Operand::Copy(Place::from(local_mut_yield)), span },
                    rustc_span::Spanned {
                        node: Operand::Copy(Place::from(local_mut_return)),
                        span,
                    },
                ]),
                destination: Place::from(local_ret_cont_ptr),
                target: Some(bb_yield),
                unwind: unwind_action,
                call_source: CallSource::Misc,
                fn_span: span,
            },
            attributes: Default::default(),
        }),
        false,
    ));

    // BB_YIELD: Check returned pointer to see if finished
    let mut bb_yield_stmts = Vec::new();
    // Reload `local_mut_coroutine = (_1.0: &mut Coroutine)` after `@llvm.coro.suspend.retcon` returns
    // so `local_mut_coroutine` loaded in `BB0` is not live across the call (`B.getStructSize() = 0`).
    bb_yield_stmts.push(Statement::new(
        source_info,
        StatementKind::Assign(Box::new((
            Place::from(local_mut_coroutine),
            Rvalue::Use(
                Operand::Copy(Place {
                    local: local_self,
                    projection: tcx.mk_place_elems(&[ProjectionElem::Field(
                        FieldIdx::from_usize(0),
                        ref_coroutine_ty,
                    )]),
                }),
                rustc_middle::mir::WithRetag::No,
            ),
        ))),
    ));
    bb_yield_stmts.push(Statement::new(
        source_info,
        StatementKind::Assign(Box::new((
            Place {
                local: local_mut_coroutine,
                projection: tcx.mk_place_elems(&[
                    ProjectionElem::Deref,
                    ProjectionElem::Field(cont_field_idx, const_u8_ptr),
                ]),
            },
            Rvalue::Use(
                Operand::Copy(Place::from(local_ret_cont_ptr)),
                rustc_middle::mir::WithRetag::No,
            ),
        ))),
    ));
    // _local_is_null = _local_ret_cont_ptr == _local_null_ptr
    bb_yield_stmts.push(Statement::new(
        source_info,
        StatementKind::Assign(Box::new((
            Place::from(local_is_null),
            Rvalue::BinaryOp(
                rustc_middle::mir::BinOp::Eq,
                Box::new((
                    Operand::Copy(Place::from(local_ret_cont_ptr)),
                    Operand::Copy(Place::from(local_null_ptr)),
                )),
            ),
        ))),
    ));
    basic_blocks.push(BasicBlockData::new_stmts(
        bb_yield_stmts,
        Some(Terminator {
            source_info,
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from(local_is_null)),
                targets: SwitchTargets::new(std::iter::once((1, bb_complete)), bb_yield_ret),
            },
            attributes: Default::default(),
        }),
        false,
    ));

    // BB_YIELD_RET: Read from yield uninit buffer and return Yielded / Pending / Some
    let adt_did = state_adt_ref.did();
    let (yield_variant, yield_operands) = match coroutine_kind {
        CoroutineKind::Desugared(CoroutineDesugaring::Async, _) => {
            (VariantIdx::from_usize(1), IndexVec::new()) // Poll::Pending
        }
        CoroutineKind::Desugared(CoroutineDesugaring::Gen, _) => {
            (
                VariantIdx::from_usize(1),
                IndexVec::from_elem_n(Operand::Move(Place::from(local_yield)), 1),
            ) // Some(val)
        }
        CoroutineKind::Coroutine(_) => {
            (
                VariantIdx::from_usize(0),
                IndexVec::from_elem_n(Operand::Move(Place::from(local_yield)), 1),
            ) // CoroutineState::Yielded(val)
        }
        _ => bug!("unsupported coroutine kind for retcon: {:?}", coroutine_kind),
    };

    basic_blocks.push(BasicBlockData::new_stmts(
        vec![
            // _local_yield = (*_local_mut_yield)
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_yield),
                    Rvalue::Use(
                        Operand::Copy(Place {
                            local: local_mut_yield,
                            projection: tcx.mk_place_elems(&[ProjectionElem::Deref]),
                        }),
                        rustc_middle::mir::WithRetag::No,
                    ),
                ))),
            ),
            // _RETURN_PLACE = Adt(yield_variant, yield_operands)
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(RETURN_PLACE),
                    Rvalue::Aggregate(
                        Box::new(AggregateKind::Adt(
                            adt_did,
                            yield_variant,
                            state_args,
                            None,
                            None,
                        )),
                        yield_operands,
                    ),
                ))),
            ),
            Statement::new(source_info, StatementKind::StorageDead(local_yield_uninit)),
            Statement::new(source_info, StatementKind::StorageDead(local_return_uninit)),
        ],
        Some(Terminator {
            source_info,
            kind: TerminatorKind::Goto { target: bb_return },
            attributes: Default::default(),
        }),
        false,
    ));

    // BB_COMPLETE: Read from return uninit buffer and return Complete / Ready / None
    let (ret_variant, ret_operands) = match coroutine_kind {
        CoroutineKind::Desugared(CoroutineDesugaring::Async, _) => {
            (
                VariantIdx::from_usize(0),
                IndexVec::from_elem_n(Operand::Move(Place::from(local_return)), 1),
            ) // Poll::Ready(val)
        }
        CoroutineKind::Desugared(CoroutineDesugaring::Gen, _) => {
            (VariantIdx::from_usize(0), IndexVec::new()) // None
        }
        CoroutineKind::Coroutine(_) => {
            (
                VariantIdx::from_usize(1),
                IndexVec::from_elem_n(Operand::Move(Place::from(local_return)), 1),
            ) // CoroutineState::Complete(val)
        }
        _ => bug!("unsupported coroutine kind for retcon: {:?}", coroutine_kind),
    };

    basic_blocks.push(BasicBlockData::new_stmts(
        vec![
            // Reload `local_mut_coroutine = (_1.0: &mut Coroutine)` before setting `cont_field_idx = null`
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_mut_coroutine),
                    Rvalue::Use(
                        Operand::Copy(Place {
                            local: local_self,
                            projection: tcx.mk_place_elems(&[ProjectionElem::Field(
                                FieldIdx::from_usize(0),
                                ref_coroutine_ty,
                            )]),
                        }),
                        rustc_middle::mir::WithRetag::No,
                    ),
                ))),
            ),
            // ((*_local_mut_coroutine).cont_field_idx: *mut u8) = null
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place {
                        local: local_mut_coroutine,
                        projection: tcx.mk_place_elems(&[
                            ProjectionElem::Deref,
                            ProjectionElem::Field(cont_field_idx, const_u8_ptr),
                        ]),
                    },
                    Rvalue::Use(
                        Operand::Copy(Place::from(local_null_ptr)),
                        rustc_middle::mir::WithRetag::No,
                    ),
                ))),
            ),
            // discriminant(*_local_mut_coroutine) = 1 (Returned)
            Statement::new(
                source_info,
                StatementKind::SetDiscriminant {
                    place: Box::new(tcx.mk_place_deref(Place::from(local_mut_coroutine))),
                    variant_index: rustc_abi::VariantIdx::from_usize(1), // Returned
                },
            ),
            // _local_return = (*_local_mut_return)
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_return),
                    Rvalue::Use(
                        Operand::Copy(Place {
                            local: local_mut_return,
                            projection: tcx.mk_place_elems(&[ProjectionElem::Deref]),
                        }),
                        rustc_middle::mir::WithRetag::No,
                    ),
                ))),
            ),
            // _RETURN_PLACE = Adt(ret_variant, ret_operands)
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(RETURN_PLACE),
                    Rvalue::Aggregate(
                        Box::new(AggregateKind::Adt(adt_did, ret_variant, state_args, None, None)),
                        ret_operands,
                    ),
                ))),
            ),
            Statement::new(source_info, StatementKind::StorageDead(local_yield_uninit)),
            Statement::new(source_info, StatementKind::StorageDead(local_return_uninit)),
        ],
        Some(Terminator {
            source_info,
            kind: TerminatorKind::Goto { target: bb_return },
            attributes: Default::default(),
        }),
        false,
    ));

    // BB_PANIC: Panic if a Coroutine-trait coroutine is resumed after completion.
    // Uses Assert(false, ResumedAfterReturn) to match the standard StateTransform behavior.
    basic_blocks.push(BasicBlockData::new_stmts(
        vec![],
        Some(Terminator {
            source_info,
            kind: TerminatorKind::Assert {
                cond: Operand::Constant(Box::new(ConstOperand {
                    span,
                    user_ty: None,
                    const_: rustc_middle::mir::Const::from_bool(tcx, false),
                })),
                expected: true,
                msg: Box::new(rustc_middle::mir::AssertKind::ResumedAfterReturn(coroutine_kind)),
                target: bb_panic, // self-loop (unreachable since assert always fails)
                unwind: unwind_action,
            },
            attributes: Default::default(),
        }),
        false,
    ));

    // BB_RETURN: Merged return block
    basic_blocks.push(BasicBlockData::new_stmts(
        vec![],
        Some(Terminator {
            source_info,
            kind: TerminatorKind::Return,
            attributes: Default::default(),
        }),
        false,
    ));

    let mut new_body = crate::shim::new_body(body.source, basic_blocks, local_decls, 2, span);
    new_body.phase = body.phase;
    new_body.mentioned_items = body.mentioned_items.clone();
    if let Some(coroutine) = body.coroutine.clone() {
        new_body.coroutine = Some(coroutine);
    }
    std::mem::swap(body, &mut new_body);
}

pub(crate) fn transform_into_drop_shim<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    coroutine_ty: Ty<'tcx>,
) {
    let span = body.span;
    let source_info = SourceInfo::outermost(span);

    let old_ret_ty = body.return_ty();
    let old_yield_ty = body.yield_ty().unwrap_or(tcx.types.unit);
    let resume_ty = if body.arg_count == 2 {
        body.local_decls[Local::from_usize(2)].ty
    } else {
        tcx.types.unit
    };

    let _ = body.coroutine.take();
    body.arg_count = 1;
    body.basic_blocks_mut().raw.clear();
    body.local_decls.raw.clear();
    body.var_debug_info.clear();

    let unwind_action = if tcx.sess.panic_strategy().unwinds() {
        UnwindAction::Continue
    } else {
        UnwindAction::Unreachable
    };

    let mut_ptr_yield_ty = Ty::new_mut_ptr(tcx, old_yield_ty);
    let mut_ptr_return_ty = Ty::new_mut_ptr(tcx, old_ret_ty);
    let mut_ptr_resume_ty = Ty::new_mut_ptr(tcx, resume_ty);
    let const_u8_ptr = Ty::new_mut_ptr(tcx, tcx.types.u8);
    let bool_ty = tcx.types.bool;

    let cont_fn_sig = tcx.mk_fn_sig(
        [const_u8_ptr, bool_ty, mut_ptr_resume_ty, mut_ptr_yield_ty, mut_ptr_return_ty],
        const_u8_ptr,
        rustc_middle::ty::FnSigKind::default().set_safety(rustc_hir::Safety::Unsafe),
    );
    let cont_fn_ptr_ty = Ty::new_fn_ptr(tcx, rustc_middle::ty::Binder::dummy(cont_fn_sig));

    let ref_coroutine_ty = Ty::new_mut_ref(tcx, tcx.lifetimes.re_erased, coroutine_ty);
    let ty::Coroutine(_def_id, args) = *coroutine_ty.kind() else { unreachable!() };
    let cont_field_idx = FieldIdx::from_usize(args.as_coroutine().upvar_tys().len());

    // _0: ()
    let local_ret = body.local_decls.push(LocalDecl::new(tcx.types.unit, span));
    assert_eq!(local_ret, RETURN_PLACE);

    // _1: &mut Coroutine
    let arg_self = body.local_decls.push(LocalDecl::new(ref_coroutine_ty, span));
    assert_eq!(arg_self, Local::from_usize(1));

    let local_mut_coro_ptr_ptr =
        body.local_decls.push(LocalDecl::new(Ty::new_mut_ptr(tcx, coroutine_ty), span)); // _2
    let local_u8_ptr = body.local_decls.push(LocalDecl::new(const_u8_ptr, span)); // _4
    let local_cont_ptr = body.local_decls.push(LocalDecl::new(const_u8_ptr, span)); // _8
    let local_is_null = body.local_decls.push(LocalDecl::new(tcx.types.bool, span)); // _9
    let local_null_ptr = body.local_decls.push(LocalDecl::new(const_u8_ptr, span)); // _10

    let local_fn_ptr = body.local_decls.push(LocalDecl::new(cont_fn_ptr_ty, span)); // _11
    let local_buffer_ptr = body.local_decls.push(LocalDecl::new(const_u8_ptr, span)); // _13

    let local_mut_yield = body.local_decls.push(LocalDecl::new(mut_ptr_yield_ty, span)); // _14
    let local_mut_return = body.local_decls.push(LocalDecl::new(mut_ptr_return_ty, span)); // _15
    let local_mut_resume = body.local_decls.push(LocalDecl::new(mut_ptr_resume_ty, span)); // _16
    let local_ret_cont_ptr = body.local_decls.push(LocalDecl::new(const_u8_ptr, span)); // _17

    let null_usize_operand = Operand::Constant(Box::new(ConstOperand {
        span,
        user_ty: None,
        const_: Const::from_usize(tcx, 0),
    }));

    let true_bool_operand = Operand::Constant(Box::new(ConstOperand {
        span,
        user_ty: None,
        const_: rustc_middle::mir::Const::from_bool(tcx, true),
    }));

    let bb_setup = BasicBlock::from_usize(1);
    let bb_call = BasicBlock::from_usize(2);
    let bb_return = BasicBlock::from_usize(3);

    // BB0: Check if cont_ptr is null
    let mut bb0_stmts = vec![
        // _2 = &raw mut (*_1)
        Statement::new(
            source_info,
            StatementKind::Assign(Box::new((
                Place::from(local_mut_coro_ptr_ptr),
                Rvalue::RawPtr(
                    rustc_middle::mir::RawPtrKind::Mut,
                    Place {
                        local: arg_self,
                        projection: tcx.mk_place_elems(&[ProjectionElem::Deref]),
                    },
                ),
            ))),
        ),
        // _4 = _2 as *mut u8
        Statement::new(
            source_info,
            StatementKind::Assign(Box::new((
                Place::from(local_u8_ptr),
                Rvalue::Cast(
                    CastKind::PtrToPtr,
                    Operand::Copy(Place::from(local_mut_coro_ptr_ptr)),
                    const_u8_ptr,
                ),
            ))),
        ),
        // _8 = ((*_1).0: *mut u8)
        Statement::new(
            source_info,
            StatementKind::Assign(Box::new((
                Place::from(local_cont_ptr),
                Rvalue::Use(
                    Operand::Copy(Place {
                        local: arg_self,
                        projection: tcx.mk_place_elems(&[
                            ProjectionElem::Deref,
                            ProjectionElem::Field(cont_field_idx, const_u8_ptr),
                        ]),
                    }),
                    rustc_middle::mir::WithRetag::No,
                ),
            ))),
        ),
    ];
    bb0_stmts.extend(vec![
        // _10 = null
        Statement::new(
            source_info,
            StatementKind::Assign(Box::new((
                Place::from(local_null_ptr),
                Rvalue::Cast(
                    CastKind::PointerWithExposedProvenance,
                    null_usize_operand.clone(),
                    const_u8_ptr,
                ),
            ))),
        ),
        // _9 = _8 == _10
        Statement::new(
            source_info,
            StatementKind::Assign(Box::new((
                Place::from(local_is_null),
                Rvalue::BinaryOp(
                    rustc_middle::mir::BinOp::Eq,
                    Box::new((
                        Operand::Copy(Place::from(local_cont_ptr)),
                        Operand::Copy(Place::from(local_null_ptr)),
                    )),
                ),
            ))),
        ),
    ]);
    body.basic_blocks_mut().push(BasicBlockData::new_stmts(
        bb0_stmts,
        Some(Terminator {
            source_info,
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Move(Place::from(local_is_null)),
                targets: SwitchTargets::new(std::iter::once((1, bb_return)), bb_setup),
            },
            attributes: Default::default(),
        }),
        false,
    ));

    // BB_SETUP: Call continuation with is_unwind=true.
    // Cleanup paths are guaranteed not to yield (MIR validator enforces this),
    // so one call to the continuation with is_cleanup=true always runs to completion.
    body.basic_blocks_mut().push(BasicBlockData::new_stmts(
        vec![
            // _13 = _4
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_buffer_ptr),
                    Rvalue::Use(
                        Operand::Copy(Place::from(local_u8_ptr)),
                        rustc_middle::mir::WithRetag::No,
                    ),
                ))),
            ),
            // _14 = null
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_mut_yield),
                    Rvalue::Cast(
                        CastKind::PointerWithExposedProvenance,
                        null_usize_operand.clone(),
                        mut_ptr_yield_ty,
                    ),
                ))),
            ),
            // _15 = null
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_mut_return),
                    Rvalue::Cast(
                        CastKind::PointerWithExposedProvenance,
                        null_usize_operand.clone(),
                        mut_ptr_return_ty,
                    ),
                ))),
            ),
            // _16 = null
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_mut_resume),
                    Rvalue::Cast(
                        CastKind::PointerWithExposedProvenance,
                        null_usize_operand.clone(),
                        mut_ptr_resume_ty,
                    ),
                ))),
            ),
            // _11 = _8 as fn(...) -> *mut u8
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(local_fn_ptr),
                    Rvalue::Cast(
                        CastKind::Transmute,
                        Operand::Copy(Place::from(local_cont_ptr)),
                        cont_fn_ptr_ty,
                    ),
                ))),
            ),
        ],
        Some(Terminator {
            source_info,
            kind: TerminatorKind::Call {
                func: Operand::Copy(Place::from(local_fn_ptr)),
                args: Box::new([
                    rustc_span::Spanned {
                        node: Operand::Copy(Place::from(local_buffer_ptr)),
                        span,
                    },
                    rustc_span::Spanned { node: true_bool_operand.clone(), span },
                    rustc_span::Spanned {
                        node: Operand::Copy(Place::from(local_mut_resume)),
                        span,
                    },
                    rustc_span::Spanned { node: Operand::Copy(Place::from(local_mut_yield)), span },
                    rustc_span::Spanned {
                        node: Operand::Copy(Place::from(local_mut_return)),
                        span,
                    },
                ]),
                destination: Place::from(local_ret_cont_ptr),
                target: Some(bb_call),
                unwind: unwind_action,
                call_source: CallSource::Misc,
                fn_span: span,
            },
            attributes: Default::default(),
        }),
        false,
    ));

    // BB_CALL: we returned from the continuation pointer
    body.basic_blocks_mut().push(BasicBlockData::new_stmts(
        vec![
            // ((*_1).0: *mut u8) = _17  (store returned ptr to continuation_ptr)
            Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place {
                        local: arg_self,
                        projection: tcx.mk_place_elems(&[
                            ProjectionElem::Deref,
                            ProjectionElem::Field(cont_field_idx, const_u8_ptr),
                        ]),
                    },
                    Rvalue::Use(
                        Operand::Copy(Place::from(local_ret_cont_ptr)),
                        rustc_middle::mir::WithRetag::No,
                    ),
                ))),
            ),
        ],
        Some(Terminator {
            source_info,
            kind: TerminatorKind::Goto { target: bb_return },
            attributes: Default::default(),
        }),
        false,
    ));

    // BB_RETURN: return
    body.basic_blocks_mut().push(BasicBlockData::new_stmts(
        vec![],
        Some(Terminator {
            source_info,
            kind: TerminatorKind::Return,
            attributes: Default::default(),
        }),
        false,
    ));
}

struct BackendAccessReplacementVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    saved_local_1: Local,
    local_coro_ptr: Local,
    saved_local_1_ty: Ty<'tcx>,
}

impl<'tcx> MutVisitor<'tcx> for BackendAccessReplacementVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_place(&mut self, place: &mut Place<'tcx>, context: PlaceContext, location: Location) {
        if place.local == self.saved_local_1 {
            place.local = self.local_coro_ptr;
            let mut curr_ty = self.saved_local_1_ty;
            let mut slice_idx = 0;
            for (i, elem) in place.projection.iter().enumerate() {
                if matches!(curr_ty.kind(), rustc_middle::ty::Coroutine(..)) {
                    break;
                }
                match elem {
                    ProjectionElem::Deref => {
                        if let rustc_middle::ty::Ref(_, inner, _)
                        | rustc_middle::ty::RawPtr(inner, _) = *curr_ty.kind()
                        {
                            curr_ty = inner;
                            slice_idx = i + 1;
                        }
                    }
                    ProjectionElem::Field(f, inner) if f.as_usize() == 0 => {
                        if let rustc_middle::ty::Adt(adt, _) = *curr_ty.kind() {
                            if self.tcx.is_lang_item(adt.did(), rustc_hir::LangItem::Pin) {
                                curr_ty = inner;
                                slice_idx = i + 1;
                            }
                        }
                    }
                    _ => {}
                }
            }
            let mut new_proj = vec![ProjectionElem::Deref];
            new_proj.extend_from_slice(&place.projection[slice_idx..]);
            place.projection = self.tcx.mk_place_elems(&new_proj);
            return;
        }
        self.super_place(place, context, location);
    }
}
