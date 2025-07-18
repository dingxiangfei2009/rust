#![allow(unused)]
use std::assert_matches::assert_matches;
use std::{fmt, iter};

use rustc_abi::{ExternAbi, FIRST_VARIANT, FieldIdx, VariantIdx};
use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_hir::lang_items::LangItem;
use rustc_index::{Idx, IndexVec};
use rustc_middle::mir::visit::{MutVisitor, PlaceContext};
use rustc_middle::query::Providers;
use rustc_middle::ty::{
    self, CoroutineArgs, CoroutineArgsExt, EarlyBinder, GenericArgs, Ty, TyCtxt,
};
use rustc_middle::{bug, span_bug};
use rustc_span::source_map::{Spanned, dummy_spanned};
use rustc_span::{DUMMY_SP, Span};
use tracing::{debug, instrument};

use crate::elaborate_drop::{DropElaborator, DropFlagMode, DropStyle, Unwind, elaborate_drop};
use crate::patch::MirPatch;
use crate::{
    abort_unwinding_calls, add_call_guards, add_moves_for_packed_drops, deref_separator, inline,
    instsimplify, mentioned_items, pass_manager as pm, remove_noop_landing_pads,
    run_optimization_passes, simplify,
};

pub(super) fn build_inplace_init(tcx: TyCtxt<'tcx>, def_id: DefId, ty: Ty<'tcx>) -> Body<'tcx> {}

pub(super) fn build_inplace_init_layout_query(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    ty: Ty<'tcx>,
) -> Body<'tcx> {
    todo!()
}
