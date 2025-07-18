use rustc_infer::traits::SelectionError;
use rustc_middle::ty::fast_reject::DeepRejectCtxt;
use rustc_middle::{bug, ty};
use smallvec::SmallVec;
use tracing::{debug, instrument};

use super::SelectionCandidate::*;
use super::{SelectionCandidateSet, SelectionContext, TraitObligationStack};

impl<'cx, 'tcx> SelectionContext<'cx, 'tcx> {
    /// This procedure select candidates and return, whether an unsizing candidate is chosen
    #[instrument(level = "debug", skip_all, fields(?stack.obligation))]
    pub(super) fn choose_array_unsizing_candidates<'o>(
        &mut self,
        stack: &TraitObligationStack<'o, 'tcx>,
        bounds: impl Iterator<Item = ty::PolyTraitPredicate<'tcx>>,
        candidates: &mut SelectionCandidateSet<'tcx>,
    ) -> Result<bool, SelectionError<'tcx>> {
        let obligation = stack.obligation;
        let self_ty = obligation.self_ty().skip_binder();
        let &ty::Slice(elem_ty) =
            obligation.predicate.skip_binder().trait_ref.args.type_at(1).kind()
        else {
            bug!()
        };
        let tcx = self.tcx();
        let drcx = DeepRejectCtxt::relate_rigid_rigid(tcx);
        let mut candidate_bounds: SmallVec<[ty::PolyTraitPredicate<'tcx>; _]> = SmallVec::default();
        for bound in bounds {
            debug!(?bound);
            let target_ty = bound.skip_binder().trait_ref.args.type_at(1);
            let &ty::Array(other_elem_ty, _) = target_ty.kind() else {
                debug!("skip non-array candidate");
                continue;
            };
            if !drcx.types_may_unify(self_ty, bound.self_ty().skip_binder())
                || !drcx.types_may_unify(elem_ty, other_elem_ty)
            {
                debug!("skip on no unification");
                continue;
            }
            // We now have one candidate by unsizing the array
            // but rejects when there are multiple different impls.
            // There is a potential issue: what if there are multiple `Init<[T; N]>`
            // with potentially different `N` or un-unifiable `T`?
            // This can become an opportunity to bait-and-switch, so we keep a list of them.
            // It is probably enough to just test fast-reject on the last candidate bound,
            // and we will fail later at confirmation.
            if let Some(candidate) = candidate_bounds.last() {
                let other_target_ty = candidate.skip_binder().trait_ref.args.type_at(1);
                if !drcx.types_may_unify(target_ty, other_target_ty) {
                    debug!(?candidate_bounds, another_candidate = ?bound, "ambiguous array unsizing init");
                    candidates.ambiguous = true;
                    return Ok(true);
                }
            }
            candidate_bounds.push(bound);
        }
        debug!(?candidate_bounds);
        if candidate_bounds.is_empty() {
            Ok(false)
        } else {
            candidates.vec.push(ArrayUnsizeInitCandidate(candidate_bounds));
            Ok(true)
        }
    }
}
