#![allow(unused)]
use rustc_ast::{AsmMacro, InlineAsmOptions};
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::stack::ensure_sufficient_stack;
use rustc_hir as hir;
use rustc_hir::lang_items::LangItem;
use rustc_middle::mir::*;
use rustc_middle::span_bug;
use rustc_middle::thir::*;
use rustc_middle::ty::{self, CanonicalUserTypeAnnotation, Ty};
use rustc_span::DUMMY_SP;
use rustc_span::source_map::{Spanned, respan};
use rustc_trait_selection::infer::InferCtxtExt;
use tracing::{debug, instrument};

use crate::builder::expr::category::{Category, RvalueFunc};
use crate::builder::matches::{DeclareLetBindings, HasMatchGuard};
use crate::builder::{BlockAnd, BlockAndExtension, BlockFrame, Builder, NeedsTemporary};
use crate::errors::{LoopMatchArmWithGuard, LoopMatchUnsupportedType};

impl<'a, 'tcx> Builder<'a, 'tcx> {
    #[instrument(level = "debug", skip(self))]
    pub(crate) fn inplace_init(
        &mut self,
        destination: Place<'tcx>,
        mut block: BasicBlock,
        expr: &Expr<'tcx>,
        kind: &InitKind,
    ) -> BlockAnd<()> {
        let expr_span = expr.span;
        let source_info = self.source_info(expr_span);
        let &ty::Tuple(target_and_err) = expr.ty.kind() else {
            span_bug!(expr_span, "expected 2-tuple")
        };
        let [target_ty, err_ty] = **target_and_err else {
            span_bug!(expr_span, "expected 2-tuple")
        };
        match &*kind {
            &InitKind::Free(expr_id) => {
                // Evaluate the free expression as-is
                let value = unpack!(
                    block =
                        self.as_temp(block, self.local_temp_lifetime(), expr_id, Mutability::Not)
                );
                let Some(ctxt) = &self.inplace_init_context else {
                    span_bug!(
                        expr_span,
                        "we need to init value in-place but there is no in-place init context"
                    )
                };
                // Synthesis the `Init::init` call
                let init_init = self.tcx.require_lang_item(LangItem::InitInit, expr_span);
                let result = self.local_decls.push(LocalDecl {
                    mutability: Mutability::Not,
                    local_info: ClearCrossCrate::Clear,
                    ty: todo!(),
                    user_ty: None,
                    source_info,
                });
                block = {
                    let continuation = self.cfg.start_new_block();
                    self.cfg.terminate(
                        block,
                        source_info,
                        TerminatorKind::Call {
                            func: Operand::Constant(Box::new(ConstOperand {
                                span: expr_span,
                                user_ty,
                                const_,
                            })),
                            args: Box::new([
                                respan(expr_span, Operand::Move(value.into())),
                                respan(DUMMY_SP, Operand::Copy(ctxt.current_slot.into())),
                            ]),
                            destination: result.into(),
                            target: Some(continuation),
                            unwind: UnwindAction::Continue,
                            call_source: CallSource::Misc,
                            fn_span: expr_span,
                        },
                    );
                    continuation
                };
                // Synthesis the error handling

                todo!()
            }
            InitKind::Array(expr_ids) => {
                // Synthesis a guard
                // let guard = this.as_local_call_operand(block, expr);
                for &eid in expr_ids {
                    let operand = unpack!(
                        block = self.as_call_operand(block, self.local_temp_lifetime(), eid)
                    );
                    // Call
                }
                todo!()
            }
        }
        todo!()
    }
}
