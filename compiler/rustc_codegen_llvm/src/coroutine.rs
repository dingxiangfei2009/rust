use rustc_codegen_ssa::traits::{
    BaseTypeCodegenMethods, BuilderMethods, ConstCodegenMethods, CoroutineBuilderMethods,
    MiscCodegenMethods,
};
use rustc_hir::LangItem;
use rustc_middle::ty::Instance;
use rustc_middle::ty::layout::HasTyCtxt;

use crate::builder::Builder;
use crate::llvm;

impl<'a, 'll, 'tcx> CoroutineBuilderMethods<'tcx> for Builder<'a, 'll, 'tcx> {
    fn coro_id_retcon(
        &mut self,
        size: Self::Value,
        align: Self::Value,
        buffer: Self::Value,
        prototype_name: &str,
    ) -> Self::Value {
        // 1. Synthesize the prototype signature
        let ptr_ty = self.type_ptr();
        let i1_ty = self.type_i1();
        let sig = self.type_func(&[ptr_ty, i1_ty, ptr_ty, ptr_ty, ptr_ty], ptr_ty);
        let prototype = self.declare_cfn(prototype_name, llvm::UnnamedAddr::Global, sig);
        let attr = llvm::CreateAttrString(self.cx().llcx, "is-coroutine-ramp");
        crate::attributes::apply_to_llfn(prototype, crate::llvm::AttributePlace::Function, &[attr]);
        crate::attributes::apply_to_llfn(
            self.llfn(),
            crate::llvm::AttributePlace::Function,
            &[attr],
        );

        let dummy_sp = rustc_span::DUMMY_SP;
        // 2. Look up the unreachable allocators (panicking lang items)
        let alloc_def_id =
            self.cx().tcx().require_lang_item(LangItem::CoroutineAllocPanic, dummy_sp);
        let alloc_instance = Instance::mono(self.cx().tcx(), alloc_def_id);
        let alloc_fn = self.cx().get_fn_addr(alloc_instance, None);

        let dealloc_def_id =
            self.cx().tcx().require_lang_item(LangItem::CoroutineDeallocPanic, dummy_sp);
        let dealloc_instance = Instance::mono(self.cx().tcx(), dealloc_def_id);
        let dealloc_fn = self.cx().get_fn_addr(dealloc_instance, None);

        // 3. Emit llvm.coro.id.retcon
        // llvm.coro.id.retcon(size, align, buffer, prototype, alloc, dealloc)
        self.call_intrinsic(
            "llvm.coro.id.retcon",
            &[],
            &[size, align, buffer, prototype, alloc_fn, dealloc_fn],
        )
    }

    fn coro_size(&mut self) -> Self::Value {
        self.call_intrinsic("llvm.coro.size", &[self.type_isize()], &[])
    }

    fn coro_begin(&mut self, coro_id: Self::Value, mem: Self::Value) -> Self::Value {
        self.call_intrinsic("llvm.coro.begin", &[], &[coro_id, mem])
    }

    fn coro_suspend_retcon(&mut self) -> Self::Value {
        let ptr_ty = self.type_ptr();
        let i1_ty = self.type_i1();
        // The return type of suspend.retcon matches the arguments passed to the continuation function after the buffer.
        // Therefore, it returns { is_unwind: i1, resume_arg: ptr, yield_out: ptr, return_out: ptr }
        let ret_ty = self.type_struct(&[i1_ty, ptr_ty, ptr_ty, ptr_ty], false);
        // It takes zero arguments because the yield types sequence (defined by the prototype's return type `ptr`) is empty.
        self.call_intrinsic("llvm.coro.suspend.retcon", &[ret_ty], &[])
    }

    fn coro_end(&mut self, handle: Self::Value, unwind: bool) -> Self::Value {
        let unwind_val = self.const_bool(unwind);
        self.call_intrinsic("llvm.coro.end", &[], &[handle, unwind_val])
    }

    fn coro_destroy(&mut self, handle: Self::Value) {
        self.call_intrinsic("llvm.coro.destroy", &[], &[handle]);
    }
}
