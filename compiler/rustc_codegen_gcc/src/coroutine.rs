use rustc_codegen_ssa::traits::CoroutineBuilderMethods;

use crate::builder::Builder;

impl<'a, 'gcc, 'tcx> CoroutineBuilderMethods<'tcx> for Builder<'a, 'gcc, 'tcx> {
    fn coro_id_retcon(
        &mut self,
        _size: Self::Value,
        _align: Self::Value,
        _buffer: Self::Value,
        _prototype_name: &str,
    ) -> Self::Value {
        unimplemented!("backend coroutines are not yet implemented for GCC")
    }

    fn coro_size(&mut self) -> Self::Value {
        unimplemented!("backend coroutines are not yet implemented for GCC")
    }

    fn coro_begin(&mut self, _coro_id: Self::Value, _mem: Self::Value) -> Self::Value {
        unimplemented!("backend coroutines are not yet implemented for GCC")
    }

    fn coro_suspend_retcon(&mut self) -> Self::Value {
        unimplemented!("backend coroutines are not yet implemented for GCC")
    }

    fn coro_end(&mut self, _handle: Self::Value, _unwind: bool) -> Self::Value {
        unimplemented!("backend coroutines are not yet implemented for GCC")
    }

    fn coro_destroy(&mut self, _handle: Self::Value) {
        unimplemented!("backend coroutines are not yet implemented for GCC")
    }
}
