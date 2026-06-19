use super::BackendTypes;

pub trait CoroutineBuilderMethods<'tcx>: BackendTypes {
    /// Generates `llvm.coro.id.retcon`
    fn coro_id_retcon(
        &mut self,
        size: Self::Value,
        align: Self::Value,
        buffer: Self::Value,
        prototype_name: &str,
    ) -> Self::Value;

    /// Generates `llvm.coro.size.i32` or `.i64`
    fn coro_size(&mut self) -> Self::Value;

    /// Generates `llvm.coro.begin`
    fn coro_begin(&mut self, coro_id: Self::Value, mem: Self::Value) -> Self::Value;

    /// Generates `llvm.coro.suspend.retcon`
    fn coro_suspend_retcon(&mut self) -> Self::Value;

    /// Generates `llvm.coro.end`
    fn coro_end(&mut self, handle: Self::Value, unwind: bool) -> Self::Value;

    /// Generates `llvm.coro.destroy`
    fn coro_destroy(&mut self, handle: Self::Value);
}
