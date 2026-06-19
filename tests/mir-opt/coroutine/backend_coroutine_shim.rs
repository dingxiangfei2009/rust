//@ skip-filecheck
// EMIT_MIR_FOR_EACH_PANIC_STRATEGY
// EMIT_MIR backend_coroutine_shim.main-{closure#0}.BackendCoroutineTransform.after.mir

//@ compile-flags: -Zbackend-coroutines -Zmir-opt-level=0
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

fn main() {
    let mut coro = #[coroutine]
    |arg: i32| {
        yield 1;
        let x = yield 2;
        x
    };
}
