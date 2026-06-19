//@ skip-filecheck
//@ compile-flags: -Zbackend-coroutines -Zmir-opt-level=0 -C panic=abort
//@ edition: 2024
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

// EMIT_MIR backend_coroutine.foo-{closure#0}.BackendCoroutineTransform.diff
struct CustomResume(i32);
struct CustomYield(i32);

fn foo() {
    let mut upvar = CustomResume(5);
    let _coro = #[coroutine]
    |arg: CustomResume| {
        let mut x = 1;
        yield CustomYield(x);
        let y = 2;
        x += y;
        upvar.0 += arg.0;
        yield CustomYield(x);
    };
}

fn main() {
    foo();
}
