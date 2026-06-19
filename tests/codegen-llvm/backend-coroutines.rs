//@ compile-flags: -Zbackend-coroutines=yes -C no-prepopulate-passes

#![crate_type = "lib"]
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

#[no_mangle]
pub fn test_coro() {
    let mut coro = #[coroutine]
    #[inline(never)]
    || {
        yield 1;
        yield 2;
    };

    let mut coro = Pin::new(&mut coro);
    match coro.as_mut().resume(()) {
        CoroutineState::Yielded(_) => {}
        _ => (),
    }
}

// Ensure the switch-based coroutine intrinsics are NOT used.
// CHECK-NOT: llvm.coro.suspend(
// CHECK-NOT: llvm.coro.id(

// Check that the ramp function initializes the retcon coroutine.
// CHECK: define {{.*}} ptr @{{.*}}ramp{{.*}}(ptr{{.*}} %{{.*}})
// CHECK: call token @llvm.coro.id.retcon(
// CHECK: call ptr @llvm.coro.begin(
// CHECK: call { i1, ptr, ptr, ptr } (...) @llvm.coro.suspend.retcon.sl_i1p0p0p0s(
