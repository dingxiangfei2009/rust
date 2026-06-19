//@ compile-flags: -Z backend-coroutines -C no-prepopulate-passes
//@ edition: 2021
//@ revisions: x86_64
//@[x86_64] compile-flags: --target x86_64-unknown-linux-gnu
//@[x86_64] needs-llvm-components: x86

#![crate_type = "lib"]

use std::future::{Future, poll_fn};
use std::pin::pin;
use std::task::{Context, Poll, Waker};

async fn add_async(x: i32, y: i32) -> i32 {
    poll_fn(|_| Poll::<()>::Pending).await;
    x + y
}

// CHECK-LABEL: define {{(dso_local )?}}noundef i32 @test_async()
#[no_mangle]
pub fn test_async() -> i32 {
    let mut fut = pin!(add_async(10, 20));
    let waker = Waker::noop();
    let mut cx = Context::from_waker(&waker);

    match fut.as_mut().poll(&mut cx) {
        Poll::Ready(val) => val,
        Poll::Pending => 0,
    }
}

// Check that switch intrinsics are NOT emitted and retcon intrinsics ARE emitted.
// CHECK-NOT: call token @llvm.coro.id(
// CHECK-DAG: declare token @llvm.coro.id.retcon
// CHECK-DAG: declare { i1, ptr, ptr, ptr } @llvm.coro.suspend.retcon.sl_i1p0p0p0s(...)
