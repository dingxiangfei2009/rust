//@ compile-flags: -O -Zbackend-coroutines
//@ edition: 2021

#![crate_type = "lib"]

use std::cell::RefCell;
use std::future::poll_fn;
use std::rc::Rc;
use std::task::Poll;

// Verify that for retcon coroutines (`-Zbackend-coroutines`):
// 1. Prior to splitting, `CoroMakeOutsideFrameVolatilePass` marked `!coro.outside.frame` allocas
//    as volatile to prevent premature SROA promotion across yield points (preventing frame spills).
// 2. After coroutine splitting (`CoroSplitPass`), `CoroRemoveVolatilePass` runs
//    on the generated continuation clone (`.resume.0`), strips all `volatile`
//    flags, and runs `SROA` + `SimplifyCFG`.
// 3. As a result, `.resume.0` contains zero stack allocations (`alloca`), zero `volatile` accesses,
//    and accesses coroutine state fields directly via frame offset projections
//    (`getelementptr ... %0`).

// CHECK-LABEL: define internal noundef ptr @{{.*}}run_steps{{.*}}.resume.0(
// Verify zero stack allocas remain inside the continuation clone after post-split SROA:
// CHECK-NOT: alloca
// Verify all temporary volatile flags have been stripped by CoroRemoveVolatilePass:
// CHECK-NOT: volatile
// Verify high-level frame field projections off argument %0 (the coroutine frame pointer):
// CHECK: getelementptr inbounds nuw i8, ptr %0, i64 16
// CHECK: }
#[no_mangle]
pub async fn run_steps(step: Rc<RefCell<u32>>) -> u32 {
    *step.borrow_mut() += 10;
    poll_fn(|_| {
        if *step.borrow() < 15 {
            *step.borrow_mut() += 5;
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    })
    .await;
    *step.borrow()
}
