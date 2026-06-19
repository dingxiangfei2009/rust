//@ compile-flags: -Zbackend-coroutines=yes

#![crate_type = "lib"]
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::ops::Coroutine;
use std::pin::Pin;

#[inline(never)]
fn touch(ptr: *mut u8) {
    unsafe {
        std::ptr::write_volatile(ptr, 42);
    }
}

#[no_mangle]
pub fn test_coro() {
    let mut c = #[coroutine]
    #[inline(never)]
    || {
        {
            let mut buf = [0u8; 1024];
            touch(buf.as_mut_ptr());
        }
        yield ();
    };
    let _ = Pin::new(&mut c).resume(());
}

// CHECK-LABEL: define internal {{.*}}ptr @{{.*}}test_coro{{.*}}ramp{{.*}}.resume.0(
// CHECK-NOT: coroutine_alloc_panic
