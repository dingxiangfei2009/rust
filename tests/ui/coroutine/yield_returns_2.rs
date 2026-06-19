//@ run-pass
//@ compile-flags: -Zbackend-coroutines

#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]
use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

fn main() {
    let mut coro = #[coroutine] static |arg: String| {
        let borrow = &arg;
        assert_eq!(borrow, "A");
        let x = yield ();
        assert_eq!(borrow, "A");
        assert_eq!(x, "B");
    };

    let mut pinned = unsafe { Pin::new_unchecked(&mut coro) };
    assert_eq!(pinned.as_mut().resume(String::from("A")), CoroutineState::Yielded(()));
    assert_eq!(pinned.as_mut().resume(String::from("B")), CoroutineState::Complete(()));
}
