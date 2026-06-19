//@ run-pass
//@ compile-flags: -Zbackend-coroutines

#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]
use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

fn main() {
    let mut coro = #[coroutine] |_arg: i32| {
        let x = yield 1;
        assert_eq!(x, 42);
        2
    };

    let mut pinned = Pin::new(&mut coro);
    assert_eq!(pinned.as_mut().resume(0), CoroutineState::Yielded(1));
    assert_eq!(pinned.as_mut().resume(42), CoroutineState::Complete(2));
}
