//@ run-pass
//@ compile-flags: -Zbackend-coroutines -C opt-level=0
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

fn main() {
    let mut coro = #[coroutine] || {
        let x = 1;
        yield x;
        let y = 2;
        yield x + y;
    };

    let mut pinned = Pin::new(&mut coro);

    match pinned.as_mut().resume(()) {
        CoroutineState::Yielded(1) => println!("First yield ok"),
        _ => panic!("Expected Yielded(1)"),
    }

    match pinned.as_mut().resume(()) {
        CoroutineState::Yielded(3) => println!("Second yield ok"),
        other => panic!("Expected Yielded(3), got {:?}", other),
    }

    match pinned.as_mut().resume(()) {
        CoroutineState::Complete(()) => println!("Complete ok"),
        _ => panic!("Expected Complete"),
    }
}
