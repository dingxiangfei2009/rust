//@ run-pass
//@ compile-flags: -Zbackend-coroutines -C opt-level=2

#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::ops::{CoroutineState, Coroutine};
use std::pin::Pin;

fn return_after_yield() {
    let a = String::from("foo");
    let mut foo = #[coroutine] || {
        yield;
        return a
    };

    match Pin::new(&mut foo).resume(()) {
        CoroutineState::Yielded(()) => {}
        s => panic!("bad state: {:?}", s),
    }
    match Pin::new(&mut foo).resume(()) {
        CoroutineState::Complete(s) => assert_eq!(s, "foo"),
        s => panic!("bad state: {:?}", s),
    }
}

fn main() {
    return_after_yield();
}
