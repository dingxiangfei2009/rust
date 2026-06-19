//@ run-pass
//@ compile-flags: -Z backend-coroutines --test

#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::ops::{CoroutineState, Coroutine};
use std::pin::Pin;

fn main() {
    let mut foo = #[coroutine] || {
        yield String::from("bar");
        return String::from("foo")
    };

    match Pin::new(&mut foo).resume(()) {
        CoroutineState::Yielded(ref s) if *s == "bar" => {}
        s => panic!("bad state: {:?}", s),
    }
    match Pin::new(&mut foo).resume(()) {
        CoroutineState::Complete(ref s) if *s == "foo" => {}
        s => panic!("bad state: {:?}", s),
    }
}
