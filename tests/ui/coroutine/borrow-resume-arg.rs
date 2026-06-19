//@ run-pass
//@ compile-flags: -Zbackend-coroutines

#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]
use std::ops::Coroutine;

fn main() {
    let coro = #[coroutine] static |arg: String| {
        let borrow = &arg;
        println!("before yield: borrow={}, arg={}", borrow, arg);
        let new_arg = yield ();
        println!("after yield: borrow={}, arg={}, new_arg={}", borrow, arg, new_arg);
    };

    let mut pinned = std::pin::pin!(coro);
    pinned.as_mut().resume(String::from("A"));
    pinned.as_mut().resume(String::from("B"));
}
