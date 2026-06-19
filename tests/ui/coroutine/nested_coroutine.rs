//@ run-pass
//@ revisions: default retcon
//@[retcon] compile-flags: -Zbackend-coroutines

#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

fn main() {
    let mut coroutine = #[coroutine]
    || {
        let mut sub_coroutine = #[coroutine]
        || {
            yield 2;
        };

        match Pin::new(&mut sub_coroutine).resume(()) {
            CoroutineState::Yielded(x) => {
                yield x;
            }
            _ => panic!(),
        };
    };

    assert_eq!(Pin::new(&mut coroutine).resume(()), CoroutineState::Yielded(2));
    assert_eq!(Pin::new(&mut coroutine).resume(()), CoroutineState::Complete(()));
}
