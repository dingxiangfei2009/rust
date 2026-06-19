//@ run-pass
//@ compile-flags: -Z backend-coroutines
//@ edition: 2021

use std::cell::RefCell;
use std::future::{Future, poll_fn};
use std::pin::pin;
use std::rc::Rc;
use std::task::{Context, Poll, Waker};

async fn run_steps(step: Rc<RefCell<u32>>) -> u32 {
    *step.borrow_mut() += 10;
    // Suspend once
    let step2 = step.clone();
    poll_fn(move |_| {
        let val = *step2.borrow();
        if val < 15 {
            *step2.borrow_mut() += 5;
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }).await;
    *step.borrow_mut() += 20;
    *step.borrow()
}

fn main() {
    println!("main start");
    let step = Rc::new(RefCell::new(0));
    let mut fut = pin!(run_steps(step.clone()));
    let waker = Waker::noop();
    let mut cx = Context::from_waker(&waker);

    // Poll 1: step increments 0 -> 10 -> 15, returns Pending
    println!("before poll 1");
    assert_eq!(fut.as_mut().poll(&mut cx), Poll::Pending);
    println!("after poll 1");
    assert_eq!(*step.borrow(), 15);

    // Poll 2: returns Ready, step increments 15 -> 35
    println!("before poll 2");
    assert_eq!(fut.as_mut().poll(&mut cx), Poll::Ready(35));
    println!("after poll 2");
    assert_eq!(*step.borrow(), 35);
    println!("main end");
}
