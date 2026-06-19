//@ run-pass
//@ check-run-results
//@ revisions: default retcon
//@[retcon]compile-flags: -Z backend-coroutines
//@ edition: 2021

#![feature(async_drop)]
#![allow(incomplete_features)]

use std::future::{async_drop_in_place, AsyncDrop, Future};
use std::mem::ManuallyDrop;
use std::pin::{pin, Pin};
use std::sync::mpsc;
use std::sync::Arc;
use std::task::{Context, Poll, Wake, Waker};

#[allow(dead_code)]
struct Foo(usize);

impl Drop for Foo {
    fn drop(&mut self) {}
}

impl AsyncDrop for Foo {
    async fn drop(self: Pin<&mut Self>) {
        println!("dropping {}", self.0);
    }
}

fn block_on<F: Future>(fut_unpin: F) -> F::Output {
    let mut fut_pin = pin!(ManuallyDrop::new(fut_unpin));
    let mut fut: Pin<&mut F> = unsafe {
        Pin::map_unchecked_mut(fut_pin.as_mut(), |x| &mut **x)
    };
    let (waker, rx) = simple_waker();
    let mut context = Context::from_waker(&waker);
    let rv = loop {
        match fut.as_mut().poll(&mut context) {
            Poll::Ready(out) => break out,
            Poll::Pending => rx.try_recv().unwrap(),
        }
    };
    let drop_fut_unpin = unsafe { async_drop_in_place(fut.get_unchecked_mut()) };
    let mut drop_fut = pin!(drop_fut_unpin);
    loop {
        match drop_fut.as_mut().poll(&mut context) {
            Poll::Ready(()) => break,
            Poll::Pending => rx.try_recv().unwrap(),
        }
    }
    rv
}

fn simple_waker() -> (Waker, mpsc::Receiver<()>) {
    struct SimpleWaker {
        tx: mpsc::Sender<()>,
    }
    impl Wake for SimpleWaker {
        fn wake(self: Arc<Self>) {
            self.tx.send(()).unwrap();
        }
    }
    let (tx, rx) = mpsc::channel();
    (Waker::from(Arc::new(SimpleWaker { tx })), rx)
}

struct Counter(usize);

impl Counter {
    fn add(self, n: usize) -> Self {
        Counter(self.0 + n)
    }
}

async fn repro() {
    let mut c = Counter(10);
    let mut i = 0;
    loop {
        if i >= 4 { break; }
        i += 1;
        yield_now().await;
        c = c.add(1);
        println!("{}", c.0);
    }
}

struct YieldNow(bool);
fn yield_now() -> YieldNow { YieldNow(false) }
impl Future for YieldNow {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if !self.0 {
            self.0 = true;
            cx.waker().wake_by_ref();
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}

fn main() {
    block_on(repro());
}
