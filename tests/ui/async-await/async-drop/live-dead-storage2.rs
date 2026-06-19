// ex-ice: #140531
//@ compile-flags: -Zlint-mir --crate-type lib
//@ edition:2024
//@ check-pass
//@ revisions: default retcon
//@[retcon]compile-flags: -Z backend-coroutines

#![feature(async_drop)]
#![allow(incomplete_features)]

async fn call_once(f: impl AsyncFnOnce()) {
    let fut = Box::pin(f());
}
