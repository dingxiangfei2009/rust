// ex-ice: #140429
//@ compile-flags: -Zlint-mir --crate-type lib
//@ edition:2024
//@ check-pass
//@ revisions: default retcon
//@[retcon]compile-flags: -Z backend-coroutines

#![feature(async_drop)]
#![allow(incomplete_features)]

async fn a<T>(x: T) {}
