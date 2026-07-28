//@ check-pass
#![feature(supertrait_auto_impl)]
#![allow(dead_code)]

use std::fmt::Debug;

trait Super {
    fn s(&self) -> i32;
}

trait Sub: Super {
    fn m(&self) -> i32;
}

auto impl Super for trait Sub {
    fn s(&self) -> i32 { 0 }
}

// Only implement Sub for types where T: Debug
#[derive(Debug)]
struct Wrapper<T>(T);
impl<T: Debug> Sub for Wrapper<T> {
    fn s(&self) -> i32 { 42 }
    fn m(&self) -> i32 { 1 }
}

// This should NOT compile: Wrapper<NoDebug> doesn't impl Sub,
// so it shouldn't impl Super either.
struct NoDebug;

fn check_super<S: Super>(_: &S) {}

fn main() {
    // This should work - i32: Debug
    check_super(&Wrapper(42i32));
}
