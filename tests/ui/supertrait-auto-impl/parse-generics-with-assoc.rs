//@ check-pass
// Test that auto impl with generics and associated types parses correctly.
// This documents the intended semantics:
// - auto impl provides a default associated type
// - manual impl can override it

#![feature(supertrait_auto_impl)]

trait Super<T> {
    type A;
}
trait Sub: Super<u8, A = u8> {}

auto impl<T> Super<T> for trait Sub {
    type A = u8;
}

fn main() {}
