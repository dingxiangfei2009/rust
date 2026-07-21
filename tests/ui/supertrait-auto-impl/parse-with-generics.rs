//@ check-pass
// Test that auto impl with generics on supertrait parses correctly.
// The generics apply to the auto impl (and supertrait), not the subtrait.

#![feature(supertrait_auto_impl)]

trait Super<T> {}
trait Sub: Super<u8> {}

auto impl<T> Super<T> for trait Sub {}

fn main() {}
