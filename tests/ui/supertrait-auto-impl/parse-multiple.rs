//@ check-pass
// Test that multiple auto impls for different supertraits parse correctly.

#![feature(supertrait_auto_impl)]

trait A {}
trait B {}
trait Sub: A + B {}

auto impl A for trait Sub {}
auto impl B for trait Sub {}

fn main() {}
