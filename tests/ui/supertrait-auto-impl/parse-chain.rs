//@ check-pass
// Test that chained auto impls parse correctly.

#![feature(supertrait_auto_impl)]

trait A {}
trait B: A {}
trait C: B {}

auto impl A for trait B {}
auto impl B for trait C {}

fn main() {}
