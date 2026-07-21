//@ check-pass
// Test that basic `auto impl` syntax parses and compiles with the feature gate.

#![feature(supertrait_auto_impl)]

trait Super {}
trait Sub: Super {}

auto impl Super for trait Sub {}

fn main() {}
