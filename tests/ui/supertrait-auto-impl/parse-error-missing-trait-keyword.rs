// Test that `auto impl Super for Sub {}` (missing `trait` keyword) is an error.

#![feature(supertrait_auto_impl)]

trait Super {}
trait Sub: Super {}

auto impl Super for Sub {} //~ ERROR expected `trait`, found `Sub`

fn main() {}
