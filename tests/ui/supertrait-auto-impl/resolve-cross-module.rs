//@ check-pass
// Test that auto impl works with traits from other modules in the same crate.

#![feature(supertrait_auto_impl)]

mod traits {
    pub trait Super {}
    pub trait Sub: Super {}
}

use traits::*;

auto impl Super for trait Sub {}

fn main() {}
