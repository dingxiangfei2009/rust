//@ check-pass
// Test that unsafe auto impl parses correctly.

#![feature(supertrait_auto_impl)]

unsafe trait Super {}
trait Sub: Super {}

unsafe auto impl Super for trait Sub {}

fn main() {}
