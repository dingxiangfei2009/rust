// Test that unresolved supertrait in auto impl produces an error.

#![feature(supertrait_auto_impl)]

trait Sub {}

auto impl Nonexistent for trait Sub {}
//~^ ERROR: cannot find trait `Nonexistent`

fn main() {}
