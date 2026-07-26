//@ check-pass
//@ aux-build: foreign-trait.rs
// Test that auto impl currently accepts foreign subtraits.
// FIXME: This should error — the subtrait in `auto impl` should be local (orphan rule).

#![feature(supertrait_auto_impl)]

extern crate foreign_trait;
use foreign_trait::ForeignSub;

trait Super {}

auto impl Super for trait ForeignSub {}

fn main() {}
