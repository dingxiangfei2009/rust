// Test that delegation fails when there's no matching auto impl.
// The delegation path refers to SubA::Super, but there's no
// `auto impl Super for trait SubA`.

//@ compile-flags: --crate-type lib

#![feature(supertrait_auto_impl)]

trait Super {
    fn value(&self) -> i32;
}

trait SubA: Super {
    fn a(&self) -> i32;
}

// No auto impl for SubA!

struct Foo;
impl SubA for Foo {
    fn a(&self) -> i32 { 1 }
}
impl Super for Foo = SubA::Super;
//~^ ERROR not all trait items implemented, missing: `value`
