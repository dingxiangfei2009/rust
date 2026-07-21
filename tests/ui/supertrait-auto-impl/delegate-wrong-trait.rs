// Test that delegation to a wrong trait produces an error.
// SubA has an auto impl for Super, not Unrelated.
// The delegation creates a second impl of Unrelated for Foo, which conflicts.

//@ compile-flags: --crate-type lib

#![feature(supertrait_auto_impl)]

trait Super {
    fn value(&self) -> i32;
}

trait Unrelated {
    fn other(&self) -> i32;
}

trait SubA: Super {
    fn a(&self) -> i32;
}

auto impl Super for trait SubA {
    fn value(&self) -> i32 {
        self.a()
    }
}

struct Foo;
impl SubA for Foo {
    fn a(&self) -> i32 { 1 }
}
impl Unrelated for Foo {
    fn other(&self) -> i32 { 99 }
}

// Delegation to wrong trait — SubA has auto impl for Super, not Unrelated.
// This creates a conflicting impl.
impl Unrelated for Foo = SubA::Unrelated;
//~^ ERROR conflicting implementations of trait `Unrelated` for type `Foo` [E0119]
