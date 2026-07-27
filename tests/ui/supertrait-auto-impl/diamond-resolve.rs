// Test that diamond ambiguity from two auto impls for the same supertrait
// can be resolved using `impl Super for Foo = SubA::Super;` delegation syntax.

//@ check-pass

#![feature(supertrait_auto_impl)]

trait Super {
    fn value(&self) -> i32;
}

trait SubA: Super {
    fn a(&self) -> i32;
}

trait SubB: Super {
    fn b(&self) -> i32;
}

auto impl Super for trait SubA {
    fn value(&self) -> i32 {
        self.a()
    }
}

auto impl Super for trait SubB {
    fn value(&self) -> i32 {
        self.b()
    }
}

struct Foo;
impl SubA for Foo {
    fn a(&self) -> i32 { 1 }
}
impl SubB for Foo {
    fn b(&self) -> i32 { 2 }
}
impl Super for Foo = SubA::Super; // OK — picks SubA's auto impl

struct Bar;
impl SubA for Bar {
    fn a(&self) -> i32 { 10 }
}
impl SubB for Bar {
    fn b(&self) -> i32 { 20 }
}
impl Super for Bar = SubB::Super; // OK — picks SubB's auto impl

fn main() {}
