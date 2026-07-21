// Test diamond disambiguation with two subtraits choosing different auto impls
// at runtime, verifying the correct body is executed.

//@ run-pass

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
impl Super for Foo = SubA::Super; // picks SubA's auto impl

struct Bar;
impl SubA for Bar {
    fn a(&self) -> i32 { 10 }
}
impl SubB for Bar {
    fn b(&self) -> i32 { 20 }
}
impl Super for Bar = SubB::Super; // picks SubB's auto impl

fn call_super(t: &dyn Super) -> i32 {
    t.value()
}

fn main() {
    assert_eq!(Foo.value(), 1);  // SubA's impl: returns a()
    assert_eq!(Bar.value(), 20); // SubB's impl: returns b()

    // Also test through trait objects
    assert_eq!(call_super(&Foo), 1);
    assert_eq!(call_super(&Bar), 20);
}
