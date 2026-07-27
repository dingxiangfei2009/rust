// Test that a type implementing two subtraits that both have
// auto impl for the same marker supertrait does not cause
// a coherence overlap error.

//@ check-pass

#![feature(supertrait_auto_impl)]

trait Marker {}

trait SubA: Marker {
    fn a(&self) -> i32;
}

trait SubB: Marker {
    fn b(&self) -> i32;
}

auto impl Marker for trait SubA {}
auto impl Marker for trait SubB {}

struct Foo;
impl SubA for Foo {
    fn a(&self) -> i32 { 1 }
}
impl SubB for Foo {
    fn b(&self) -> i32 { 2 }
}

fn requires_marker<T: Marker>(_t: &T) {}

fn main() {
    let foo = Foo;
    requires_marker(&foo);
}
