// Test that auto impl actually provides the supertrait implementation.

//@ check-pass

#![feature(supertrait_auto_impl)]

trait Super {}
trait Sub: Super {}
auto impl Super for trait Sub {}

struct Foo;
impl Sub for Foo {}

fn requires_super<T: Super>(_t: &T) {}

fn main() {
    let foo = Foo;
    requires_super(&foo);
}
