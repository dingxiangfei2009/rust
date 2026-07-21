// Test delegation with a generic supertrait.
// The delegation impl must resolve through the auto impl
// that has the correct type parameter.

//@ run-pass

#![feature(supertrait_auto_impl)]

trait Super<T> {
    fn get(&self) -> T;
}

trait SubA {
    fn a_val(&self) -> i32;
}

trait SubB {
    fn b_val(&self) -> i32;
}

auto impl Super<i32> for trait SubA {
    fn get(&self) -> i32 {
        self.a_val()
    }
}

auto impl Super<i32> for trait SubB {
    fn get(&self) -> i32 {
        self.b_val() + 100
    }
}

struct Foo;
impl SubA for Foo {
    fn a_val(&self) -> i32 { 1 }
}
impl SubB for Foo {
    fn b_val(&self) -> i32 { 2 }
}
impl Super<i32> for Foo = SubA::Super;

fn main() {
    assert_eq!(Foo.get(), 1); // SubA's auto impl
}
