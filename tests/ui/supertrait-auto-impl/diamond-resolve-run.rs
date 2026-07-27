// Test that diamond disambiguation via `= SubA::Super;` delegation syntax
// actually picks the correct auto impl body at runtime.

//@ run-pass

#![feature(supertrait_auto_impl)]

trait Super {
    fn value(&self) -> i32;
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
impl Super for Foo = SubA::Super;

fn main() {
    assert_eq!(Foo.value(), 1);
}
