// Test that auto impl can delegate to subtrait methods.
// This is the primary use case: providing a default supertrait impl
// that delegates to the subtrait's methods.

//@ run-pass

#![feature(supertrait_auto_impl)]

trait Super {
    fn foo(&self) -> i32;
}

trait Sub: Super {
    fn bar(&self) -> i32;
}

auto impl Super for trait Sub {
    fn foo(&self) -> i32 {
        self.bar() + 1
    }
}

struct Foo;
impl Sub for Foo {
    fn bar(&self) -> i32 { 42 }
}

fn requires_super<T: Super>(t: &T) -> i32 {
    t.foo()
}

fn main() {
    let foo = Foo;
    assert_eq!(requires_super(&foo), 43);
}
