// Test that a manual impl of the supertrait can coexist with an auto impl.
// The manual impl should take precedence (suppress the auto impl).

//@ run-pass

#![feature(supertrait_auto_impl)]

trait Super {
    fn value(&self) -> i32;
}

trait Sub: Super {
    fn sub_value(&self) -> i32;
}

auto impl Super for trait Sub {
    fn value(&self) -> i32 {
        self.sub_value()
    }
}

struct Foo;
impl Sub for Foo {
    fn sub_value(&self) -> i32 { 1 }
}

// Manual impl of Super for Foo — should override the auto impl.
impl Super for Foo {
    fn value(&self) -> i32 { 42 }
}

fn main() {
    let foo = Foo;
    assert_eq!(foo.value(), 42);
}
