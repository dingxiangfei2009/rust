// Test that transparent supertrait items override auto impl defaults.
// The user's `fn super_method()` in `impl Sub for Foo` should be used
// instead of the auto impl's default.

//@ run-pass

#![feature(supertrait_auto_impl)]
#![allow(dead_code)]

trait Super {
    fn super_method(&self) -> i32;
}

trait Sub: Super {
    fn sub_method(&self) -> i32;
}

auto impl Super for trait Sub {
    fn super_method(&self) -> i32 { 0 }  // default
}

struct Foo;
impl Sub for Foo {
    fn super_method(&self) -> i32 { 42 }  // override!
    fn sub_method(&self) -> i32 { 1 }
}

struct Bar;
impl Sub for Bar {
    // No override -- uses auto impl's default (0)
    fn sub_method(&self) -> i32 { 2 }
}

fn main() {
    let foo = Foo;
    assert_eq!(foo.super_method(), 42);  // override
    assert_eq!(foo.sub_method(), 1);

    let bar = Bar;
    assert_eq!(bar.super_method(), 0);   // default from auto impl
    assert_eq!(bar.sub_method(), 2);
}
