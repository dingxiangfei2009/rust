// Test cross-crate usage of auto impl with methods.
// The auto impl is defined in the auxiliary crate and provides
// a default super_method that delegates to sub_method.

//@ run-pass
//@ aux-build: cross-crate-with-methods.rs

extern crate cross_crate_with_methods;
use cross_crate_with_methods::{Super, Sub};

struct Foo;
impl Sub for Foo {
    fn sub_method(&self) -> i32 { 42 }
}

fn call_super<T: Super>(t: &T) -> i32 {
    t.super_method()
}

fn main() {
    let foo = Foo;
    // Auto impl from the other crate provides super_method = sub_method + 100
    assert_eq!(foo.super_method(), 142);
    assert_eq!(call_super(&foo), 142);
}
