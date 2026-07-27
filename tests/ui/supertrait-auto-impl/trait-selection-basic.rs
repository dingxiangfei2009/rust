// Test that trait selection works for auto impl in various scenarios.

//@ run-pass

#![feature(supertrait_auto_impl)]

trait Super {
    fn super_method(&self) -> i32;
}

trait Sub: Super {
    fn sub_method(&self) -> i32;
}

auto impl Super for trait Sub {
    fn super_method(&self) -> i32 {
        self.sub_method() * 2
    }
}

struct Foo;
impl Sub for Foo {
    fn sub_method(&self) -> i32 { 10 }
}

struct Bar;
impl Sub for Bar {
    fn sub_method(&self) -> i32 { 20 }
}

// Test trait object coercion
fn call_via_bound<T: Super>(t: &T) -> i32 {
    t.super_method()
}

// Test that different implementors get different results
fn main() {
    let foo = Foo;
    let bar = Bar;
    assert_eq!(foo.super_method(), 20); // 10 * 2
    assert_eq!(bar.super_method(), 40); // 20 * 2
    assert_eq!(call_via_bound(&foo), 20);
    assert_eq!(call_via_bound(&bar), 40);
}
