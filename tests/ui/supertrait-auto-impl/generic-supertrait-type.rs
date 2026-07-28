// Test auto impl and delegation with a generic supertrait (type parameter).

//@ run-pass

#![feature(supertrait_auto_impl)]

trait Super<T> {
    fn get(&self) -> T;
}

trait Sub {
    fn value(&self) -> i32;
}

auto impl Super<i32> for trait Sub {
    fn get(&self) -> i32 {
        self.value() * 2
    }
}

struct Foo;
impl Sub for Foo {
    fn value(&self) -> i32 { 21 }
}

fn requires_super<T: Super<i32>>(t: &T) -> i32 {
    t.get()
}

fn main() {
    let foo = Foo;
    assert_eq!(requires_super(&foo), 42);
}
