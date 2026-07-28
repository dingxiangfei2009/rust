// Test auto impl with a lifetime-generic supertrait.

//@ run-pass

#![feature(supertrait_auto_impl)]

trait Super<'a> {
    fn get(&self) -> &'a str;
}

trait Sub {
    fn name(&self) -> &'static str;
}

auto impl<'a> Super<'a> for trait Sub {
    fn get(&self) -> &'a str {
        self.name()
    }
}

struct Foo;
impl Sub for Foo {
    fn name(&self) -> &'static str { "hello" }
}

fn requires_super<'a, T: Super<'a>>(t: &T) -> &'a str {
    t.get()
}

fn main() {
    let foo = Foo;
    assert_eq!(requires_super(&foo), "hello");
}
