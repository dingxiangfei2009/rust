//@ run-pass
#![feature(supertrait_auto_impl)]
#![allow(dead_code)]

trait Super { fn s(&self) -> i32; }
trait Sub: Super { fn m(&self) -> i32; }
auto impl Super for trait Sub { fn s(&self) -> i32 { 0 } }

struct Foo;
impl Sub for Foo {
    fn s(&self) -> i32 { 42 }
    fn m(&self) -> i32 { 1 }
}

fn main() {
    let foo = Foo;
    let _ = foo.s();
}
