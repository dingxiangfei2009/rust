//@ run-pass
#![feature(supertrait_auto_impl)]
#![allow(dead_code)]

trait Super {
    fn s(&self) -> i32;
}

trait Sub: Super {
    fn m(&self) -> i32;
}

auto impl Super for trait Sub {
    fn s(&self) -> i32 { 0 }
}

struct Wrapper<'a>(&'a i32);
impl<'a> Sub for Wrapper<'a> {
    fn s(&self) -> i32 { *self.0 }  // transparent override
    fn m(&self) -> i32 { 1 }
}

fn main() {
    let val = 42;
    let w = Wrapper(&val);
    assert_eq!(w.s(), 42);
    assert_eq!(w.m(), 1);
}
