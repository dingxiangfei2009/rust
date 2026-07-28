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

struct Wrapper<const N: usize>;
impl<const N: usize> Sub for Wrapper<N> {
    fn s(&self) -> i32 { N as i32 }  // transparent override
    fn m(&self) -> i32 { 1 }
}

fn main() {
    let w = Wrapper::<42>;
    assert_eq!(w.s(), 42);
    assert_eq!(w.m(), 1);
}
