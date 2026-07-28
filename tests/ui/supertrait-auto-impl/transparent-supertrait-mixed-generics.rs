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

// Test with lifetime + type + const generic params
struct Wrapper<'a, T, const N: usize>(&'a T, [u8; N]);
impl<'a, T: Clone, const N: usize> Sub for Wrapper<'a, T, N> {
    fn s(&self) -> i32 { N as i32 }  // transparent override
    fn m(&self) -> i32 { 1 }
}

fn main() {
    let val = 42i32;
    let w = Wrapper::<'_, i32, 5>(&val, [0; 5]);
    assert_eq!(w.s(), 5);
    assert_eq!(w.m(), 1);
}
