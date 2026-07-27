// Test auto impl with methods that take self by value, by mut ref, etc.

//@ run-pass

#![feature(supertrait_auto_impl)]

trait Super {
    fn by_ref(&self) -> i32;
    fn by_mut(&mut self) -> i32;
    fn by_value(self) -> i32 where Self: Sized;
}

trait Sub: Super {
    fn val(&self) -> i32;
}

auto impl Super for trait Sub {
    fn by_ref(&self) -> i32 {
        self.val()
    }
    fn by_mut(&mut self) -> i32 {
        self.val() + 1
    }
    fn by_value(self) -> i32 where Self: Sized {
        self.val() + 2
    }
}

#[derive(Clone)]
struct S(i32);
impl Sub for S {
    fn val(&self) -> i32 { self.0 }
}

fn main() {
    let s = S(10);
    assert_eq!(s.by_ref(), 10);
    assert_eq!(s.clone().by_mut(), 11);
    assert_eq!(s.by_value(), 12);
}
