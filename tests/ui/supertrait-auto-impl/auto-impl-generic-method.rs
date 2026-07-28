// Test auto impl where the supertrait has a generic method.

//@ run-pass

#![feature(supertrait_auto_impl)]

trait Super {
    fn convert<T: From<i32>>(&self) -> T;
}

trait Sub: Super {
    fn raw(&self) -> i32;
}

auto impl Super for trait Sub {
    fn convert<T: From<i32>>(&self) -> T {
        T::from(self.raw())
    }
}

struct S;
impl Sub for S {
    fn raw(&self) -> i32 { 42 }
}

fn main() {
    let s = S;
    let v: i64 = s.convert();
    assert_eq!(v, 42i64);
    let v: f64 = s.convert();
    assert_eq!(v, 42.0f64);
}
