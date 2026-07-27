// Test auto impl where method returns Self (requires Sized bound).

//@ run-pass

#![feature(supertrait_auto_impl)]

trait Super: Sized {
    fn double(self) -> Self;
}

trait Sub: Super + Clone {
    fn val(&self) -> i32;
    fn from_val(v: i32) -> Self;
}

auto impl Super for trait Sub {
    fn double(self) -> Self {
        Self::from_val(self.val() * 2)
    }
}

#[derive(Clone)]
struct Num(i32);
impl Sub for Num {
    fn val(&self) -> i32 { self.0 }
    fn from_val(v: i32) -> Self { Num(v) }
}

fn main() {
    let n = Num(21);
    let d = n.double();
    assert_eq!(d.val(), 42);
}
