// Test auto impl through a deep trait hierarchy:
// GrandSuper <- Super <- Sub, with auto impls at each level.

//@ run-pass

#![feature(supertrait_auto_impl)]

trait GrandSuper {
    fn grand(&self) -> i32;
}

trait Super: GrandSuper {
    fn sup(&self) -> i32;
}

trait Sub: Super {
    fn base(&self) -> i32;
}

auto impl GrandSuper for trait Super {
    fn grand(&self) -> i32 {
        self.sup() * 10
    }
}

auto impl Super for trait Sub {
    fn sup(&self) -> i32 {
        self.base() + 1
    }
}

struct S;
impl Sub for S {
    fn base(&self) -> i32 { 5 }
}

fn main() {
    let s = S;
    assert_eq!(s.base(), 5);
    assert_eq!(s.sup(), 6);    // base + 1
    assert_eq!(s.grand(), 60); // sup * 10
}
