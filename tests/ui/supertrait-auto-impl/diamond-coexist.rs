// Test that two auto impls for the same non-marker supertrait via
// different subtraits can coexist. The ambiguity is resolved when a
// concrete type implements both subtraits by writing a manual impl
// (see `diamond-resolve.rs`).

//@ check-pass

#![feature(supertrait_auto_impl)]

trait Super {
    fn value(&self) -> i32;
}

trait SubA: Super {
    fn a(&self) -> i32;
}

trait SubB: Super {
    fn b(&self) -> i32;
}

auto impl Super for trait SubA {
    fn value(&self) -> i32 {
        self.a()
    }
}

auto impl Super for trait SubB {
    fn value(&self) -> i32 {
        self.b()
    }
}

fn main() {}
