// Tests for semantic validation of `auto impl` trait blocks.
// Ensures the compiler correctly rejects invalid auto impl constructs.

#![feature(supertrait_auto_impl)]

// === Test: Self-implementation error ===
trait SelfTrait {
    fn foo(&self);
}

auto impl SelfTrait for trait SelfTrait {
    //~^ ERROR: cannot implement a trait for itself
    fn foo(&self) {}
}

// === Test: Non-supertrait auto impl (should be OK — no supertrait required) ===
trait Unrelated {
    fn unrelated(&self);
}

trait Sub1 {
    fn sub(&self);
}

auto impl Unrelated for trait Sub1 {
    fn unrelated(&self) {}
}

// === Test: Transitive supertrait (should be OK) ===
trait A {
    fn a(&self);
}
trait B: A {
    fn b(&self);
}
trait C: B {
    fn c(&self);
}

auto impl A for trait C {
    fn a(&self) {}
}

// === Test: Valid auto impl (positive test) ===
trait Super {
    fn super_method(&self);
}
trait SubOfSuper: Super {
    fn sub_method(&self);
}

auto impl Super for trait SubOfSuper {
    fn super_method(&self) {}
}

// === Test: Diamond pattern (should be OK) ===
trait Base { fn base(&self); }
trait Left: Base { fn left(&self); }
trait Right: Base { fn right(&self); }
trait Diamond: Left + Right { fn diamond(&self); }
auto impl Base for trait Diamond { fn base(&self) {} }

fn main() {}
