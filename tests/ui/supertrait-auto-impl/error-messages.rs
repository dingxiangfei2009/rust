// Test error messages when auto impl obligations are not satisfied.
// (Tests 7a and 7b from test plan)
//
// Verifies that error diagnostics properly cite the auto impl when
// a type doesn't satisfy the required trait bound.

#![feature(supertrait_auto_impl)]

// === 7a: Type doesn't implement Sub, so can't get Super via auto impl ===
trait Super {
    fn super_method(&self) -> i32;
}

trait Sub: Super {
    fn sub_method(&self) -> i32;
}

auto impl Super for trait Sub {
    fn super_method(&self) -> i32 {
        self.sub_method() * 2
    }
}

fn requires_super<T: Super>(t: &T) -> i32 {
    t.super_method()
}

struct NoImpl;

fn test_7a() {
    let x = NoImpl;
    requires_super(&x);
    //~^ ERROR the trait bound `NoImpl: Super` is not satisfied
}

// === 7b: Type implements SubForBound but not Sub ===
trait SuperWithBound {
    fn compute(&self) -> i32;
}

trait SubForBound: SuperWithBound {
    fn value(&self) -> i32;
}

auto impl SuperWithBound for trait SubForBound {
    fn compute(&self) -> i32 {
        self.value()
    }
}

struct Implemented;
impl SubForBound for Implemented {
    fn value(&self) -> i32 { 42 }
}

fn requires_both<T: Super + SuperWithBound>(t: &T) -> i32 {
    t.super_method() + t.compute()
}

fn test_7b() {
    let x = Implemented;
    requires_both(&x);
    //~^ ERROR the trait bound `Implemented: Super` is not satisfied
}

fn main() {}
