// Test auto impl with associated types.
// (Test 6b from test plan)
//
// Currently fails due to a known issue where the associated type definition
// in the auto impl body is shadowed by the where-bound `Self`.
// See: https://github.com/rust-lang/rust/issues/152409
//
//@ known-bug: #152409

#![feature(supertrait_auto_impl)]

trait Super {
    type Output;
    fn compute(&self) -> Self::Output;
}

trait Sub: Super {
    fn value(&self) -> u32;
}

auto impl Super for trait Sub {
    type Output = u32;
    fn compute(&self) -> Self::Output {
        self.value()
    }
}

fn main() {}
