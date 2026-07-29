// Test for missing supertrait path in auto impl.
// (Test 3b from test plan)

#![feature(supertrait_auto_impl)]

trait Sub {
    fn sub(&self);
}

auto impl for trait Sub {} //~ ERROR

fn main() {}
