// Test that auto impl emits an error for unresolved subtrait.
// (Test 4b from test plan)

#![feature(supertrait_auto_impl)]

trait Super {
    fn foo(&self);
}

auto impl Super for trait Nonexistent {}
//~^ ERROR cannot find trait `Nonexistent` in this scope

fn main() {}
