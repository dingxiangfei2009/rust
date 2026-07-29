// Test for missing subtrait name in auto impl.
// (Test 3c from test plan)

#![feature(supertrait_auto_impl)]

trait Super {
    fn foo(&self);
}

auto impl Super for trait {} //~ ERROR

fn main() {}
