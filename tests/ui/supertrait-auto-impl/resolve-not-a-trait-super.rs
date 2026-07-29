// Test that auto impl rejects non-trait items as the supertrait.
// (Test 4c from test plan)

#![feature(supertrait_auto_impl)]

struct NotATrait;

trait Sub {
    fn sub(&self);
}

auto impl NotATrait for trait Sub {} //~ ERROR

fn main() {}
