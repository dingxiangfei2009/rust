// Test that auto impl with a where clause referencing Self doesn't work
// because Self isn't available in auto impl scope.

#![feature(supertrait_auto_impl)]

use std::fmt::Debug;

trait Super {
    fn describe(&self) -> String;
}

trait Sub: Super {
    fn value(&self) -> i32;
}

auto impl Super for trait Sub where Self: Debug {
//~^ ERROR cannot find type `Self` in this scope
    fn describe(&self) -> String {
        format!("{:?}", self)
    }
}

fn main() {}
