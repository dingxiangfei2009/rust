// Test that qualified paths for subtraits are not currently supported.
// (Test 4e from test plan)
// The subtrait position only accepts a simple identifier, not a path.

#![feature(supertrait_auto_impl)]

mod inner {
    pub trait Sub {
        fn sub(&self);
    }
}

trait Super {
    fn foo(&self);
}

// This should ideally work but currently doesn't —
// the parser expects an identifier, not a path.
auto impl Super for trait inner::Sub {}
//~^ ERROR expected one of `where` or `{`, found `::`

fn main() {}
