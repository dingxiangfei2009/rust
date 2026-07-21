// Test cross-crate usage of auto impl.

//@ check-pass
//@ aux-build: cross-crate-auto-impl.rs

extern crate cross_crate_auto_impl;
use cross_crate_auto_impl::{Super, Sub};

struct Foo;
impl Sub for Foo {}

// This works because auto impl Super for trait Sub
// means implementing Sub automatically provides Super.
fn requires_super<T: Super>(_t: &T) {}

fn main() {
    let foo = Foo;
    requires_super(&foo);
}
