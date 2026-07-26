// Test transparent supertrait item resolution:
// items in `impl Sub for Foo` that belong to a supertrait `Super`
// should be accepted without E0407.
//
// For now, this requires an `auto impl` to satisfy the supertrait bound.
// The transparent item overrides the auto impl's default.

//@ check-pass

#![feature(supertrait_auto_impl)]

trait Super {
    fn super_method(&self) -> i32;
}

trait Sub: Super {
    fn sub_method(&self) -> i32;
}

// Auto impl provides the default Super impl.
auto impl Super for trait Sub {
    fn super_method(&self) -> i32 { 0 }
}

struct Foo;
impl Sub for Foo {
    // This overrides the auto impl's super_method:
    fn super_method(&self) -> i32 { 42 }
    fn sub_method(&self) -> i32 { 1 }
}

fn main() {}
