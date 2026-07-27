// Test that providing a supertrait item in `impl Sub` when an explicit
// `impl Super` already exists produces an error.

#![feature(supertrait_auto_impl)]

trait Super {
    fn super_method(&self) -> i32;
}

trait Sub: Super {
    fn sub_method(&self) -> i32;
}

struct Foo;
impl Super for Foo {
    fn super_method(&self) -> i32 { 1 }
}
impl Sub for Foo {
    fn super_method(&self) -> i32 { 2 }  //~ ERROR supertrait item
    fn sub_method(&self) -> i32 { 3 }
}

fn main() {}
