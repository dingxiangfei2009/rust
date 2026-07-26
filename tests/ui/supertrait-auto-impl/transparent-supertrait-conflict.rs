// Test that providing a supertrait item in `impl Sub` when an explicit
// `impl Super` already exists compiles for now (the supertrait item in
// impl Sub is accepted but currently unused).
//
// FIXME(supertrait_auto_impl): When transparent resolution generates
// synthetic impls, this should become a coherence error (E0119).

//@ check-pass

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
    fn super_method(&self) -> i32 { 2 }  // Accepted but currently unused
    fn sub_method(&self) -> i32 { 3 }
}

fn main() {}
