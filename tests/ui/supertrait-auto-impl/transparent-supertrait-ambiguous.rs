// Test that providing a supertrait item in `impl Sub` when multiple
// supertraits define the same method name produces an ambiguity error.

#![feature(supertrait_auto_impl)]
#![allow(dead_code)]

trait Super1 {
    fn foo(&self) -> i32;
}

trait Super2 {
    fn foo(&self) -> i32;
}

trait Sub: Super1 + Super2 {
    fn bar(&self) -> i32;
}

auto impl Super1 for trait Sub {
    fn foo(&self) -> i32 { 1 }
}

auto impl Super2 for trait Sub {
    fn foo(&self) -> i32 { 2 }
}

struct MyTy;
impl Sub for MyTy {
    fn foo(&self) -> i32 { 42 }
    //~^ ERROR item `foo` is ambiguous because it is defined in multiple supertraits: `Super1`, `Super2`
    fn bar(&self) -> i32 { 0 }
}

fn main() {}
