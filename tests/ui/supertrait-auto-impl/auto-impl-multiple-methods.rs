// Test auto impl that provides multiple methods, some calling each other.

//@ run-pass

#![feature(supertrait_auto_impl)]

trait Super {
    fn foo(&self) -> i32;
    fn bar(&self) -> i32;
    fn baz(&self) -> i32;
}

trait Sub: Super {
    fn base(&self) -> i32;
}

auto impl Super for trait Sub {
    fn foo(&self) -> i32 {
        self.base()
    }
    fn bar(&self) -> i32 {
        self.foo() + 1  // calls another auto impl method
    }
    fn baz(&self) -> i32 {
        self.bar() + self.foo()  // calls two auto impl methods
    }
}

struct S;
impl Sub for S {
    fn base(&self) -> i32 { 10 }
}

fn main() {
    let s = S;
    assert_eq!(s.foo(), 10);
    assert_eq!(s.bar(), 11);
    assert_eq!(s.baz(), 21); // 11 + 10
}
