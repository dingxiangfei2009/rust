// Test that auto impl interacts correctly with where clauses
// and that the correct impl is selected.

//@ run-pass

#![feature(supertrait_auto_impl)]

trait Super {
    fn value(&self) -> i32;
}

trait Sub: Super {
    fn sub_value(&self) -> i32;
}

auto impl Super for trait Sub {
    fn value(&self) -> i32 {
        self.sub_value() + 100
    }
}

struct AutoFoo;
impl Sub for AutoFoo {
    fn sub_value(&self) -> i32 { 1 }
}

// ManualFoo has both Sub and a manual Super impl.
// The manual impl should take priority over the auto impl.
struct ManualFoo;
impl Sub for ManualFoo {
    fn sub_value(&self) -> i32 { 2 }
}
impl Super for ManualFoo {
    fn value(&self) -> i32 { -1 }
}

// DirectFoo only implements Super directly, not Sub.
struct DirectFoo;
impl Super for DirectFoo {
    fn value(&self) -> i32 { 999 }
}

// Where clause with Super bound — should accept all three.
fn call_super<T: Super>(t: &T) -> i32 {
    t.value()
}

// Where clause with Sub bound — should accept AutoFoo and ManualFoo.
fn call_sub<T: Sub>(t: &T) -> i32 {
    t.sub_value()
}

// Sub bound alone suffices for calling Super methods.
fn call_both<T: Sub>(t: &T) -> i32 {
    t.value() + t.sub_value()
}

// Generic function with Sub bound calling Super method.
// This works because Sub: Super.
fn call_super_via_sub<T: Sub>(t: &T) -> i32 {
    t.value()
}

fn main() {
    let auto_foo = AutoFoo;
    let manual_foo = ManualFoo;
    let direct_foo = DirectFoo;

    // Auto impl provides Super for AutoFoo via Sub.
    assert_eq!(call_super(&auto_foo), 101);  // sub_value(1) + 100
    assert_eq!(call_sub(&auto_foo), 1);
    assert_eq!(call_both(&auto_foo), 102);   // 101 + 1
    assert_eq!(call_super_via_sub(&auto_foo), 101);

    // Manual impl takes priority for ManualFoo.
    assert_eq!(call_super(&manual_foo), -1);  // manual impl
    assert_eq!(call_sub(&manual_foo), 2);
    assert_eq!(call_both(&manual_foo), 1);    // -1 + 2
    assert_eq!(call_super_via_sub(&manual_foo), -1);

    // DirectFoo only has Super, not Sub.
    assert_eq!(call_super(&direct_foo), 999);
}
