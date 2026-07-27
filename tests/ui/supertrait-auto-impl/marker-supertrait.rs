// Test that auto impl works with marker supertraits that have no associated items.

//@ run-pass

#![feature(supertrait_auto_impl)]

// Marker trait with no methods or associated items.
trait Marker {}

trait Sub: Marker {
    fn value(&self) -> i32;
}

auto impl Marker for trait Sub {}

struct Foo;
impl Sub for Foo {
    fn value(&self) -> i32 { 42 }
}

struct Bar;
impl Sub for Bar {
    fn value(&self) -> i32 { 99 }
}

// A type that only implements Marker directly, not via Sub.
struct Direct;
impl Marker for Direct {}

fn requires_marker<T: Marker>(_t: &T) {}

fn requires_sub<T: Sub>(t: &T) -> i32 {
    t.value()
}

// Multiple marker supertraits.
trait MarkerA {}
trait MarkerB {}
#[allow(dead_code)]

trait Multi: MarkerA + MarkerB {
    fn id(&self) -> i32;
}

auto impl MarkerA for trait Multi {}
auto impl MarkerB for trait Multi {}

struct Baz;
impl Multi for Baz {
    fn id(&self) -> i32 { 7 }
}

fn requires_a<T: MarkerA>(_t: &T) {}
fn requires_b<T: MarkerB>(_t: &T) {}
fn requires_both<T: MarkerA + MarkerB>(_t: &T) {}

fn main() {
    let foo = Foo;
    let bar = Bar;
    let direct = Direct;
    let baz = Baz;

    // Auto impl provides Marker for Foo and Bar via Sub.
    requires_marker(&foo);
    requires_marker(&bar);
    requires_marker(&direct);
    assert_eq!(requires_sub(&foo), 42);
    assert_eq!(requires_sub(&bar), 99);

    // Auto impls provide both MarkerA and MarkerB for Baz via Multi.
    requires_a(&baz);
    requires_b(&baz);
    requires_both(&baz);
}
