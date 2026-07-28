// Test auto impl where the subtrait has a higher-ranked trait bound
// on the supertrait: `trait Sub: for<'a> Super<'a>`.

//@ run-pass

#![feature(supertrait_auto_impl)]
#![allow(dead_code)]

trait Super<'a> {
    fn get(&self, s: &'a str) -> &'a str;
}

trait Sub: for<'a> Super<'a> {
    fn prefix(&self) -> &'static str;
}

auto impl<'a> Super<'a> for trait Sub {
    fn get(&self, s: &'a str) -> &'a str {
        // Just return the input — proves HRTB lifetime works
        s
    }
}

struct Echo;
impl Sub for Echo {
    fn prefix(&self) -> &'static str { "echo: " }
}

fn call_with_hrtb<T: for<'a> Super<'a>>(t: &T, s: &str) -> String {
    t.get(s).to_string()
}

fn main() {
    let e = Echo;
    assert_eq!(call_with_hrtb(&e, "hello"), "hello");
    // Also works with different lifetimes
    let owned = String::from("world");
    assert_eq!(call_with_hrtb(&e, &owned), "world");
}
