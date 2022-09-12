// Test that the borrow checker prevents pointers to temporaries
// with statement lifetimes from escaping.
// run-pass

struct StackBox<T> {
    f: T,
}

#[allow(unused)]
struct AddFlags {
    bits: u64,
}

#[allow(non_snake_case)]
fn AddFlags(bits: u64) -> AddFlags {
    AddFlags { bits }
}

fn arg(x: &AddFlags) -> &AddFlags {
    x
}

impl AddFlags {
    fn get(&self) -> &AddFlags {
        self
    }
}

pub fn main() {
    let x1 = arg(&AddFlags(1));
    let x2 = AddFlags(1).get();
    let x3 = &*arg(&AddFlags(1));
    let ref x4 = *arg(&AddFlags(1));
    let &ref x5 = arg(&AddFlags(1));
    let x6 = AddFlags(1).get();
    let StackBox { f: x7 } = StackBox { f: AddFlags(1).get() };
    (x1, x2, x3, x4, x5, x6, x7);
}
