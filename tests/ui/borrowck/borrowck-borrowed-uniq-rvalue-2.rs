// run-pass

struct Defer<'a> {
    x: &'a [&'a str],
}

impl<'a> Drop for Defer<'a> {
    fn drop(&mut self) {
        println!("{:?}", self.x);
    }
}

fn defer<'r>(x: &'r [&'r str]) -> Defer<'r> {
    Defer { x: x }
}

fn main() {
    let x = defer(&vec!["Goodbye", "world!"]);
    x.x[0];
}
