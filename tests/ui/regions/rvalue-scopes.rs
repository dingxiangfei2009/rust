// edition:2021
// run-pass
// check-run-results
use std::cell::Cell;
use std::ops::{Index, IndexMut};

struct Droppy(u8);
impl Drop for Droppy {
    fn drop(&mut self) {
        println!("AH! {}", self.0)
    }
}

struct A<'a>(Cell<&'a mut Droppy>);

impl<'a> Index<&'a mut Droppy> for A<'a> {
    type Output = Droppy;
    fn index(&self, idx: &'a mut Droppy) -> &Self::Output {
        &*self.0.replace(idx)
    }
}

impl<'a> IndexMut<&'a mut Droppy> for A<'a> {
    fn index_mut(&mut self, idx: &'a mut Droppy) -> &mut Self::Output {
        self.0.replace(idx)
    }
}

fn main() {
    let t = &mut Droppy(0);
    let mut a = A(Cell::new(t));
    a[&mut Droppy(1)] = Droppy(2);
}
