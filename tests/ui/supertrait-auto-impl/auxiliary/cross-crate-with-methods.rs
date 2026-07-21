#![feature(supertrait_auto_impl)]

pub trait Super {
    fn super_method(&self) -> i32;
}

pub trait Sub: Super {
    fn sub_method(&self) -> i32;
}

auto impl Super for trait Sub {
    fn super_method(&self) -> i32 {
        self.sub_method() + 100
    }
}
