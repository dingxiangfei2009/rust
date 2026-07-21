#![feature(supertrait_auto_impl)]

pub trait Super {}

pub trait Sub: Super {}

auto impl Super for trait Sub {}
