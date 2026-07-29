// Verify HIR representation of `auto impl` trait blocks.
// (Test 5a from test plan)
//@ compile-flags: -Zunpretty=hir
//@ check-pass

#![feature(supertrait_auto_impl)]

trait Super {
    fn super_method(&self) -> i32;
}

trait Sub: Super {
    fn sub_method(&self) -> i32;
}

auto impl Super for trait Sub {
    fn super_method(&self) -> i32 {
        self.sub_method() * 2
    }
}
