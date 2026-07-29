// Tests for safety validation of `auto impl` trait blocks.
// Checks that unsafe traits require unsafe auto impl and vice versa.

#![feature(supertrait_auto_impl)]

// === Test 10a: Safe auto impl for unsafe trait (should error) ===
unsafe trait UnsafeTrait {
    fn foo(&self);
}

trait SubOfUnsafe: UnsafeTrait {
    fn bar(&self);
}

auto impl UnsafeTrait for trait SubOfUnsafe {
    //~^ ERROR the trait `UnsafeTrait` requires an `unsafe impl` declaration
    fn foo(&self) {}
}

// === Test 10b: Unsafe auto impl for safe trait (should error) ===
trait SafeTrait {
    fn safe_method(&self);
}

trait SubOfSafe: SafeTrait {
    fn sub_method(&self);
}

unsafe auto impl SafeTrait for trait SubOfSafe {
    //~^ ERROR implementing the trait `SafeTrait` is not unsafe
    fn safe_method(&self) {}
}

// === Test 10c: Correct unsafe auto impl (should be OK) ===
unsafe trait AnotherUnsafe {
    fn unsafe_method(&self);
}

trait SubOfAnotherUnsafe: AnotherUnsafe {
    fn sub_method2(&self);
}

unsafe auto impl AnotherUnsafe for trait SubOfAnotherUnsafe {
    fn unsafe_method(&self) {}
}

// === Test 10d: Correct safe auto impl (should be OK) ===
trait AnotherSafe {
    fn another_safe_method(&self);
}

trait SubOfAnotherSafe: AnotherSafe {
    fn another_sub_method(&self);
}

auto impl AnotherSafe for trait SubOfAnotherSafe {
    fn another_safe_method(&self) {}
}

fn main() {}
