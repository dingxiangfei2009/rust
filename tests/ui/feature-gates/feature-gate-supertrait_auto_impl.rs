// Test that `auto impl` syntax requires the `supertrait_auto_impl` feature gate.

trait Super {}
trait Sub: Super {}

auto impl Super for trait Sub {}
//~^ ERROR: `auto impl` syntax is experimental

fn main() {}
