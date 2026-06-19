//@ run-pass
//@ compile-flags: -Zbackend-coroutines

// Test that retcon coroutine struct sizes are reasonable.
// The retcon struct always includes:
//   - continuation function pointer (*mut u8, 8 bytes on 64-bit)
//   - discriminant (up to 1 byte for small variant counts)
//   - saved locals (overlapped across yield points where possible)
//
// The layout engine packs variant fields into the padding between the
// continuation pointer and the struct's alignment boundary, so small
// saved locals (i32, i64) don't increase the struct size beyond 16 bytes.

#![feature(coroutines, stmt_expr_attributes)]

use std::hint::black_box;
use std::mem::size_of_val;

fn main() {
    // No saved locals across yield — just the continuation ptr + discriminant.
    // Layout: ptr(8) + disc(1) + padding(7) = 16 bytes.
    let no_locals = #[coroutine]
    || {
        yield;
    };
    #[cfg(target_pointer_width = "64")]
    assert_eq!(16, size_of_val(&no_locals));

    // One i32 saved across yield — fits in the 7-byte padding after discriminant.
    // Layout: ptr(8) + disc(1) + pad(3) + i32(4) = 16 bytes.
    let one_local = #[coroutine]
    || {
        let x: i32 = 42;
        yield;
        black_box(x);
    };
    #[cfg(target_pointer_width = "64")]
    assert_eq!(16, size_of_val(&one_local));

    // One i64 saved across yield — also fits in the padding.
    // Layout: ptr(8) + i64(8) = 16 bytes (disc shares space with variant field).
    let one_i64 = #[coroutine]
    || {
        let x: i64 = 42;
        yield;
        black_box(x);
    };
    #[cfg(target_pointer_width = "64")]
    assert_eq!(16, size_of_val(&one_i64));

    // Two non-overlapping i32 locals across different yields.
    // Overlap optimization shares the slot; still fits in padding.
    // Layout: ptr(8) + disc(1) + pad(3) + overlapped_i32(4) = 16 bytes.
    let overlap = #[coroutine]
    || {
        {
            let a: i32 = 1;
            yield;
            black_box(a);
        }
        {
            let b: i32 = 2;
            yield;
            black_box(b);
        }
    };
    #[cfg(target_pointer_width = "64")]
    assert_eq!(16, size_of_val(&overlap));

    // Upvar captured by move — stored as an additional prefix field.
    // Layout: upvar_i32(4) + pad(4) + ptr(8) + disc(1) + pad(7) = 24 bytes.
    // The upvar increases the prefix size beyond what fits in 16 bytes.
    let captured = 99i32;
    let with_upvar = #[coroutine]
    move || {
        yield;
        black_box(captured);
    };
    #[cfg(target_pointer_width = "64")]
    assert_eq!(24, size_of_val(&with_upvar));
}
