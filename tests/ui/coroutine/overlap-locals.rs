//@ run-pass
//@ revisions: default retcon
//@[retcon] compile-flags: -Zbackend-coroutines

#![feature(coroutines, stmt_expr_attributes)]

fn main() {
    let a = #[coroutine]
    || {
        {
            let w: i32 = 4;
            yield;
            println!("{:?}", w);
        }
        {
            let x: i32 = 5;
            yield;
            println!("{:?}", x);
        }
        {
            let y: i32 = 6;
            yield;
            println!("{:?}", y);
        }
        {
            let z: i32 = 7;
            yield;
            println!("{:?}", z);
        }
    };
    // Default layout: discriminant (1 byte) + overlapped i32 (4 bytes) = 5, padded to 8.
    // All four locals (w, x, y, z) have non-overlapping liveness and share one 4-byte slot.
    #[cfg(not(retcon))]
    assert_eq!(8, std::mem::size_of_val(&a));
    // Retcon layout: continuation pointer (8 bytes) + discriminant (1 byte) + padding (7 bytes)
    // = 16-byte prefix, then overlapped i32 (4 bytes) + padding (4 bytes) = 24 total.
    // The extra 16 bytes vs default come from the continuation function pointer and its
    // alignment requirements. The overlap optimization still works — all four i32s share
    // one slot; without overlap this would be 32 bytes.
    #[cfg(retcon)]
    assert_eq!(24, std::mem::size_of_val(&a));
}
