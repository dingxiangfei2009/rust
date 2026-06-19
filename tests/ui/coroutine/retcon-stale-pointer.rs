//@ run-pass
//@ compile-flags: -Zbackend-coroutines -C opt-level=2

// Adversarial test for retcon coroutine out-pointer correctness.
//
// The coroutine is resumed from different stack frames via #[inline(never)]
// functions. Between resumes, we clobber the stack to invalidate any
// stale pointers from previous resumes. If the coroutine uses a stale
// yield_out or return_out pointer, it writes to dead stack memory,
// producing garbage values or a crash.

#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

/// Clobber stack memory to invalidate stale pointers.
/// The volatile writes prevent the optimizer from removing this.
#[inline(never)]
fn clobber_stack() {
    let mut garbage = [0xDEADBEEFu32; 64];
    for i in 0..garbage.len() {
        // Use black_box to prevent optimization
        garbage[i] = std::hint::black_box(0xCAFEBABEu32);
    }
    std::hint::black_box(&garbage);
}

#[inline(never)]
fn resume_from_deep_stack(
    mut coro: Pin<&mut impl Coroutine<(), Yield = u64, Return = u64>>,
) -> CoroutineState<u64, u64> {
    // Allocate a large-ish stack frame to push the out pointers
    // to different addresses than previous resumes.
    let padding = [0u8; 256];
    std::hint::black_box(&padding);
    coro.as_mut().resume(())
}

#[inline(never)]
fn resume_from_shallow_stack(
    mut coro: Pin<&mut impl Coroutine<(), Yield = u64, Return = u64>>,
) -> CoroutineState<u64, u64> {
    // Minimal stack frame — different address than deep_stack.
    coro.as_mut().resume(())
}

fn main() {
    // Test: Alternate between deep and shallow stack resumes.
    // Each resume gets different out-pointer addresses.
    // If the coroutine uses a stale pointer, the yielded value will be garbage.
    {
        let mut coro = #[coroutine]
        || {
            let mut acc: u64 = 0;
            // 8 yields, alternating between deep and shallow stack resumes
            acc += 1;
            yield acc;  // 1
            acc += 2;
            yield acc;  // 3
            acc += 3;
            yield acc;  // 6
            acc += 4;
            yield acc;  // 10
            acc += 5;
            yield acc;  // 15
            acc += 6;
            yield acc;  // 21
            acc += 7;
            yield acc;  // 28
            acc += 8;
            acc          // return 36
        };

        let mut pinned = Pin::new(&mut coro);
        let expected_yields = [1u64, 3, 6, 10, 15, 21, 28];

        for (i, &expected) in expected_yields.iter().enumerate() {
            // Clobber stack between resumes to invalidate stale pointers
            clobber_stack();

            let result = if i % 2 == 0 {
                resume_from_deep_stack(pinned.as_mut())
            } else {
                resume_from_shallow_stack(pinned.as_mut())
            };

            match result {
                CoroutineState::Yielded(val) => {
                    assert_eq!(val, expected, "yield {} mismatch: got {}, expected {}", i, val, expected);
                }
                other => panic!("Expected Yielded({}) at step {}, got {:?}", expected, i, other),
            }
        }

        // Final resume should complete
        clobber_stack();
        match resume_from_deep_stack(pinned.as_mut()) {
            CoroutineState::Complete(36) => {},
            other => panic!("Expected Complete(36), got {:?}", other),
        }
    }

    // Test 2: Diamond with clobbered stack between resumes
    {
        let take_left = std::hint::black_box(true);
        let mut coro = #[coroutine]
        move || {
            if take_left {
                yield 100u64;
            } else {
                yield 200u64;
            }
            // Join point — uses out pointer from a different stack frame
            yield 300u64;
            400u64
        };

        let mut pinned = Pin::new(&mut coro);

        // First resume from deep stack
        let r1 = resume_from_deep_stack(pinned.as_mut());
        assert_eq!(r1, CoroutineState::Yielded(100));

        // Clobber stack, then resume from shallow stack (different out pointers!)
        clobber_stack();
        let r2 = resume_from_shallow_stack(pinned.as_mut());
        assert_eq!(r2, CoroutineState::Yielded(300));

        // Clobber again, resume from deep stack
        clobber_stack();
        let r3 = resume_from_deep_stack(pinned.as_mut());
        assert_eq!(r3, CoroutineState::Complete(400));
    }

    // Test 3: Loop with yield, clobbered between each iteration
    {
        let n = std::hint::black_box(10u64);
        let mut coro = #[coroutine]
        move || {
            let mut sum = 0u64;
            let mut i = 0u64;
            while i < n {
                sum += i;
                yield sum;
                i += 1;
            }
            sum
        };

        let mut pinned = Pin::new(&mut coro);
        let mut expected_sum = 0u64;
        for i in 0..10u64 {
            expected_sum += i;
            clobber_stack();
            let result = if i % 3 == 0 {
                resume_from_deep_stack(pinned.as_mut())
            } else {
                resume_from_shallow_stack(pinned.as_mut())
            };
            assert_eq!(result, CoroutineState::Yielded(expected_sum),
                "loop iteration {} failed", i);
        }
        clobber_stack();
        let final_result = resume_from_deep_stack(pinned.as_mut());
        assert_eq!(final_result, CoroutineState::Complete(45));
    }
}
