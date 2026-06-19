//@ run-pass
//@ compile-flags: -Zbackend-coroutines -C opt-level=2

// Test that retcon coroutines correctly handle diamond CFG patterns
// where different branches yield and then join. The coroutine is
// resumed through #[inline(never)] functions to prevent the optimizer
// from constant-propagating pointer values — forcing each resumption
// to use genuinely different out-pointer addresses.

#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

#[inline(never)]
fn resume_once(coro: Pin<&mut impl Coroutine<(), Yield = i32, Return = i32>>) -> CoroutineState<i32, i32> {
    coro.resume(())
}

#[inline(never)]
fn resume_twice(mut coro: Pin<&mut impl Coroutine<(), Yield = i32, Return = i32>>) -> (CoroutineState<i32, i32>, CoroutineState<i32, i32>) {
    let first = coro.as_mut().resume(());
    let second = coro.as_mut().resume(());
    (first, second)
}

#[inline(never)]
fn resume_to_completion(mut coro: Pin<&mut impl Coroutine<(), Yield = i32, Return = i32>>) -> Vec<CoroutineState<i32, i32>> {
    let mut results = Vec::new();
    loop {
        let state = coro.as_mut().resume(());
        let done = matches!(state, CoroutineState::Complete(_));
        results.push(state);
        if done { break; }
    }
    results
}

fn main() {
    // Test 1: Linear coroutine through #[inline(never)] boundary
    {
        let mut coro = #[coroutine]
        || {
            let x = 10;
            yield x;
            let y = 20;
            yield x + y;
            x + y + 30
        };
        let mut pinned = Pin::new(&mut coro);
        assert_eq!(resume_once(pinned.as_mut()), CoroutineState::Yielded(10));
        assert_eq!(resume_once(pinned.as_mut()), CoroutineState::Yielded(30));
        assert_eq!(resume_once(pinned.as_mut()), CoroutineState::Complete(60));
    }

    // Test 2: Diamond pattern — branch, yield on each side, join
    {
        let condition = std::hint::black_box(true);
        let mut coro = #[coroutine]
        move || {
            let base = 100;
            if condition {
                yield base + 1;  // yield 101
            } else {
                yield base + 2;  // yield 102
            }
            // Join point: after the diamond, yield the sum
            yield base + 3;      // yield 103
            base + 4             // return 104
        };
        let mut pinned = Pin::new(&mut coro);
        // First resume: enters the coroutine, condition=true → yields 101
        match pinned.as_mut().resume(()) {
            CoroutineState::Yielded(101) => {},
            other => panic!("Expected Yielded(101), got {:?}", other),
        }
        // Second resume through a DIFFERENT #[inline(never)] fn → yields 103 (join point)
        // This forces a different stack frame with different out-pointer addresses.
        #[inline(never)]
        fn resume_join(coro: Pin<&mut impl Coroutine<(), Yield = i32, Return = i32>>) -> CoroutineState<i32, i32> {
            coro.resume(())
        }
        match resume_join(pinned.as_mut()) {
            CoroutineState::Yielded(103) => {},
            other => panic!("Expected Yielded(103), got {:?}", other),
        }
        // Third resume through yet another #[inline(never)] fn → returns 104
        #[inline(never)]
        fn resume_final(coro: Pin<&mut impl Coroutine<(), Yield = i32, Return = i32>>) -> CoroutineState<i32, i32> {
            coro.resume(())
        }
        match resume_final(pinned.as_mut()) {
            CoroutineState::Complete(104) => {},
            other => panic!("Expected Complete(104), got {:?}", other),
        }
    }

    // Test 3: Loop with yield — each iteration is a new epoch.
    // First 2 iterations resume in main, remaining iterations + completion
    // resume in a separate #[inline(never)] subroutine to force different
    // out-pointer addresses mid-loop.
    {
        let mut coro = #[coroutine]
        || {
            let mut i = 0i32;
            while i < 5 {
                yield i;
                i += 1;
            }
            i * 10
        };
        let mut pinned = Pin::new(&mut coro);
        // First 2 iterations in main's stack frame
        assert_eq!(pinned.as_mut().resume(()), CoroutineState::Yielded(0));
        assert_eq!(pinned.as_mut().resume(()), CoroutineState::Yielded(1));

        // Hand off to a subroutine for remaining iterations
        #[inline(never)]
        fn finish_loop(
            mut coro: Pin<&mut impl Coroutine<(), Yield = i32, Return = i32>>,
        ) -> Vec<CoroutineState<i32, i32>> {
            let mut results = Vec::new();
            loop {
                let state = coro.as_mut().resume(());
                let done = matches!(state, CoroutineState::Complete(_));
                results.push(state);
                if done { break; }
            }
            results
        }
        let rest = finish_loop(pinned.as_mut());
        assert_eq!(rest.len(), 4); // yields 2,3,4 + complete
        assert_eq!(rest[0], CoroutineState::Yielded(2));
        assert_eq!(rest[1], CoroutineState::Yielded(3));
        assert_eq!(rest[2], CoroutineState::Yielded(4));
        assert_eq!(rest[3], CoroutineState::Complete(50));
    }

    // Test 4: Nested calls through multiple #[inline(never)] levels
    {
        let mut coro = #[coroutine]
        || {
            yield 1i32;
            yield 2;
            yield 3;
            4
        };
        let (first, second) = resume_twice(Pin::new(&mut coro));
        assert_eq!(first, CoroutineState::Yielded(1));
        assert_eq!(second, CoroutineState::Yielded(2));
        // Resume the rest through another #[inline(never)] call
        let rest = resume_to_completion(Pin::new(&mut coro));
        assert_eq!(rest, vec![CoroutineState::Yielded(3), CoroutineState::Complete(4)]);
    }

    // Test 5: Move coroutine into Box after resuming once on stack
    {
        let mut coro = #[coroutine]
        || {
            yield 500i32;
            yield 600;
            700
        };
        let mut pinned = Pin::new(&mut coro);
        assert_eq!(pinned.as_mut().resume(()), CoroutineState::Yielded(500));
        drop(pinned);

        // Move the coroutine structure from the stack to the heap (Box)
        let boxed = Box::new(coro);
        let mut pinned2 = Box::into_pin(boxed);

        // Resume again from the new address
        assert_eq!(pinned2.as_mut().resume(()), CoroutineState::Yielded(600));
        assert_eq!(pinned2.as_mut().resume(()), CoroutineState::Complete(700));
    }
}
