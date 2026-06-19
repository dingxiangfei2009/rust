# Reusable GDB script for inspecting runtime crashes in compiled Rust / coroutine binaries.
# Usage: rust-gdb -batch -x /usr/local/google/home/xfding/rust2/.agents/skills/llvm-pass-inspection/scripts/coro_crash.gdb --args <binary>

set pagination off
set print pretty on

# Break on standard panic entry points before stack unwinding crashes or corrupts registers
break panic_already_borrowed
break core::panicking::coroutine_alloc_panic
break core::panicking::panic_cannot_unwind
break rust_panic

run

echo \n=== STACK BACKTRACE ===\n
bt

echo \n=== HARDWARE REGISTERS ===\n
info registers rdi rsi rdx rcx r8 r9 rax rsp rbp rip eflags

echo \n=== DISASSEMBLY AROUND $pc ===\n
x/25i $pc - 30

echo \n=== FIRST ARGUMENT (%rdi) MEMORY DUMP (Upvars & Continuation Pointers) ===\n
x/8gx $rdi

echo \n=== STACK FRAME MEMORY DUMP (%rsp) ===\n
x/16gx $rsp
