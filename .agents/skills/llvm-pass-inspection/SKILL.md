---
name: llvm-pass-inspection
description: Comprehensive guide and toolkit for inspecting initial/intermediate LLVM IR passes, MIR transformations, and low-level GDB debugging tricks (`rust-gdb -batch`, register/disassembly tracing, memory layout inspection) for compiled Rust coroutine binaries.
---

# LLVM Pass, MIR & GDB Debugging Guide for Coroutines

When diagnosing runtime crashes (`SIGSEGV`, `RefCell already borrowed`, `coroutine frame exceeded LLVM buffer size`), verifying zero-overhead codegen (`Id->getStorageSize() == 0`), or inspecting pass-by-pass transformations (`CoroSplitPass`, `CoroFrame`), use the exact flags, debugging tricks, and GDB scripts below.

---

## Part 1: GDB Debugging Tricks (`rust-gdb -batch`)

Per `AGENTS.md`, never use `println!` tracing or blind `compiletest` retries to debug runtime crashes or ABI violations in compiled tests. Always use `rust-gdb -batch` directly on the compiled test binary (`-g` enabled).

### 1. Catching Panics Before Unwinding Crashes (`SIGSEGV`)
Often, when a coroutine or `RefCell` panics (`coroutine_alloc_panic` or `RefCell already borrowed`), stack unwinding encounters `SIGSEGV` or aborts (`core dumped`), obscuring the exact failure frame.
Break directly on standard library panic entry points:
```bash
rust-gdb -batch \
    -ex "b panic_already_borrowed" \
    -ex "b core::panicking::coroutine_alloc_panic" \
    -ex "run" \
    -ex "bt" \
    -ex "frame 1" \
    -ex "info locals" \
    -ex "info registers" \
    --args ./async-fn-retcon
```

### 2. Inspecting Disassembly and Hardware Registers Around `$pc`
To see exact instructions, stack pointer (`%rsp`), and register state (`%rdi`, `%rsi`, `%rax`) around the crash address:
```bash
rust-gdb -batch \
    -ex "run" \
    -ex "x/25i \$pc - 30" \
    -ex "info registers rdi rsi rdx rcx rax rsp rbp" \
    --args ./async-fn-retcon
```

### 3. Tracing Coroutine Struct Layout & Memory Words in GDB
To verify what sits inside a `Coroutine` (`&mut Coroutine` or `fut` passed in `%rdi`) during `Future::poll` or `ramp_instance`:
```bash
rust-gdb -batch \
    -ex "b async_fn_retcon::run_steps::{async_fn#0}::{closure#0}::{shim:ramp#0}" \
    -ex "run" \
    -ex "info registers rdi" \
    -ex "x/6gx \$rdi" \
    --args ./async-fn-retcon
```
**Memory Verification Checklist**:
- **Upvars (`offset 0x00..` under `prefix N -> field N`)**: Check if `0x00` (`fut.0`) holds a valid heap `RcBox` address (`0x00005555...` with strong/weak counts) or if it has been corrupted by stack pointers (`0x00007fff...`).
- **Continuation Pointer (`offset 0x08..` or `upvar_count * 8`)**: Check if the function pointer field (`cont_field_idx`) holds the address of `ramp_instance` (`0x00005555...`) or `null` (`0x0000000000000000`).

---

## Part 2: MIR Debugging & Liveness Tricks (`rustc` internal flags)

Before lowering to `rustc_codegen_llvm`, inspect how `rustc_mir_transform` transforms coroutine shims (`shim.rs`):

### 1. Dump All MIR Stages (`-Z dump-mir=all`)
```bash
./build/x86_64-unknown-linux-gnu/stage1/bin/rustc --edition=2021 \
    tests/ui/coroutine/async-fn-retcon.rs \
    -Zbackend-coroutines \
    -Z dump-mir=run_steps \
    -o async-fn-retcon
```
Inspect the dumped files (`mir_dump/async_fn_retcon.run_steps-04-ramp.MakeShim.0.mir`) to check exact statements in `BB0`, `BB_SETUP`, and `BB_YIELD`.

### 2. Inspecting Cross-Call Liveness (`-Z dump-mir-dataflow`)
To check which variables are live across `TerminatorKind::Call` (`@llvm.coro.suspend.retcon`) before LLVM `CoroFrame` runs:
```bash
./build/x86_64-unknown-linux-gnu/stage1/bin/rustc --edition=2021 \
    tests/ui/coroutine/async-fn-retcon.rs \
    -Zbackend-coroutines \
    -Z dump-mir-dataflow=run_steps \
    -o async-fn-retcon
```

---

## Part 3: LLVM Pass & Intermediate IR Inspection (`-C llvm-args`)

### 1. Dumping Initial & Stage-by-Stage Bitcode (`-C save-temps`)
```bash
./build/x86_64-unknown-linux-gnu/stage1/bin/rustc --edition=2021 \
    tests/ui/coroutine/async-fn-retcon.rs \
    -Zbackend-coroutines \
    -C save-temps \
    --emit=llvm-ir,asm \
    -o async-fn-retcon
```
- `*.0.pre-opt.ll`: Unoptimized initial LLVM IR from `rustc_codegen_llvm`.
- `*.1.opt.ll`: Optimized LLVM IR after `CoroSplitPass`.

### 2. Printing Intermediate IR Across Passes (`-print-after-all`)
```bash
./build/x86_64-unknown-linux-gnu/stage1/bin/rustc --edition=2021 \
    tests/ui/coroutine/async-fn-retcon.rs \
    -Zbackend-coroutines \
    -C llvm-args=-print-before-all \
    -C llvm-args=-print-after-all \
    -o async-fn-retcon 2> llvm_passes.log
```

### 3. Filtering on `CoroSplitPass` with Module Scope
```bash
./build/x86_64-unknown-linux-gnu/stage1/bin/rustc --edition=2021 \
    tests/ui/coroutine/async-fn-retcon.rs \
    -Zbackend-coroutines \
    -C llvm-args=-print-after-all \
    -C llvm-args=-filter-passes=CoroSplitPass \
    -C llvm-args=-print-module-scope \
    -o async-fn-retcon
```
**CoroSplitPass Verification**:
1. Check the synthesized coroutine frame struct (`%.coro.frame = type { ... }`).
2. If `%.coro.frame` has fields beyond `.resume.0`, those fields are local variables (`%buffer`, `%return_ptr`) live across `@llvm.coro.suspend.retcon`.
3. Eliminate their liveness in `coroutine/shim.rs` (`bb_yield`) so `%.coro.frame` size (`B.getStructSize()`) equals `0`.

---

## Part 4: Reusable GDB Scripts (`scripts/`)

This skill includes reusable GDB scripts in `scripts/`:
- `scripts/coro_crash.gdb`: Automatically sets breakpoints on `coroutine_alloc_panic`, `panic_already_borrowed`, and `SIGSEGV`, prints backtraces, registers, disassembly, and local memory blocks.
