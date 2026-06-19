---
name: force-llvm-rebuild
description: How to force x.py / bootstrap to rebuild internal LLVM C++ code (`src/llvm-project/`) by purging the hidden `.llvm-stamp` timestamp file using relative paths. Use this when you edit `CoroFrame.cpp`, `CoroSplit.cpp`, or any LLVM C++ files in `src/llvm-project/` and need stage 1 `rustc_llvm` to relink against the new LLVM static libraries.
---

# Forcing LLVM Rebuild (`.llvm-stamp` Trick)

When you modify internal LLVM C++ source files under `src/llvm-project/` (such as `lib/Transforms/Coroutines/CoroFrame.cpp` or `CoroSplit.cpp`), running `./x b --stage 1` or `./x b llvm` may not recompile the C++ static libraries if `bootstrap` (`x.py`) finds an existing build stamp.

To force `bootstrap` (`x.py`) to recompile the LLVM C++ libraries (`libLLVMCoroutines.a`, etc.) and link them cleanly into `rustc_llvm`, you **must remove the hidden `.llvm-stamp` timestamp file using a relative path before running your build**.

---

## 1. The Exact Command (Using Relative Path)

Always use the **relative path** (`build/x86_64-unknown-linux-gnu/llvm/.llvm-stamp`) when purging the stamp file:

```bash
rm -f build/x86_64-unknown-linux-gnu/llvm/.llvm-stamp
./x b --stage 1
```

Or when building only LLVM:
```bash
rm -f build/x86_64-unknown-linux-gnu/llvm/.llvm-stamp
./x b llvm
```

---

## 2. Why This Is Required

1. **Hidden Stamp Location**: `bootstrap` (`src/bootstrap/src/core/build_steps/llvm.rs`) tracks LLVM build freshness by writing an empty marker file named `.llvm-stamp` (notice the leading dot `.`) into `build/<target>/llvm/`.
2. **Standard Find/Rm Misses Hidden Files**: Because `.llvm-stamp` begins with `.`, normal glob searches or high-level build checks often overlook it.
3. **Triggering C++ Re-compilation & Relinking**: Once `build/x86_64-unknown-linux-gnu/llvm/.llvm-stamp` is deleted, `bootstrap` recognizes that LLVM build state is missing, re-invokes CMake/Ninja on `src/llvm-project/`, re-compiles modified `.cpp` files (`CoroFrame.cpp.o`), and relinks `rustc_llvm` inside `stage1`.
