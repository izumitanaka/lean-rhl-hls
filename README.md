# Lean RHL HLS

A Lean 4 research prototype integrating **RHL-based memory optimization with a verified path from Lean programs to SystemVerilog**. It extends [*Relational Hoare Logic for High-Level Synthesis of Hardware Accelerators*](https://arxiv.org/abs/2601.09217) (Tanaka, Sakayori, Takamaeda-Yamazaki and Kobayashi, ESOP 2026). Implementation author: **Izumi Tanaka**.

RHL relates programs using arrays to programs using buffers and FIFOs, even though their internal states differ. This project mechanizes that reasoning and connects it to a Lean frontend and a proved RTL backend.

```text
Lean program → hybrid computation IR → buffer insertion / FIFO selection
             → circuit lowering and scheduling → SystemVerilog
```

For the supported fragment, independent syntax and static conditions imply successful RTL generation. Under the documented execution and post-start initialization conditions, the generated text's formal interpretation terminates and preserves source success/failure and public outputs. The guarantee covers a defined two-state SystemVerilog subset; external EDA tools and physical timing are outside it. [Proofs and assumptions](hls/docs/PROOF-MAP.md).

## Current scope and direction

The input uses 32-bit words (`Word = BitVec 32`), predeclared fixed arrays, and supported Lean loops, branches and helper functions. There are two entry points into the common optimizer and backend:

- **`hls_fixed_program`** takes a complete Lean function, array declarations and public outputs. The function is currently treated as one stage.
- **`hls_certified`** registers a processing body. Explicit stage order, iteration ranges and array information expose opportunities for buffer reuse and inter-stage FIFO conversion. SMT-assisted search is available through `CertifiedHLS.compileWithSMT`; candidates are rechecked in Lean.

The goal is to infer that stage information from supported complete Lean functions and automatically apply buffering and eligible FIFO conversion. Automatic stage extraction is not yet implemented. [Entry details](hls/docs/LEAN-ENTRY.ja.md#入口の使い分け).

## Try it

[Browse runnable Lean programs alongside their generated RTL](hls/examples/README.md): increment, filter, swap, nested loops and prefix sum.

```lean
import IRComparison.Frontend.LeanHLSCommand
open IRComparison HybridWord

def buffers : FixedMemory.Declarations := #[(0,5),(1,5)]
def increment (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 5 1 do
    let v ← (t.arrays 0)[i.toNat]?
    t ← t.write 1 i (v+1)
  return t

hls_fixed_program increment using buffers as incrementHLS
-- incrementHLS.compile [1] produces an artifact whose .text is SystemVerilog.
```

Array 0 containing `[3,6,9,12,15]` produces `[4,7,10,13,16]` in array 1. Run this example and a producer/filter example with buffering and FIFO conversion:

```sh
cd hls
lake build IRComparison IRComparison.Tests
lake env lean --run scripts/intro-example.lean
python3 scripts/check-intro-example.py
```

Use the pinned Lean 4.29.0 toolchain; these examples also require Z3, Python 3, Icarus Verilog and Yosys. Generated RTL and local check results go to `hls/artifacts/intro-example/`. The [walkthrough](hls/docs/WALKTHROUGH.md) explains each transformation and shows the emitted RTL interface.

## Documentation

- [Proof map](hls/docs/PROOF-MAP.md#rhl-rules-in-the-executable-memory-transformation): RHL rules → Lean declarations → transformation proofs and the end-to-end guarantee.
- [Technical note](hls/docs/TECHNICAL-NOTE.md): design, relationship to the paper, automatic choices and guarantee boundaries.
- [Input specification](hls/docs/LEAN-ENTRY.ja.md) and [IR syntax/transformation rules](hls/docs/HLS-SYNTAX-RULES.ja.md) (Japanese).
- [Reproduction](hls/docs/REPRODUCING.md), [workloads](hls/docs/BENCHMARKS.md), and [dependencies](hls/docs/DEPENDENCIES.md).

`hls/` is a self-contained Lean project. [Citation metadata](CITATION.cff) identifies this implementation; cite a specific commit for reproducibility. A project license has not yet been assigned.
