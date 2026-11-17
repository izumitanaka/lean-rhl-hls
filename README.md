# Lean RHL HLS

This project extends the framework introduced in [*Relational Hoare Logic for High-Level Synthesis of Hardware Accelerators*](https://arxiv.org/abs/2601.09217) (Tanaka, Sakayori, Takamaeda-Yamazaki and Kobayashi, ESOP 2026) toward a Lean-based, formally verified HLS compiler. Implementation author: **Izumi Tanaka**.

The focus is the **integration of relational memory transformations with a verified path from Lean computations to RTL**. RHL explains why a program using arrays and a program using buffers/FIFOs compute the same observable result, even though their internal states differ. This implementation connects that reasoning to an ordinary-Lean frontend and a SystemVerilog backend.

For the supported Lean fragment, independent syntax and static conditions imply successful RTL generation. Separately, under the documented execution and initialization conditions, the generated circuit finishes and preserves source success/failure and public outputs. These are general proofs, not just tests of individual examples. See [what this guarantee assumes](#what-is-proved-and-trusted).

## What goes in, and what comes out?

```text
ordinary Lean definitions (32-bit words, fixed arrays)
    │
    ├─ a complete function + array declarations + public outputs
    │      source loops and sequencing are kept inside one stage
    │
    └─ processing bodies + explicit stage order and iteration ranges
           exposes producer/consumer relations for memory optimization
    │
    ▼
hybrid computation IR: values + ordered reads/updates + structured control
    → buffer insertion, then whole-array FIFO / memory selection
    → structured circuit control and shared combinational expressions
    → clock scheduling, finite-width storage and SystemVerilog text
```

Both entries use the common optimizer and backend. A complete function is currently supplied as **one stage with one external iteration**; its inner loops are not automatically extracted into separate producer/consumer stages. Explicit stage information exposes opportunities for cross-iteration reuse and communication conversion. This is a current frontend distinction, not a requirement for two different backends.

| Entry | You provide | Automatic work and result |
|---|---|---|
| `hls_fixed_program` | A complete `State → Option State` function, fixed array IDs/lengths, public outputs | Parse loops/branches/updates, construct the fixed-array entry and proof connection, compile to RTL; source-syntax generation-success theorem applies under its conditions |
| `hls_certified` | A processing body; then its designated input array and iteration range; for multiple bodies, stage order, sizes/layout and public outputs | Construct body correspondence proofs; analyze buffer reuse and array routing from the supplied stages; compile the accepted plan to RTL |

`hls_certified` does not invoke SMT by itself. Its `.compile` uses the pure compiler; `CertifiedHLS.compileWithSMT` adds SMT-assisted candidate search with Lean-side rechecking. `hls_word` and `hls_program` expose lower-level parts of these entries. [Exact entry API](hls/docs/LEAN-ENTRY.ja.md#入口の使い分け).

## A small example you can run

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

Here `State` supplies scalar registers and arrays. `Word` is `BitVec 32`, so arithmetic wraps. The function writes `[4,7,10,13,16]` when array 0 contains `[3,6,9,12,15]`. The generated module has clock/reset/start, configuration and readout ports, and done/error outputs.

The [input-to-RTL walkthrough](hls/docs/WALKTHROUGH.md) shows the actual generated RTL interface and a second example:

```text
producer writes B → filter repeatedly reads B[i], B[i+1], B[i+2]
    ↓ buffer insertion: hold reusable values, read one new value per refill
    ↓ FIFO conversion: replace B's storage by ordered sends and receives
producer sends 5 values → buffered filter receives 5 values → public output C
```

Buffer insertion reduces repeated reads; FIFO conversion changes the storage/communication mechanism. Either may be useful without the other. A FIFO decision does not by itself parallelize the stages.

```sh
cd hls
lake build IRComparison IRComparison.Tests
lake env lean --run scripts/intro-example.lean
python3 scripts/check-intro-example.py
```

Use the pinned Lean 4.29.0 toolchain. These examples additionally need Z3, Python 3, Icarus Verilog and Yosys. They generate `increment.sv` and `filter.sv` under `hls/artifacts/intro-example/`, check the formal text interpreter, and check the external RTL including restart. [Full reproduction guide](hls/docs/REPRODUCING.md).

## What comes from the paper, and what is added here?

| Foundation from the RHL paper | What this Lean implementation adds |
|---|---|
| Relate array and stream states using logical index sequences; justify insertion/read replacement by relational rules | Mechanize the reasoning and adapt it to the BV32 hybrid IR, including buffers backed by retained memory |
| Buffer insertion and stream conversion as HLS-oriented memory transformations | Compose checked transformations with ordinary Lean source correspondence and a proof-carrying compilation plan |
| A framework used with an external HLS flow | Implement and prove structured circuit lowering, scheduling, shared expressions, finite-width evaluation and SystemVerilog text emission |

The paper did not provide this Lean compiler. [`PaperCore`](hls/src/PaperCore/README.md) is named for the paper's core language: its Lean formalization supplies semantic, array-analysis, index-sequence and SMT support. HLS-specific rules and backend theorems live in `IRComparison`; importing PaperCore alone does not prove the whole compiler. [Design and attribution](hls/docs/TECHNICAL-NOTE.md).

## What is proved and trusted?

| Claim or boundary | Meaning |
|---|---|
| **Generation success** | `OrdinarySource.generates` derives frontend success, code correspondence, construction of a fixed-array Entry and RTL generation from independent syntax/type/scope/environment/declaration conditions. Parser success and a generated Entry are not assumptions. |
| **Execution preservation** | Entry and backend correctness connect the original Lean computation to the defined interpretation of emitted SystemVerilog text. Under layout, plan-readiness, input-fit and post-start storage-agreement conditions, execution terminates with the same success/failure and public outputs. |
| **Proof checking and SMT** | Lean checks the proofs. The Lean implementation and native environment interface are trusted. SMT proposes optimization candidates; Lean checks their admissibility and constructs a certified plan. Rejection or timeout retains the last accepted plan. |
| **Setup and external tools** | Reset/configuration/readout have separate conditional theorems. External 32-bit IDs/addresses need representability checks; arbitrary source-state configuration is not proved. The formal text semantics covers a specified two-state subset, not all IEEE SystemVerilog, external EDA correctness or physical timing. |

Compilation success does not mean every source input avoids an out-of-bounds access. Finite FIFOs fail on empty receive/full send rather than wait for backpressure. Failure reasons and intermediate post-failure state are outside the observation relation. [Premises and theorem map](hls/docs/PROOF-MAP.md).

## Where to read next

- [Walkthrough](hls/docs/WALKTHROUGH.md): Lean → hybrid IR → memory transformation → RTL, with executable examples.
- [Technical note](hls/docs/TECHNICAL-NOTE.md): IR design, RHL rules, automatic choices and implementation scope.
- [Proof map](hls/docs/PROOF-MAP.md): source files, theorem statements and trust boundaries.
- [Input specification](hls/docs/LEAN-ENTRY.ja.md) and [IR syntax/transformation rules](hls/docs/HLS-SYNTAX-RULES.ja.md) (Japanese).
- [Reproduction](hls/docs/REPRODUCING.md), [workloads](hls/docs/BENCHMARKS.md), and [dependencies](hls/docs/DEPENDENCIES.md).

`hls/` is a self-contained Lean project. `IRComparison` originated in experiments comparing imperative, functional and hybrid IR designs; the current path described here uses the hybrid design. Generated RTL and logs stay in local `artifacts/`.

[Citation metadata](CITATION.cff) identifies this project; cite a specific commit for reproducibility. No DOI or project license is assigned. The implementation does not establish a priority claim or inherit the original paper's measured FPGA speedups.
