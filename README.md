# Lean RHL HLS

A Lean 4 research prototype for certified memory transformations and SystemVerilog generation. Author: **Izumi Tanaka**.

```text
supported ordinary Lean definitions (Word = BitVec 32)
    → argument-retaining frontend and source correspondence
    → hybrid computation IR
    → buffer insertion and whole-array FIFO / memory decisions
    → structured control, shared expressions, cycle scheduling
    → finite circuit → SystemVerilog text
```

The fixed-array whole-function entry and the optimization entry with explicit kernel/task information are distinct. Automatic extraction of a FIFO task decomposition from arbitrary whole functions is not implemented.

## What is proved

- `OrdinarySource.generates`: independent source syntax, typing, scope, environment and fixed-array conditions imply success of the ordinary `compileRetained` frontend, a code correspondence, construction of a fixed-array entry, and RTL generation. Parser success and an already-generated entry are **not** premises of this theorem.
- Semantic preservation is a separate chain of general theorems. Under the specified input, layout and initial-state conditions, generated execution preserves source success/failure and public outputs. Compilation success does not imply that every source input executes successfully.
- The ordinary structured backend uses shared combinational values and validity conditions through analysis, finite-width lowering and RTL emission. It retains loops and supports checked scheduling and limited overlap across iteration boundaries.
- Optimization candidates are checked in Lean. Greedy whole-array FIFO selection retains the last certified plan on rejection or timeout. Removed frontend modes are not automatic fallbacks.

See the [proof map](hls/docs/PROOF-MAP.md), [technical scope](hls/docs/TECHNICAL-NOTE.md), and [reproduction guide](hls/docs/REPRODUCING.md). The [implementation guide](hls/README.md) links the input specification and IR transformation rules.

## Input example

```lean
import IRComparison.Frontend.LeanHLSCommand
open IRComparison HybridWord

def buffers : FixedMemory.Declarations := #[(0,4),(1,4)]

def program (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for i in HybridWord.range 0 3 1 do
    t ← t.copy 1 0 4
    let v ← (t.arrays 1)[i.toNat]?
    t ← t.write 0 i (v+1)
  return t

hls_fixed_program program using buffers as generated
#check generated.compile
#check generated.correct
#check generated.generates
```

Arrays are declared before computation; copies use declared equal-length regions. Helper scalar arguments retain their call-time values even if the helper updates State. The generated `.generates` declaration concerns the constructed Entry; the independent source-syntax theorem is `OrdinarySource.generates`. See [input conditions](hls/docs/LEAN-ENTRY.ja.md).

## Check the artifact

```sh
cd hls
lake build IRComparison IRComparison.Tests
lake env lean Audit.lean
lake env lean scripts/structural-frontend.lean
lake env lean scripts/check-current-entry.lean
lake env lean --run scripts/shared-normal-hls.lean
python3 scripts/check-shared-normal-hls.py
```

Use Lean 4.29.0 and the pinned dependencies. External RTL checks require Python, Icarus Verilog and Yosys; additional SMT tests require Z3. The commands above reproduce the proof audit, ordinary-input regressions and focused RTL checks. Generated logs and measurements stay local; see [workload scope](hls/docs/BENCHMARKS.md).

## Boundaries

This is a restricted ordinary-Lean frontend, not arbitrary Lean compilation. The text semantics covers a specified two-state SystemVerilog subset, not all IEEE semantics. Finite FIFO empty reads and full writes fail rather than wait for backpressure. Memories use combinational reads and clocked writes; synchronous RAM, physical timing and external EDA correctness are outside the guarantee. External 32-bit ports require representability conditions; arbitrary initial-state configuration through those ports is not yet proved.

The current source and proof path no longer includes the old direct-substitution body or compatibility parser fallback. Type-conversion budgets and Word/BitVec alias cleanup remain separate work.

## Layout and attribution

| Path | Purpose |
|---|---|
| `hls/` | Current compiler, proofs, examples, comparison paths and scripts |
| `hls/src/PaperCore/` | 14 support modules compiled within the HLS package |
| `hls/docs/` | Public overview, proof map, reproduction and measurement scope |

The `IRComparison` namespace is retained from the comparison experiments. This artifact builds on the earlier RHL research; see the [technical note](hls/docs/TECHNICAL-NOTE.md) for attribution and scope. No priority or performance superiority over other certified HLS systems is claimed.

[Citation metadata](CITATION.cff) identifies the project; cite a specific commit or release for reproducibility. No DOI or project license is assigned. [Dependency provenance](hls/docs/DEPENDENCIES.md).
