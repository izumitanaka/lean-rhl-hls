# From Lean to RTL, with and without memory transformation

This walkthrough uses two runnable examples: a complete Lean function, then two processing stages whose intermediate array becomes a FIFO. Both use the same compiler backend. The complete source and checks are in [intro-example.lean](../scripts/intro-example.lean).

From `hls/`, after building the project:

```sh
lake env lean --run scripts/intro-example.lean
python3 scripts/check-intro-example.py
```

The first command requires Z3 for the second example. It checks the native computations, the selected memory plan, and execution of the emitted text in the formal SystemVerilog interpreter. The second requires Icarus Verilog and Yosys; it checks configuration, two invocations of each circuit, readout, and synthesis structure. It does not measure physical timing. Outputs are generated under `artifacts/intro-example/`.

## 1. A complete Lean function

The source reads five words from array 0 and writes each word plus one to array 1:

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
```

`State` contains scalar registers (`regs`) and arrays (`arrays`), indexed by numeric IDs. Source programs do not contain the backend's FIFO storage, program counter, or holding registers. `Word` is an alias for `BitVec 32`: arithmetic wraps modulo 2³². This fixed width is the current source interface; the backend may use wider intermediate calculations followed by explicit rounding.

Array IDs and lengths are declared before computation. The input values live in the initial State. The loop visits 0 through 4; `Option` makes failed accesses explicit. No scheduling pragmas are needed.

The command registers these operations and proofs:

| Declaration | Role |
|---|---|
| `incrementHLS.compile [1]` | Compile with array 1 as the public output; returns a compiled artifact or an error |
| `incrementHLS.correct` | Relate successful compilation and admissible initial states to the original `increment` computation |
| `incrementHLS.generates` | Prove generation succeeds for this constructed fixed-array Entry and declared outputs |

The general theorem that constructs an Entry from independent source syntax and static conditions is separately named `OrdinarySource.generates`. It is not inferred from the fact that this example compiles.

The runnable script writes the compiled artifact's `.text` to `increment.sv`. For input `[3,6,9,12,15]`, it checks output `[4,7,10,13,16]`.

## 2. What the hybrid computation IR represents

Here is a readable schematic of the lowered body; it is explanatory notation, not another accepted source language:

```text
for iteration in 0..<5:
    i := wrap32(iteration)
    let v ← read array[0][i]
    write array[1][i] := wrap32(v + 1)
```

The actual constructor dump is generated as `increment-ir.txt`. Three concepts are kept separate:

| Part | Example | Meaning |
|---|---|---|
| `Value` | `wrap32(v + 1)` | Compute from already available values; no memory or register read |
| `ReadCode` | Read array 0; bind its result | Perform ordered reads and value computations, retaining their success/failure behavior |
| Commands | Write array 1; sequence; branch; loop | Change state and specify structured execution order; the target also supports buffers and communication |

“Hybrid” refers to this combination of value expressions/bindings and explicit stateful execution. It is close to an imperative structured program with an expression layer; it is not a flat SSA control-flow graph. Value bindings let proofs retain a call-time value, while explicit memory operations let the memory transformation change how that value is obtained.

For example, two uses of a bound value may share one combinational node and its validity condition. This preserves evaluation order: an unused invalid read still fails, while a read in an unselected branch is not performed. Sharing does not introduce a new clocked register or a pipeline stage by itself.

## 3. Exposing stages for buffer insertion and FIFO conversion

The complete-function version is [Filter.lean](../examples/Filter.lean): its two loops are extracted automatically, so no stage list or separate range metadata is needed. The example below exposes those stages explicitly to show how buffer insertion and FIFO conversion work. Both use the same optimizer and backend.

The optimization example describes a producer and a three-point filter:

```lean
def producer (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let v ← (s.arrays 0)[i.toNat]?
  s.write 1 i (v+1)

def filter (i _x _y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 1)[i.toNat]?
  let b ← (s.arrays 1)[(i+1).toNat]?
  let c ← (s.arrays 1)[(i+2).toNat]?
  s.write 2 i ((a+b+c)/3)

hls_certified producer as producerHLS
hls_certified filter as filterHLS
```

The script supplies stage metadata: producer indices 0…4, filter indices 0…2, designated input arrays 0 and 1, array lengths, and public output array 2. It constructs a `CertifiedHLS.Entry` from the generated body entries and calls `CertifiedHLS.compileWithSMT`. The `hls_certified` command itself does not launch Z3; its generated `.compile` uses the pure compiler.

The stage API currently also takes a `supplier : Unit → List Int` field. This example passes `fun _ => []`; the symbolic path derives the producer's index sequence from its code and range rather than enumerating this field. The complete API invocation is in the runnable script.

Before optimization, the computation is:

```text
for i = 0..4: B[i] := A[i] + 1
for i = 0..2: C[i] := (B[i] + B[i+1] + B[i+2]) / 3
```

First, **buffer insertion** retains values reused across filter iterations. This still works with B stored in memory:

```text
b0 := B[0]; b1 := B[1]; b2 := B[2]
for i = 0..2:
    C[i] := (b0 + b1 + b2) / 3
    if i < 2:
        b0 := b1; b1 := b2; b2 := B[i+3]
```

These are scalar holding locations replacing repeated array reads, not a second full-sized copy of B. The filter reads B five times instead of nine. Its final iteration does not perform an out-of-bounds refill. Arithmetic in these schematics has the same BV32 rounding as the Lean source.

Second, **FIFO conversion** replaces B's storage and accesses, once the producer's write order and the buffered consumer's read order are shown to match:

```text
for i = 0..4: send q (A[i] + 1)
b0 := receive q; b1 := receive q; b2 := receive q
for i = 0..2:
    C[i] := (b0 + b1 + b2) / 3
    if i < 2:
        b0 := b1; b1 := b2; b2 := receive q
```

There are five sends and five receives. The example verifies that the actual selected FIFO-array set is `[1]`, the buffer has three values, and each refill retains two values and reads one new value. Starting with zero-filled output storage gives `[7,10,13,0,0]`; the last two output elements are unchanged.

The stages execute in source order here. FIFO selection alone does not make them concurrent or establish a performance gain. If FIFO conversion is rejected, a valid memory plan is retained; a memory-backed buffer can still be useful. Selection is currently whole-array: mixing FIFO and random-access views of the same array would need additional coherence reasoning.

## 4. Where RHL enters this example

The source stores B as an array, while the target stores a queue and held values. Their complete states are different. A relation states which source elements are held by `b0`, `b1`, and `b2`, and which indexed values remain in the queue. The index sequence is proof information, not data sent alongside every hardware word.

This is the central idea inherited from [*Relational Hoare Logic for High-Level Synthesis of Hardware Accelerators* (ESOP 2026)](https://arxiv.org/abs/2601.09217). The current implementation composes relational insertion, read-replacement, sequencing and loop rules, then connects that relation to the backend's public-output observation. See [BufferRules](../src/IRComparison/Memory/BufferRules.lean), [RelationalRules](../src/IRComparison/Hybrid/RelationalRules.lean), and the [formal rules](HLS-SYNTAX-RULES.ja.md).

SMT assists candidate selection. The returned candidate must pass Lean-side checks that construct a proof-carrying plan. The current HLS theorem does not assume the SMT solver always answers correctly. The rule instances and verification conditions concern this implementation's BV32 hybrid IR; they are not a verbatim reuse of the paper's source syntax or solver encoding.

## 5. The generated RTL and its guarantee

Both examples continue through structured control, shared expression analysis, clock scheduling, finite-width storage and SystemVerilog emission. Loops can remain as control loops. The default used here is rolled execution; optional checked iteration overlap is a separate transformation.

These declarations are copied from the generated `increment.sv`, with whitespace adjusted. The intervening control, expression and assignment code is omitted:

```systemverilog
module hls_top (
  input wire clk, input wire rst, input wire start,
  input wire [31:0] x, input wire [31:0] y,
  input wire cfg_we, input wire cfg_reg,
  input wire [31:0] cfg_id, input wire [31:0] cfg_addr,
  input wire [31:0] cfg_data, input wire read_reg,
  input wire [31:0] read_id, input wire [31:0] read_addr,
  output reg [31:0] read_data, output reg read_valid,
  output reg busy, output reg done, output reg error
);
// ...
(* mem2reg *) reg [31:0] m0 [0:4];
// ...
(* mem2reg *) reg [31:0] m1 [0:4];
// ...
endmodule
```

The host configures initial storage, starts the circuit, waits for `done`, then requests public output elements. The unused `x`/`y` ports come from the common body interface. Full RTL, IR dumps and external-check logs are generated locally rather than committed as another source of truth.

The general functional theorem says: given a compiled artifact and the stated layout, readiness, representability and post-start state-agreement conditions, the interpreted output text finishes after finitely many clocks and preserves source success/failure and public outputs. The separate source-generation theorem establishes compilation success from the supported syntax and static conditions. [The proof map](PROOF-MAP.md) explains how these claims compose.

The post-start theorem does not by itself show that every legal Lean initial state can be installed through the configuration ports. This script explicitly calls `checkExternalPorts`, and its external tests exercise the concrete setup/readout protocol. Icarus and Yosys checks supplement the formal text-semantics proof; they do not verify those external tools or physical timing.
