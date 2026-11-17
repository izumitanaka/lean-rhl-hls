# Lean programs and generated RTL

Each `.lean` file is an independent, runnable example: a complete input program, fixed array declarations, sample input/output, and a short RTL-generation command. Open the source and its generated SystemVerilog side by side.

| Program | Lean input | Generated RTL | Sample result |
|---|---|---|---|
| Add one to each array element | [Increment.lean](Increment.lean) | [Increment.sv](generated/Increment.sv) | `[3,6,9,12,15]` → `[4,7,10,13,16]` |
| Produce an intermediate array, then average three adjacent elements | [Filter.lean](Filter.lean) | [Filter.sv](generated/Filter.sv) | `[3,6,9,12,15]` → `[7,10,13,0,0]` |
| Swap two arrays through a declared temporary array | [Swap.lean](Swap.lean) | [Swap.sv](generated/Swap.sv) | Arrays 0 and 1 exchange contents |
| Reverse traversal, nested loops and conditional copies | [NestedLoops.lean](NestedLoops.lean) | [NestedLoops.sv](generated/NestedLoops.sv) | Both branches execute; output `[9,1,7,6]` |
| Accumulate a prefix sum | [PrefixSum.lean](PrefixSum.lean) | [PrefixSum.sv](generated/PrefixSum.sv) | `[3,6,9,12,15]` → `[3,9,18,30,45]` |

All examples use BV32 arithmetic and `hls_fixed_program`. In the filter example, the last two output elements are not written and retain their initial values. `sample` and `#guard` evaluate/check the Lean function; they do **not** bake these inputs into the circuit. The circuit receives data through configuration ports and exposes the selected output arrays through read ports.

## Run or regenerate

From `hls/`, with the pinned Lean toolchain:

```sh
lake build IRComparison
lake env lean --run examples/Increment.lean
```

Replace `Increment` with any name above. Each command checks its sample output, compiles the program and overwrites its matching `examples/generated/*.sv`. The checked-in RTL is actual compiler output with line breaks added for browsing; its tokens are unchanged. Every file defines a module named `hls_top`; use each independently. For ports and reset/configuration/start/readout, see the [walkthrough](../docs/WALKTHROUGH.md).

The [broader example catalog](../docs/EXAMPLES.md) also covers explicitly staged buffer/FIFO transformations, pipeline overlap and error handling, with their regression runners. These five files focus on readable whole-function input programs.

To regenerate all five files and check the sample outputs in Icarus, followed by Yosys structural checks:

```sh
python3 scripts/check-examples.py
```

This additional check requires Python 3, Icarus Verilog and Yosys. Logs stay in `artifacts/standalone-examples/`; it does not measure physical timing.
