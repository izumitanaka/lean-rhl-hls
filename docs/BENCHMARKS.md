# Workload and measurement scope

The baseline contains 23 transformation/interface regression cases and 22 additional inputs: nominal and boundary inputs for each of 11 small workload families. All 45 pass the Lean checks and Icarus simulation; the 30 distinct RTL texts pass Yosys synthesis.

| Workload family | Size and purpose |
| --- | --- |
| AXPY | 8 elements; arithmetic, multiple input arrays, wrapping |
| FIR4 | 8 inputs, 5 valid outputs; reuse of a four-element window |
| Prefix sum | 8 elements; dependence on previously written output |
| Dot product | 8 elements; two inputs and accumulation |
| Histogram | 8 inputs, 4 bins; data-dependent updates |
| Gather | 8 elements; indirect and repeated indices |
| Matrix multiplication | 2 by 2; different row/column accesses |
| Two-dimensional stencil | 4 by 4 input, 3 by 3 window, 4 valid outputs |
| Zero replacement | 8 elements; data-dependent branching |
| In-place recurrence | 8 elements; aliasing and updated-value dependence |
| FIR followed by zero replacement | Two kernels; intermediate communication |

The source definitions are in [HLSBenchmarks](../hls/src/IRComparison/Examples/HLSBenchmarks.lean). The [independent Python oracle](../hls/scripts/hls-benchmark-fixtures.py) uses integer algorithms reduced modulo 2^32 and does not inspect compiler IR or RTL. Boundary inputs include large bit patterns and repeated indices. Separate existing regression cases cover invalid accesses and source failure.

The examples are small adaptations, not a port of an entire benchmark suite. Matrix multiplication and stencil shapes were informed by [MachSuite](https://github.com/breagen/MachSuite), specifically [GEMM](https://github.com/breagen/MachSuite/blob/master/gemm/ncubed/gemm.c) and [stencil2d](https://github.com/breagen/MachSuite/blob/master/stencil/stencil2d/stencil.c). The [Vitis HLS introductory examples](https://github.com/Xilinx/Vitis-HLS-Introductory-Examples) informed DSP topic selection. This artifact uses its own small BV32 definitions, fixed sizes and weights, and explicit kernel metadata; it does not include vendor IP or reproduce those suites' full semantics and configurations.

The current frontend does not accept all surface forms used in conventional benchmark code. For example, the included fixed-divisor remainder expressions use `v - (v / d) * d`, and zero tests use a supported nonzero test with exchanged branches. These choices are input-adapter limitations, not new special-purpose optimization rules.

## Reading the results

- Compute cycles run from start to done and exclude reset/configuration cycles.
- Memory is implemented as finite register banks, not block RAM.
- FIFO capacity figures are logical word capacities; they need not equal useful communication-channel count or physical storage after synthesis.
- Generic Yosys cell counts are not FPGA LUT/DSP/BRAM utilization or post-placement area/Fmax.
- Identical RTL is synthesized once per run, but every testbench is simulated independently.
- Generation timing includes source reference evaluation, compilation, repeated harness emission/parsing, and checks as instrumented; it is not a controlled compiler-performance comparison.

See [saved results](../evidence/baseline/circuit/synthesis-results.json) and [workload CSV](../evidence/baseline/benchmarks/results.csv). This baseline makes no claim of performance superiority over commercial HLS, nor does it inherit the FPGA performance results of the earlier RHL paper.
