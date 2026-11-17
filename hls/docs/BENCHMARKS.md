# Workload scope

The executable examples include small fixed-size BV32 computations and transformation/interface regressions. The broader circuit harness contains nominal and boundary inputs for the 11 families below; the focused shared-backend suite in [REPRODUCING](REPRODUCING.md) is a separate set. No saved measurement directory is required to run either suite.

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

The source definitions are in [HLSBenchmarks](../src/IRComparison/Examples/HLSBenchmarks.lean). The [independent Python oracle](../scripts/hls-benchmark-fixtures.py) uses integer algorithms reduced modulo 2^32 and does not inspect compiler IR or RTL. Boundary inputs include large bit patterns and repeated indices. Separate existing regression cases cover invalid accesses and source failure.

The examples are small adaptations, not a port of an entire benchmark suite. Matrix multiplication and stencil shapes were informed by [MachSuite](https://github.com/breagen/MachSuite), specifically [GEMM](https://github.com/breagen/MachSuite/blob/master/gemm/ncubed/gemm.c) and [stencil2d](https://github.com/breagen/MachSuite/blob/master/stencil/stencil2d/stencil.c). The [Vitis HLS introductory examples](https://github.com/Xilinx/Vitis-HLS-Introductory-Examples) informed DSP topic selection. This artifact uses its own small BV32 definitions, fixed sizes and weights, and explicit kernel metadata; it does not include vendor IP or reproduce those suites' full semantics and configurations.

## Reading the results

- Compute cycles run from start to done and exclude reset/configuration cycles.
- Memory is implemented as finite register banks, not block RAM.
- FIFO capacity figures are logical word capacities; they need not equal useful communication-channel count or physical storage after synthesis.
- Generic Yosys cell counts are not FPGA LUT/DSP/BRAM utilization or post-placement area/Fmax.
- Identical RTL is synthesized once per run, but every testbench is simulated independently.
- Generation timing includes source reference evaluation, compilation, repeated harness emission/parsing, and checks as instrumented; it is not a controlled compiler-performance comparison.

Run the relevant scripts to obtain results for your checkout. This repository makes no claim of performance superiority over commercial HLS and does not inherit FPGA performance results from the earlier RHL paper.
