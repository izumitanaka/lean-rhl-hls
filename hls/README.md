# Current HLS implementation

See the [repository overview](../README.md), [technical note](../docs/TECHNICAL-NOTE.md), and [proof map](../docs/PROOF-MAP.md).

Run `lake build` and `lake env lean Audit.lean` here. `../papercore` is a local source dependency included in this repository; the archived NativeRHL project is not required. Three reused NativeRHL modules are included in `src/NativeRHL`.

`src/IRComparison/Frontend` contains Lean input handling; `Hybrid` contains the main computation IR and BV32 connection; `Memory` and `Core` contain shared transformations and semantics; `Circuit` contains the backend and SystemVerilog proofs; `Examples` contains inputs and comparisons. `Components` and `Experimental` retain explicitly separate experiments; they do not enable additional optimizations on the main path.
