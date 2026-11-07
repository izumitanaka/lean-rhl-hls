# Reproducing the baseline

## Environment

Use Lean **4.29.0**, as fixed in both `lean-toolchain` files, with `lake` on `PATH`. The external Lean dependencies are pinned by commit in `hls/lake-manifest.json`. PaperCore is included as a sibling source directory. Initial dependency fetching needs network access.

The recorded macOS baseline used Python 3.9.6, Z3 4.16.0, Icarus Verilog 13.0, and Yosys `0.70+post` (commit `0c11ea098be065e585a90a06e7b7da49936cf231`). These tool versions describe the measured run; compatibility with every other platform/version has not been established. Synthesis cell counts and timings can differ across tool versions and machines.

External tools have separate roles:

- `lake` / `lean`: build definitions and proofs; run the audited compiler and Lean regression harness.
- `python3`: construct independent expectations and orchestrate RTL tests.
- `iverilog` / `vvp`: compile and simulate generated SystemVerilog.
- `yosys`: optional generic logic synthesis (`--synth`).
- `z3`: additional SMT-candidate regressions, not required for the pure proof build.

## Proof build

From the repository root:

```sh
cd hls
lake build
lake env lean Audit.lean
lake env lean --run scripts/circuit-validation.lean
```

Expected results: successful library build, `Checked assumptions of 844 entry-bridge theorems`, and a `PASS` message for seven circuit validation checks. Linter warnings about unused simp arguments are present in this baseline and do not indicate failed proofs. The total Lake job count is not a stable API and may depend on caching.

## One end-to-end example

Still inside `hls/`:

```sh
python3 scripts/check-circuit.py --case filter-three --synth
```

This generates the circuit, checks the Lean reference and parsed output, runs the actual emitted RTL through Icarus, and synthesizes it using Yosys. Output is written under `artifacts/circuit/filter-three/`, including `design.sv`, `tb.sv`, `metrics.json`, and logs. A selected run writes `selected-*.json` summaries, so it does not replace the full-run summary files.

List the available cases after building:

```sh
HLS_LIST_CASES=1 lake env lean --run scripts/circuit-check.lean
```

## Full regression

```sh
python3 scripts/check-circuit.py --synth
lake env lean --run scripts/hybrid-word.lean
```

The first command generates and checks 45 cases, simulates each case, and synthesizes 30 distinct RTL texts. It can take several minutes; the stencil cases are substantially slower than the small arithmetic examples. Generation has a per-case timeout of 600 seconds, adjustable with `--generation-timeout`. A failed case is recorded and makes the overall run fail; an old generated design is not silently substituted for failed generation.

The second command checks 15 BV32 cases, including actual Z3 candidate queries, memory fallback, reverse traversal, wrapping, and failure behavior. Generated SMT requests and replies remain under `hls/artifacts/`.

The complete driver and examples are in [circuit-check.lean](../hls/scripts/circuit-check.lean), [WordFrontendExamples](../hls/src/IRComparison/Examples/WordFrontendExamples.lean), and [HLSBenchmarks](../hls/src/IRComparison/Examples/HLSBenchmarks.lean). Tests are supplementary evidence, not replacements for the general theorems.

## Baseline evidence

The saved [manifest](../evidence/baseline/circuit/manifest.json), [synthesis results](../evidence/baseline/circuit/synthesis-results.json), and [audit log](../evidence/baseline/reorganization/audit.log) describe the source baseline. `evidence/source-files.json` records SHA256 hashes of the copied code, configuration, scripts, and original evidence. From the root, run:

```sh
python3 scripts/check-source-manifest.py
```

The publication copy is validated independently. Its [validation record](../evidence/publication/validation.json) identifies which checks were rerun and whether emitted RTL matches the saved baseline. Existing timing measurements are machine-dependent and are not expected to reproduce byte for byte.

No build cache, external dependency checkout, compiled binary, manuscript history, or authentication configuration is distributed. The build does not depend on the original working directory.
