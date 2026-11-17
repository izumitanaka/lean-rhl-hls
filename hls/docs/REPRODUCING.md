# Reproducing the current source update

Use Lean 4.29.0, fixed by `hls/lean-toolchain`, with Lake on PATH. The committed manifests pin Lean4Lean and Batteries; PaperCore support is included in `hls/src/PaperCore/` within the same package. Initial dependency fetching requires network access. No original research directory or build cache is required.

## Start with two input-to-RTL examples

After `lake build IRComparison IRComparison.Tests`, from `hls/`:

```sh
lake env lean --run scripts/intro-example.lean
python3 scripts/check-intro-example.py
```

See the [walkthrough](WALKTHROUGH.md). The Lean script compiles a whole-function increment and an explicitly staged producer/filter, checks native results and the emitted text interpreter, and checks that the latter selects FIFO array 1 with a three-value reuse buffer. It requires Z3. The Python script requires Icarus (`iverilog`, `vvp`) and Yosys; both examples are configured and invoked twice, then structurally synthesized. Generated RTL, constructor dumps, SMT records and logs are under `artifacts/intro-example/`. This is functional/structural validation, not a physical timing measurement.

## General proofs and frontend regressions

From this HLS directory (or first run `cd hls` from the repository root):

```sh
lake build IRComparison IRComparison.Tests
lake env lean Audit.lean
lake env lean scripts/structural-frontend.lean
lake env lean scripts/check-current-entry.lean
```

The expected audit is 2273 entries (2272 distinct declarations), allowing only `propext`, `Classical.choice` and `Quot.sound`. The normal-entry regression covers 131 source cases. The entry guard checks the current entry and generation theorem and the absence of 53 retired declarations. Lake job counts depend on cache state; linter warnings are not failed proofs.

## Emitted RTL, restart and synthesis

Still inside `hls/`:

```sh
lake env lean --run scripts/shared-normal-hls.lean
python3 scripts/check-shared-normal-hls.py
```

This generates 9 current ordinary-HLS cases, simulates each with two invocations (restart), and structurally synthesizes 4 cases. Python 3, `iverilog`, `vvp` and `yosys` must be on PATH. Results and generated RTL go to `hls/artifacts/shared-normal-hls/`.

Additional suites are provided, but should not be treated as rerun unless recorded:

```sh
lake env lean --run scripts/rule-vcg.lean
python3 scripts/check-rule-vcg.py
lake env lean --run scripts/pipelining-rtl.lean
python3 scripts/check-pipelining-rtl.py
python3 scripts/check-circuit.py --synth
```

The routing suite also requires Z3. The broad circuit suite can take substantially longer. Its workload families and measurement boundaries are described in [BENCHMARKS](BENCHMARKS.md).

## Repository and generated output

PaperCore support is compiled as a library in the HLS package, with no sibling-directory dependency. No private research directory is required. Toolchain and dependency revisions are pinned in the committed manifests.

Generated RTL, timing measurements and test logs stay under local `hls/artifacts/`; they are not committed. Git identifies the source revision. To compare runs, record the commit, tool versions, commands and inputs together with your local results.
