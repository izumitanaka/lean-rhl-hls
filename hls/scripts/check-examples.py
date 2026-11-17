#!/usr/bin/env python3
"""Regenerate the standalone examples and check their RTL sample outputs."""
from pathlib import Path
import json
import runpy
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "artifacts/standalone-examples"
NAMES = ["Increment", "Filter", "Swap", "NestedLoops", "PrefixSum"]


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    def run(command, log, timeout=180):
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        (OUT / log).write_text(result.stdout + result.stderr)
        result.check_returncode()
        return result.stdout

    for name in NAMES:
        run(["lake", "env", "lean", "--run", f"examples/{name}.lean"], f"{name}.lean.log")
        print(f"PASS Lean and RTL generation: {name}", flush=True)
    bench = runpy.run_path(str(ROOT / "scripts/check-pipelining-rtl.py"))["bench"]
    cases = [
        ("Increment", {0: [3,6,9,12,15], 1: [0]*5}, 1, [4,7,10,13,16]),
        ("Filter", {0: [3,6,9,12,15], 1: [0]*5, 2: [0]*5}, 2, [7,10,13,0,0]),
        ("Swap", {0: [10,20,30,40], 1: [5,6,7,8], 2: [0]*4}, 0, [5,6,7,8]),
        ("Swap", {0: [10,20,30,40], 1: [5,6,7,8], 2: [0]*4}, 1, [10,20,30,40]),
        ("NestedLoops", {0: [0,2,3,4], 1: [0]*4, 2: [9,8,7,6]}, 1, [9,1,7,6]),
        ("PrefixSum", {0: [3,6,9,12,15], 1: [0]*5}, 1, [3,9,18,30,45]),
    ]
    checks = []
    for name, inputs, output, expected in cases:
        stem = f"{name}-{output}"
        tb, binary = OUT / f"{stem}.tb.sv", OUT / f"{stem}.vvp"
        # One invocation per sample: a second swap would restore the original arrays.
        tb.write_text(bench(inputs, output, expected, None).replace("repeat (2) begin", "repeat (1) begin"))
        run(["iverilog", "-g2012", "-s", "tb", "-o", str(binary),
             str(ROOT / f"examples/generated/{name}.sv"), str(tb)], f"{stem}.compile.log", 60)
        result = run(["vvp", str(binary)], f"{stem}.simulation.log", 60)
        if "PASS external RTL" not in result:
            raise RuntimeError(f"missing simulation marker: {stem}")
        checks.append({"program": name, "output": output, "icarus": "PASS"})
        print(f"PASS RTL sample output: {stem}", flush=True)
    for name in NAMES:
        sv = ROOT / f"examples/generated/{name}.sv"
        run(["yosys", "-Q", "-T", "-p",
             f'read_verilog -sv "{sv}"; hierarchy -check -top hls_top; proc; opt; check'],
            f"{name}.yosys.log", 60)
        checks.append({"program": name, "yosys_structure": "PASS"})
        print(f"PASS Yosys structure: {name}", flush=True)
    (OUT / "checks.json").write_text(json.dumps(checks, indent=2) + "\n")


if __name__ == "__main__":
    main()
