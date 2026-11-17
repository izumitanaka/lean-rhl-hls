#!/usr/bin/env python3
"""Simulate the memory-optimized pipelining path and its structured control route."""
import json
from pathlib import Path
import runpy
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "artifacts/pipelining/rtl"
bench = runpy.run_path(str(ROOT / "scripts/check-pipelining-rtl.py"))["bench"]


def main():
    nominal = [10, 20, 30, 40, 50]
    # input-fifo is the historical fixture name: its supplier hint now retains memory.
    # Expected clocks are from the current Lean static schedule in integrated.log.
    cases = [
        ("buffer", "nominal", nominal, 1, [15,25,35,45,0], 17, 0, 0),
        ("input-fifo", "nominal", nominal, 1, [15,25,35,45,0], 17, 0, 0),
        ("chain", "nominal", nominal, 2, [32,52,72,92,0], 27, 0, 0),
        ("reverse", "nominal", nominal, 1, [15,25,35,45,0], 17, 0, 0),
        ("dilated", "nominal", nominal, 1, [15,0,35,0,0], 9, 0, 0),
        ("overflow", "overflow", [0xffffffff,1,0xffffffff,1,0xffffffff], 1, [0]*5, 17, 0, 0),
        ("budget-structured", "nominal", nominal, 1, [15,25,35,45,0], None, 0, 0),
        ("dynamic-structured", "false", nominal, 0, nominal, None, 7, 0),
        ("dynamic-structured", "true", nominal, 0, [7,20,30,40,50], None, 7, 1),
    ]
    records = []
    for name, pattern, data, output, expected, clocks, x, y in cases:
        name = "integrated-" + name
        stem = f"{name}-{pattern}"
        tb, executable = OUT / f"{stem}-tb.sv", OUT / f"{stem}.vvp"
        inputs = {0: data} if "dynamic" in name else {0: data, 1: [0]*5, 2: [0]*5}
        tb.write_text(bench(inputs, output, expected, clocks, x=x, y=y))
        for phase, command in [
            ("compile", ["iverilog", "-g2012", "-s", "tb", "-o", str(executable), str(OUT / f"{name}.sv"), str(tb)]),
            ("simulation", ["vvp", str(executable)]),
        ]:
            result = subprocess.run(command, text=True, capture_output=True, timeout=60)
            (OUT / f"{stem}-{phase}.log").write_text(result.stdout + result.stderr)
            if result.returncode:
                raise RuntimeError(f"{stem}/{phase}: {result.stdout}{result.stderr}")
        if "PASS external RTL" not in result.stdout:
            raise RuntimeError(f"missing success marker: {stem}")
        print(f"PASS\t{stem}")
        records.append({"case": stem, "status": "pass", "invocations": 2,
                        "compute_clocks_including_halt": clocks})
    (OUT / "integrated-simulation.json").write_text(json.dumps(
        {"tool": "iverilog/vvp", "synthesis_run": False, "cases": records}, indent=2) + "\n")


if __name__ == "__main__":
    main()
