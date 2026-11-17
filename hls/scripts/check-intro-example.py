#!/usr/bin/env python3
"""Check the introductory examples' emitted RTL, configuration and restart."""
from pathlib import Path
import json
import runpy
import subprocess

root = Path(__file__).resolve().parents[1]
out = root / "artifacts/intro-example"
bench = runpy.run_path(str(root / "scripts/check-pipelining-rtl.py"))["bench"]
cases = [
    ("increment", {0: [3, 6, 9, 12, 15], 1: [0] * 5}, 1, [4, 7, 10, 13, 16]),
    ("filter", {0: [3, 6, 9, 12, 15], 2: [0] * 5}, 2, [7, 10, 13, 0, 0]),
]
records = []
for name, inputs, output, expected in cases:
    tb = out / f"{name}.tb.sv"
    tb.write_text(bench(inputs, output, expected, None))
    binary = out / f"{name}.vvp"
    commands = [
        ("compile", ["iverilog", "-g2012", "-s", "tb", "-o", str(binary), str(out / f"{name}.sv"), str(tb)]),
        ("simulation", ["vvp", str(binary)]),
        ("yosys", ["yosys", "-Q", "-T", "-p",
                   f'read_verilog -sv "{out / (name + ".sv")}"; hierarchy -check -top hls_top; proc; opt; check']),
    ]
    for phase, command in commands:
        run = subprocess.run(command, capture_output=True, text=True, timeout=60)
        (out / f"{name}.{phase}.log").write_text(run.stdout + run.stderr)
        run.check_returncode()
        if phase == "simulation" and "PASS external RTL" not in run.stdout:
            raise RuntimeError(f"missing simulation success marker: {name}")
    records.append({"case": name, "expected": expected, "invocations": 2,
                    "icarus": "PASS", "yosys_structure": "PASS"})
    print(f"PASS {name}: Icarus (configuration and two invocations), Yosys structure", flush=True)
(out / "external.json").write_text(json.dumps(records, indent=2) + "\n")
