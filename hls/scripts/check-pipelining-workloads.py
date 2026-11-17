#!/usr/bin/env python3
"""Three distinct workload families, using the production integrated emitter.
One invocation per reset: histogram and compaction intentionally mutate state.
No synthesis or physical timing measurement.
"""
import json
from pathlib import Path
import runpy
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "artifacts/pipelining/workloads"
bench = runpy.run_path(str(ROOT / "scripts/check-pipelining-rtl.py"))["bench"]


def main():
    zero = [0]*4
    cases = [
        ("gather", "nominal", [2,0,3,1], [10,20,30,40], 2, [31,11,41,21], 7, False, None),
        ("gather", "oob", [2,4,3,1], [10,20,30,40], 2, [], None, True, None),
        ("histogram", "repeated", [3,3,1,3], zero, 1, [0,1,0,3], 10, False, None),
        ("histogram", "distinct", [0,1,2,3], zero, 1, [1]*4, 10, False, None),
        ("histogram", "wrap", [0]*4, [0xffffffff,0,0,0], 1, [3,0,0,0], 10, False, None),
        ("histogram", "oob", [0,4,0,0], zero, 1, [], None, True, None),
        ("select", "mixed", [0,8,0,9], zero, 1, [8,9,0,0], None, False, 2),
        ("select", "none", zero, zero, 1, zero, None, False, 0),
        ("select", "all", [2,8,1,9], zero, 1, [2,8,1,9], None, False, 4),
    ]
    records = []
    for name, pattern, data, second, output, expected, clocks, fail, count in cases:
        stem = f"{name}-{pattern}"
        tb, executable = OUT / f"{stem}-tb.sv", OUT / f"{stem}.vvp"
        text = bench({0: data, 1: second, 2: zero}, output, expected, clocks, fail)
        text = text.replace("repeat (2) begin", "repeat (1) begin")
        if count is not None:
            text = text.replace('end $display("PASS external RTL")',
                f'read_reg=1; read_id=0; #1; if (!read_valid || read_data !== 32\'d{count}) $fatal(1,"count"); end $display("PASS external RTL")')
        tb.write_text(text)
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
        records.append({"case": stem, "status": "pass", "invocations": 1,
                        "expected_error": fail, "compute_clocks_including_halt": clocks})
    (OUT / "simulation.json").write_text(json.dumps(
        {"tool": "iverilog/vvp", "synthesis_run": False, "cases": records}, indent=2) + "\n")


if __name__ == "__main__":
    main()
