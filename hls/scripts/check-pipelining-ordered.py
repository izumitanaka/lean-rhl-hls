#!/usr/bin/env python3
"""Check old-value reads and same-edge buffer shifts in emitted SystemVerilog."""
import json
from pathlib import Path
import runpy
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "artifacts/pipelining/ordered"
bench = runpy.run_path(str(ROOT / "scripts/check-pipelining-rtl.py"))["bench"]


def main():
    cases = [
        ("window2", [10,20,30,40,50], [15,25,35,45], False),
        ("window3", [10,20,30,40,50,60], [60,90,120,150], False),
        ("window2-wrap", [0xffffffff,1,0xffffffff,1,0xffffffff], [0]*4, False),
        ("window3-wrap", [0xffffffff,1,0xffffffff,1,0xffffffff,1], [0xffffffff,1,0xffffffff,1], False),
        ("window2-oob", [10,20,30,40], [], True),
    ]
    records = []
    for name, data, expected, fail in cases:
        tb, executable = OUT / f"{name}-tb.sv", OUT / f"{name}.vvp"
        tb.write_text(bench({0: data, 1: [0]*4}, 1, expected, 6, fail))
        for phase, command in [
            ("compile", ["iverilog", "-g2012", "-s", "tb", "-o", str(executable), str(OUT / f"{name}.sv"), str(tb)]),
            ("simulation", ["vvp", str(executable)]),
        ]:
            result = subprocess.run(command, text=True, capture_output=True, timeout=60)
            (OUT / f"{name}-{phase}.log").write_text(result.stdout + result.stderr)
            if result.returncode:
                raise RuntimeError(f"{name}/{phase}: {result.stdout}{result.stderr}")
        if "PASS external RTL" not in result.stdout:
            raise RuntimeError(f"missing success marker: {name}")
        print(f"PASS\t{name}")
        records.append({"case": name, "status": "pass", "invocations": 2,
                        "expected_error": fail, "compute_clocks_including_halt": None if fail else 6})
    (OUT / "simulation.json").write_text(json.dumps(
        {"tool": "iverilog/vvp", "synthesis_run": False, "cases": records}, indent=2) + "\n")


if __name__ == "__main__":
    main()
