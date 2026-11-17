#!/usr/bin/env python3
"""External simulation of the actual certified entry's emitted strings."""
import json
import re
from pathlib import Path
import runpy
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "artifacts/certified-hls"
bench = runpy.run_path(str(ROOT / "scripts/check-pipelining-rtl.py"))["bench"]


def main():
    nominal = [3, 6, 9, 12, 15]
    cases = [
        ("filter-expanded", nominal, 1, [6, 9, 12, 0, 0], 0, 0, False),
        ("filter", nominal, 1, [6, 9, 12, 0, 0], 0, 0, False),
        ("filter-overflow", [0xffffffff, 1, 2, 3, 4], 1, [0, 2, 3, 0, 0], 0, 0, False),
        ("reverse", nominal, 1, [6, 9, 12, 0, 0], 0, 0, False),
        ("budget-structured", nominal, 1, [6, 9, 12, 0, 0], 0, 0, False),
        ("branch-true", nominal, 1, [7, 0, 0, 0, 0], 7, 1, False),
        ("branch-false", nominal, 1, [0]*5, 7, 0, False),
        ("chain", nominal, 2, [8, 14, 20, 26, 32], 0, 0, False),
        ("public-chain", nominal, 2, [8, 14, 20, 26, 32], 0, 0, False),
        ("zero-count", nominal, 1, [0]*5, 0, 0, False),
        ("stride-two", nominal, 1, [6, 0, 12, 0, 0], 0, 0, False),
        ("sequential-route", nominal, 1, [6, 9, 12, 0, 0], 0, 0, False),
        ("source-error", nominal, 1, [], 0, 0, True),
    ]
    records = []
    with tempfile.TemporaryDirectory(prefix="certified-hls-") as tmp:
        for name, data, output, expected, x, y, fail in cases:
            tb = OUT / f"{name}-tb.sv"
            executable = Path(tmp) / name
            tb.write_text(bench({0: data, 1: [0]*5, 2: [0]*5}, output,
                                expected, None, fail=fail, x=x, y=y).replace(
                                    'end $display("PASS external RTL")',
                                    '$display("CYCLES %0d", cycles); end $display("PASS external RTL")'))
            for phase, command in [
                ("compile", ["iverilog", "-g2012", "-s", "tb", "-o", str(executable),
                             str(OUT / f"{name}.sv"), str(tb)]),
                ("simulation", ["vvp", str(executable)]),
            ]:
                result = subprocess.run(command, text=True, capture_output=True, timeout=60)
                (OUT / f"{name}-{phase}.log").write_text(result.stdout + result.stderr)
                if result.returncode:
                    raise RuntimeError(f"{name}/{phase}: {result.stdout}{result.stderr}")
            if "PASS external RTL" not in result.stdout:
                raise RuntimeError(f"missing success marker: {name}")
            print(f"PASS {name}")
            records.append({"case": name, "status": "pass", "invocations": 2,
                            "expected_error": fail,
                            "compute_clocks": [int(n) for n in re.findall(r"CYCLES (\d+)", result.stdout)]})
    (OUT / "simulation.json").write_text(json.dumps(
        {"tool": "iverilog/vvp", "synthesis_run": False, "cases": records}, indent=2) + "\n")


if __name__ == "__main__":
    main()
