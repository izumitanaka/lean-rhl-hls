#!/usr/bin/env python3
"""Execute printed structured schedules. No synthesis or physical timing claims."""
import json
from pathlib import Path
import runpy
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "artifacts/pipelining/structured"
bench = runpy.run_path(str(ROOT / "scripts/check-pipelining-rtl.py"))["bench"]


def main():
    # Counted memory regions now include an explicit empty-output-queue setup clock.
    cases = [
        ("conditional", "false", 7, 0, [0]*4, 16, False),
        ("conditional", "true", 7, 1, [7,0,0,0], 17, False),
        ("dynamic-loop", "zero", 7, 0, [0]*4, 20, False),
        ("dynamic-loop", "one", 7, 1, [7,0,0,0], 23, False),
        ("dynamic-loop", "four", 7, 4, [7]*4, 32, False),
        ("dynamic-loop", "oob", 7, 5, [], 27, True),
        ("nested", "both-loops", 1, 3, [11,0,0,0], 47, False),
        ("nested", "other-branch", 0, 3, [11,0,0,0], 23, False),
        ("nested", "zero", 1, 0, [0]*4, 2, False),
    ]
    records = []
    for name, pattern, x, y, expected, clocks, fail in cases:
        stem = f"{name}-{pattern}"
        tb, executable = OUT / f"{stem}-tb.sv", OUT / f"{stem}.vvp"
        tb.write_text(bench({0:[0]*4,1:[0]*4}, 0, expected, clocks, fail, x=x, y=y))
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
        records.append({"case":stem,"status":"pass","invocations":2,"expected_error":fail,
                        "compute_clocks_including_halt":clocks})
    (OUT / "simulation.json").write_text(json.dumps(
        {"tool":"iverilog/vvp","synthesis_run":False,"cases":records}, indent=2)+"\n")


if __name__ == "__main__":
    main()
