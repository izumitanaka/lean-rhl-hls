#!/usr/bin/env python3
"""Cross-check the pipelined emitter with Icarus. No synthesis or timing run."""
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "artifacts/pipelining/rtl"


def bench(inputs, output_id, expected, clocks, fail=False, x=0, y=0):
    lines = ["""module tb;
reg clk=0; always #5 clk=~clk;
reg rst=1,start=0,cfg_we=0,cfg_reg=0,read_reg=0;
reg [31:0] x=0,y=0,cfg_id=0,cfg_addr=0,cfg_data=0,read_id=0,read_addr=0;
wire [31:0] read_data; wire read_valid,busy,done,error; integer cycles;
hls_top dut(.*);
initial begin
repeat (2) @(negedge clk); rst=0;
"""]
    lines.append(f"x=32'd{x}; y=32'd{y};")
    for bank, values in inputs.items():
        for index, value in enumerate(values):
            lines.append(f"@(negedge clk); cfg_we=1; cfg_id={bank}; cfg_addr={index}; cfg_data=32'd{value}; @(negedge clk); cfg_we=0;")
    # Exercise repeated invocation without resetting the private holding registers.
    lines.append("repeat (2) begin @(negedge clk); start=1; @(negedge clk); start=0; cycles=0;")
    lines.append("while (!done && cycles<1000) begin @(negedge clk); cycles=cycles+1; end")
    lines.append("if (!done || busy) $fatal(1, \"termination\");")
    lines.append(f"if (error !== 1'b{int(fail)}) $fatal(1, \"error flag\");")
    if not fail:
        if clocks is not None:
            lines.append(f"if (cycles != {clocks}) $fatal(1, \"cycles: %0d expected {clocks}\",cycles);")
        for index, value in enumerate(expected):
            lines.append(f"read_id={output_id}; read_addr={index}; #1; if (!read_valid || read_data !== 32'd{value}) $fatal(1, \"read {index}: %0d\",read_data);")
    lines.append('end $display("PASS external RTL"); $finish; end\ninitial begin #200000; $fatal(1,"timeout"); end\nendmodule\n')
    return "\n".join(lines)


def main():
    cases = []
    for name, n, clocks in [("filter", 4, 7), ("filter-II2", 4, 10), ("filter-reverse", 4, 7),
                             ("filter-empty", 0, 1), ("filter-long", 16, 19)]:
        for pattern in ("nominal", "overflow"):
            data = [10*(i+1) for i in range(n+1)] if pattern == "nominal" else [0xffffffff if i % 2 == 0 else 1 for i in range(n+1)]
            expected = [((data[i] + data[i+1]) & 0xffffffff)//2 for i in range(n)]
            cases.append((name, pattern, {0: data, 1: [0]*n}, 1, expected, clocks, False))
    cases.append(("filter-oob", "error", {0: [10,20,30,40,50], 1: [0]*4}, 1, [], 0, True))
    cases.append(("gather", "nominal", {0: [2,0,3,1], 1: [10,20,30,40], 2: [0]*4}, 2, [31,11,41,21], 7, False))
    records = []
    for name, pattern, inputs, output_id, expected, clocks, fail in cases:
        stem = f"{name}-{pattern}"
        testbench = OUT / f"{stem}-tb.sv"
        executable = OUT / f"{stem}.vvp"
        testbench.write_text(bench(inputs, output_id, expected, clocks, fail))
        compile_result = subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", str(executable), str(OUT / f"{name}.sv"), str(testbench)], text=True, capture_output=True, timeout=60)
        (OUT / f"{stem}-compile.log").write_text(compile_result.stdout + compile_result.stderr)
        compile_result.check_returncode()
        result = subprocess.run(["vvp", str(executable)], text=True, capture_output=True, timeout=60)
        (OUT / f"{stem}-simulation.log").write_text(result.stdout + result.stderr)
        result.check_returncode()
        if "PASS external RTL" not in result.stdout:
            raise RuntimeError(f"missing success marker: {stem}")
        print(f"PASS\t{stem}")
        records.append({"case": stem, "status": "pass", "invocations": 2, "expected_error": fail,
                        "compute_clocks_including_halt": None if fail else clocks})
    (OUT / "simulation.json").write_text(json.dumps({"tool": "iverilog/vvp", "synthesis_run": False, "cases": records}, indent=2) + "\n")


if __name__ == "__main__":
    main()
