#!/usr/bin/env python3
"""Simulate RTL from automatically extracted whole-function stages."""
from pathlib import Path
import json
import runpy
import subprocess

root = Path(__file__).resolve().parents[1]
out = root / 'artifacts/automatic-stages'
bench = runpy.run_path(str(root / 'scripts/check-pipelining-rtl.py'))['bench']
data = [3, 6, 9, 12, 15]
cases = [
    ('forward', {0: data, 2: [0]*5}, 2, [7, 10, 13, 0, 0], False),
    ('reverse', {0: data, 2: [0]*5}, 2, [7, 10, 13, 0, 0], False),
    ('mismatch', {0: data, 1: [0]*5, 2: [0]*5}, 2, [5, 8, 11, 14, 17], False),
    ('sparse', {7: data, 101: [0]*5}, 101, [8, 0, 14, 0, 20], False),
    ('sparse-both', {7: data, 42: [0]*5, 101: [0]*5}, 101, [8, 0, 14, 0, 20], False),
    ('captured', {0: data, 1: [0]*5, 2: [0]*5}, 2, [13, 16, 19, 22, 25], False),
    ('natural', {0: data, 2: [0]*5}, 2, [4, 7, 10, 13, 16], False),
    ('two-inputs', {0: data, 2: [0]*5}, 2, [7, 13, 19, 25, 31], False),
    ('invalid', {0: data, 1: [0]*5, 2: [0]*5}, 2, [], True),
    ('zero', {0: data, 1: [0]*5, 2: [0]*5}, 2, [0]*5, False),
    ('forward-smt', {0: data, 2: [0]*5}, 2, [7, 10, 13, 0, 0], False),
]
records = []
for name, inputs, output, expected, fail in cases:
    text = bench(inputs, output, expected, None, fail=fail)
    if name == 'captured':
        # Each invocation receives the same initial scalar input. The program changes it to 99.
        text = text.replace('repeat (2) begin @(negedge clk); start=1;',
            "repeat (2) begin @(negedge clk); cfg_we=1; cfg_reg=1; cfg_id=0; cfg_data=10; "
            "@(negedge clk); cfg_we=0; cfg_reg=0; @(negedge clk); start=1;")
    tb, binary = out / f'{name}.tb.sv', out / f'{name}.vvp'
    tb.write_text(text)
    for phase, command in [
        ('compile', ['iverilog', '-g2012', '-s', 'tb', '-o', str(binary), str(out/f'{name}.sv'), str(tb)]),
        ('simulation', ['vvp', str(binary)]),
    ]:
        run = subprocess.run(command, capture_output=True, text=True, timeout=60)
        (out/f'{name}.{phase}.log').write_text(run.stdout+run.stderr)
        run.check_returncode()
    if 'PASS external RTL' not in run.stdout:
        raise RuntimeError(f'missing simulation marker: {name}')
    records.append({'case': name, 'icarus': 'PASS', 'invocations': 2, 'failure_expected': fail})
    print(f'PASS Icarus {name} (two invocations)', flush=True)
for name in ['forward', 'reverse', 'sparse', 'captured', 'natural']:
    command = f'read_verilog -sv "{out/(name+".sv")}"; hierarchy -check -top hls_top; proc; opt; check'
    run = subprocess.run(['yosys', '-Q', '-T', '-p', command], capture_output=True, text=True, timeout=60)
    (out/f'{name}.yosys.log').write_text(run.stdout+run.stderr)
    run.check_returncode()
    records.append({'case': name, 'yosys_structure': 'PASS'})
    print(f'PASS Yosys {name}', flush=True)
(out/'external.json').write_text(json.dumps(records, indent=2)+'\n')
