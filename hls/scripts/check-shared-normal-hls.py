#!/usr/bin/env python3
"""Check the default shared compiler's printed modules, including restart."""
from pathlib import Path
import json
import runpy
import subprocess

root = Path(__file__).resolve().parents[1]
out = root / 'artifacts/shared-normal-hls'
bench = runpy.run_path(str(root / 'scripts/check-pipelining-rtl.py'))['bench']
records = json.loads((out / 'normal-cases.json').read_text())
results = []
for case in records:
    name, expected = case['name'], case['expected']
    tb = out / f'{name}.tb.sv'
    tb.write_text(bench({0: [20], 1: [0]}, 1, [] if expected is None else [expected],
                        None, fail=expected is None, x=case['x'], y=case['y']))
    binary = out / f'{name}.vvp'
    for phase, command in [
        ('compile', ['iverilog', '-g2012', '-s', 'tb', '-o', str(binary), str(out / f'{name}.sv'), str(tb)]),
        ('run', ['vvp', str(binary)]),
    ]:
        run = subprocess.run(command, capture_output=True, text=True, timeout=60)
        (out / f'{name}.{phase}.log').write_text(run.stdout + run.stderr)
        run.check_returncode()
    assert 'PASS external RTL' in run.stdout, run.stdout
    results.append({'name': name, 'tool': 'Icarus', 'invocations': 2, 'status': 'PASS'})
    print(f'PASS Icarus {name}', flush=True)
for name in ['unused-invalid', 'unchosen-invalid', 'growth-10', 'growth-100']:
    command = f'read_verilog -sv "{out / (name + ".sv")}"; hierarchy -check -top hls_top; proc; opt; check'
    run = subprocess.run(['yosys', '-Q', '-T', '-p', command], capture_output=True, text=True, timeout=60)
    (out / f'{name}.yosys.log').write_text(run.stdout + run.stderr)
    run.check_returncode()
    results.append({'name': name, 'tool': 'Yosys', 'status': 'PASS'})
    print(f'PASS Yosys {name}', flush=True)
(out / 'normal-external.json').write_text(json.dumps(results, indent=2) + '\n')
