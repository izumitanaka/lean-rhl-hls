#!/usr/bin/env python3
"""Cross-check the shared/ordinary expression adapter in real clocked modules.
These are adapter tests, not the default Lean frontend's end-to-end theorem.
"""
from pathlib import Path
import argparse
import importlib.util
import json
import subprocess

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--output-dir', type=Path, default=Path('artifacts/shared-integration'))
args = parser.parse_args()
out = root / args.output_dir
spec = importlib.util.spec_from_file_location('pipeline_testbench', root / 'scripts/check-pipelining-rtl.py')
fixture = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fixture)
records = json.loads((out / 'modules.json').read_text())
results = []
for case in records:
    name, expected = case['name'], case['expected']
    tb = out / f'{name}.tb.sv'
    tb.write_text(fixture.bench({0: [case['input']], 1: [0]}, 1,
                              [] if expected is None else [expected], None,
                              fail=expected is None, x=case['flag'], y=7))
    sim = out / f'{name}.vvp'
    compilation = subprocess.run(['iverilog', '-g2012', '-s', 'tb', '-o', str(sim),
                                  str(out / f'{name}.sv'), str(tb)], capture_output=True, text=True, timeout=60)
    (out / f'{name}.compile.log').write_text(compilation.stdout + compilation.stderr)
    compilation.check_returncode()
    run = subprocess.run(['vvp', str(sim)], capture_output=True, text=True, timeout=60)
    (out / f'{name}.run.log').write_text(run.stdout + run.stderr)
    run.check_returncode()
    assert 'PASS external RTL' in run.stdout, run.stdout
    results.append({'name': name, 'tool': 'Icarus', 'invocations': 2, 'status': 'PASS'})
    print(f'PASS Icarus {name}: reset/config/start, FIFO, memory output, restart', flush=True)
for name in ['twice', 'unchosen-invalid', 'shared-twice', 'shared-unchosen-invalid']:
    command = f'read_verilog -sv "{out / (name + ".sv")}"; hierarchy -check -top hls_top; proc; opt; check'
    run = subprocess.run(['yosys', '-Q', '-T', '-p', command], capture_output=True, text=True, timeout=60)
    (out / f'{name}.yosys.log').write_text(run.stdout + run.stderr)
    run.check_returncode()
    results.append({'name': name, 'tool': 'Yosys', 'status': 'PASS'})
    print(f'PASS Yosys {name}: complete module', flush=True)
(out / 'external.json').write_text(json.dumps(results, indent=2) + '\n')
