#!/usr/bin/env python3
"""Check separately emitted shared combinational expressions, not full HLS."""
from pathlib import Path
import json
import argparse
import subprocess

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--output-dir', type=Path, default=Path('artifacts/shared-erasure'))
args = parser.parse_args()
out = root / args.output_dir
results = []
for sv in sorted((out / 'rtl').glob('*.sv')):
    if sv.name.endswith('.design.sv'):
        continue
    exe = sv.with_suffix('.vvp')
    compile_result = subprocess.run(['iverilog', '-g2012', '-s', 'shared_test', '-o', str(exe), str(sv)], capture_output=True, text=True, timeout=60)
    (sv.with_suffix('.compile.log')).write_text(compile_result.stdout + compile_result.stderr)
    compile_result.check_returncode()
    run = subprocess.run(['vvp', str(exe)], capture_output=True, text=True, timeout=60)
    sv.with_suffix('.run.log').write_text(run.stdout + run.stderr)
    run.check_returncode()
    if f'PASS {sv.stem}' not in run.stdout:
        raise SystemExit(f'{sv.name}: missing success marker')
    results.append({'case': sv.stem, 'status': 'PASS'})
    print(f'PASS Icarus {sv.stem}', flush=True)
for name in ['chain10', 'reused-binding', 'wrap-product', 'div-negative', 'unchosen-invalid-read']:
    sv = out / 'rtl' / f'{name}.design.sv'
    netlist = out / 'rtl' / f'{name}.yosys.json'
    # All paths are constructed locally, with no user text interpolation.
    command = f'read_verilog -sv "{sv}"; hierarchy -check -top shared_synth; proc; opt; check; write_json "{netlist}"'
    run = subprocess.run(['yosys', '-Q', '-T', '-p', command], capture_output=True, text=True, timeout=60)
    (out / 'rtl' / f'{name}.yosys.log').write_text(run.stdout + run.stderr)
    run.check_returncode()
    data = json.loads(netlist.read_text())
    cells = data['modules']['shared_synth']['cells']
    types = [v['type'] for v in cells.values()]
    if any(any(marker in typ.lower() for marker in ['dff', 'latch', 'ff_']) for typ in types):
        raise SystemExit(f'{name}: unexpected sequential cell {types}')
    results.append({'case': name, 'tool': 'Yosys', 'status': 'PASS', 'cell_types': types, 'sequential_cells': 0})
    print(f'PASS Yosys {name}: combinational only', flush=True)
(out / 'external-checks.json').write_text(json.dumps({'checks': results, 'scope': 'standalone shared net emitter only; not default HLS route'}, indent=2) + '\n')
