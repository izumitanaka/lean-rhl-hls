#!/usr/bin/env python3
"""Simulate SMT-selected, counted-loop RTL with independent Icarus.
Checks every public output twice, with reset/config/start on the real interface.
No synthesis, area, frequency or physical timing claim.
"""
import json
import re
from pathlib import Path
import runpy
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'artifacts/rule-vcg'
bench = runpy.run_path(str(ROOT / 'scripts/check-pipelining-rtl.py'))['bench']
CASES = ['chain', 'nonadjacent', 'interleaved', 'intervening-read', 'public-array',
         'reverse', 'reverse-mismatch', 'window', 'reverse-window', 'dilated-window',
         'stride-two', 'empty', 'singleton']


def main():
    records = []
    with tempfile.TemporaryDirectory(prefix='rule-vcg-rtl-') as tmp:
        for name in CASES:
            path = OUT / name
            expected = json.loads((path / 'expected.json').read_text())
            for output in expected['outputs']:
                a = output['array']
                tb = path / f'output-{a}-tb.sv'
                tb.write_text(bench({k: [0]*8 for k in range(7)}, a, output['values'],
                                    None, fail=expected['error']).replace(
                                        'end $display("PASS external RTL")',
                                        '$display("CYCLES %0d", cycles); end $display("PASS external RTL")'))
                exe = Path(tmp) / f'{name}-{a}'
                for phase, cmd in [
                    ('compile', ['iverilog', '-g2012', '-s', 'tb', '-o', str(exe),
                                 str(path / 'output.sv'), str(tb)]),
                    ('simulation', ['vvp', str(exe)])]:
                    result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
                    (path / f'output-{a}-{phase}.log').write_text(result.stdout+result.stderr)
                    if result.returncode:
                        raise RuntimeError(f'{name}/{a}/{phase}: {result.stdout}{result.stderr}')
                if 'PASS external RTL' not in result.stdout:
                    raise RuntimeError(f'{name}/{a}: no success marker')
                print(f'PASS {name}/output-{a}')
                records.append({'case': name, 'output': a, 'policy': expected['policy'],
                                'status': 'pass', 'invocations': 2,
                                'compute_clocks': [int(n) for n in re.findall(r'CYCLES (\d+)', result.stdout)]})
    (OUT / 'simulation.json').write_text(json.dumps(
        {'tool': 'iverilog/vvp', 'synthesis_run': False, 'cases': records}, indent=2)+'\n')


if __name__ == '__main__':
    main()
