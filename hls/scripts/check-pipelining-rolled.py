#!/usr/bin/env python3
"""Cross-check rolled boundary overlap using Icarus, without synthesis."""
import json
from pathlib import Path
import runpy
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'artifacts/rolled-pipeline'
bench = runpy.run_path(str(ROOT / 'scripts/check-pipelining-rtl.py'))['bench']

def main():
    values = [10 * (i + 1) for i in range(8)]
    cases = [
        ('copy', values, 8, 0, False),
        ('gather', values[::-1], 8, 0, False),
        ('zero', [0] * 8, 0, 0, False),
        ('one', [10] + [0] * 7, 1, 0, False),
        ('head-error', [], 8, 0, True),
        ('later-head-error', [], 9, 0, True),
        ('alias', [0] * 8, 8, 0, False),
        ('nested-branch', values, 8, 1, False),
    ]
    records = []
    with tempfile.TemporaryDirectory(prefix='rolled-hls-') as tmp:
        for name, expected, count, flag, fail in cases:
            # These are control-IR unit tests with initially zero holding
            # registers; native entry restart coverage is check-certified-hls.
            tb = bench({0: values, 1: [0]*8, 2: [0]*8}, 1, expected,
                       None, fail=fail, x=flag, y=count)
            tb = tb.replace('repeat (2) begin', 'repeat (1) begin')
            path = OUT / f'{name}-tb.sv'
            path.write_text(tb)
            exe = str(Path(tmp) / name)
            for phase, command in [
                ('compile', ['iverilog', '-g2012', '-s', 'tb', '-o', exe,
                             str(OUT / f'{name}.sv'), str(path)]),
                ('simulation', ['vvp', exe]),
            ]:
                result = subprocess.run(command, text=True, capture_output=True, timeout=60)
                (OUT / f'{name}-{phase}.log').write_text(result.stdout + result.stderr)
                result.check_returncode()
                if phase == 'simulation' and 'PASS external RTL' not in result.stdout:
                    raise RuntimeError(name)
            print(f'PASS {name}')
            records.append({'case': name, 'expected_error': fail, 'status': 'pass'})
    (OUT / 'simulation.json').write_text(json.dumps({'tool': 'iverilog/vvp',
        'synthesis_run': False, 'cases': records}, indent=2) + '\n')

if __name__ == '__main__':
    main()
