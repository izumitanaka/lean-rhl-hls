#!/usr/bin/env python3
"""Independent Icarus checks for whole-program input, including repeated start."""
import json
from pathlib import Path
import runpy
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'artifacts/whole-program'
bench = runpy.run_path(str(ROOT / 'scripts/check-pipelining-rtl.py'))['bench']


def main():
    nominal = [3, 6, 9, 12, 15, 18, 21, 24]
    cases = [
        ('filter', nominal, 2, [5, 8, 11, 14, 17, 20, 23, 0], False),
        ('nested', [0, 5, 8, 0, 0, 0, 0, 0], 1, [0, 0, 6, 7, 9, 10, 0, 0], False),
        ('ascending', nominal, 1, [4, 0, 10, 0, 16, 0, 22, 0], False),
        ('descending', nominal, 1, [4, 0, 10, 0, 16, 0, 22, 0], False),
        ('empty', nominal, 1, [0] * 8, False),
        ('wrapping', nominal, 1, [4, 7, 0, 0, 0, 0, 0, 0], False),
        ('failing', nominal, 1, [], True),
    ]
    records = []
    with tempfile.TemporaryDirectory(prefix='whole-program-') as tmp:
        for name, values, output, expected, failure in cases:
            tb = OUT / f'{name}-tb.sv'
            tb.write_text(bench({0: values, 1: [0] * 8, 2: [0] * 8}, output, expected, None, fail=failure))
            exe = Path(tmp) / name
            for phase, command in [
                ('compile', ['iverilog', '-g2012', '-s', 'tb', '-o', str(exe), str(OUT / f'{name}.sv'), str(tb)]),
                ('simulation', ['vvp', str(exe)]),
            ]:
                result = subprocess.run(command, text=True, capture_output=True, timeout=60)
                (OUT / f'{name}-{phase}.log').write_text(result.stdout + result.stderr)
                if result.returncode:
                    raise RuntimeError(f'{name}/{phase}: {result.stdout}{result.stderr}')
            if 'PASS external RTL' not in result.stdout:
                raise RuntimeError(f'{name}: missing success marker')
            records.append({'case': name, 'status': 'pass', 'invocations': 2, 'expected_error': failure})
            print(f'PASS {name}')
    (OUT / 'simulation.json').write_text(json.dumps(
        {'tool': 'iverilog/vvp', 'synthesis_run': False, 'cases': records}, indent=2) + '\n')


if __name__ == '__main__':
    main()
