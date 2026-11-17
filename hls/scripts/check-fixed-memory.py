#!/usr/bin/env python3
"""Check all declared arrays independently, including both sides of a copy."""
import json
from pathlib import Path
import runpy
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'artifacts/fixed-memory'
bench = runpy.run_path(str(ROOT / 'scripts/check-pipelining-rtl.py'))['bench']


def main():
    ordinary = {0: [10, 20, 30, 40], 1: [5, 6, 7, 8], 2: [101, 102, 103, 104]}
    cases = [
        ('independent', ordinary, [[99, 20, 30, 40], [10, 77, 30, 40], [10, 77, 30, 40]]),
        ('repeated', ordinary, [[11, 21, 31, 40], [11, 21, 30, 40], ordinary[2]]),
        ('swap', ordinary, [ordinary[1], ordinary[0], ordinary[0]]),
        ('nested-mixed', {**ordinary, 0: [0, 20, 30, 40]},
         [[0, 20, 30, 40], [101, 1, 103, 104], ordinary[2]]),
        ('nested-true', ordinary, [ordinary[0], [10, 1, 30, 40], ordinary[2]]),
        ('self', ordinary, [ordinary[0], ordinary[1], ordinary[2]]),
    ]
    records = []
    with tempfile.TemporaryDirectory(prefix='fixed-memory-') as tmp:
        for name, arrays, expected in cases:
            for output, values in enumerate(expected):
                label = f'{name}-array{output}'
                tb = OUT / f'{label}-tb.sv'
                # These kernels modify their input arrays. Reload the declared
                # inputs before EACH invocation, without resetting the circuit.
                # The shared bench otherwise assumes a read-only input bank.
                source = bench(arrays, output, values, None)
                start = 'repeat (2) begin @(negedge clk); start=1;'
                setup = "x=32'd0; y=32'd0;"
                assert source.count(start) == source.count(setup) == 1
                source = source.replace(start, '@(negedge clk); start=1;')
                source = source.replace(setup, 'repeat (2) begin\n' + setup)
                tb.write_text(source)
                exe = Path(tmp) / label
                for phase, command in [
                    ('compile', ['iverilog', '-g2012', '-s', 'tb', '-o', str(exe),
                                 str(OUT / f'{name}.sv'), str(tb)]),
                    ('simulation', ['vvp', str(exe)]),
                ]:
                    result = subprocess.run(command, text=True, capture_output=True, timeout=60)
                    (OUT / f'{label}-{phase}.log').write_text(result.stdout + result.stderr)
                    if result.returncode:
                        raise RuntimeError(f'{label}/{phase}: {result.stdout}{result.stderr}')
                if 'PASS external RTL' not in result.stdout:
                    raise RuntimeError(f'{label}: missing success marker')
                records.append({'case': name, 'output': output, 'status': 'pass', 'invocations': 2})
                print(f'PASS {label}')
    (OUT / 'simulation.json').write_text(json.dumps(
        {'tool': 'iverilog/vvp', 'synthesis_run': False, 'cases': records}, indent=2) + '\n')


if __name__ == '__main__':
    main()
