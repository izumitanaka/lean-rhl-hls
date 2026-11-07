#!/usr/bin/env python3
"""Independent integer reference models for small BV32 HLS workloads.

Does not read Lean source, IR, generated RTL, or simulator results. Python's
unbounded integers are reduced mod 2**32 at the specified word boundary.
These fixtures are correctness inputs, not full-size MachSuite datasets.
"""
import json
from pathlib import Path

MOD = 1 << 32

def word(n):
    return n % MOD

def make_cases():
    cases = []
    families = ['axpy', 'fir4', 'prefix', 'dot', 'histogram', 'gather',
                'gemm2', 'stencil3', 'replace-zero', 'recurrence', 'fir-pipeline']
    for family in families:
        for variant in ['nominal', 'boundary']:
            size = 16 if family == 'stencil3' else 4 if family == 'gemm2' else 8
            a = list(range(1, size + 1))
            b = [3 * j + 2 for j in range(size)]
            alpha = 3
            if variant == 'boundary':
                pool = [MOD-1, 0, 1, 1<<31, (1<<31)-1, 2, MOD-2, 0]
                a = [pool[j % len(pool)] for j in range(size)]
                b = [pool[(3*j+2) % len(pool)] for j in range(size)]
                alpha = MOD-1
            expected = [0] * size
            out = 2
            inputs = {0: a, 1: b}
            if family == 'axpy':
                expected = [word(alpha*u+v) for u,v in zip(a,b)]
            elif family in ('fir4', 'fir-pipeline'):
                inputs = {0: a}
                for j in range(size-3):
                    expected[j] = word(sum((k+1)*a[j+k] for k in range(4)))
                out = 1 if family == 'fir4' else 2
                if family == 'fir-pipeline':
                    # Replacement covers exactly the five valid FIR outputs.
                    for j in range(size-3):
                        if expected[j] == 0:
                            expected[j] = alpha
            elif family == 'prefix':
                inputs = {0: a}
                expected = [word(sum(a[:j+1])) for j in range(size)]
                out = 1
            elif family == 'dot':
                expected[0] = word(sum(u*v for u,v in zip(a,b)))
            elif family == 'histogram':
                inputs = {0: a}
                expected = [sum(v % 4 == bucket for v in a) if bucket < 4 else 0 for bucket in range(size)]
                out = 1
            elif family == 'gather':
                keys = list(reversed(range(size))) if variant == 'nominal' else [3,3,0,7,1,0,7,2]
                inputs = {0: keys, 1: b}
                expected = [b[key] for key in keys]
            elif family == 'gemm2':
                expected = [word(sum(a[row*2+k]*b[k*2+col] for k in range(2)))
                            for row in range(2) for col in range(2)]
            elif family == 'stencil3':
                inputs = {0: a}
                weights = [[1,2,1],[2,4,2],[1,2,1]]
                for row in range(2):
                    for col in range(2):
                        expected[row*2+col] = word(sum(weights[u][v]*a[(row+u)*4+col+v]
                                                       for u in range(3) for v in range(3)))
                out = 1
            elif family == 'replace-zero':
                b = [0,1,0,2,0,3,0,4] if variant == 'nominal' else b
                inputs = {1: b}
                expected = [v if v != 0 else alpha for v in b]
            elif family == 'recurrence':
                inputs = {0: a}
                expected = [word(2*sum(a[:j+1])) for j in range(size)]
                out = 0
            cases.append({'name': f'bench-{family}-{variant}', 'family': family, 'variant': variant,
                          'size': size, 'x': alpha, 'y': 0,
                          'inputs': [{'id': i, 'values': values} for i,values in sorted(inputs.items())],
                          'expected': [{'id': out, 'values': expected}]})
    return cases

def main():
    root = Path(__file__).resolve().parent.parent
    destination = root / 'artifacts/benchmarks/fixtures.json'
    destination.parent.mkdir(parents=True, exist_ok=True)
    cases = make_cases()
    destination.write_text(json.dumps({'word_width': 32, 'cases': cases}, indent=2) + '\n')
    print(f'Wrote {len(cases)} independent reference fixtures to {destination.relative_to(root)}')

if __name__ == '__main__':
    main()
