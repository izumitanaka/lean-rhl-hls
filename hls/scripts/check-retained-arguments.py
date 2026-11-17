#!/usr/bin/env python3
"""Check call-time argument retention in printed RTL, including restart."""
import json
from pathlib import Path
import runpy
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'artifacts/retained-arguments'
bench = runpy.run_path(str(ROOT / 'scripts/check-pipelining-rtl.py'))['bench']
records = []
with tempfile.TemporaryDirectory(prefix='retained-arguments-') as temporary:
    for case in json.loads((OUT / 'cases.json').read_text()):
        name, expected = case['name'], case['expected']
        tb = OUT / f'{name}.tb.sv'
        tb.write_text(bench({0: [20], 1: [0]}, 1, [] if expected is None else [expected],
                            None, fail=expected is None, x=case['x'], y=case['y']))
        executable = Path(temporary) / name
        for phase, command in [
            ('compile', ['iverilog', '-g2012', '-s', 'tb', '-o', str(executable),
                         str(OUT / f'{name}.sv'), str(tb)]),
            ('run', ['vvp', str(executable)]),
        ]:
            result = subprocess.run(command, capture_output=True, text=True, timeout=60)
            (OUT / f'{name}.{phase}.log').write_text(result.stdout + result.stderr)
            result.check_returncode()
        assert 'PASS external RTL' in result.stdout
        command = f'read_verilog -sv "{OUT / (name + ".sv")}"; hierarchy -check -top hls_top; proc; opt; check'
        result = subprocess.run(['yosys', '-Q', '-T', '-p', command], capture_output=True, text=True, timeout=60)
        (OUT / f'{name}.yosys.log').write_text(result.stdout + result.stderr)
        result.check_returncode()
        records.append({**case, 'status': 'PASS', 'invocations': 2,
                        'tools': ['iverilog/vvp', 'yosys structure check']})
        print(f'PASS {name}', flush=True)
(OUT / 'external.json').write_text(json.dumps(records, indent=2) + '\n')
