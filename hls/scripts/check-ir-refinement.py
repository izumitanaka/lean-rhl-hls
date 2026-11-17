#!/usr/bin/env python3
"""Runtime BV32 boundary checks of the regenerated ordinary-Lean HLS output."""
import json
import argparse
from pathlib import Path
import runpy
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--output-dir', type=Path, default=Path('artifacts/ir-refinement'))
OUT = ROOT / parser.parse_args().output_dir
bench = runpy.run_path(str(ROOT / 'scripts/check-pipelining-rtl.py'))['bench']
cases = [
    ('zero', 0, [4294967295, 4294967295, 0, 0]),
    ('one', 1, [0, 0, 4294967295, 4294967295]),
    ('high-bit', 2147483648, [2147483647, 2147483647, 2147483648, 2147483648]),
    ('maximum', 4294967295, [4294967294, 4294967294, 1, 1]),
]
records = []
with tempfile.TemporaryDirectory(prefix='wrap32-rtl-') as tmp:
    for name, value, expected in cases:
        tb = OUT / f'{name}-tb.sv'
        text = bench({0: [value, 0, 0, 0], 1: [0]*4}, 1, expected, None)
        boundary_checks = """
read_reg=0; read_id=1; read_addr=4; #1;
if (read_valid || read_data !== 0) $fatal(1,"one-past address");
read_addr=32'hffffffff; #1;
if (read_valid || read_data !== 0) $fatal(1,"maximum address");
read_id=32'hffffffff; read_addr=0; #1;
if (read_valid || read_data !== 0) $fatal(1,"unknown maximum ID");
@(negedge clk); rst=1; start=1; cfg_we=1;
@(negedge clk);
if (busy || done || error) $fatal(1,"reset must win over start/configure");
rst=0; start=0; cfg_we=0;
"""
        text = text.replace('end $display("PASS external RTL")',
                            'end ' + boundary_checks + '$display("PASS external RTL")')
        tb.write_text(text)
        exe = Path(tmp) / name
        for phase, args in [
            ('compile', ['iverilog', '-g2012', '-s', 'tb', '-o', str(exe), str(OUT/'arithmetic.sv'), str(tb)]),
            ('simulation', ['vvp', str(exe)]),
        ]:
            result = subprocess.run(args, text=True, capture_output=True, timeout=60)
            (OUT/f'{name}-{phase}.log').write_text(result.stdout + result.stderr)
            if result.returncode:
                raise RuntimeError(f'{name}/{phase}: {result.stdout}{result.stderr}')
        if 'PASS external RTL' not in result.stdout:
            raise RuntimeError(f'{name}: no success marker')
        records.append({'case': name, 'status': 'pass', 'invocations': 2, 'port_boundaries': 'pass', 'reset_start_priority': 'pass'})
        print(f'PASS wrap32 {name}')
(OUT/'simulation.json').write_text(json.dumps({'tool': 'iverilog/vvp', 'cases': records}, indent=2)+'\n')
