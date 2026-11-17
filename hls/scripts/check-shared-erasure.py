#!/usr/bin/env python3
"""Regenerate C and reject old expression building in the shared compiler.

Inspect the generated unit (not a stale Lake artifact); source input Expr
leaves are allowed, but recursive read/value reconstruction is not.
"""
from pathlib import Path
import hashlib
import json
import argparse
import re
import subprocess

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--output-dir', type=Path, default=Path('artifacts/shared-erasure'))
args = parser.parse_args()
out = root / args.output_dir
out.mkdir(parents=True, exist_ok=True)
source = root / 'src/IRComparison/Circuit/SharedExpr.lean'
cfile = out / 'SharedExpr.c'
result = subprocess.run(['lake', 'env', 'lean', '-c', str(cfile), str(source)],
                        cwd=root, text=True, capture_output=True, timeout=120)
(out / 'c-generation.log').write_text(result.stdout + result.stderr)
result.check_returncode()
c = cfile.read_text()
for forbidden in [r'\b\w*Circuit_(?:read|value)\(',
                  r'\b\w*Shared_(?:lowerRead|lowerValue|build)\(']:
    matches = re.findall(forbidden, c)
    if matches:
        raise SystemExit(f'old expression/specification builder remains in C: {matches[:4]}')
for required in ['Shared_Raw_read(', 'Shared_Raw_value(', 'Shared_Raw_build(', 'Shared_compile(']:
    if required not in c:
        raise SystemExit(f'missing executable builder: {required}')
record = {'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
          'c_sha256': hashlib.sha256(cfile.read_bytes()).hexdigest(),
          'old_read_value_calls': 0, 'proof_builder_calls': 0,
          'status': 'PASS', 'note': 'Caller Expr leaves remain; specification builders are explicitly noncomputable. Public compile uses Raw.build; build_projection is kernel checked.'}
additional = []
for stem, symbol in [('SharedEmitInto', 'Shared_NetEmission_intoPair'), ('SharedStatements', 'Shared_prepare'),
                     ('SharedStatementSound', 'Shared_instExpressionSemanticsPrepared'),
                     ('SharedLower', 'Shared_command'), ('SharedPipeline', 'Shared_pipeline'),
                     ('SharedGraph', 'Shared_generateGraphModule'), ('SharedCompiler', 'Shared_compileStructured'),
                     ('SharedAnalysis', 'Shared_Program_reads')]:
    unit = root / f'src/IRComparison/Circuit/{stem}.lean'
    generated = out / f'{stem}.c'
    check = subprocess.run(['lake', 'env', 'lean', '-c', str(generated), str(unit)],
                           cwd=root, text=True, capture_output=True, timeout=120)
    (out / f'{stem}-c-generation.log').write_text(check.stdout + check.stderr)
    check.check_returncode()
    body = generated.read_text()
    for forbidden in [r'\b\w*Circuit_(?:read|value)\(', r'\b\w*Shared_(?:lowerRead|lowerValue|build)\(']:
        if re.search(forbidden, body):
            raise SystemExit(f'{stem}: old expression/specification construction remains')
    if symbol not in body:
        raise SystemExit(f'{stem}: expected executable adapter not generated')
    additional.append({'module': stem, 'source_sha256': hashlib.sha256(unit.read_bytes()).hexdigest(),
                       'c_sha256': hashlib.sha256(generated.read_bytes()).hexdigest(),
                       'old_read_value_calls': 0, 'status': 'PASS'})
record['additional_units'] = additional
(out / 'erasure.json').write_text(json.dumps(record, indent=2) + '\n')
print('PASS: regenerated C has no old read/value or proof-builder calls')
