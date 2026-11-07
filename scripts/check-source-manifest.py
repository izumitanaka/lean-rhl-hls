#!/usr/bin/env python3
"""Verify the frozen baseline files; no dependency beyond Python is required."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent.parent
records = json.loads((root / "evidence/source-files.json").read_text())
failures = []
for record in records:
    path = root / record["path"]
    if not path.is_file():
        failures.append(f"missing: {record['path']}")
    elif hashlib.sha256(path.read_bytes()).hexdigest() != record["sha256"]:
        failures.append(f"changed: {record['path']}")
if failures:
    raise SystemExit("\n".join(failures))
print(f"PASS: {len(records)} copied baseline files match their SHA256 records")
