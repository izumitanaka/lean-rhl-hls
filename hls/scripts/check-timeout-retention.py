#!/usr/bin/env python3
"""Real HLS entry: keep an accepted plan after a later solver pipe timeout."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
real_z3 = shutil.which('z3')
assert real_z3
with tempfile.TemporaryDirectory(prefix='hls-descendant-solver-') as tmp:
    tmp = Path(tmp)
    count = tmp/'calls'
    solver = tmp/'z3'
    solver.write_text(f'''#!/usr/bin/env python3
import pathlib,subprocess,sys
if '-version' in sys.argv:
    print('HLS deadline-test wrapper around {real_z3}')
    sys.exit(0)
p = pathlib.Path({str(count)!r})
n = int(p.read_text()) if p.exists() else 0
p.write_text(str(n+1))
if n == 0:
    sys.exit(subprocess.call([{real_z3!r}] + sys.argv[1:]))
subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)'])
print('solver parent exited', flush=True)
''')
    solver.chmod(0o700)
    env = dict(os.environ, PATH=str(tmp)+os.pathsep+os.environ['PATH'])
    r = subprocess.run(['lake','env','lean','--run','scripts/smt-timeout-retention.lean'],
                       cwd=ROOT,env=env,capture_output=True,text=True,timeout=20)
    print(r.stdout,end='')
    print(r.stderr,end='')
    r.check_returncode()
    assert int(count.read_text()) >= 2
    assert 'PASS adopted policy retained' in r.stdout
