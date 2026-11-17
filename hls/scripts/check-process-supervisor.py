#!/usr/bin/env python3
"""Exercise the exact supervisor embedded in Lean, including cleanup faults."""
import json
import os
from pathlib import Path
import signal
import sys
import time
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
text = (ROOT/'src/IRComparison/Hybrid/HybridRoutingVC.lean').read_text()
source = text.split('private def processSupervisor : String := r###"\n', 1)[1].split('"###', 1)[0]
ns = {'__name__': 'supervisor_regression'}
exec(compile(source, 'embedded-process-supervisor', 'exec'), ns)
run = ns['supervise']
records = []


def record(name, result):
    records.append({k: v for k, v in result.items() if k not in ('stdout', 'stderr')} |
                   {'case': name, 'stdout_bytes': len(result['stdout']), 'stderr_bytes': len(result['stderr'])})
    print('PASS', name, result['elapsed_ms'], 'ms')


r = run([sys.executable, '-c', "import sys; sys.stdout.write('o'*100000); sys.stderr.write('e'*100000)"], 2000)
assert r['exit_code'] == 0 and not r['errors'] and not r['timed_out'], r
assert len(r['stdout']) == len(r['stderr']) == 100000
record('both-pipes-larger-than-buffer', r)

for name, code in [('stdout-and-stderr', 'import time; time.sleep(30)'),
                   ('stderr-only', 'import os,time; os.close(1); time.sleep(30)'),
                   ('stdout-only', 'import os,time; os.close(2); time.sleep(30)')]:
    r = run([sys.executable, '-c', f'import subprocess; subprocess.Popen([{sys.executable!r}, "-c", {code!r}]); print("parent exited", flush=True)'], 100)
    assert r['timed_out'] and r['exit_code'] == 0 and not r['errors'], r
    assert all(r['eof'].values()) and r['elapsed_ms'] < 1500, r
    record('parent-exits-'+name, r)

# Even a child that leaves the managed group cannot force pipe cleanup to
# wait forever. This test explicitly kills its escaped fixture afterwards.
child = 'import time; time.sleep(30)'
r = run([sys.executable, '-c', f'import subprocess; p=subprocess.Popen([{sys.executable!r}, "-c", {child!r}], start_new_session=True); print(p.pid, flush=True)'], 100)
try:
    assert r['timed_out'] and r['errors'] and r['elapsed_ms'] < 1500, r
    record('escaped-writer-bounded-close', r)
finally:
    os.killpg(int(r['stdout'].strip()), signal.SIGKILL)

# Failed signaling must be reported and must not turn cleanup into wait().
with patch.object(ns['os'], 'killpg', side_effect=PermissionError('injected kill failure')):
    r = run([sys.executable, '-c', 'import time; time.sleep(30)'], 50)
try:
    assert r['timed_out'] and r['errors'] and r['exit_code'] is None and r['elapsed_ms'] < 1500, r
    record('kill-error-bounded-cleanup', r)
finally:
    os.killpg(r['pid'], signal.SIGKILL)
    stop = time.monotonic()+2
    while os.waitpid(r['pid'], os.WNOHANG)[0] == 0:
        if time.monotonic() >= stop:
            raise RuntimeError('test cleanup could not reap injected failure child')
        time.sleep(.005)

original_poll = ns['subprocess'].Popen.poll
calls = 0

def flaky_poll(self):
    global calls
    calls += 1
    if calls == 1:
        raise OSError('injected waitpid failure')
    return original_poll(self)

with patch.object(ns['subprocess'].Popen, 'poll', flaky_poll):
    r = run([sys.executable, '-c', 'import time; time.sleep(30)'], 1000)
assert r['errors'] and r['exit_code'] is not None and r['elapsed_ms'] < 1500, r
record('poll-error-cleanup', r)

original_read = os.read
failed = False

def flaky_read(fd, size):
    global failed
    # Popen's exec-status pipe uses a different size. Inject only into drain.
    if size == 65536 and not failed:
        failed = True
        raise OSError('injected output collection failure')
    return original_read(fd, size)

with patch.object(ns['os'], 'read', flaky_read):
    r = run([sys.executable, '-c', 'import time; print("ready", flush=True); time.sleep(30)'], 1000)
assert failed and r['errors'] and r['exit_code'] is not None and r['elapsed_ms'] < 1500, r
record('output-read-error-cleanup', r)

r = run(['/no-such-hls-test-solver'], 100)
assert r['errors'] and r['pid'] is None
record('spawn-error', r)

out = ROOT/'artifacts/process-deadline'
out.mkdir(exist_ok=True)
(out/'supervisor-cases.json').write_text(json.dumps(records, indent=2)+'\n')
