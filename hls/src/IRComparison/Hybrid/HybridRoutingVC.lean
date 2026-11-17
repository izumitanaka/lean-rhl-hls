import IRComparison.Hybrid.HybridCompactFIFO

/-! RHL receive/copy/sequence/loop obligations. Unknown affine discard counts
are synthesized by SMT; the model is checked by the general rule constructors.
This is not a counterexample query and does not enumerate loop iterations. -/
namespace IRComparison.HybridRoutingVC
open AffineAddress CompactRouting
open PaperCore (SMT)

structure Term where
  coefficient : SMT
  offset : SMT

def literal (e : Linear) : Term := ⟨.num e.coefficient,.num e.offset⟩
def param (name : String) : Term := ⟨.param (name++".coefficient"),.param (name++".offset")⟩
def add (a b : Term) : Term := ⟨SMT.add a.coefficient b.coefficient,SMT.add a.offset b.offset⟩
def sub (a b : Term) : Term := ⟨SMT.sub a.coefficient b.coefficient,SMT.sub a.offset b.offset⟩
def mul (k : Int) (a : Term) : Term := ⟨SMT.mul (.num k) a.coefficient,SMT.mul (.num k) a.offset⟩
def evaluate (a : Term) (i : Int) : SMT := SMT.add (SMT.mul a.coefficient (.num i)) a.offset
def equal (a b : Term) : SMT := SMT.conj [SMT.eq a.coefficient b.coefficient,SMT.eq a.offset b.offset]
def shifted (a : Term) (delta : Int) : Term := ⟨a.coefficient,SMT.add a.offset (SMT.mul a.coefficient (.num delta))⟩

structure Cursor where
  first : Term
  step : Int
  count : Term

def advance (s : Cursor) (d : Term) : Cursor :=
  let used := add d (literal ⟨0,1⟩)
  ⟨add s.first (mul s.step used),s.step,sub s.count used⟩

def nonnegative (e : Term) (start stride : Int) (count : Nat) : SMT :=
  if count = 0 then SMT.truth else SMT.conj
    [SMT.le (.num 0) (evaluate e start),SMT.le (.num 0) (evaluate e (start+(count-1:Int)*stride))]

/-- Tr-InsMove contributes no cursor change. Tr-InsRBuf contributes address
agreement, nonnegative discard, and enough tokens. Tr-Seq threads the cursor. -/
def loads (label : String) (start stride : Int) (count : Nat) :
    Nat → List SymbolicWindowSchedule.Load → Cursor → Cursor × List SMT
  | _,[],before => (before,[])
  | j,.saved _::rest,before => loads label start stride count (j+1) rest before
  | j,.memory address::rest,before =>
      let d := param (label++toString j)
      let next := advance before d
      let (after,conditions) := loads label start stride count (j+1) rest next
      (after,equal (add before.first (mul before.step d)) (literal address) ::
        nonnegative d start stride count :: nonnegative next.count start stride count :: conditions)

/-- Initial establishment and preservation of the FIFO cursor invariant.
Only affine endpoints are used; they imply the guards for every iteration. -/
def query (memory : HybridSymbolicLoop.Code) (producer : CompactSequence.Seq) : SMT :=
  let before : Cursor := ⟨literal ⟨0,producer.first⟩,producer.step,literal ⟨0,producer.count⟩⟩
  let (initial,initVC) := loads "initial." memory.start 0 1 0 memory.initial before
  let nextHead : Cursor := ⟨shifted initial.first (-memory.stride),initial.step,
    shifted initial.count (-memory.stride)⟩
  let (after,stepVC) := loads "refill." memory.start memory.stride memory.count 0 memory.refill nextHead
  SMT.conj (initVC ++ stepVC ++ [equal after.first initial.first,equal after.count initial.count])

def modelLinear (values : String → Int) (name : String) : Linear :=
  ⟨values (name++".coefficient"),values (name++".offset")⟩

/-- Reconstruct the derivation using the actual model. Every memory replacement
uses the same generally proved take/copy rules, with exact address equality. -/
def checkLoads (values : String → Int) (label : String) :
    Nat → (source : List SymbolicWindowSchedule.Load) → (before : Sequence) → Option (Route source before)
  | _,[],before => some ⟨[],before,[],by intro i h input old q hq; exact ⟨rfl,by intro vs qs eq; cases eq; exact hq⟩⟩
  | j,.saved n::rest,before => do
      return CompactRouting.saved (← checkLoads values label (j+1) rest before) n
  | j,.memory address::rest,before => do
      let discard := modelLinear values (label++toString j)
      if same : plus before.first (scale before.step discard) = address then
        return take discard address same (← checkLoads values label (j+1) rest (CompactRouting.advance before discard))
      else none

def accept (memory : HybridSymbolicLoop.Code) (producer : CompactSequence.Seq)
    (request response : String) : Option (HybridCompactFIFO.Plan memory producer) := do
  let bindings ← PaperCore.SMTConnection.acceptResponse (query memory producer) request response
  let values := fun name => (bindings.lookup name).getD 0
  let initial ← checkLoads values "initial." 0 memory.initial ⟨⟨0,producer.first⟩,producer.step,⟨0,producer.count⟩⟩
  let refill ← checkLoads values "refill." 0 memory.refill (shift initial.after (-memory.stride))
  if closes : refill.after = initial.after then
    if firstSafe : checkGuards initial.guards memory.start 0 1 = true then
      if restSafe : checkGuards refill.guards memory.start memory.stride memory.count = true then
        return ⟨initial,refill,closes,by
          simpa only [Int.natCast_zero,Int.zero_mul,Int.add_zero] using checkGuards_sound (k:=0) firstSafe (by omega),
          by intro k hk; exact checkGuards_sound restSafe hk⟩
      else none
    else none
  else none

/-- Soundness depends on checked rule premises, even if SMT is faulty. No
individual source-input evaluation or proof search replaces this theorem. -/
theorem accept_correct (h : accept memory producer request response = some plan)
    (hq : CommunicationIR.Corresponds input producer.entries q) :
    (plan.code.eval x y s q).map Prod.fst = memory.eval input x y s :=
  plan.correct s q hq

/-- External-process supervision is an IO boundary, not parser fuel or a
source runtime bound. Python's POSIX nonblocking descriptors avoid orphaned
Lean readToEnd tasks. The supervisor owns the only outer output descriptors;
solver descendants inherit separate pipes which it closes after bounded cleanup.
No subprocess wait/communicate or blocking pipe read is used by the supervisor. -/
private def processSupervisor : String := r###"
# Embedded in HybridRoutingVC.lean. POSIX subprocess supervision only;
# solver answers are still independently checked by Lean.
import json, os, selectors, signal, subprocess, sys, time


def supervise(command, budget_ms, cleanup_ms=250):
    started = time.monotonic()
    deadline = started + budget_ms / 1000
    selector = selectors.DefaultSelector()
    process = None
    buffers = {'stdout': bytearray(), 'stderr': bytearray()}
    errors = []
    signals = []
    timed_out = False
    code = None
    eof = {'stdout': False, 'stderr': False}

    def poll():
        nonlocal code
        try:
            code = process.poll()  # waitpid(WNOHANG), never wait()
        except Exception as e:
            errors.append('poll: ' + repr(e))
        return code

    def kill_group():
        try:
            os.killpg(process.pid, signal.SIGKILL)
            signals.append('SIGKILL: sent')
        except ProcessLookupError:
            signals.append('SIGKILL: group already absent')
        except Exception as e:
            signals.append('SIGKILL: failed')
            errors.append('killpg: ' + repr(e))

    def close_stream(key):
        try:
            selector.unregister(key.fileobj)
        except Exception as e:
            errors.append('unregister: ' + repr(e))
        try:
            key.fileobj.close()
        except Exception as e:
            errors.append('close: ' + repr(e))

    def drain(until):
        # One bounded read per ready descriptor. A flooding child cannot
        # prevent the outer loop from checking the wall-clock deadline.
        for key, _ in selector.select(max(0, min(0.005, until-time.monotonic()))):
            try:
                chunk = os.read(key.fd, 65536)
                if chunk:
                    buffers[key.data].extend(chunk)
                else:
                    eof[key.data] = True
                    close_stream(key)
            except BlockingIOError:
                pass
            except Exception as e:
                errors.append('read ' + key.data + ': ' + repr(e))
                close_stream(key)

    try:
        if time.monotonic() >= deadline:
            timed_out = True
        else:
            process = subprocess.Popen(command, stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                start_new_session=True, close_fds=True, bufsize=0)
            for name, stream in [('stdout', process.stdout), ('stderr', process.stderr)]:
                os.set_blocking(stream.fileno(), False)
                selector.register(stream, selectors.EVENT_READ, name)
            while True:
                poll()
                if errors:
                    break
                if code is not None and all(eof.values()):
                    break
                if time.monotonic() >= deadline:
                    timed_out = True
                    break
                drain(deadline)
    except Exception as e:
        errors.append('supervision: ' + repr(e))
    finally:
        if process is not None:
            # The parent may already have exited: never condition killpg on
            # its return code. Descendants can still own the pipe writers.
            if timed_out or errors:
                kill_group()
                cleanup_deadline = time.monotonic() + cleanup_ms / 1000
                try:
                    while time.monotonic() < cleanup_deadline:
                        poll()
                        if code is not None and not selector.get_map():
                            break
                        drain(cleanup_deadline)
                except Exception as e:
                    errors.append('cleanup: ' + repr(e))
            poll()
            if code is None:
                errors.append('direct process not reaped before cleanup deadline')
            if not all(eof.values()):
                errors.append('output incomplete; closing readers at cleanup deadline')
            for key in list(selector.get_map().values()):
                close_stream(key)
            # Also close descriptors if setup failed before registration.
            for stream in (process.stdout, process.stderr):
                if stream is not None and not stream.closed:
                    try:
                        stream.close()
                    except Exception as e:
                        errors.append('final close: ' + repr(e))
        selector.close()
    return {'exit_code': code, 'pid': process.pid if process is not None else None,
        'timed_out': timed_out,
        'stdout': buffers['stdout'].decode('utf-8', errors='replace'),
        'stderr': buffers['stderr'].decode('utf-8', errors='replace'),
        'errors': errors, 'signals': signals, 'eof': eof,
        'elapsed_ms': int((time.monotonic()-started)*1000),
        'cleanup_budget_ms': cleanup_ms}

if __name__ == '__main__':
    # Only this supervisor owns the outer stdout/stderr inherited from Lean.
    # Solver descendants get the separate pipes created by Popen above.
    print(json.dumps(supervise(sys.argv[2:], int(sys.argv[1]))), flush=True)
"###

structure ProcessResult where
  output : IO.Process.Output
  timedOut : Bool
  managementError : Bool := false
  /-- Full supervisor result, including actual exit code (possibly null), EOF,
  signal outcomes and cleanup errors. A missing exit code uses 124 only in
  the compatibility Output field, never in this audit record. -/
  report : String := ""

def processUntil (command : String) (args : Array String) (deadline : Nat) : IO ProcessResult := do
  let remaining := deadline - (← IO.monoMsNow)
  if remaining = 0 then
    return ⟨⟨124,"",""⟩,true,false,"{\"timed_out\":true,\"not_started\":true}"⟩
  let result ← IO.Process.output {cmd := "python3", args := #["-I","-S","-c",processSupervisor,toString remaining,command] ++ args}
  if result.exitCode != 0 then
    throw (IO.userError s!"process supervisor exited {result.exitCode}: {result.stderr}")
  let report ← IO.ofExcept (Lean.Json.parse result.stdout)
  let timedOut ← IO.ofExcept ((report.getObjVal? "timed_out").bind Lean.Json.getBool?)
  let errors ← IO.ofExcept ((report.getObjVal? "errors").bind Lean.Json.getArr?)
  let exit ← IO.ofExcept (report.getObjVal? "exit_code")
  let code : UInt32 := match exit.getInt? with
    | .ok n => if n < 0 then UInt32.ofNat (128 + n.natAbs) else UInt32.ofNat n.toNat
    | .error _ => 124
  let stdout ← IO.ofExcept ((report.getObjVal? "stdout").bind Lean.Json.getStr?)
  let stderr ← IO.ofExcept ((report.getObjVal? "stderr").bind Lean.Json.getStr?)
  let expired := decide ((← IO.monoMsNow) ≥ deadline)
  let record := Lean.Json.mkObj [("supervisor",report),("host_deadline_reached",Lean.toJson expired)]
  return ⟨⟨code,stdout,stderr⟩,timedOut || expired,!errors.isEmpty,record.pretty⟩

/-- Atomic directory creation isolates concurrent calls even under one root.
Retries here concern filesystem name collisions, not compiler completeness. -/
def freshDirectory (root : System.FilePath) : IO System.FilePath := do
  IO.FS.createDirAll root
  for _ in [:64] do
    let nonce ← IO.rand 0 18446744073709551615
    let directory := root / s!"call-{nonce}"
    try
      IO.FS.createDir directory
      return directory
    catch e =>
      if !(← directory.pathExists) then throw e
  throw (IO.userError "could not allocate an isolated solver log directory")

def solve (memory : HybridSymbolicLoop.Code) (producer : CompactSequence.Seq)
    (directory : System.FilePath) (deadline : Option Nat := none)
    (solver : String := "z3") : IO (Option (HybridCompactFIFO.Plan memory producer)) := do
  let started ← IO.monoMsNow
  let stop := min (started+15000) (deadline.getD (started+15000))
  if started ≥ stop then return none
  let directory ← freshDirectory directory
  let request := PaperCore.SMT.script (query memory producer)
  let path := directory / "request.smt2"
  IO.FS.writeFile path request
  try
    let version ← processUntil solver #["-version"] (min stop (started+2000))
    IO.FS.writeFile (directory / "version-process.json") version.report
    if version.managementError then throw (IO.userError "solver version supervision failed")
    IO.FS.writeFile (directory / "version.txt") (version.output.stdout ++ version.output.stderr)
    if (← IO.monoMsNow) ≥ stop then
      IO.FS.writeFile (directory / "decision.txt") "rejected: deadline during solver version query\n"
      return none
    let result ← processUntil solver #["-T:15",path.toString] stop
    IO.FS.writeFile (directory / "process.json") result.report
    IO.FS.writeFile (directory / "response.txt") result.output.stdout
    IO.FS.writeFile (directory / "stderr.txt") result.output.stderr
    IO.FS.writeFile (directory / "exit-code.txt") (toString result.output.exitCode)
    let accepted := if result.timedOut || result.managementError || result.output.exitCode != 0 then none
      else accept memory producer request result.output.stdout
    let reason := if result.timedOut then "rejected: host deadline"
      else if result.managementError then "rejected: process/output cleanup error"
      else if result.output.exitCode != 0 then "rejected: solver exit status"
      else if accepted.isSome then "accepted: Lean routing checker constructed a plan"
      else "rejected: response parser or Lean routing conditions"
    IO.FS.writeFile (directory / "decision.txt") (reason ++ "\n")
    IO.FS.writeFile (directory / "elapsed-ms.txt") (toString ((← IO.monoMsNow)-started))
    return accepted
  catch e =>
    IO.FS.writeFile (directory / "decision.txt") s!"rejected: external process error: {e}\n"
    return none

end IRComparison.HybridRoutingVC
