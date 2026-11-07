import IRComparison.Circuit.Backend
open IRComparison IRComparison.Circuit

/-- A missing source array must not acquire the ID of a private snapshot. -/
def missingSource : HybridUnifiedPipeline.Code := .expanded [
  ⟨0,.memory 0 [] false,none,[⟨0,[],.assign 0 (.memory 1 (.lit 0))⟩]⟩]

def malformedQueue : Artifact :=
  ⟨⟨0,#[.send 7 (.lit 0) 1,.halt],#[]⟩,#[wordRange,wordRange],#[],#[]⟩

def main : IO Unit := do
  match Circuit.compile #[(0,4)] missingSource with
  | .ok _ => throw (IO.userError "undeclared source array aliased a private snapshot")
  | .error msg => unless msg.startsWith "source arrays missing" do throw (IO.userError msg)
  match Circuit.emit malformedQueue [] with
  | .ok _ => throw (IO.userError "RTL referenced an undeclared queue")
  | .error msg => unless msg.startsWith "unknown queue" do throw (IO.userError msg)
  let malformedEdge : Artifact := { malformedQueue with machine := ⟨0,#[.jump 5],#[]⟩ }
  match Circuit.emit malformedEdge [] with
  | .ok _ => throw (IO.userError "RTL accepted an out-of-range control edge")
  | .error msg => unless msg == "invalid circuit edge" do throw (IO.userError msg)
  let variableSend : HybridUnifiedPipeline.Code := .expanded [
    ⟨0,.memory 0 [] false,none,[⟨0,[],.forRange (.register 0) (.send (.pure (.lit 1)))⟩]⟩]
  match Circuit.compile #[(0,4)] variableSend with
  | .ok _ => throw (IO.userError "unknown send count was treated as capacity zero")
  | .error msg => unless msg.startsWith "finite FIFO capacity is unknown" do throw (IO.userError msg)
  let twoSends : HybridUnifiedPipeline.Code := .expanded [
    ⟨0,.memory 0 [] false,some 1,[⟨0,[],.repeat 2 (.send (.pure (.lit 1)))⟩]⟩]
  let accepted ← match Circuit.compile #[(0,1),(1,1)] twoSends with
    | .ok c => pure c
    | .error msg => throw (IO.userError msg)
  unless accepted.artifact.machine.capacity 0 ≥ 2 do
    throw (IO.userError "FIFO capacity did not include the static send budget")
  let undersizedSnapshot : Artifact :=
    ⟨⟨0,#[.snapshot 1 0 1,.halt],#[]⟩,#[wordRange,wordRange],#[(0,4),(1,2)],#[(0,4)]⟩
  match Circuit.certify undersizedSnapshot with
  | .ok _ => throw (IO.userError "snapshot silently truncated the source memory")
  | .error msg => unless msg.startsWith "circuit storage layout" do throw (IO.userError msg)
  match Circuit.certify malformedQueue with
  | .ok _ => throw (IO.userError "finite circuit accepted an undeclared queue")
  | .error msg => unless msg.startsWith "circuit storage layout" do throw (IO.userError msg)
  IO.println "PASS: 7 checks covering source layout, queues, control edges, send budgets, and finite storage"
