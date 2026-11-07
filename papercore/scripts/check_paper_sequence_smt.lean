import PaperCore.IndexSequenceSMT

open PaperCore (SMT)
open PaperCore.IndexSequence

/-- Integration check of actual generated SMT-LIB and parsed SAT models.
    This exercises the proved sequence-equality encoder, not the full HLS pipeline. -/
def runCase (name : String) (first step : Int) (count : Nat) (extra : List SMT) : IO Unit := do
  let formula := SMT.conj (equality (.num first) (.num step) (.num count)
    (.param "first") (.param "step") (.param "count") :: extra)
  let request := SMT.script formula
  let base := "artifacts/paper-sequence-smt/" ++ name
  IO.FS.writeFile (base ++ ".smt2") request
  let response ← IO.Process.output {cmd := "z3", args := #[base ++ ".smt2"]}
  IO.FS.writeFile (base ++ ".stdout") response.stdout
  IO.FS.writeFile (base ++ ".stderr") response.stderr
  if response.exitCode != 0 then throw (IO.userError ("z3 failed: " ++ name))
  let some bindings := PaperCore.SMTConnection.acceptResponse formula request response.stdout
    | throw (IO.userError ("response rejected: " ++ name))
  let some f := bindings.lookup "first" | throw (IO.userError "missing first")
  let some s := bindings.lookup "step" | throw (IO.userError "missing step")
  let some n := bindings.lookup "count" | throw (IO.userError "missing count")
  if n < 0 || entries first step count != entries f s n.toNat then
    throw (IO.userError ("decoded sequence differs: " ++ name))
  IO.FS.writeFile (base ++ ".model.txt") (reprStr bindings ++ "\n")
  IO.println (name ++ ": accepted SAT model " ++ reprStr bindings)

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/paper-sequence-smt"
  runCase "descending" 6 (-2) 4 []
  runCase "empty-noncanonical" 99 7 0
    [SMT.neg (SMT.eq (.param "first") (.num 99)), SMT.neg (SMT.eq (.param "step") (.num 7))]
  runCase "singleton-noncanonical" 6 4 1 [SMT.neg (SMT.eq (.param "step") (.num 4))]
