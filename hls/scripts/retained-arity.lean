import IRComparison.Frontend.WordRetainedArguments
/-! Regression beyond the ordinary conversion search depth. This ordinary
Lean helper has 66 scalar actuals plus current State. The retained prefix is
bounded by its argument list, not by a new fixed conversion limit.
This concrete check does not replace the general generation proof. -/
open Lean Elab Command IRComparison
set_option maxHeartbeats 0
set_option maxRecDepth 65536
set_option linter.unusedVariables false
def argumentCountProbe (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  let f := fun (a0 : HybridWord.Word) (a1 : HybridWord.Word) (a2 : HybridWord.Word) (a3 : HybridWord.Word) (a4 : HybridWord.Word) (a5 : HybridWord.Word) (a6 : HybridWord.Word) (a7 : HybridWord.Word) (a8 : HybridWord.Word) (a9 : HybridWord.Word) (a10 : HybridWord.Word) (a11 : HybridWord.Word) (a12 : HybridWord.Word) (a13 : HybridWord.Word) (a14 : HybridWord.Word) (a15 : HybridWord.Word) (a16 : HybridWord.Word) (a17 : HybridWord.Word) (a18 : HybridWord.Word) (a19 : HybridWord.Word) (a20 : HybridWord.Word) (a21 : HybridWord.Word) (a22 : HybridWord.Word) (a23 : HybridWord.Word) (a24 : HybridWord.Word) (a25 : HybridWord.Word) (a26 : HybridWord.Word) (a27 : HybridWord.Word) (a28 : HybridWord.Word) (a29 : HybridWord.Word) (a30 : HybridWord.Word) (a31 : HybridWord.Word) (a32 : HybridWord.Word) (a33 : HybridWord.Word) (a34 : HybridWord.Word) (a35 : HybridWord.Word) (a36 : HybridWord.Word) (a37 : HybridWord.Word) (a38 : HybridWord.Word) (a39 : HybridWord.Word) (a40 : HybridWord.Word) (a41 : HybridWord.Word) (a42 : HybridWord.Word) (a43 : HybridWord.Word) (a44 : HybridWord.Word) (a45 : HybridWord.Word) (a46 : HybridWord.Word) (a47 : HybridWord.Word) (a48 : HybridWord.Word) (a49 : HybridWord.Word) (a50 : HybridWord.Word) (a51 : HybridWord.Word) (a52 : HybridWord.Word) (a53 : HybridWord.Word) (a54 : HybridWord.Word) (a55 : HybridWord.Word) (a56 : HybridWord.Word) (a57 : HybridWord.Word) (a58 : HybridWord.Word) (a59 : HybridWord.Word) (a60 : HybridWord.Word) (a61 : HybridWord.Word) (a62 : HybridWord.Word) (a63 : HybridWord.Word) (a64 : HybridWord.Word) (a65 : HybridWord.Word) (t : HybridWord.State) => some (t.set 0 a0)
  f (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) s

def argumentCountNested (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  let f := fun (a0 : HybridWord.Word) (a1 : HybridWord.Word) (a2 : HybridWord.Word) (a3 : HybridWord.Word) (a4 : HybridWord.Word) (a5 : HybridWord.Word) (a6 : HybridWord.Word) (a7 : HybridWord.Word) (a8 : HybridWord.Word) (a9 : HybridWord.Word) (a10 : HybridWord.Word) (a11 : HybridWord.Word) (a12 : HybridWord.Word) (a13 : HybridWord.Word) (a14 : HybridWord.Word) (a15 : HybridWord.Word) (a16 : HybridWord.Word) (a17 : HybridWord.Word) (a18 : HybridWord.Word) (a19 : HybridWord.Word) (a20 : HybridWord.Word) (a21 : HybridWord.Word) (a22 : HybridWord.Word) (a23 : HybridWord.Word) (a24 : HybridWord.Word) (a25 : HybridWord.Word) (a26 : HybridWord.Word) (a27 : HybridWord.Word) (a28 : HybridWord.Word) (a29 : HybridWord.Word) (a30 : HybridWord.Word) (a31 : HybridWord.Word) (a32 : HybridWord.Word) (a33 : HybridWord.Word) (a34 : HybridWord.Word) (a35 : HybridWord.Word) (a36 : HybridWord.Word) (a37 : HybridWord.Word) (a38 : HybridWord.Word) (a39 : HybridWord.Word) (a40 : HybridWord.Word) (a41 : HybridWord.Word) (a42 : HybridWord.Word) (a43 : HybridWord.Word) (a44 : HybridWord.Word) (a45 : HybridWord.Word) (a46 : HybridWord.Word) (a47 : HybridWord.Word) (a48 : HybridWord.Word) (a49 : HybridWord.Word) (a50 : HybridWord.Word) (a51 : HybridWord.Word) (a52 : HybridWord.Word) (a53 : HybridWord.Word) (a54 : HybridWord.Word) (a55 : HybridWord.Word) (a56 : HybridWord.Word) (a57 : HybridWord.Word) (a58 : HybridWord.Word) (a59 : HybridWord.Word) (a60 : HybridWord.Word) (a61 : HybridWord.Word) (a62 : HybridWord.Word) (a63 : HybridWord.Word) (a64 : HybridWord.Word) (a65 : HybridWord.Word) (t : HybridWord.State) => some (t.set 0 a0)
  if s.regs 1 != 0 then
    f (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) (s.regs 0) s
  else
    some s

run_cmd do
  let native ← getEnv
  let some result := WordFrontend.StructuralBody.compileRetained native ``argumentCountProbe
    | throwError "66 retained scalar arguments failed at the ordinary entry"
  let _ := result.correct
  logInfo "PASS 66 scalar actuals + current State → compileRetained (typed certificate for original named definition)"

run_cmd do
  let native ← getEnv
  let some result := WordFrontend.StructuralBody.compileRetained native ``argumentCountNested
    | throwError "66 retained scalar arguments inside a branch failed"
  let _ := result.correct
  logInfo "PASS 66 scalar actuals inside a branch → compileRetained (retained-prefix type used by enclosing certificate)"
