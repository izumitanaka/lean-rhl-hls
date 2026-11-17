import IRComparison.Frontend.LeanWordCommand

namespace IRComparison.ScalarEnvironmentExamples
open HybridWord Lean Elab Command

def shared (i x y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 (let a := x + 1; let b := a * a; b + a + y + i))

def shadow (i x y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 (let a := x + y; let b := a; let a := i + 1; b - a))

def selected (i x y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 (let a := x + 1; if a != 0 then -(a / (y+1)) else i))

/-- Two convertible lexical sources must keep distinct exact proof types
when the surrounding expression reuses both cached values. -/
def retypedPair (i x y : Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 (let a := x + i; let b := (let c := a; c); a + b + y))

-- Require the new parser itself to succeed: the compatibility fallback must
-- not hide a failed lexical traversal in these regression cases.
run_cmd do
  let native ← getEnv
  for name in [``shared,``shadow,``selected,``retypedPair] do
    let some lib := WordFrontend.load native name | throwError "loading failed: {name}"
    let .lam _ _ (.lam _ _ (.lam _ _ (.lam _ _ original _) _) _) _ :=
      LeanSourceEntry.strip lib.source.declaration.value | throwError "wrong source shape"
    let some stateValue := original.getAppArgs.toList.getLast? | throwError "missing return"
    let some scalarValue := stateValue.getAppArgs.toList.getLast? | throwError "missing scalar"
    let some _ := WordFrontend.ScalarEnvironment.parse lib.model lib.conversion lib.exposure
      WordFrontend.context WordFrontend.parameters scalarValue
      | throwError "lexical parser failed without legacy fallback: {name}"

hls_word shared as generatedShared
hls_word shadow as generatedShadow
hls_word selected as generatedSelected
hls_word retypedPair as generatedRetypedPair

example (i x y : Word) (s : HybridWord.State) :
    generatedShared.wordBody.eval i x y s [] = shared i x y s :=
  generatedShared.wordBody_correct i x y s

example (i x y : Word) (s : HybridWord.State) :
    generatedShadow.wordBody.eval i x y s [] = shadow i x y s :=
  generatedShadow.wordBody_correct i x y s

example (i x y : Word) (s : HybridWord.State) :
    generatedRetypedPair.wordBody.eval i x y s [] = retypedPair i x y s :=
  generatedRetypedPair.wordBody_correct i x y s

end IRComparison.ScalarEnvironmentExamples
