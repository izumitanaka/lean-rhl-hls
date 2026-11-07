import PaperCore.HybridBody
import PaperCore.LoopAnalysis
import PaperCore.LoopRule

namespace PaperCore.Hybrid.Loop
open AccessAnalysis

/-- A logical queue invariant indexed by the current counter. -/
def invariant (counter : Var) (shape : Int → IndexMap → Prop) : Assertion :=
  fun regs _ indices => ∃ k, regs.lookup counter = some k ∧ shape k indices

/-- The cursor obligation is over every loop-head state admitted by the
    invariant. In particular the next counter is the analyzed *post-body*
    counter, not an assumption that the body leaves it unchanged. -/
def Obligation (policy : Array → Bool) (summary : Summary) (counterAfter : Affine)
    (shape : Int → IndexMap → Prop) (stop step : Int) : Prop :=
  ∀ k indices, shape k indices → k ≠ stop →
    ∃ afterIndices,
      DirectBody.consume indices ((summary.accesses.filter (fun e => policy e.array)).map (SymbolicAccess.eval k)) = some afterIndices ∧
      shape (counterAfter.eval k + step) afterIndices

theorem body_correct_ordinary
    (ops : ArithmeticSound classify meaning)
    (analyzed : analyze classify (Env.initial counter) sourceBody = .ok summary)
    (lowered : Body.lower policy sourceBody = .ok targetBody)
    (typed : BufferView.Typed ordinary sourceBody) (counterTyped : ordinary counter)
    (counterKnown : summary.env counter = some counterAfter)
    (tracked : ∀ event ∈ summary.accesses, arrays event.array ↔ policy event.array = true)
    (valid : Obligation policy summary counterAfter shape stop step) :
    Translation meaning ordinary arrays (loopGuard (invariant counter shape) counter stop)
      sourceBody targetBody (advancePre (invariant counter shape) counter step) := by
  intro source target indices related
  obtain ⟨corr,⟨k,value,atHead⟩,j,jValue,nonzero⟩ := related
  have same : k = j := Option.some.inj (value.symm.trans jValue)
  subst j
  have sourceValue := (corr.registers counter counterTyped).trans value
  have envMatches := LoopAnalysis.Env.initial_matches sourceValue
  obtain ⟨afterIndices,cursor,shapeAfter⟩ := valid k indices atHead nonzero
  constructor
  · intro source' run
    obtain ⟨target',targetRun,after⟩ := Body.forward_ordinary ops sourceBody analyzed lowered typed
      envMatches tracked cursor corr run
    have counterValue := (analyze_sound ops sourceBody analyzed envMatches run).1 counter counterAfter counterKnown
    refine ⟨target',afterIndices,targetRun,after,?_⟩
    intro next nextValue
    have nextSame : next = counterAfter.eval k := Option.some.inj
      (nextValue.symm.trans ((after.registers counter counterTyped).symm.trans counterValue))
    subst next
    exact ⟨_,lookup_put_same ..,shapeAfter⟩
  · intro target' run
    obtain ⟨source',sourceRun,after⟩ := Body.backward_ordinary ops sourceBody analyzed lowered typed
      envMatches tracked cursor corr run
    have counterValue := (analyze_sound ops sourceBody analyzed envMatches sourceRun).1 counter counterAfter counterKnown
    refine ⟨source',afterIndices,sourceRun,after,?_⟩
    intro next nextValue
    have nextSame : next = counterAfter.eval k := Option.some.inj
      (nextValue.symm.trans ((after.registers counter counterTyped).symm.trans counterValue))
    subst next
    exact ⟨_,lookup_put_same ..,shapeAfter⟩

theorem correct_ordinary
    (ops : ArithmeticSound classify meaning)
    (analyzed : analyze classify (Env.initial counter) sourceBody = .ok summary)
    (lowered : Body.lower policy sourceBody = .ok targetBody)
    (typed : BufferView.Typed ordinary sourceBody) (counterTyped : ordinary counter)
    (counterKnown : summary.env counter = some counterAfter)
    (tracked : ∀ event ∈ summary.accesses, arrays event.array ↔ policy event.array = true)
    (valid : Obligation policy summary counterAfter shape stop step) (startTyped : start.ordinary ordinary) :
    Translation meaning ordinary arrays (assignPre meaning counter start (invariant counter shape))
      (.loop counter start stop step sourceBody) (.loop counter start stop step targetBody)
      (loopPost (invariant counter shape) counter stop) := by
  apply Translation.loop meaning
  · exact startTyped
  · exact counterTyped
  · exact body_correct_ordinary ops analyzed lowered typed counterTyped counterKnown tracked valid


#print axioms correct_ordinary
end PaperCore.Hybrid.Loop
