import IRComparison.Circuit.BudgetCheck
import IRComparison.Circuit.StaticCapacity
import IRComparison.Hybrid.WordTyping
import IRComparison.Hybrid.HybridWordGlobal

/-! Structural consequences of the existing producer rules. The rules record
store-to-send replacement, not an assumption that backend checks succeed. -/
namespace IRComparison

namespace HybridSymbolicProducer
open HybridIR

variable {source : MemoryCmd} {target : Cmd} {locals : WordBindings}

theorem BodyShape.word (shape : BodyShape source target)
    (typed : WordCommand locals source.target) : WordCommand locals target := by
  induction shape generalizing locals with
  | memory => exact typed
  | skip => exact .skip
  | assign => cases typed with | assign h => exact .assign h
  | store => cases typed with | store h => exact .store h
  | send => cases typed with | store h => exact .send h
  | letValue _ ih => cases typed with | letValue h b => exact .letValue h (ih b)
  | seq _ _ ia ib => cases typed with | seq a b => exact .seq (ia a) (ib b)
  | branch _ _ ia ib => cases typed with | branch a b => exact .branch (ia a) (ib b)

theorem BodyShape.sendBound (shape : BodyShape source target) :
    ∃ bound, Circuit.sendBound target = some bound := by
  induction shape with
  | memory => exact ⟨0,Circuit.sendBound_memory _⟩
  | skip | assign | store => exact ⟨0,rfl⟩
  | send => exact ⟨1,rfl⟩
  | letValue _ ih => exact ih
  | seq _ _ ia ib =>
    obtain ⟨a,ha⟩ := ia
    obtain ⟨b,hb⟩ := ib
    exact ⟨a+b,by simp [Circuit.sendBound,ha,hb]⟩
  | branch _ _ ia ib =>
    obtain ⟨a,ha⟩ := ia
    obtain ⟨b,hb⟩ := ib
    exact ⟨max a b,by simp [Circuit.sendBound,ha,hb]⟩

theorem Compiled.word (p : Compiled array size source)
    (typed : WordCommand locals source.target) : WordCommand locals p.code :=
  p.shape.word typed

theorem Compiled.sendBound (p : Compiled array size source) :
    ∃ bound, Circuit.sendBound p.code = some bound := p.shape.sendBound

end HybridSymbolicProducer

namespace HybridSymbolicLoop
open HybridIR
variable {source : MemoryCmd}

theorem Selected.word (p : Selected size array source start stride count)
    (typed : WordCommand (fun _ => True) source.target) :
    WordCommand (fun _ => True) p.code.body.target := by
  cases p with
  | optimized p =>
    have h := p.body.word _ typed
    simpa [Selected.code,Plan.code,bufferWords] using h
  | original => exact typed

end HybridSymbolicLoop

namespace HybridSymbolicGlobal
open HybridIR

theorem Plan.word (p : Plan outputs sizes hidden env ps)
    (typed : ∀ stage ∈ ps, WordCommand (fun _ => True) stage.code.body.target) :
    ∀ c ∈ p.code, WordCommand (fun _ => True) c.body := by
  induction p with
  | nil => simp [Plan.code]
  | cons first tail ih =>
    intro c member
    rcases List.mem_cons.mp member with rfl | member
    · exact first.bodyShape.word (typed _ (by simp))
    · exact ih (fun stage hm => typed stage (by simp [hm])) c member

end HybridSymbolicGlobal

namespace Circuit

theorem word_compactStages (ks : List HybridWord.Kernel) :
    ∀ stage ∈ HybridUnifiedPipeline.compactStages (ks.map HybridWord.Kernel.lower),
      HybridIR.WordCommand (fun _ => True) stage.code.body.target := by
  intro stage member
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp member
  obtain ⟨wordKernel,_,rfl⟩ := List.mem_map.mp hk
  exact (HybridSymbolicLoop.select _ _ _ _ _ _).word wordKernel.body.lower_word

theorem symbolicBody_body (c : HybridSymbolicGlobal.Instruction) :
    (symbolicBody c).body = c.body := by cases c <;> rfl

/-- This covers all instructions certified by the existing memory/FIFO rules,
including results of SMT-assisted routing. It does not assume a backend check. -/
theorem symbolic_step_sendBound (s : HybridSymbolicGlobal.Step sizes hidden env p) :
    ∃ bound, sendBound (symbolicBody s.instruction).body = some bound := by
  rw [symbolicBody_body]
  exact s.bodyShape.sendBound

theorem symbolic_plan_sendBounds (p : HybridSymbolicGlobal.Plan outputs sizes hidden env ps) :
    hasSendBounds (.symbolic p.code) = true := by
  induction p with
  | nil => rfl
  | cons first tail ih =>
    obtain ⟨bound,known⟩ := symbolic_step_sendBound first
    simpa [HybridSymbolicGlobal.Plan.code,hasSendBounds,known] using ih

/-- The ordinary memory optimizer always returns a plan whose FIFO capacities
are computable. Failure to find an optional FIFO policy retains memory. -/
theorem compile_sendBudgets (outputs : List Nat) (sizes : Nat → Nat)
    (ks : List HybridIR.Kernel) :
    ∃ p, HybridUnifiedPipeline.compile outputs sizes ks = some p ∧
      checkSendBudgets (HybridUnifiedPipeline.lower p) = .ok () := by
  unfold HybridUnifiedPipeline.compile
  split
  · rename_i p hp
    refine ⟨.symbolic p,rfl,?_⟩
    have known := symbolic_plan_sendBounds p.plan
    simp [HybridUnifiedPipeline.lower,checkSendBudgets,known]
  · exact ⟨.regions,rfl,rfl⟩

end Circuit
end IRComparison
