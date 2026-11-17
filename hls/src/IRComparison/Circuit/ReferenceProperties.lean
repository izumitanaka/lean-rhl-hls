import IRComparison.Circuit.PolicyProperties
import IRComparison.Frontend.FixedLowering
import IRComparison.Circuit.AllocationLayout

namespace IRComparison
open HybridIR

namespace HybridSymbolicProducer
variable {source : MemoryCmd}

theorem BodyShape.arrays (shape : BodyShape source target)
    (sourceClosed : source.target.ArraysWithin allowed) : target.ArraysWithin allowed := by
  induction shape with
  | memory => exact sourceClosed
  | skip => trivial
  | assign | store => exact sourceClosed
  | send => exact sourceClosed.2.2
  | letValue _ ih => exact ⟨sourceClosed.1,ih sourceClosed.2⟩
  | seq _ _ ia ib => exact ⟨ia sourceClosed.1,ib sourceClosed.2⟩
  | branch _ _ ia ib => exact ⟨sourceClosed.1,ia sourceClosed.2.1,ib sourceClosed.2.2⟩

end HybridSymbolicProducer

namespace HybridSymbolicLoop
variable {source : MemoryCmd}

theorem Selected.arrays (p : Selected size array source start stride count)
    (sourceClosed : source.target.ArraysWithin allowed) : p.code.body.target.ArraysWithin allowed := by
  cases p with
  | optimized p => exact p.body.arrays _ sourceClosed
  | original => exact sourceClosed

end HybridSymbolicLoop

namespace HybridEffects

theorem writes_declared (c : MemoryCmd) (h : c.target.ArraysWithin allowed) :
    ∀ a ∈ writes c, allowed a := by
  induction c <;> simp_all [writes,MemoryCmd.target,Cmd.ArraysWithin,or_imp,forall_and]

end HybridEffects

namespace Circuit

/-- Connect the syntax-level reference property to the real layout scanner. -/
theorem readArrays_closed (e : ReadCode) :
    e.ArraysWithin allowed ↔ ∀ a ∈ readArrays e, allowed a := by
  induction e <;> simp_all [ReadCode.ArraysWithin,readArrays,or_imp,forall_and]

theorem commandArrays_closed (c : Cmd) :
    c.ArraysWithin allowed ↔ ∀ a ∈ allCommandArrays c, allowed a := by
  induction c <;> simp_all [Cmd.ArraysWithin,allCommandArrays,readArrays_closed,or_imp,forall_and,← and_assoc]

open HybridSymbolicGlobal

private theorem selected_write (xs policy : List Nat) (output : Nat)
    (h : xs.eraseDups.filter (fun a => decide (a ∈ policy)) = [output]) : output ∈ xs := by
  have hm : output ∈ xs.eraseDups.filter (fun a => decide (a ∈ policy)) := by rw [h]; simp
  exact List.mem_eraseDups.mp (List.mem_filter.mp hm).1

/-- Selection introduces no new public array names. Producer output names are
chosen from actual stores; private snapshots are allocated in the next pass. -/
theorem compileStep_references (h : compileStep policy sizes hidden env p = some step)
    (input : allowed p.array) (closed : p.code.body.target.ArraysWithin allowed) :
    allowed (symbolicInput step.instruction) ∧
      (∀ a ∈ (symbolicOutput step.instruction).toList, allowed a) ∧
      step.instruction.body.ArraysWithin allowed := by
  refine ⟨?_,?_,step.bodyShape.arrays closed⟩
  all_goals
    simp only [compileStep,compileStepWith,fromOption,OptionT.bind,OptionT.run,
      OptionT.mk,Bind.bind,pure] at h
    repeat' first | contradiction | split at h
    all_goals simp only [OptionT.pure,OptionT.mk,pure] at h
    all_goals cases Option.some.inj h
    all_goals simp only [symbolicInput,symbolicOutput,keepMemory,receive,sendMemory,sendChannel,sendStep,
      Option.toList,List.mem_singleton,List.not_mem_nil,forall_eq]
    all_goals first
      | exact input
      | simp
      | exact HybridEffects.writes_declared _ closed _ (selected_write _ policy _ (by assumption))

theorem compilePolicy_references (h : compilePolicy outputs sizes policy hidden env ps = some plan)
    (sourceClosed : ∀ p ∈ ps, allowed p.array ∧ p.code.body.target.ArraysWithin allowed) :
    ∀ a ∈ sourceArrays (.symbolic plan.code), allowed a := by
  induction ps generalizing hidden env with
  | nil =>
    simp only [compilePolicy] at h
    split at h
    · split at h
      · cases h; simp [Plan.code,sourceArrays]
      · cases h
    · cases h
  | cons p ps ih =>
    cases first : compileStep policy sizes hidden env p with
    | none => simp [compilePolicy,first] at h
    | some s =>
      cases rest : compilePolicy outputs sizes policy s.nextHidden s.nextEnv ps with
      | none => simp [compilePolicy,first,rest] at h
      | some tail =>
        simp only [compilePolicy,first,rest,bind,Option.bind,pure,Option.some.injEq] at h
        subst plan
        have head := compileStep_references first (sourceClosed p (by simp)).1 (sourceClosed p (by simp)).2
        have body := (commandArrays_closed s.instruction.body).mp head.2.2
        have tailClosed := ih rest (fun p hp => sourceClosed p (by simp [hp]))
        intro a member
        simp only [sourceArrays,Plan.code,List.flatMap_cons,List.mem_append,List.mem_cons] at member
        rcases member with ((rfl | ho) | hb) | ht
        · exact head.1
        · exact head.2.1 a ho
        · exact body a (by simpa only [symbolicBody_body] using hb)
        · exact tailClosed a ht

theorem compile_references (h : HybridSymbolicGlobal.compile outputs sizes ps = some program)
    (sourceClosed : ∀ p ∈ ps, allowed p.array ∧ p.code.body.target.ArraysWithin allowed) :
    ∀ a ∈ sourceArrays (.symbolic program.plan.code), allowed a := by
  exact compilePolicy_references (compile_selected h) sourceClosed

/-- Source declaration closure survives both buffer insertion and FIFO policy
search. The actual layout check therefore succeeds, not just its semantic VC. -/
theorem compile_layout (outputs : List Nat) (sizes : Nat → Nat) (ks : List HybridWord.Kernel)
    (layout : Array (Nat × Nat)) (unique : (layout.toList.map Prod.fst).Nodup)
    (sourceClosed : ∀ k ∈ ks, (∃ n, (k.array,n) ∈ layout.toList) ∧
      k.body.lower.target.ArraysWithin (fun a => ∃ n, (a,n) ∈ layout.toList)) :
    ∃ p, HybridWord.compileProgram outputs sizes ks = some p ∧
      checkLayout layout (HybridUnifiedPipeline.lower p) = .ok () := by
  obtain ⟨p,compiled⟩ := symbolic_compile_total outputs sizes
    (HybridUnifiedPipeline.compactStages (ks.map HybridWord.Kernel.lower))
  have closed := compile_references compiled (allowed:=fun a => ∃ n, (a,n) ∈ layout.toList) (by
    intro stage member
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp member
    obtain ⟨wordKernel,hw,rfl⟩ := List.mem_map.mp hk
    exact ⟨(sourceClosed wordKernel hw).1,(HybridSymbolicLoop.select _ _ _ _ _ _).arrays (sourceClosed wordKernel hw).2⟩)
  have covered : layoutCovers layout (.symbolic p.plan.code) = true := by
    apply List.all_eq_true.mpr
    intro a member
    obtain ⟨n,hn⟩ := closed a member
    rw [← Array.any_toList,List.any_eq_true]
    exact ⟨(a,n),hn,by simp⟩
  refine ⟨.symbolic p,?_,?_⟩
  · simp [HybridWord.compileProgram,HybridUnifiedPipeline.compile,compiled]
  · have uniq := Allocation.unique_length unique
    simp [HybridUnifiedPipeline.lower,checkLayout,uniq,covered,pure,Except.pure,bind,Except.bind]

end Circuit
end IRComparison
