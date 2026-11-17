import IRComparison.Circuit.CommunicationCheck
import IRComparison.Circuit.ProducerProperties

namespace IRComparison.Circuit
open HybridSymbolicGlobal

/-- Local consequence of selecting one representation per array. -/
def RespectsPolicy (policy : List Nat) : Instruction → Prop
  | .memory input _ => input ∉ policy
  | .producer input output _ => input ∉ policy ∧ output ∈ policy
  | .receiver input _ => input ∈ policy
  | .duplex input output _ => input ∈ policy ∧ output ∈ policy ∧ input ≠ output

private theorem selected_output (xs policy : List Nat) (output : Nat)
    (h : xs.eraseDups.filter (fun a => decide (a ∈ policy)) = [output]) :
    output ∈ xs ∧ output ∈ policy := by
  have hm : output ∈ xs.eraseDups.filter (fun a => decide (a ∈ policy)) := by rw [h]; simp
  simpa only [List.mem_filter,List.mem_eraseDups,decide_eq_true_eq] using hm

theorem compileStep_policy (h : compileStep policy sizes hidden env p = some step) :
    RespectsPolicy policy step.instruction := by
  simp only [compileStep,compileStepWith,fromOption,OptionT.bind,OptionT.run,
    OptionT.mk,Bind.bind,pure] at h
  repeat' first
    | contradiction
    | split at h
  all_goals simp only [OptionT.pure,OptionT.mk,pure] at h
  all_goals cases Option.some.inj h
  all_goals simp only [RespectsPolicy,keepMemory,receive,sendMemory,sendChannel,sendStep]
  all_goals try assumption
  · refine ⟨by assumption,(selected_output (HybridEffects.writes p.code.body) policy _ (by assumption)).2,?_⟩
    intro same
    subst_vars
    have written : p.array ∈ HybridEffects.writes p.code.body :=
      (selected_output (HybridEffects.writes p.code.body) policy p.array (by assumption)).1
    grind
  · exact ⟨by assumption,(selected_output (HybridEffects.writes p.code.body) policy _ (by assumption)).2⟩

theorem compilePolicy_policy (h : compilePolicy outputs sizes policy hidden env ps = some plan) :
    ∀ c ∈ plan.code, RespectsPolicy policy c := by
  induction ps generalizing hidden env with
  | nil =>
    simp only [compilePolicy] at h
    split at h
    · split at h
      · cases h; simp [Plan.code]
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
        intro c member
        rcases List.mem_cons.mp member with rfl | member
        · exact compileStep_policy first
        · exact ih rest c member

theorem compile_policy (h : HybridSymbolicGlobal.compile outputs sizes ps = some program) :
    ∀ c ∈ program.plan.code, RespectsPolicy program.policy c := by
  exact compilePolicy_policy (compile_selected h)

theorem respects_channels (cs : List Instruction)
    (valid : ∀ c ∈ cs, RespectsPolicy policy c) :
    ∀ a ∈ symbolicChannels cs, a ∈ policy := by
  intro a member
  obtain ⟨c,hc,member⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp member)
  have h := valid c hc
  cases c <;> simp_all [RespectsPolicy,symbolicOutput,symbolicMode] <;> grind

theorem respects_communication (cs : List Instruction)
    (valid : ∀ c ∈ cs, RespectsPolicy policy c) : checkCommunication (.symbolic cs) = .ok () := by
  have all : cs.all (fun c => decide (symbolicInstructionChannels (symbolicChannels cs) c)) = true := by
    apply List.all_eq_true.mpr
    intro c member
    apply decide_eq_true
    have h := valid c member
    have channels := respects_channels cs valid
    have inputMember {a : Nat} (h : symbolicMode c = .channel a) : a ∈ symbolicChannels cs := by
      apply List.mem_eraseDups.mpr
      apply List.mem_flatMap.mpr
      exact ⟨c,member,by simp [h]⟩
    cases c with
    | memory a code | producer a b code =>
      simp only [RespectsPolicy] at h
      simp only [symbolicInstructionChannels,symbolicMode,symbolicInput,true_and]
      intro hc
      first | exact h (channels a hc) | exact h.1 (channels a hc)
    | receiver a code =>
      exact ⟨rfl,inputMember rfl,by simp [symbolicOutput]⟩
    | duplex a b code =>
      exact ⟨rfl,inputMember rfl,by simpa [symbolicOutput] using Ne.symm h.2.2⟩
  simp [checkCommunication,all]

/-- Representation consistency follows from the actual whole-array selector;
it is not an additional source-language restriction or a checker hypothesis. -/
theorem compile_communication (outputs : List Nat) (sizes : Nat → Nat)
    (ks : List HybridIR.Kernel) :
    ∃ p, HybridUnifiedPipeline.compile outputs sizes ks = some p ∧
      checkCommunication (HybridUnifiedPipeline.lower p) = .ok () := by
  unfold HybridUnifiedPipeline.compile
  split
  · rename_i p hp
    exact ⟨.symbolic p,rfl,respects_communication _ (compile_policy hp)⟩
  · exact ⟨.regions,rfl,rfl⟩

theorem compile_memory_checks (outputs : List Nat) (sizes : Nat → Nat)
    (ks : List HybridIR.Kernel) :
    ∃ p, HybridUnifiedPipeline.compile outputs sizes ks = some p ∧
      checkSendBudgets (HybridUnifiedPipeline.lower p) = .ok () ∧
      checkCommunication (HybridUnifiedPipeline.lower p) = .ok () := by
  obtain ⟨p,hp,budget⟩ := compile_sendBudgets outputs sizes ks
  obtain ⟨q,hq,communication⟩ := compile_communication outputs sizes ks
  have same := Option.some.inj (hp.symm.trans hq)
  subst q
  exact ⟨p,hp,budget,communication⟩

theorem compilePolicy_empty_total (outputs : List Nat) (sizes : Nat → Nat)
    (ps : List HybridCompactStage.Stage) :
    ∃ p, compilePolicy outputs sizes [] [] [] ps = some p := by
  induction ps with
  | nil => exact ⟨.nil (by simp),by simp [compilePolicy]⟩
  | cons p ps ih =>
    obtain ⟨tail,ht⟩ := ih
    simp only [compilePolicy]
    have first : ∃ s, compileStep [] sizes [] [] p = some s ∧ s.nextHidden = [] ∧ s.nextEnv = [] := by
      simp only [compileStep,compileStepWith,fromOption,OptionT.bind,OptionT.run,OptionT.mk,Bind.bind,pure]
      simp [HybridCompactStage.check,OptionT.pure,OptionT.mk,keepMemory,remove]
      have emptyFilter : ((HybridEffects.writes p.code.body).eraseDups.filter
          (fun x => decide (x ∈ ([] : List Nat)))) = [] := by simp
      split
      · exact ⟨_,rfl,rfl,rfl⟩
      · rename_i output selected
        have impossible : ([] : List Nat) = [output] := emptyFilter.symm.trans selected
        cases impossible
      · simp_all
    obtain ⟨s,hs,hidden,env⟩ := first
    rcases s with ⟨instruction,bodyShape,nextHidden,nextEnv,correct⟩
    dsimp only at hidden env
    subst nextHidden nextEnv
    rw [hs]
    simp only [bind,Option.bind,ht]
    exact ⟨_,rfl⟩

/-- Optional greedy improvements cannot lose the successful memory baseline. -/
theorem symbolic_compile_total (outputs : List Nat) (sizes : Nat → Nat)
    (ps : List HybridCompactStage.Stage) :
    ∃ p, HybridSymbolicGlobal.compile outputs sizes ps = some p := by
  obtain ⟨p,hp⟩ := compilePolicy_empty_total outputs sizes ps
  exact ⟨improve ⟨[],p⟩ (candidates outputs ps),by simp [HybridSymbolicGlobal.compile,hp]⟩

end IRComparison.Circuit
