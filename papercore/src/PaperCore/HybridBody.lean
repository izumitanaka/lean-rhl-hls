import PaperCore.HybridRules

namespace PaperCore.Hybrid.Body
open AccessAnalysis DirectBody

/-- Lower the actual straight-line input. Scalar code is preserved verbatim.
    Control nodes are reported, never replaced by a sample program. -/
def lower (policy : Array → Bool) : Source Op → Except String (MixedTarget.Code Op)
  | .assign x e => .ok (.assign x e)
  | .action (.read x a e) => .ok (.action (if policy a then .stream (.read x a) else .memory (.read x a e)))
  | .action (.write a e x) => .ok (.action (if policy a then .stream (.write a x) else .memory (.write a e x)))
  | .seq a b =>
    match lower policy a,lower policy b with
    | .ok ta,.ok tb => .ok (.seq ta tb)
    | .error err,_ | _,.error err => .error err
  | .branch x a b =>
    match lower policy a,lower policy b with
    | .ok ta,.ok tb => .ok (.branch x ta tb)
    | .error err,_ | _,.error err => .error err
  | .loop .. => .error "direct-body-loop-not-yet-supported"
  | .kernel .. => .error "direct-body-kernel-not-yet-supported"

theorem forward_ordinary {Op : Type} {meaning : Op → Int → Int → Int} {classify : Op → Option Arithmetic}
    {targetCode : MixedTarget.Code Op}
    (ops : ArithmeticSound classify meaning) (code : Source Op)
    (analyzed : analyze classify env code = .ok summary)
    (lowered : lower policy code = .ok targetCode)
    (typed : BufferView.Typed ordinary code)
    (agrees : env.Matches left.regs counter)
    (tracked : ∀ event ∈ summary.accesses, arrays event.array ↔ policy event.array = true)
    (cursors : consume indices ((summary.accesses.filter (fun e => policy e.array)).map (SymbolicAccess.eval counter)) = some finalIndices)
    (corr : Corresponds ordinary arrays left right indices)
    (run : SourceExec meaning code left left') :
    ∃ right', MixedTarget.Execution meaning targetCode right right' ∧ Corresponds ordinary arrays left' right' finalIndices := by
  induction code generalizing env summary targetCode left left' right indices finalIndices with
  | assign x e =>
    simp [analyze] at analyzed; subst summary
    simp [lower] at lowered; subst targetCode
    simp [consume] at cursors; subst finalIndices
    cases run with
    | assign value =>
      exact ⟨right.setReg x _,.assign ((corr.eval_eq meaning e typed.2).symm.trans value),corr.setReg x _⟩
  | action cmd =>
    cases cmd with
    | write a e x =>
      cases hi : infer classify env e with
      | none => simp [analyze,hi] at analyzed
      | some affine =>
        simp [analyze,hi] at analyzed; subst summary
        by_cases chosen : policy a = true
        · simp [lower,chosen] at lowered; subst targetCode
          simp [chosen] at cursors
          obtain ⟨values,witness,fresh,rfl⟩ := consume_write cursors
          have arrayTracked : arrays a := (tracked ⟨.write,a,affine⟩ (by simp)).2 chosen
          have index := infer_sound ops agrees hi
          cases run with
          | action step =>
            cases step with
            | write actual value =>
              have same := Option.some.inj (actual.symm.trans index)
              subst_vars
              obtain ⟨out,written,after⟩ := corr.push arrayTracked witness fresh typed.1 value
              exact ⟨out,.action written,after⟩
        · simp [lower,chosen] at lowered; subst targetCode
          simp [chosen,consume] at cursors; subst finalIndices
          exact retained_write_forward corr (fun h => chosen ((tracked ⟨.write,a,affine⟩ (by simp)).1 h)) typed run
    | read x a e =>
      cases hi : infer classify env e with
      | none => simp [analyze,hi] at analyzed
      | some affine =>
        simp [analyze,hi] at analyzed; subst summary
        by_cases chosen : policy a = true
        · simp [lower,chosen] at lowered; subst targetCode
          simp [chosen] at cursors
          obtain ⟨tail,head,rfl⟩ := consume_read cursors
          have arrayTracked : arrays a := (tracked ⟨.read,a,affine⟩ (by simp)).2 chosen
          obtain ⟨value,rest,cell,queue,after⟩ := corr.pop arrayTracked head x
          have index := infer_sound ops agrees hi
          have sourceStep : SourceExec meaning (.action (.read x a e)) left (left.setReg x value) :=
            .action (.read index cell)
          have same := memoryAction_unique run sourceStep
          subst left'
          exact ⟨⟨put right.regs x value,(right.memory.1,put right.memory.2 a rest)⟩,
            .action (stream_step_iff.mpr ⟨.read queue,rfl⟩),after⟩
        · simp [lower,chosen] at lowered; subst targetCode
          simp [chosen,consume] at cursors; subst finalIndices
          exact retained_read_forward corr (fun h => chosen ((tracked ⟨.read,a,affine⟩ (by simp)).1 h)) typed.2 run
  | seq a b ia ib =>
    cases ha : analyze classify env a with
    | error err => simp [analyze,ha] at analyzed
    | ok first =>
      cases hb : analyze classify first.env b with
      | error err => simp [analyze,ha,hb] at analyzed
      | ok second =>
        simp [analyze,ha,hb] at analyzed; subst summary
        cases la : lower policy a with
        | error err => simp [lower,la] at lowered
        | ok ta =>
          cases lb : lower policy b with
          | error err => simp [lower,la,lb] at lowered
          | ok tb =>
            simp [lower,la,lb] at lowered; subst targetCode
            simp only [List.filter_append,List.map_append,consume_append] at cursors
            cases ca : consume indices ((first.accesses.filter (fun e => policy e.array)).map (SymbolicAccess.eval counter)) with
            | none => simp [ca] at cursors
            | some midIndices =>
              simp [ca] at cursors
              cases run with
              | seq leftRun rightRun =>
                obtain ⟨midRight,rt,midCorr⟩ := ia ha la typed.1 agrees
                  (fun e he => tracked e (List.mem_append_left _ he)) ca corr leftRun
                have midEnv := (analyze_sound ops a ha agrees leftRun).1
                obtain ⟨endRight,rr,endCorr⟩ := ib hb lb typed.2 midEnv
                  (fun e he => tracked e (List.mem_append_right _ he)) cursors midCorr rightRun
                exact ⟨endRight,.seq rt rr,endCorr⟩
  | branch c a b ia ib =>
    cases ha : analyze classify env a with
    | error reason => simp [analyze,ha] at analyzed
    | ok first =>
      cases hb : analyze classify env b with
      | error reason => simp [analyze,ha,hb] at analyzed
      | ok second =>
        by_cases same : first.accesses = second.accesses
        · simp only [analyze,ha,hb,if_pos same,Except.ok.injEq] at analyzed
          subst summary
          cases la : lower policy a with
          | error reason => simp [lower,la] at lowered
          | ok ta =>
            cases lb : lower policy b with
            | error reason => simp [lower,la,lb] at lowered
            | ok tb =>
              simp [lower,la,lb] at lowered; subst targetCode
              cases run with
              | ifTrue condition nonzero chosen =>
                obtain ⟨out,executed,after⟩ := ia ha la typed.2.1 agrees tracked cursors corr chosen
                exact ⟨out,.ifTrue ((corr.registers c typed.1).symm.trans condition) nonzero executed,after⟩
              | ifFalse condition chosen =>
                obtain ⟨out,executed,after⟩ := ib hb lb typed.2.2 agrees
                  (by simpa only [same] using tracked) (by simpa only [same] using cursors) corr chosen
                exact ⟨out,.ifFalse ((corr.registers c typed.1).symm.trans condition) executed,after⟩
        · simp [analyze,ha,hb,same] at analyzed
  | loop x start stop step body ih => simp [lower] at lowered
  | kernel body ih => simp [lower] at lowered

theorem backward_ordinary {Op : Type} {meaning : Op → Int → Int → Int} {classify : Op → Option Arithmetic}
    {targetCode : MixedTarget.Code Op}
    (ops : ArithmeticSound classify meaning) (code : Source Op)
    (analyzed : analyze classify env code = .ok summary)
    (lowered : lower policy code = .ok targetCode)
    (typed : BufferView.Typed ordinary code)
    (agrees : env.Matches left.regs counter)
    (tracked : ∀ event ∈ summary.accesses, arrays event.array ↔ policy event.array = true)
    (cursors : consume indices ((summary.accesses.filter (fun e => policy e.array)).map (SymbolicAccess.eval counter)) = some finalIndices)
    (corr : Corresponds ordinary arrays left right indices)
    (run : MixedTarget.Execution meaning targetCode right right') :
    ∃ left', SourceExec meaning code left left' ∧ Corresponds ordinary arrays left' right' finalIndices := by
  induction code generalizing env summary targetCode left right right' indices finalIndices with
  | assign x e =>
    simp [analyze] at analyzed; subst summary
    simp [lower] at lowered; subst targetCode
    simp [consume] at cursors; subst finalIndices
    cases run with
    | assign value =>
      exact ⟨left.setReg x _,.assign ((corr.eval_eq meaning e typed.2).trans value),corr.setReg x _⟩
  | action cmd =>
    cases cmd with
    | write a e x =>
      cases hi : infer classify env e with
      | none => simp [analyze,hi] at analyzed
      | some affine =>
        simp [analyze,hi] at analyzed; subst summary
        by_cases chosen : policy a = true
        · simp [lower,chosen] at lowered; subst targetCode
          simp [chosen] at cursors
          obtain ⟨values,witness,fresh,rfl⟩ := consume_write cursors
          have arrayTracked : arrays a := (tracked ⟨.write,a,affine⟩ (by simp)).2 chosen
          have index := infer_sound ops agrees hi
          cases run with
          | action step =>
            have h := (stream_step_iff.mp step).1
            rcases right' with ⟨rr,rh,rq⟩
            cases h with
            | write queue value =>
              have sourceValue := (corr.registers x typed.1).trans value
              obtain ⟨out,written,after⟩ := corr.push arrayTracked witness fresh typed.1 sourceValue
              have same := step_deterministic step written
              subst out
              exact ⟨_,.action (.write index sourceValue),after⟩
        · simp [lower,chosen] at lowered; subst targetCode
          simp [chosen,consume] at cursors; subst finalIndices
          exact retained_write_backward corr (fun h => chosen ((tracked ⟨.write,a,affine⟩ (by simp)).1 h)) typed run
    | read x a e =>
      cases hi : infer classify env e with
      | none => simp [analyze,hi] at analyzed
      | some affine =>
        simp [analyze,hi] at analyzed; subst summary
        by_cases chosen : policy a = true
        · simp [lower,chosen] at lowered; subst targetCode
          simp [chosen] at cursors
          obtain ⟨tail,head,rfl⟩ := consume_read cursors
          have arrayTracked : arrays a := (tracked ⟨.read,a,affine⟩ (by simp)).2 chosen
          obtain ⟨value,rest,cell,queue,after⟩ := corr.pop arrayTracked head x
          have index := infer_sound ops agrees hi
          cases run with
          | action step =>
            have actual : MixedTarget.Step meaning (.stream (.read x a)) right
                ⟨put right.regs x value,(right.memory.1,put right.memory.2 a rest)⟩ :=
                stream_step_iff.mpr ⟨StreamStep.read queue,rfl⟩
            have same := step_deterministic step actual
            subst right'
            exact ⟨_,.action (.read index cell),after⟩
        · simp [lower,chosen] at lowered; subst targetCode
          simp [chosen,consume] at cursors; subst finalIndices
          exact retained_read_backward corr (fun h => chosen ((tracked ⟨.read,a,affine⟩ (by simp)).1 h)) typed.2 run
  | seq a b ia ib =>
    cases ha : analyze classify env a with
    | error err => simp [analyze,ha] at analyzed
    | ok first =>
      cases hb : analyze classify first.env b with
      | error err => simp [analyze,ha,hb] at analyzed
      | ok second =>
        simp [analyze,ha,hb] at analyzed; subst summary
        cases la : lower policy a with
        | error err => simp [lower,la] at lowered
        | ok ta =>
          cases lb : lower policy b with
          | error err => simp [lower,la,lb] at lowered
          | ok tb =>
            simp [lower,la,lb] at lowered; subst targetCode
            simp only [List.filter_append,List.map_append,consume_append] at cursors
            cases ca : consume indices ((first.accesses.filter (fun e => policy e.array)).map (SymbolicAccess.eval counter)) with
            | none => simp [ca] at cursors
            | some midIndices =>
              simp [ca] at cursors
              cases run with
              | seq leftRun rightRun =>
                obtain ⟨midLeft,rs,midCorr⟩ := ia ha la typed.1 agrees
                  (fun e he => tracked e (List.mem_append_left _ he)) ca corr leftRun
                have midEnv := (analyze_sound ops a ha agrees rs).1
                obtain ⟨endLeft,rr,endCorr⟩ := ib hb lb typed.2 midEnv
                  (fun e he => tracked e (List.mem_append_right _ he)) cursors midCorr rightRun
                exact ⟨endLeft,.seq rs rr,endCorr⟩
  | branch c a b ia ib =>
    cases ha : analyze classify env a with
    | error reason => simp [analyze,ha] at analyzed
    | ok first =>
      cases hb : analyze classify env b with
      | error reason => simp [analyze,ha,hb] at analyzed
      | ok second =>
        by_cases same : first.accesses = second.accesses
        · simp only [analyze,ha,hb,if_pos same,Except.ok.injEq] at analyzed
          subst summary
          cases la : lower policy a with
          | error reason => simp [lower,la] at lowered
          | ok ta =>
            cases lb : lower policy b with
            | error reason => simp [lower,la,lb] at lowered
            | ok tb =>
              simp [lower,la,lb] at lowered; subst targetCode
              cases run with
              | ifTrue condition nonzero chosen =>
                obtain ⟨out,executed,after⟩ := ia ha la typed.2.1 agrees tracked cursors corr chosen
                exact ⟨out,.ifTrue ((corr.registers c typed.1).trans condition) nonzero executed,after⟩
              | ifFalse condition chosen =>
                obtain ⟨out,executed,after⟩ := ib hb lb typed.2.2 agrees
                  (by simpa only [same] using tracked) (by simpa only [same] using cursors) corr chosen
                exact ⟨out,.ifFalse ((corr.registers c typed.1).trans condition) executed,after⟩
        · simp [analyze,ha,hb,same] at analyzed
  | loop x start stop step body ih => simp [lower] at lowered
  | kernel body ih => simp [lower] at lowered


#print axioms forward_ordinary
#print axioms backward_ordinary
end PaperCore.Hybrid.Body
