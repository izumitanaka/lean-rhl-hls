import IRComparison.Circuit.WindowIteration

namespace IRComparison.Circuit

def frozenLoader (input : Input) (start stride : Int) (initial refill : List Load) : WindowLoader :=
  fun j old q => WindowFIFO.execute input old ((if j = 0 then initial else refill).map (Load.at (start+(j:Int)*stride))) q

theorem sourceCountedStep_frozen (state : WindowState) (same : arrayInput (state.1.arrays input) = frozen) :
    sourceCountedStep input start stride x y initial refill body j state =
      iterationStep (frozenLoader frozen start stride initial refill)
        (fun j s q vs => body.eval (start+(j:Int)*stride) x y s q vs) j state := by
  obtain ⟨s,old,qi,qo⟩ := state
  simp only [sourceCountedStep,iterationStep,frozenLoader,same]

theorem sourceCountedStep_array_frame (state result : WindowState)
    (readonly : input ∉ commandWrites body)
    (he : sourceCountedStep input start stride x y initial refill body j state = some result) :
    result.1.arrays input = state.1.arrays input := by
  obtain ⟨s,old,qi,qo⟩ := state
  obtain ⟨t,values,rest,out⟩ := result
  cases hl : WindowFIFO.execute (arrayInput (s.arrays input)) old
      ((if j = 0 then initial else refill).map (Load.at (start+(j:Int)*stride))) qi with
  | none => simp [sourceCountedStep,hl] at he
  | some pair =>
    obtain ⟨vs,remaining⟩ := pair
    cases hb : body.eval (start+(j:Int)*stride) x y s qo vs with
    | none => simp [sourceCountedStep,hl,hb] at he
    | some pair =>
      obtain ⟨u,qu⟩ := pair
      simp only [sourceCountedStep,hl,hb,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,rfl,rfl,rfl⟩ := he
      exact command_array_frame body readonly hb

theorem sourceCountedFold_frozen (iterations : List Nat) (state : WindowState)
    (readonly : input ∉ commandWrites body) (same : arrayInput (state.1.arrays input) = frozen) :
    iterations.foldlM (fun st j => sourceCountedStep input start stride x y initial refill body j st) state =
      iterations.foldlM (fun st j => iterationStep (frozenLoader frozen start stride initial refill)
        (fun j s q vs => body.eval (start+(j:Int)*stride) x y s q vs) j st) state := by
  induction iterations generalizing state with
  | nil => rfl
  | cons j js ih =>
    rw [List.foldlM_cons,List.foldlM_cons,← sourceCountedStep_frozen state same]
    cases he : sourceCountedStep input start stride x y initial refill body j state with
    | none => rfl
    | some mid =>
      apply ih mid
      exact (congrArg arrayInput (sourceCountedStep_array_frame state mid readonly he)).trans same

theorem frozenLoader_memory (initial refill : List SymbolicWindowSchedule.Load) :
    frozenLoader input start stride (initial.map fromMemoryLoad) (refill.map fromMemoryLoad) j old q =
      (SymbolicWindowSchedule.execute input (start+(j:Int)*stride) old (if j = 0 then initial else refill)).map (fun vs => (vs,q)) := by
  unfold frozenLoader
  by_cases hz : j = 0 <;> simp only [hz,↓reduceIte,memoryLoads_at,HybridSymbolicWindowControl.instantiate_correct]

end IRComparison.Circuit
