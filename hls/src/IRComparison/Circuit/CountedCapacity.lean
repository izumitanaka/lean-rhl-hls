import IRComparison.Circuit.CountedSound

namespace IRComparison.Circuit

abbrev WindowState := State × List Int × List Int × List Int

def sourceCountedStep (input : Nat) (start stride x y : Int) (initial refill : List Load)
    (body : HybridIR.Cmd) (j : Nat) (state : WindowState) : Option WindowState := do
  let (s,old,qi,qo) := state
  let (vs,rest) ← WindowFIFO.execute (arrayInput (s.arrays input)) old
    ((if j = 0 then initial else refill).map (Load.at (start+(j:Int)*stride))) qi
  let (t,out) ← body.eval (start+(j:Int)*stride) x y s qo vs
  return (t,vs,rest,out)

theorem countedStep_complete (state result : WindowState)
    (he : sourceCountedStep input start stride x y initial refill body j state = some result) :
    state.2.2.2.length ≤ result.2.2.2.length ∧ (result.2.2.2.length ≤ capacity →
      countedStep capacity input start stride x y initial refill body j state = some result) := by
  obtain ⟨s,old,qi,qo⟩ := state
  obtain ⟨t,vs,rest,out⟩ := result
  cases hl : WindowFIFO.execute (arrayInput (s.arrays input)) old
      ((if j = 0 then initial else refill).map (Load.at (start+(j:Int)*stride))) qi with
  | none => simp [sourceCountedStep,hl] at he
  | some pair =>
    obtain ⟨values,remaining⟩ := pair
    cases hb : body.eval (start+(j:Int)*stride) x y s qo values with
    | none => simp [sourceCountedStep,hl,hb] at he
    | some pair =>
      obtain ⟨u,qu⟩ := pair
      simp only [sourceCountedStep,hl,hb,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,rfl,rfl,rfl⟩ := he
      have h := bounded_complete (capacity:=capacity) body s qo values u qu hb
      exact ⟨h.1,fun fits => by simp [countedStep,bufferStep,hl,h.2 fits]⟩

theorem countedStep_refines (state result : WindowState)
    (he : countedStep capacity input start stride x y initial refill body j state = some result) :
    sourceCountedStep input start stride x y initial refill body j state = some result := by
  obtain ⟨s,old,qi,qo⟩ := state
  obtain ⟨t,vs,rest,out⟩ := result
  cases hl : WindowFIFO.execute (arrayInput (s.arrays input)) old
      ((if j = 0 then initial else refill).map (Load.at (start+(j:Int)*stride))) qi with
  | none => simp [countedStep,bufferStep,hl] at he
  | some pair =>
    obtain ⟨values,remaining⟩ := pair
    cases hb : bounded capacity (start+(j:Int)*stride) x y body s qo values with
    | none => simp [countedStep,bufferStep,hl,hb] at he
    | some pair =>
      obtain ⟨u,qu⟩ := pair
      simp only [countedStep,bufferStep,hl,hb,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,rfl,rfl,rfl⟩ := he
      simp [sourceCountedStep,hl,bounded_refines body s qo values u qu hb]

theorem countedFold_complete (iterations : List Nat) (state result : WindowState)
    (he : iterations.foldlM (fun st j => sourceCountedStep input start stride x y initial refill body j st) state = some result) :
    state.2.2.2.length ≤ result.2.2.2.length ∧ (result.2.2.2.length ≤ capacity →
      iterations.foldlM (fun st j => countedStep capacity input start stride x y initial refill body j st) state = some result) := by
  induction iterations generalizing state with
  | nil => cases he; exact ⟨Nat.le_refl _,fun _ => rfl⟩
  | cons j js ih =>
    cases hf : sourceCountedStep input start stride x y initial refill body j state with
    | none => simp [List.foldlM_cons,hf] at he
    | some mid =>
      have tail := ih mid (by simpa [List.foldlM_cons,hf] using he)
      have head := countedStep_complete (capacity:=capacity) state mid hf
      exact ⟨Nat.le_trans head.1 tail.1,fun fits => by
        simpa [List.foldlM_cons,head.2 (Nat.le_trans tail.1 fits)] using tail.2 fits⟩

theorem countedFold_refines (iterations : List Nat) (state result : WindowState)
    (he : iterations.foldlM (fun st j => countedStep capacity input start stride x y initial refill body j st) state = some result) :
    iterations.foldlM (fun st j => sourceCountedStep input start stride x y initial refill body j st) state = some result := by
  induction iterations generalizing state with
  | nil => exact he
  | cons j js ih =>
    cases hf : countedStep capacity input start stride x y initial refill body j state with
    | none => simp [List.foldlM_cons,hf] at he
    | some mid =>
      simpa [List.foldlM_cons,countedStep_refines state mid hf] using ih mid (by simpa [List.foldlM_cons,hf] using he)

theorem countedFold_eq (iterations : List Nat) (state : WindowState)
    (fits : ∀ result, iterations.foldlM (fun st j => sourceCountedStep input start stride x y initial refill body j st) state = some result →
      result.2.2.2.length ≤ capacity) :
    iterations.foldlM (fun st j => countedStep capacity input start stride x y initial refill body j st) state =
      iterations.foldlM (fun st j => sourceCountedStep input start stride x y initial refill body j st) state := by
  cases hs : iterations.foldlM (fun st j => sourceCountedStep input start stride x y initial refill body j st) state with
  | none =>
    cases ht : iterations.foldlM (fun st j => countedStep capacity input start stride x y initial refill body j st) state with
    | none => rfl
    | some result => have h := countedFold_refines iterations state result ht; rw [hs] at h; cases h
  | some result => exact (countedFold_complete iterations state result hs).2 (fits result hs)

end IRComparison.Circuit
