import IRComparison.Circuit.CountedCapacity
import IRComparison.Circuit.SendBudget

namespace IRComparison.Circuit

theorem fold_growth {f : α → β → Option α} {measure : α → Nat} {bound : Nat}
    (step : ∀ s a t, f s a = some t → measure t ≤ measure s+bound)
    (xs : List β) (s t : α) (he : xs.foldlM f s = some t) :
    measure t ≤ measure s + xs.length*bound := by
  induction xs generalizing s with
  | nil => cases he; simp
  | cons a xs ih =>
    cases hf : f s a with
    | none => simp [List.foldlM_cons,hf] at he
    | some u =>
      have tail := ih u (by simpa [List.foldlM_cons,hf] using he)
      have head := step s a u hf
      simp only [List.length_cons,Nat.succ_mul]
      omega

theorem sendBound_sound (c : HybridIR.Cmd) (hb : sendBound c = some bound)
    (he : c.eval i x y s q ls = some (t,out)) : out.length ≤ q.length+bound := by
  induction c generalizing bound s q ls t out with
  | skip => cases he; simp [sendBound] at hb; subst bound; omega
  | assign r e =>
    cases hv : e.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hv] at he
    obtain ⟨rfl,rfl⟩ := he
    simp [sendBound] at hb; subst bound; omega
  | store a j e =>
    cases hj : j.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hj] at he
    next index =>
      cases hv : e.eval i x y s ls [] <;> simp [hv] at he
      next value =>
        cases hw : s.write a index value <;> simp [hw] at he
        obtain ⟨rfl,rfl⟩ := he
        simp [sendBound] at hb; subst bound; omega
  | send e =>
    cases hv : e.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hv] at he
    obtain ⟨rfl,rfl⟩ := he
    simp [sendBound] at hb; subst bound; simp
  | letValue e b ih =>
    cases hv : e.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hv] at he
    exact ih hb he
  | seq a b ia ib =>
    cases ba : sendBound a <;> simp [sendBound,ba] at hb
    next na =>
      cases bb : sendBound b <;> simp [bb] at hb
      next nb =>
        subst bound
        cases ha : a.eval i x y s q ls <;> simp [HybridIR.Cmd.eval,ha] at he
        next pair =>
          obtain ⟨u,qu⟩ := pair
          have first := ia ba ha
          have second := ib bb he
          dsimp only at first second
          omega
  | branch e a b ia ib =>
    cases ba : sendBound a <;> simp [sendBound,ba] at hb
    next na =>
      cases bb : sendBound b <;> simp [bb] at hb
      next nb =>
        subst bound
        cases hv : e.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hv] at he
        next v =>
          split at he
          · have := ib bb he; omega
          · have := ia ba he; omega
  | «repeat» n b ih =>
    cases bb : sendBound b <;> simp [sendBound,bb] at hb
    next nb =>
      subst bound
      simpa using fold_growth (measure:=fun p : State × List Int => p.2.length)
        (bound:=nb) (fun u _ v hh => ih bb hh) (List.range n) (s,q) (t,out) he
  | forRange e b ih =>
    by_cases bb : sendBound b = some 0
    · simp [sendBound,bb] at hb; subst bound
      cases hv : e.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hv] at he
      next n =>
        simpa using fold_growth (measure:=fun p : State × List Int => p.2.length)
          (bound:=0) (fun u (j:Nat) v hh => ih (ls:=(j:Int)::ls) bb hh) (List.range n.toNat) (s,q) (t,out) he
    · simp [sendBound,bb] at hb

theorem countedStep_sendBound (hb : sendBound body = some bound) (state result : WindowState)
    (he : sourceCountedStep input start stride x y initial refill body j state = some result) :
    result.2.2.2.length ≤ state.2.2.2.length+bound := by
  obtain ⟨s,old,qi,qo⟩ := state
  obtain ⟨t,values,rest,out⟩ := result
  cases hl : WindowFIFO.execute (arrayInput (s.arrays input)) old
      ((if j = 0 then initial else refill).map (Load.at (start+(j:Int)*stride))) qi with
  | none => simp [sourceCountedStep,hl] at he
  | some pair =>
    obtain ⟨vs,remaining⟩ := pair
    cases hbody : body.eval (start+(j:Int)*stride) x y s qo vs with
    | none => simp [sourceCountedStep,hl,hbody] at he
    | some pair =>
      obtain ⟨u,qu⟩ := pair
      simp only [sourceCountedStep,hl,hbody,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at he
      obtain ⟨rfl,rfl,rfl,rfl⟩ := he
      exact sendBound_sound body hb hbody

theorem countedFold_sendBound (hb : sendBound body = some bound) (iterations : List Nat)
    (state result : WindowState)
    (he : iterations.foldlM (fun st j => sourceCountedStep input start stride x y initial refill body j st) state = some result) :
    result.2.2.2.length ≤ state.2.2.2.length+iterations.length*bound :=
  fold_growth (measure:=fun st : WindowState => st.2.2.2.length)
    (fun st _ r hr => countedStep_sendBound hb st r hr) iterations state result he

end IRComparison.Circuit
