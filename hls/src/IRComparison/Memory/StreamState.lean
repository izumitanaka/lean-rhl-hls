import IRComparison.Memory.WindowTransport

namespace IRComparison.StreamState

/-- The eliminated array has no required representation in target memory. -/
structure Agree (array : Nat) (source target : State) : Prop where
  regs : source.regs = target.regs
  arrays : ∀ a, a ≠ array → source.arrays a = target.arrays a

def avoids (array : Nat) : Expr → Bool
  | .read a e => a != array && avoids array e
  | .add a b | .sub a b | .mul a b | .div a b => avoids array a && avoids array b
  | .select c a b => avoids array c && avoids array a && avoids array b
  | .natIndex e => avoids array e
  | _ => true

theorem expr_correct (e : Expr) (safe : avoids array e = true) (h : Agree array s t) :
    e.eval i x y s locals = e.eval i x y t locals := by
  induction e with
  | lit | index | left | right | «local» => rfl
  | reg r => simp [Expr.eval,h.regs]
  | natIndex e ih => simp only [Expr.eval,ih safe]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb =>
    simp only [avoids,Bool.and_eq_true] at safe
    simp only [Expr.eval,ha safe.1,hb safe.2]
  | select c a b hc ha hb =>
    simp only [avoids,Bool.and_eq_true] at safe
    simp only [Expr.eval,hc safe.1.1,ha safe.1.2,hb safe.2]
  | read a e ih =>
    simp only [avoids,Bool.and_eq_true,bne_iff_ne] at safe
    simp only [Expr.eval,ih safe.2,h.arrays a safe.1]

theorem Agree.set (h : Agree array s t) (r : Nat) (v : Int) : Agree array (s.set r v) (t.set r v) := by
  exact ⟨by simp [State.set,h.regs],h.arrays⟩

/-- Read correspondence is indexed by a logical sequence, never by tags in the
    transmitted data. Size belongs to the source safety contract, not target RAM. -/
structure Related (array size : Nat) (keys : List Int) (s t : State) (q : List Int) : Prop where
  agree : Agree array s t
  sized : (s.arrays array).size = size
  values : CommunicationIR.Corresponds (arrayInput (s.arrays array)) keys q

inductive Result (array size : Nat) (keys : List Int) : Option State → Option (State × List Int) → Prop where
  | none : Result array size keys none none
  | some : Related array size keys s t q → Result array size keys (some s) (some (t,q))

theorem write_output {size array : Nat} (s : State) (bounds : 0 ≤ j ∧ j < (size:Int))
    (sized : (s.arrays array).size = size) :
    ∃ t, s.write array j v = some t ∧ Agree array t s ∧ (t.arrays array).size = size ∧
      arrayInput (t.arrays array) j = some v ∧
      ∀ k, k ≠ j → arrayInput (t.arrays array) k = arrayInput (s.arrays array) k := by
  have hn : ¬ j < 0 := by omega
  have hj : j.toNat < (s.arrays array).size := by omega
  let t : State := {s with arrays := fun a => if a = array then (s.arrays array).set j.toNat v hj else s.arrays a}
  refine ⟨t,by simp [State.write,hn,hj,t],?_,?_,?_,?_⟩
  · exact ⟨rfl,by intro a ha; simp [t,ha]⟩
  · simp [t,sized]
  · simp [arrayInput,t,hn,hj]
  · intro k hk
    by_cases neg : k < 0
    · simp [arrayInput,neg]
    · have different : k.toNat ≠ j.toNat := by omega
      simp [arrayInput,t,neg,Ne.symm different]

theorem corresponds_change (h : CommunicationIR.Corresponds input keys q)
    (same : ∀ k ∈ keys, other k = input k) : CommunicationIR.Corresponds other keys q := by
  induction h with
  | nil => exact .nil
  | @cons k v ks vs hv ht ih =>
    exact .cons ((same k (by simp)).trans hv) (ih (by intro k hk; exact same k (by simp [hk])))

theorem corresponds_append (h : CommunicationIR.Corresponds input keys q) (hv : input j = some v) :
    CommunicationIR.Corresponds input (keys++[j]) (q++[v]) := by
  induction h with
  | nil => exact .cons hv .nil
  | cons hk ht ih => exact .cons hk ih

theorem Related.set (h : Related array size keys s t q) (r : Nat) (v : Int) :
    Related array size keys (s.set r v) (t.set r v) q :=
  ⟨h.agree.set r v,h.sized,h.values⟩

theorem Related.send (h : Related array size keys s t q) (bounds : 0 ≤ j ∧ j < (size:Int))
    (fresh : j ∉ keys) (v : Int) :
    Result array size (keys++[j]) (s.write array j v) (some (t,q++[v])) := by
  obtain ⟨u,hu,ha,hs,hv,others⟩ := write_output s bounds h.sized (v:=v)
  rw [hu]
  apply Result.some
  refine ⟨⟨ha.regs.trans h.agree.regs,fun a hn => (ha.arrays a hn).trans (h.agree.arrays a hn)⟩,hs,?_⟩
  apply corresponds_append _ hv
  exact corresponds_change h.values (by
    intro k hk
    exact others k (by intro eq; subst k; exact fresh hk))

theorem Related.write_other (h : Related array size keys s t q) (different : a ≠ array) (j v : Int) :
    Result array size keys (s.write a j v) ((t.write a j v).map (fun u => (u,q))) := by
  have arr := h.agree.arrays a different
  unfold State.write
  by_cases neg : j < 0
  · simp [neg]; exact .none
  · simp only [neg,↓reduceIte]
    by_cases hj : j.toNat < (s.arrays a).size
    · have ht : j.toNat < (t.arrays a).size := arr ▸ hj
      simp only [hj,ht,↓reduceDIte,Option.map_some]
      apply Result.some
      refine ⟨⟨h.agree.regs,?_⟩,?_,?_⟩
      · intro b hb
        by_cases eq : b = a
        · subst b; simp [arr]
        · simp [eq,h.agree.arrays b hb]
      · simpa [Ne.symm different] using h.sized
      · simpa [Ne.symm different] using h.values
    · have ht : ¬j.toNat < (t.arrays a).size := arr ▸ hj
      simp only [hj,ht,↓reduceDIte,Option.map_none]
      exact .none

end IRComparison.StreamState
