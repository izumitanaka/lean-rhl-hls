import IRComparison.Memory.WindowTransport
import IRComparison.Core.Relational

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

theorem Result.asRel (h : Result array size keys source target) :
    Option.Rel (fun s t => Related array size keys s t.1 t.2) source target := by
  cases h with
  | none => exact .none
  | some h => exact .some h

theorem Result.ofRel
    (h : Option.Rel (fun s t => Related array size keys s t.1 t.2) source target) :
    Result array size keys source target := by
  cases h with
  | none => exact .none
  | some h => exact .some h

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

/-- A target-only buffer binding used between Tr-WriteMem and Tr-InsWBuf.
This is a proof-level decomposition of the existing local-value/send path,
not an extra physical memory or an extension of the input language. -/
structure WriteBuffer where
  data : State
  queue : List Int
  value : Int

def BufferRelated (array size : Nat) (keys : List Int) (s : State) (t : WriteBuffer) : Prop :=
  Related array size keys s t.data t.queue

def Holds (array : Nat) (j : Int) (s : State) (t : WriteBuffer) : Prop :=
  arrayInput (s.arrays array) j = some t.value

def setBuffer (v : Int) (t : WriteBuffer) : Option WriteBuffer := some {t with value := v}
def sendBuffer (t : WriteBuffer) : Option WriteBuffer := some {t with queue := t.queue ++ [t.value]}

/-- Tr-WriteMem: update source memory, but only the target buffer.
Already queued source elements must not be overwritten. -/
theorem writeMem_rule {size : Nat} (bounds : 0 ≤ j ∧ j < (size:Int)) (fresh : j ∉ keys) (v : Int) :
    Relational.Translation (BufferRelated array size keys)
      (fun s => s.write array j v) (setBuffer v)
      (fun s t => BufferRelated array size keys s t ∧ Holds array j s t) := by
  intro s t h
  obtain ⟨u,hu,ha,hs,hv,others⟩ := write_output s bounds h.sized (v:=v)
  simp only [hu,setBuffer]
  apply Option.Rel.some
  refine ⟨⟨⟨ha.regs.trans h.agree.regs,fun a hn => (ha.arrays a hn).trans (h.agree.arrays a hn)⟩,hs,?_⟩,hv⟩
  exact corresponds_change h.values (fun k hk => others k (by intro eq; subst k; exact fresh hk))

/-- Tr-InsWBuf: the source stays put; append the held source value to FIFO.
The ghost index is appended only to the relation, not sent at runtime. -/
theorem insertWrite_rule (_fresh : j ∉ keys) :
    Relational.Insertion
      (fun s t => BufferRelated array size keys s t ∧ Holds array j s t)
      sendBuffer (BufferRelated array size (keys++[j])) := by
  intro s t h
  exact .some ⟨h.1.agree,h.1.sized,corresponds_append h.1.values h.2⟩

/-- Direct send is derived by Tr-InsertR, not a new primitive rule. -/
theorem directSend_rule {size : Nat} (bounds : 0 ≤ j ∧ j < (size:Int)) (fresh : j ∉ keys) (v : Int) :
    Relational.Translation (BufferRelated array size keys)
      (fun s => s.write array j v) (fun t => (setBuffer v t).bind sendBuffer)
      (BufferRelated array size (keys++[j])) :=
  Relational.insertRight (writeMem_rule bounds fresh v) (insertWrite_rule fresh)

theorem Related.send (h : Related array size keys s t q) (bounds : 0 ≤ j ∧ j < (size:Int))
    (fresh : j ∉ keys) (v : Int) :
    Result array size (keys++[j]) (s.write array j v) (some (t,q++[v])) := by
  have hr := directSend_rule bounds fresh v s ⟨t,q,0⟩ h
  cases hw : s.write array j v <;> simp only [hw,setBuffer,sendBuffer,Option.bind_some] at hr
  · cases hr
  · cases hr with
    | some h => exact .some h

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
