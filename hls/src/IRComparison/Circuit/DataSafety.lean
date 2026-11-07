import IRComparison.Circuit.Invariant
import IRComparison.Hybrid.HybridWordCommand

namespace IRComparison.Circuit

structure DataWords (s : IRComparison.State) : Prop where
  regs : ∀ n, wordRange.Contains (s.regs n)
  arrays : ∀ (a n : Nat) (v : Int), (s.arrays a)[n]? = some v → wordRange.Contains v

theorem word_encoded (w : HybridWord.Word) : wordRange.Contains (HybridWord.encode w) := by
  have := w.isLt
  simp only [wordRange,Interval.Contains,HybridWord.encode]
  omega

theorem DataWords.encoded (s : HybridWord.State) : DataWords s.encode := by
  constructor
  · intro n; exact word_encoded _
  · intro a n v h
    simp only [HybridWord.State.encode,Array.getElem?_map] at h
    cases he : (s.arrays a)[n]? with
    | none => simp [he] at h
    | some w => simp only [he,Option.map_some,Option.some.injEq] at h; subst v; exact word_encoded w

theorem DataWords.input {f : Frame} (h : DataWords s) (hf : f.contains w) : InputsBound s w f.get := by
  refine ⟨hf,h.regs,?_⟩
  intro a j v hv
  unfold arrayInput at hv
  split at hv
  · cases hv
  · exact h.arrays a j.toNat v hv

theorem DataWords.set (h : DataWords s) (hv : wordRange.Contains v) : DataWords (s.set k v) := by
  constructor
  · intro n; simp only [IRComparison.State.set]; split
    · exact hv
    · exact h.regs n
  · exact h.arrays

theorem array_set_words {xs : Array Int} {j : Nat} (h : ∀ (n : Nat) (v : Int), xs[n]? = some v → wordRange.Contains v)
    (hv : wordRange.Contains v) (hj : j < xs.size) :
    ∀ (n : Nat) (u : Int), (xs.set j v hj)[n]? = some u → wordRange.Contains u := by
  intro n u hu
  by_cases he : j = n
  · subst n
    simp only [Array.getElem?_set_self,Option.some.injEq] at hu
    subst u
    exact hv
  · rw [Array.getElem?_set_ne hj he] at hu
    exact h n u hu

theorem DataWords.write (h : DataWords s) (hv : wordRange.Contains v)
    (he : s.write a j v = some t) : DataWords t := by
  unfold IRComparison.State.write at he
  split at he
  · cases he
  · split at he
    · cases he
      refine ⟨h.regs,?_⟩
      intro b n u hu
      simp only at hu
      split at hu
      · subst b
        exact array_set_words (h.arrays a) hv _ n u hu
      · exact h.arrays b n u hu
    · cases he

theorem DataWords.replace (h : DataWords s)
    (hx : ∀ (n : Nat) (v : Int), xs[n]? = some v → wordRange.Contains v) :
    DataWords { s with arrays := fun n => if n = a then xs else s.arrays n } := by
  refine ⟨h.regs,?_⟩
  intro n k v hv
  simp only at hv
  split at hv
  · exact hx k v hv
  · exact h.arrays n k v hv

structure RuntimeBound (f : Frame) (r : Runtime) : Prop where
  data : DataWords r.data
  wires : f.contains r.wires
  queues : ∀ q v, v ∈ r.queues q → wordRange.Contains v

theorem RuntimeBound.inputs (h : RuntimeBound f r) : InputsBound r.data r.wires f.get :=
  h.data.input h.wires

theorem RuntimeBound.within (h : RuntimeBound f r) (hf : f.within g = true) : RuntimeBound g r :=
  ⟨h.data,Frame.within_sound hf h.wires,h.queues⟩

theorem RuntimeBound.setQueue (h : RuntimeBound f r)
    (hv : ∀ v ∈ vs, wordRange.Contains v) : RuntimeBound f (r.setQueue q vs) := by
  refine ⟨h.data,h.wires,?_⟩
  intro a v hm
  simp only [Runtime.setQueue] at hm
  split at hm
  · exact hv v hm
  · exact h.queues a v hm

theorem RuntimeBound.setWire (h : RuntimeBound f r) (hk : k < f.length) (hv : b.Contains v) :
    RuntimeBound (f.set k b) (r.setWire k v) :=
  ⟨h.data,Frame.set_value h.wires hk hv,h.queues⟩

theorem RuntimeBound.setPC (h : RuntimeBound f r) : RuntimeBound f { r with pc := pc } :=
  ⟨h.data,h.wires,h.queues⟩

theorem isWord_sound (h : isWord b = true) (hv : b.Contains v) : wordRange.Contains v := by
  simp only [isWord,Bool.and_eq_true,decide_eq_true_eq] at h
  simp only [Interval.Contains,wordRange] at *
  omega

end IRComparison.Circuit
