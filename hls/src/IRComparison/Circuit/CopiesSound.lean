import IRComparison.Circuit.Counter

namespace IRComparison.Circuit

structure Copied (p q : Payload) (dest source : List Nat) : Prop where
  data : q.data = p.data
  queues : q.queues = p.queues
  values : dest.map q.wires = source.map p.wires
  outside : ∀ n, n ∉ dest → q.wires n = p.wires n

/-- Copying a freshly filled scratch buffer into holding registers preserves
all source values. Disjointness is an allocation fact, not a source-program
restriction. No nondestructive FIFO read is introduced. -/
theorem copies_correct (dest source : List Nat) (p : Payload)
    (lengths : dest.length = source.length) (unique : dest.Nodup)
    (disjoint : ∀ d ∈ dest, ∀ s ∈ source, d ≠ s) :
    ∃ q, (copies dest source).Eval cap p (some q) ∧ Copied p q dest source := by
  induction dest generalizing source p with
  | nil => cases source with
    | nil => exact ⟨p,.skip,⟨rfl,rfl,rfl,fun _ _ => rfl⟩⟩
    | cons => simp at lengths
  | cons d ds ih =>
    cases source with
    | nil => simp at lengths
    | cons s ss =>
      have nd := List.nodup_cons.mp unique
      let p1 := p.setWire d (p.wires s)
      obtain ⟨q,hq,hcopy⟩ := ih ss p1 (by simpa using lengths) nd.2
        (fun d hd s hs => disjoint d (by simp [hd]) s (by simp [hs]))
      refine ⟨q,.seq (setWire_eval (e:=.wire s) rfl) hq,?_,?_,?_,?_⟩
      · exact hcopy.data
      · exact hcopy.queues
      · have head : q.wires d = p.wires s := by simpa [p1,Payload.setWire] using hcopy.outside d nd.1
        have src : ss.map p1.wires = ss.map p.wires := by
          apply List.map_congr_left
          intro n hn
          have ne := disjoint d (by simp) n (by simp [hn])
          simp [p1,Payload.setWire,Ne.symm ne]
        simp only [List.map_cons,head,hcopy.values,src]
      · intro n hn
        have nn : n ≠ d ∧ n ∉ ds := by simpa using hn
        simpa [p1,Payload.setWire,nn.1] using hcopy.outside n nn.2

end IRComparison.Circuit
