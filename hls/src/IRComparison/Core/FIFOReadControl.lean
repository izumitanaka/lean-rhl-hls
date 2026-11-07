import IRComparison.Memory.WindowFIFO

namespace IRComparison.FIFOReadControl

inductive Config where
  | loading (pending : List WindowFIFO.Load) (old values queue : List Int)
  | stopped (result : Option (List Int × List Int))

def step (input : Input) : Config → Config
  | .stopped r => .stopped r
  | .loading [] _ vs q => .stopped (some (vs,q))
  | .loading (.memory a::ls) old vs q =>
    match input a with
    | none => .stopped none
    | some v => .loading ls old (vs++[v]) q
  | .loading (.saved j::ls) old vs q =>
    match old[j]? with
    | none => .stopped none
    | some v => .loading ls old (vs++[v]) q
  | .loading (.take _::_) _ _ [] => .stopped none
  | .loading (.take 0::ls) old vs (v::q) => .loading ls old (vs++[v]) q
  | .loading (.take (n+1)::ls) old vs (_::q) => .loading (.take n::ls) old vs q

inductive Reaches (input : Input) : Config → Config → Prop where
  | refl (c) : Reaches input c c
  | next : Reaches input (step input a) b → Reaches input a b

theorem Reaches.trans (h : Reaches input a b) (g : Reaches input b c) : Reaches input a c := by
  induction h with
  | refl => exact g
  | next _ ih => exact .next (ih g)

theorem take_reduce (n : Nat) (q : List Int) :
    (∃ v, q[n]? = some v ∧ Reaches input (.loading (.take n::ls) old vs q)
      (.loading ls old (vs++[v]) (q.drop (n+1)))) ∨
    (q[n]? = none ∧ Reaches input (.loading (.take n::ls) old vs q) (.stopped none)) := by
  induction n generalizing q with
  | zero =>
    cases q with
    | nil => exact .inr ⟨rfl,.next (.refl _)⟩
    | cons v q => exact .inl ⟨v,rfl,.next (.refl _)⟩
  | succ n ih =>
    cases q with
    | nil => exact .inr ⟨rfl,.next (.refl _)⟩
    | cons a q =>
      rcases ih q with ⟨v,hv,run⟩ | ⟨hn,run⟩
      · exact .inl ⟨v,by simpa using hv,.next (by simpa using run)⟩
      · exact .inr ⟨by simpa using hn,.next run⟩

theorem correct (pending : List WindowFIFO.Load) (old vs q : List Int) :
    Reaches input (.loading pending old vs q)
      (.stopped ((WindowFIFO.execute input old pending q).map (fun p => (vs++p.1,p.2)))) := by
  induction pending generalizing vs q with
  | nil => simpa [WindowFIFO.execute] using (Reaches.next (Reaches.refl (.stopped (some (vs,q)))))
  | cons l ls ih =>
    have advance : ∀ v tail,
        Reaches input (.loading (l::ls) old vs q) (.loading ls old (vs++[v]) tail) →
        l.eval input old q = some (v,tail) →
        Reaches input (.loading (l::ls) old vs q)
          (.stopped ((WindowFIFO.execute input old (l::ls) q).map (fun p => (vs++p.1,p.2)))) := by
      intro v tail run hv
      apply run.trans
      cases he : WindowFIFO.execute input old ls tail <;>
        simpa [WindowFIFO.execute,hv,he,List.append_assoc] using ih (vs++[v]) tail
    cases l with
    | memory a =>
      cases h : input a with
      | none =>
        simp only [WindowFIFO.execute,WindowFIFO.Load.eval,h,bind,Option.bind,Option.map_none]
        apply Reaches.next
        simpa [step,h] using (Reaches.refl (.stopped none))
      | some v => exact advance v q (by
          apply Reaches.next
          simpa [step,h] using (Reaches.refl (.loading ls old (vs++[v]) q))) (by simp [WindowFIFO.Load.eval,h])
    | saved j =>
      cases h : old[j]? with
      | none =>
        simp only [WindowFIFO.execute,WindowFIFO.Load.eval,h,bind,Option.bind,Option.map_none]
        apply Reaches.next
        simpa [step,h] using (Reaches.refl (.stopped none))
      | some v => exact advance v q (by
          apply Reaches.next
          simpa [step,h] using (Reaches.refl (.loading ls old (vs++[v]) q))) (by simp [WindowFIFO.Load.eval,h])
    | take n =>
      rcases take_reduce (input:=input) (ls:=ls) (old:=old) (vs:=vs) n q with ⟨v,hv,run⟩ | ⟨hn,run⟩
      · exact advance v (q.drop (n+1)) run (by simp [WindowFIFO.Load.eval,hv])
      · simpa [WindowFIFO.execute,WindowFIFO.Load.eval,hn] using run

end IRComparison.FIFOReadControl
