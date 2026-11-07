import IRComparison.Memory.StreamProducer

namespace IRComparison.StreamAlternatives
open StreamState StreamProducer

/-- Only the proof carries the disjunction. The executable queue contains
    values, never branch tags or source addresses. -/
inductive Result (array size : Nat) (alternatives : List (List Int)) :
    Option State → Option (State × List Int) → Prop where
  | none : Result array size alternatives none none
  | some : keys ∈ alternatives → Related array size keys s t q →
      Result array size alternatives (some s) (some (t,q))

theorem Result.ofSingle (r : StreamState.Result array size keys a b)
    (member : keys ∈ alternatives) : Result array size alternatives a b := by
  cases r with
  | none => exact .none
  | some hr => exact .some member hr

theorem Result.widen (r : Result array size alternatives a b)
    (members : ∀ k ∈ alternatives, k ∈ others) : Result array size others a b := by
  cases r with
  | none => exact .none
  | some hm hr => exact .some (members _ hm) hr

structure Compiled (i : Int) (array size : Nat) (before : List (List Int)) (source : Imperative.Cmd) where
  code : StreamProducer.Cmd
  after : List (List Int)
  correct : ∀ keys ∈ before, ∀ s t q x y ls, Related array size keys s t q →
    Result array size after (source.eval i x y s ls) (code.eval i x y t q ls)

/-- Check a single executable instruction against every incoming invariant.
    The continuation is not selected by a hidden runtime branch tag. -/
def atomic (i : Int) (array size : Nat) (source : Imperative.Cmd) :
    (before : List (List Int)) → Option (Compiled i array size before source)
  | [] => none
  | keys::rest => do
    let head ← StreamProducer.compile i array size keys source
    match rest with
    | [] => return ⟨head.code,[head.after],by
        intro ks member s t q x y ls h
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        subst ks
        have result := head.correct s t q x y ls h
        exact Result.ofSingle result (by simp)⟩
    | next::tail =>
      let others ← atomic i array size source (next::tail)
      if same : head.code = others.code then
        return ⟨head.code,head.after::others.after,by
          intro ks member s t q x y ls h
          rcases List.mem_cons.mp member with rfl | hm
          · have result := head.correct s t q x y ls h
            exact Result.ofSingle result (by simp)
          · rw [same]
            have result := others.correct ks hm s t q x y ls h
            exact result.widen (fun _ hm => List.mem_cons_of_mem _ hm)⟩
      else none

def sequence (a : Compiled i array size before first)
    (b : Compiled i array size a.after second) : Compiled i array size before (.seq first second) where
  code := .seq a.code b.code
  after := b.after
  correct := by
    intro keys member s t q x y ls h
    have ha := a.correct keys member s t q x y ls h
    cases hs : first.eval i x y s ls <;> cases ht : a.code.eval i x y t q ls <;>
      simp only [hs,ht] at ha
    · simp only [Imperative.Cmd.eval,StreamProducer.Cmd.eval,hs,ht,bind,Option.bind]; exact .none
    · cases ha
    · cases ha
    · rename_i u pair
      obtain ⟨v,qs⟩ := pair
      cases ha with
      | some hm hr =>
        simpa only [Imperative.Cmd.eval,StreamProducer.Cmd.eval,hs,ht,bind,Option.bind] using b.correct _ hm u v qs x y ls hr

def branch (safe : avoids array condition = true)
    (a : Compiled i array size before yes) (b : Compiled i array size before no) :
    Compiled i array size before (.branch condition yes no) where
  code := .branch condition a.code b.code
  after := a.after ++ b.after
  correct := by
    intro keys member s t q x y ls h
    simp only [Imperative.Cmd.eval,StreamProducer.Cmd.eval,← expr_correct condition safe h.agree]
    cases he : condition.eval i x y s ls with
    | none => exact .none
    | some v =>
      simp only [bind,Option.bind]
      split
      · have r := a.correct keys member s t q x y ls h
        exact r.widen (fun _ hm => List.mem_append_left _ hm)
      · have r := b.correct keys member s t q x y ls h
        exact r.widen (fun _ hm => List.mem_append_right _ hm)

def compile (i : Int) (array size : Nat) (before : List (List Int)) :
    (source : Imperative.Cmd) → Option (Compiled i array size before source)
  | .seq a b => do
    let ca ← compile i array size before a
    let cb ← compile i array size ca.after b
    return sequence ca cb
  | .branch condition yes no =>
    if safe : avoids array condition = true then do
      let a ← compile i array size before yes
      let b ← compile i array size before no
      return branch safe a b
    else none
  | .letValue e body =>
    if safe : avoids array e = true then do
      let cb ← compile i array size before body
      return ⟨.letValue e cb.code,cb.after,by
        intro keys member s t q x y ls h
        simp only [Imperative.Cmd.eval,StreamProducer.Cmd.eval,← expr_correct e safe h.agree]
        cases he : e.eval i x y s ls with
        | none => exact .none
        | some v => exact cb.correct keys member s t q x y (v::ls) h⟩
    else none
  | other => atomic i array size other before

end IRComparison.StreamAlternatives
