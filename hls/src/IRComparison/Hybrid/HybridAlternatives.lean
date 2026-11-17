import IRComparison.Hybrid.HybridSender
import IRComparison.Memory.StreamAlternatives
namespace IRComparison.HybridAlternatives
open StreamState
open StreamAlternatives (Result)
structure Compiled (i : Int) (array size : Nat) (before : List (List Int)) (source : HybridIR.MemoryCmd) where
  code : HybridIR.Cmd
  after : List (List Int)
  correct : ∀ keys ∈ before, ∀ s t q x y ls, Related array size keys s t q →
    Result array size after (source.eval i x y s ls) (code.eval i x y t q ls)

theorem Compiled.translation (c : Compiled i array size before source) (x y : Int) (ls : List Int) :
    Relational.Translation (StreamAlternatives.RelatedAny array size before)
      (fun s => source.eval i x y s ls) (fun tq => c.code.eval i x y tq.1 tq.2 ls)
      (StreamAlternatives.RelatedAny array size c.after) := by
  intro s tq h
  obtain ⟨keys,hm,hr⟩ := h
  exact (c.correct keys hm s tq.1 tq.2 x y ls hr).asRel

/-- Check a single executable instruction against every incoming invariant.
    The continuation is not selected by a hidden runtime branch tag. -/
def atomic (i : Int) (array size : Nat) (source : HybridIR.MemoryCmd) :
    (before : List (List Int)) → Option (Compiled i array size before source)
  | [] => none
  | keys::rest => do
    let head ← HybridSender.compile i array size keys source
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
    exact Result.ofRel (Relational.seq (a.translation x y ls) (b.translation x y ls)
      s (t,q) ⟨keys,member,h⟩)

def branch (safe : HybridSafety.avoids array condition = true)
    (a : Compiled i array size before yes) (b : Compiled i array size before no) :
    Compiled i array size before (.branch condition yes no) where
  code := .branch condition a.code b.code
  after := a.after ++ b.after
  correct := by
    intro keys member s t q x y ls h
    let cs := fun s => (condition.eval i x y s ls []).map (fun v => v != 0)
    let ct := fun tq : State × List Int => cs tq.1
    have guards : ∀ s tq, StreamAlternatives.RelatedAny array size before s tq → cs s = ct tq := by
      intro s tq related
      obtain ⟨ks,hm,hr⟩ := related
      simp only [cs,ct,HybridSafety.read_correct condition safe hr.agree]
    have yesRule := Relational.consequence (a.translation x y ls)
      (fun s tq (hp : StreamAlternatives.RelatedAny array size before s tq ∧ cs s = some true) => hp.1)
      (fun s tq ⟨ks,hm,hr⟩ => show StreamAlternatives.RelatedAny array size (a.after ++ b.after) s tq from
        ⟨ks,List.mem_append_left _ hm,hr⟩)
    have noRule := Relational.consequence (b.translation x y ls)
      (fun s tq (hp : StreamAlternatives.RelatedAny array size before s tq ∧ cs s = some false) => hp.1)
      (fun s tq ⟨ks,hm,hr⟩ => show StreamAlternatives.RelatedAny array size (a.after ++ b.after) s tq from
        ⟨ks,List.mem_append_right _ hm,hr⟩)
    have result := Relational.branch_rule guards yesRule noRule s (t,q) ⟨keys,member,h⟩
    apply StreamAlternatives.Result.ofRel
    simpa [Relational.branch,cs,ct,HybridIR.MemoryCmd.eval,HybridIR.Cmd.eval,
      Option.bind_map,Function.comp_def,bne_iff_ne] using result

def compile (i : Int) (array size : Nat) (before : List (List Int)) :
    (source : HybridIR.MemoryCmd) → Option (Compiled i array size before source)
  | .seq a b => do
    let ca ← compile i array size before a
    let cb ← compile i array size ca.after b
    return sequence ca cb
  | .branch condition yes no =>
    if safe : HybridSafety.avoids array condition = true then do
      let a ← compile i array size before yes
      let b ← compile i array size before no
      return branch safe a b
    else none
  | .letValue e body =>
    if safe : HybridSafety.avoids array e = true then do
      let cb ← compile i array size before body
      return ⟨.letValue e cb.code,cb.after,by
        intro keys member s t q x y ls h
        simp only [HybridIR.MemoryCmd.eval,HybridIR.Cmd.eval,← HybridSafety.read_correct e safe h.agree]
        cases he : e.eval i x y s ls [] with
        | none => exact .none
        | some v => exact cb.correct keys member s t q x y (v::ls) h⟩
    else none
  | other => atomic i array size other before

end IRComparison.HybridAlternatives
