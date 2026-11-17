import IRComparison.Hybrid.HybridSource

/-! Structural RHL rules for the existing mixed IR. Relations are arbitrary;
neither FIFO index-list templates nor window selection are baked into them.
The source/target syntax and executable evaluators are unchanged. -/
namespace IRComparison.HybridRules
open HybridIR

abbrev Relation := State → (State × List Int) → Prop

def Translation (i x y : Int) (locals : List Int) (P : Relation)
    (source : MemoryCmd) (target : Cmd) (Q : Relation) : Prop :=
  Relational.Translation P (fun s => source.eval i x y s locals)
    (fun t => target.eval i x y t.1 t.2 locals) Q

theorem seq (a : Translation i x y ls P s t R) (b : Translation i x y ls R s' t' Q) :
    Translation i x y ls P (.seq s s') (.seq t t') Q := Relational.seq a b

theorem consequence (body : Translation i x y ls P s t Q)
    (pre : ∀ a b, P' a b → P a b) (post : ∀ a b, Q a b → Q' a b) :
    Translation i x y ls P' s t Q' := Relational.consequence body pre post

theorem letValue (values : ∀ s t, P s t → e.eval i x y s ls [] = f.eval i x y t.1 ls [])
    (body : ∀ v, Translation i x y (v::ls) P a b Q) :
    Translation i x y ls P (.letValue e a) (.letValue f b) Q := by
  intro s t hp
  have eq := values s t hp
  simp only [MemoryCmd.eval,Cmd.eval,← eq]
  cases he : e.eval i x y s ls [] with
  | none => exact .none
  | some v => exact body v s t hp

theorem repeat_rule (body : Translation i x y ls P a b P) (n : Nat) :
    Translation i x y ls P (.repeat n a) (.repeat n b) P :=
  Relational.fold_rule (fun _ => body) (List.range n)

/-- Both bounds are evaluated once. Each iteration receives its ordinal as
a local binding; source and target may use different bodies and states. -/
theorem forRange
    (bounds : ∀ s t, P s t → e.eval i x y s ls [] = f.eval i x y t.1 ls [])
    (body : ∀ k : Nat, Translation i x y (Int.ofNat k::ls) P a b P) :
    Translation i x y ls P (.forRange e a) (.forRange f b) P := by
  intro s t hp
  have eq := bounds s t hp
  simp only [MemoryCmd.eval,Cmd.eval,← eq]
  cases he : e.eval i x y s ls [] with
  | none => exact .none
  | some n => exact Relational.fold_rule body (List.range n.toNat) s t hp

end IRComparison.HybridRules
