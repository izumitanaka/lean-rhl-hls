import IRComparison.Hybrid.HybridSource

namespace IRComparison.HybridIR

/-- Declared array identifiers used by a read. Index values contain no array
reads; those are explicit `ReadCode` nodes. -/
def ReadCode.ArraysWithin (allowed : Nat → Prop) : ReadCode → Prop
  | .pure _ | .register _ => True
  | .memory a _ => allowed a
  | .bind a b | .branch _ a b => a.ArraysWithin allowed ∧ b.ArraysWithin allowed

/-- Reference closure of existing commands, independent of any compiler or
layout check. Conditions and zero-trip loop bodies are included. -/
def Cmd.ArraysWithin (allowed : Nat → Prop) : Cmd → Prop
  | .skip => True
  | .assign _ e | .send e => e.ArraysWithin allowed
  | .store a j e => allowed a ∧ j.ArraysWithin allowed ∧ e.ArraysWithin allowed
  | .letValue e b | .forRange e b => e.ArraysWithin allowed ∧ b.ArraysWithin allowed
  | .seq a b => a.ArraysWithin allowed ∧ b.ArraysWithin allowed
  | .branch e a b => e.ArraysWithin allowed ∧ a.ArraysWithin allowed ∧ b.ArraysWithin allowed
  | .repeat _ b => b.ArraysWithin allowed

theorem ReadCode.ArraysWithin.mono {e : ReadCode} {allowed extended : Nat → Prop} (h : e.ArraysWithin allowed) (more : ∀ n, allowed n → extended n) :
    e.ArraysWithin extended := by
  induction e <;> simp_all [ArraysWithin]

theorem Cmd.ArraysWithin.mono {c : Cmd} {allowed extended : Nat → Prop} (h : c.ArraysWithin allowed) (more : ∀ n, allowed n → extended n) :
    c.ArraysWithin extended := by
  induction c with
  | skip => trivial
  | assign | send => exact ReadCode.ArraysWithin.mono h more
  | store => exact ⟨more _ h.1,ReadCode.ArraysWithin.mono h.2.1 more,ReadCode.ArraysWithin.mono h.2.2 more⟩
  | letValue _ _ ih | forRange _ _ ih => exact ⟨ReadCode.ArraysWithin.mono h.1 more,ih h.2⟩
  | seq _ _ a b => exact ⟨a h.1,b h.2⟩
  | branch _ _ _ a b => exact ⟨ReadCode.ArraysWithin.mono h.1 more,a h.2.1,b h.2.2⟩
  | «repeat» _ _ ih => exact ih h

end IRComparison.HybridIR
