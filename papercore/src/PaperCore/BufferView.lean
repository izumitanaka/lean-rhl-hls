import PaperCore.AccessAnalysis
import PaperCore.AtomicRules

namespace PaperCore.BufferView
open AccessAnalysis

abbrev Slots := Array → Affine → Option Var

def View (slots : Slots) (counter : Int) (heap : Heap) (regs : Registers) : Prop :=
  ∀ array index buffer, slots array index = some buffer →
    ∃ value, heap.lookup (array,index.eval counter) = some value ∧ regs.lookup buffer = some value

def Fresh (slots : Slots) (ordinary : Var → Prop) : Prop :=
  ∀ array index buffer, slots array index = some buffer → ¬ ordinary buffer

def Typed (ordinary : Var → Prop) : Source Op → Prop
  | .assign x e => ordinary x ∧ e.ordinary ordinary
  | .action (.read x _ e) => ordinary x ∧ e.ordinary ordinary
  | .action (.write _ e x) => ordinary x ∧ e.ordinary ordinary
  | .seq a b => Typed ordinary a ∧ Typed ordinary b
  | .branch x a b => ordinary x ∧ Typed ordinary a ∧ Typed ordinary b
  | .loop x e _ _ body => ordinary x ∧ e.ordinary ordinary ∧ Typed ordinary body
  | .kernel body => Typed ordinary body

theorem view_set (fresh : Fresh slots ordinary) (view : View slots counter heap regs)
    (typed : ordinary dest) : View slots counter heap (put regs dest value) := by
  intro array index buffer found
  obtain ⟨v,cell,held⟩ := view array index buffer found
  have other : buffer ≠ dest := by intro same; subst buffer; exact fresh array index dest found typed
  exact ⟨v,cell,by simpa [lookup_put_other _ _ _ _ other] using held⟩

variable {Op : Type} {classify : Op → Option Arithmetic} {meaning : Op → Int → Int → Int}

theorem assign_env {env : Env} {e : Expr Op} (ops : ArithmeticSound classify meaning)
    (agrees : env.Matches regs counter) (value : e.eval meaning regs = some v) :
    (env.set x (infer classify env e)).Matches (put regs x v) counter := by
  cases hi : infer classify env e with
  | none => exact Env.matches_forget agrees v
  | some a =>
    have same := Option.some.inj (value.symm.trans (infer_sound ops agrees hi))
    subst v; exact Env.matches_set agrees


end PaperCore.BufferView
