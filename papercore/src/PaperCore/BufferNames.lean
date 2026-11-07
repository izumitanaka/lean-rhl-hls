import PaperCore.BufferView

namespace PaperCore.BufferNames

def exprVars : Expr Op → List Var
  | .num _ => []
  | .var x => [x]
  | .bin _ x y => [x,y]

def sourceVars : Source Op → List Var
  | .assign x e => x :: exprVars e
  | .action (.read x _ e) | .action (.write _ e x) => x :: exprVars e
  | .seq a b => sourceVars a ++ sourceVars b
  | .branch x a b => x :: (sourceVars a ++ sourceVars b)
  | .loop x e _ _ body => x :: (exprVars e ++ sourceVars body)
  | .kernel body => sourceVars body

theorem expr_typed (all : ∀ x ∈ exprVars e, ordinary x) : e.ordinary ordinary := by
  cases e <;> simp_all [exprVars,Expr.ordinary]

theorem source_typed (source : Source Op) (all : ∀ x ∈ sourceVars source, ordinary x) :
    BufferView.Typed ordinary source := by
  induction source with
  | assign x e => exact ⟨all x (by simp [sourceVars]),expr_typed (fun v hv => all v (by simp [sourceVars,hv]))⟩
  | action cmd => cases cmd <;>
      exact ⟨all _ (by simp [sourceVars]),expr_typed (fun v hv => all v (by simp [sourceVars,hv]))⟩
  | seq a b ia ib =>
    exact ⟨ia (fun v hv => all v (by simp [sourceVars,hv])),ib (fun v hv => all v (by simp [sourceVars,hv]))⟩
  | branch x a b ia ib =>
    exact ⟨all x (by simp [sourceVars]),ia (fun v hv => all v (by simp [sourceVars,hv])),
      ib (fun v hv => all v (by simp [sourceVars,hv]))⟩
  | loop x e stop step body ih =>
    exact ⟨all x (by simp [sourceVars]),expr_typed (fun v hv => all v (by simp [sourceVars,hv])),
      ih (fun v hv => all v (by simp [sourceVars,hv]))⟩
  | kernel body ih => exact ih all

def maxLength : List Var → Nat
  | [] => 0
  | x :: xs => max x.length (maxLength xs)

theorem length_le (member : x ∈ variables) : x.length ≤ maxLength variables := by
  induction variables with
  | nil => simp at member
  | cons y rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst x; exact Nat.le_max_left ..
    · exact Nat.le_trans (ih later) (Nat.le_max_right ..)

/-- Generated names are longer than every input name. No reserved prefix
    or forbidden user identifier is assumed. Distinct slots have distinct
    lengths; a more compact printable spelling can be substituted later. -/
def name (variables : List Var) (slot : Nat) : Var :=
  String.ofList (List.replicate (maxLength variables + 1 + slot) '_')

theorem name_length : (name variables slot).length = maxLength variables + 1 + slot := by
  simp [name]

theorem fresh : name variables slot ∉ variables := by
  intro member
  have bound := length_le member
  rw [name_length] at bound
  omega

theorem injective (same : name variables first = name variables second) : first = second := by
  have lengths := congrArg String.length same
  simp only [name_length] at lengths
  omega

#print axioms source_typed
#print axioms fresh
#print axioms injective
end PaperCore.BufferNames
