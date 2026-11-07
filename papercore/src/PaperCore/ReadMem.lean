import PaperCore.Correspondence

namespace PaperCore

/-- Both programs update the same ordinary variable. No heap or stream
    changes, so the index witness remains valid. -/
theorem Corresponds.setReg (h : Corresponds ordinary arrays source target indices)
    (x : Var) (value : Int) :
    Corresponds ordinary arrays (source.setReg x value) (target.setReg x value) indices := by
  constructor
  · intro y hy
    by_cases eq : y = x
    · subst y
      simp [State.setReg]
    · simpa [State.setReg,lookup_put_other _ _ _ _ eq] using h.registers y hy
  · exact h.streams

/-- The typing premise Gamma |- e : INT, without changing the expression
    grammar. In particular buffer-only variables are not source operands. -/
def Expr.ordinary (allowed : Var → Prop) : Expr Op → Prop
  | .num _ => True
  | .var x => allowed x
  | .bin _ x y => allowed x ∧ allowed y

theorem Corresponds.eval_eq (h : Corresponds ordinary arrays source target indices)
    (meaning : Op → Int → Int → Int) (e : Expr Op) (typed : e.ordinary ordinary) :
    e.eval meaning source.regs = e.eval meaning target.regs := by
  cases e with
  | num n => rfl
  | var x => exact h.registers x typed
  | bin op x y =>
    simp only [Expr.eval,h.registers x typed.1,h.registers y typed.2]

/-- Concrete output of the atomic Tr-ReadMem transformation. The caller
    must discharge the holding-value obligation; this function does not
    insert a FIFO read or assume that a buffer is initialized. -/
def readMem (dest buffer : Var) : Target Op := .assign dest (.var buffer)

/-- Structural state part of Tr-ReadMem. Assertions and their substitution
    are separate obligations, not hidden axioms of this lemma. -/
theorem readMem_correct (meaning : Op → Int → Int → Int)
    (h : Corresponds ordinary arrays source target indices)
    (address : e.eval meaning source.regs = some index)
    (cell : source.memory.lookup (a,index) = some value)
    (held : target.regs.lookup buffer = some value) :
    SourceExec meaning (.action (.read dest a e)) source (source.setReg dest value) ∧
    TargetExec meaning (readMem dest buffer) target (target.setReg dest value) ∧
    Corresponds ordinary arrays (source.setReg dest value) (target.setReg dest value) indices := by
  exact ⟨.action (.read address cell),.assign held,h.setReg dest value⟩

/-- Structural state part of Tr-Assign, over partial registers. -/
theorem assign_correct (meaning : Op → Int → Int → Int)
    (h : Corresponds ordinary arrays source target indices)
    (typed : e.ordinary ordinary)
    (value : e.eval meaning source.regs = some v) :
    SourceExec meaning (.assign dest e) source (source.setReg dest v) ∧
    TargetExec meaning (.assign dest e) target (target.setReg dest v) ∧
    Corresponds ordinary arrays (source.setReg dest v) (target.setReg dest v) indices := by
  have targetValue : e.eval meaning target.regs = some v := by
    rw [← h.eval_eq meaning e typed]
    exact value
  exact ⟨.assign value,.assign targetValue,h.setReg dest v⟩

#print axioms readMem_correct
#print axioms assign_correct
end PaperCore
