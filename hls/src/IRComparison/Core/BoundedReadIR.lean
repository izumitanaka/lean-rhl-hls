import IRComparison.Core.Common

namespace IRComparison.BoundedReadIR

inductive Imperative where | load deriving Repr
inductive Functional where | index deriving Repr

def Imperative.eval (_ : Imperative) (a : Array Int) (i : Nat) : Option Int := a[i]?
def Functional.eval (_ : Functional) (a : Array Int) (i : Nat) : Option Int := a[i]?

theorem imperative_correct (a : Array Int) (i : Fin a.size) (valid : i.val < a.size) :
    Imperative.load.eval a i.val = some (a[i]'valid) := by
  simp [Imperative.eval, valid]

theorem functional_correct (a : Array Int) (i : Fin a.size) (valid : i.val < a.size) :
    Functional.index.eval a i.val = some (a[i]'valid) := by
  simp [Functional.eval, valid]

end IRComparison.BoundedReadIR
