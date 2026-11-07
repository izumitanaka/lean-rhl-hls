import IRComparison.Circuit.SystemVerilog.Eval

namespace IRComparison.Circuit.SystemVerilog

/-- Temporary references in a net may refer only to the already declared
prefix. Physical names are governed separately by the hardware layout. -/
def Name.Before (limit : Nat) : Name → Prop
  | .temporary n => n < limit
  | _ => True

def Expr.Before (limit : Nat) : Expr → Prop
  | .reference n => n.Before limit
  | .index n addressTerm => n.Before limit ∧ addressTerm.Before limit
  | .integer _ | .literal .. | .bit _ => True
  | .unsigned e | .cast _ e _ => e.Before limit
  | .binary _ a b => a.Before limit ∧ b.Before limit
  | .select c a b => c.Before limit ∧ a.Before limit ∧ b.Before limit

structure Environment.AgreesBefore (limit : Nat) (a b : Environment) : Prop where
  types : ∀ n, n.Before limit → a.type n = b.type n
  scalars : ∀ n, n.Before limit → a.scalar n = b.scalar n
  cells : ∀ n, n.Before limit → a.cell n = b.cell n

theorem Name.before_mono {n : Name} (h : n.Before k) (larger : k ≤ m) : n.Before m := by
  cases n <;> simp_all [Before] <;> omega

theorem Expr.before_mono (e : Expr) (h : e.Before k) (larger : k ≤ m) : e.Before m := by
  induction e <;> simp_all [Before]
  · exact Name.before_mono h larger
  · exact Name.before_mono h.1 larger

theorem Expr.type_agrees (e : Expr) (scope : e.Before limit)
    (same : Environment.AgreesBefore limit a b) : e.type a = e.type b := by
  induction e with
  | reference n => exact same.types n scope
  | index n addressTerm ih => exact same.types n scope.1
  | integer | literal | bit | cast => rfl
  | unsigned e ih => simp only [type,ih scope]
  | binary op left right ihL ihR => simp only [type,ihL scope.1,ihR scope.2]
  | select c left right ihC ihL ihR => simp only [type,ihL scope.2.1,ihR scope.2.2]

/-- Growing a declaration/value prefix cannot change an already emitted
expression. Both its inferred type and downward evaluation context matter. -/
theorem Expr.eval_agrees (e : Expr) (scope : e.Before limit)
    (same : Environment.AgreesBefore limit a b) (context : Option IntegralType) :
    e.eval a context = e.eval b context := by
  induction e generalizing context with
  | reference n =>
    simp only [eval,Expr.type,same.types n scope,same.scalars n scope]
  | index n addressTerm ih =>
    rw [eval,eval]
    simp only [Expr.type_agrees _ scope same,ih scope.2,same.types n scope.1,same.cells n scope.1]
  | integer | literal | bit => rfl
  | unsigned e ih =>
    rw [eval,eval]
    simp only [Expr.type_agrees _ scope same,ih scope]
  | cast w e positive ih =>
    rw [eval,eval]
    simp only [Expr.type_agrees _ scope same,e.type_agrees scope same,ih scope]
  | binary op left right ihL ihR =>
    rw [eval,eval]
    simp only [Expr.type_agrees _ scope same,left.type_agrees scope.1 same,right.type_agrees scope.2 same,
      ihL scope.1,ihR scope.2]
  | select c left right ihC ihL ihR =>
    rw [eval,eval]
    simp only [Expr.type_agrees _ scope same,ihC scope.1,
      ihL scope.2.1,ihR scope.2.2]

theorem Expr.assignment_agrees (e : Expr) (scope : e.Before limit)
    (same : Environment.AgreesBefore limit a b) (width : Nat) :
    e.assignment a width = e.assignment b width := by
  simp only [assignment,e.type_agrees scope same,e.eval_agrees scope same]

end IRComparison.Circuit.SystemVerilog
