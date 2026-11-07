import IRComparison.Frontend.LeanFunctionNormalization
import IRComparison.Frontend.LeanSelectValue

namespace IRComparison.LeanIRQuotation
open Lean4Lean LeanTyped

/-- Quote the actual output IR as a value of its existing Lean datatype. This
    does not introduce another target language or reinterpret its evaluator. -/
def quote : Expr → Lean.Expr
  | .lit n => .app (.const ``Expr.lit []) (LeanBindings.quoteInt n)
  | .index => .const ``Expr.index []
  | .left => .const ``Expr.left []
  | .right => .const ``Expr.right []
  | .local r => .app (.const ``Expr.local []) (.lit (.natVal r))
  | .natIndex e => .app (.const ``Expr.natIndex []) (quote e)
  | .reg r => .app (.const ``Expr.reg []) (.lit (.natVal r))
  | .add a b => .app (.app (.const ``Expr.add []) (quote a)) (quote b)
  | .sub a b => .app (.app (.const ``Expr.sub []) (quote a)) (quote b)
  | .mul a b => .app (.app (.const ``Expr.mul []) (quote a)) (quote b)
  | .div a b => .app (.app (.const ``Expr.div []) (quote a)) (quote b)
  | .select c a b => .app (.app (.app (.const ``Expr.select []) (quote c)) (quote a)) (quote b)
  | .read a i => .app (.app (.const ``Expr.read []) (.lit (.natVal a))) (quote i)

def code : Expr → VExpr
  | .lit n => .app (.const ``Expr.lit []) (integer n)
  | .index => .const ``Expr.index []
  | .left => .const ``Expr.left []
  | .right => .const ``Expr.right []
  | .local r => .app (.const ``Expr.local []) (numeral r)
  | .natIndex e => .app (.const ``Expr.natIndex []) (code e)
  | .reg r => .app (.const ``Expr.reg []) (numeral r)
  | .add a b => .app (.app (.const ``Expr.add []) (code a)) (code b)
  | .sub a b => .app (.app (.const ``Expr.sub []) (code a)) (code b)
  | .mul a b => .app (.app (.const ``Expr.mul []) (code a)) (code b)
  | .div a b => .app (.app (.const ``Expr.div []) (code a)) (code b)
  | .select c a b => .app (.app (.app (.const ``Expr.select []) (code c)) (code a)) (code b)
  | .read a i => .app (.app (.const ``Expr.read []) (numeral a)) (code i)

theorem code_represents (e : Expr) : Represents (quote e) (code e) := by
  induction e with
  | lit n => exact .app (.constant rfl) (integer_represents n)
  | index | left | right => exact .constant rfl
  | «local» r => exact .app (.constant rfl) .natural
  | natIndex e ih => exact .app (.constant rfl) ih
  | reg r => exact .app (.constant rfl) .natural
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb =>
      exact .app (.app (.constant rfl) ha) hb
  | select c a b hc ha hb => exact .app (.app (.app (.constant rfl) hc) ha) hb
  | read a i hi => exact .app (.app (.constant rfl) .natural) hi

def optionInt : VExpr := .app (.const ``Option [.zero]) intType
def someInt (v : VExpr) : VExpr := .app (.app (.const ``Option.some [.zero]) intType) v
def intList : VExpr := .app (.const ``List [.zero]) intType
@[reducible] def nilInts : VExpr := .app (.const ``List.nil [.zero]) intType
@[reducible] def consInts (x xs : VExpr) : VExpr := applications (.const ``List.cons [.zero]) [intType,x,xs]
def eval (e i x y s : VExpr) (locals : VExpr := nilInts) : VExpr :=
  applications (.const ``Expr.eval []) [i,x,y,s,e,locals]
def eqResult (a b : VExpr) : VExpr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) optionInt) a) b

namespace Facts

/-- Fixed library facts about the actual IR evaluator, proved for every
    expression/state/input. They are not per-source-program equivalence tests. -/
theorem literal (n i x y : Int) (s : State) : (Expr.lit n).eval i x y s = some n := rfl
theorem index (i x y : Int) (s : State) : Expr.index.eval i x y s = some i := rfl
theorem left (i x y : Int) (s : State) : Expr.left.eval i x y s = some x := rfl
theorem right (i x y : Int) (s : State) : Expr.right.eval i x y s = some y := rfl

theorem add (a b : Expr) (i x y : Int) (s : State) (v w : Int)
    (ha : a.eval i x y s = some v) (hb : b.eval i x y s = some w) :
    (Expr.add a b).eval i x y s = some (Int.add v w) := by simp [Expr.eval, ha, hb] <;> rfl
theorem sub (a b : Expr) (i x y : Int) (s : State) (v w : Int)
    (ha : a.eval i x y s = some v) (hb : b.eval i x y s = some w) :
    (Expr.sub a b).eval i x y s = some (Int.sub v w) := by simp [Expr.eval, ha, hb] <;> rfl
theorem mul (a b : Expr) (i x y : Int) (s : State) (v w : Int)
    (ha : a.eval i x y s = some v) (hb : b.eval i x y s = some w) :
    (Expr.mul a b).eval i x y s = some (Int.mul v w) := by simp [Expr.eval, ha, hb] <;> rfl
theorem div (a b : Expr) (i x y : Int) (s : State) (v w : Int)
    (ha : a.eval i x y s = some v) (hb : b.eval i x y s = some w) :
    (Expr.div a b).eval i x y s = some (Int.ediv v w) := by simp [Expr.eval, ha, hb] <;> rfl
theorem select (c a b : Expr) (i x y : Int) (s : State) (v yes no : Int)
    (hc : c.eval i x y s = some v) (ha : a.eval i x y s = some yes)
    (hb : b.eval i x y s = some no) :
    (Expr.select c a b).eval i x y s = some (selectValue v yes no) := by
  by_cases h : v = 0 <;> simp [Expr.eval, selectValue, hc, ha, hb, h]

end Facts
end IRComparison.LeanIRQuotation
