import IRComparison.Circuit.SystemVerilog.ConcreteAtoms
import IRComparison.Circuit.SystemVerilog.LiteralTextSound

namespace IRComparison.Circuit.SystemVerilog.Concrete

def expression : Expr → Tree
  | .reference n => .group .round [name n]
  | .index n a => .group .round [name n,.group .square [expression a]]
  | .integer n => signed (bits n+1) n (by omega)
  | .literal w n h => signed w (BitVec.ofInt w n).toNat h
  | .bit b => .group .brace [if b then atom "1'b1" else atom "1'b0"]
  | .unsigned a => .group .round [atom "$signed",
      .group .round [.group .brace [atom "1'b0",atom ",",expression a]]]
  | .cast w a _ => .group .round [atom "$signed",
      .group .round [natural w,atom "'",.group .round [expression a]]]
  | .binary op a b => .group .round [expression a,operator op,expression b]
  | .select c a b => .group .round [expression c,atom "?",expression a,atom ":",expression b]

def readLiteral (token : String) : Option Expr := do
  let (w,n) ← signedDecimal token
  if h : 0 < w then some (.literal w n h) else none

theorem read_signed (w n : Nat) (h : 0 < w) :
    readLiteral (toString w ++ "'sd" ++ toString n) = some (.literal w n h) := by
  unfold readLiteral
  rw [signedDecimal_print _ _ h]
  simp only [bind,Option.bind,dif_pos h]

/-- Interpret the native SV expression grammar after bracket reconstruction.
No expected expression is supplied to this function. -/
def readExpression : Tree → Option Expr
  | .atom w => readLiteral w.text
  | .group .brace [.atom ⟨"1'b0",_⟩] => some (.bit false)
  | .group .brace [.atom ⟨"1'b1",_⟩] => some (.bit true)
  | .group .round [.atom n] => (SystemVerilog.Name.parse n.text).map Expr.reference
  | .group .round [n,.group .square [a]] => do
      return .index (← readName n) (← readExpression a)
  | .group .round [.atom ⟨"$signed",_⟩,
      .group .round [.group .brace [.atom ⟨"1'b0",_⟩,.atom ⟨",",_⟩,a]]] => do
      return .unsigned (← readExpression a)
  | .group .round [.atom ⟨"$signed",_⟩,
      .group .round [w,.atom ⟨"'",_⟩,.group .round [a]]] => do
      let width ← readNatural w
      if positive : 0 < width then return .cast width (← readExpression a) positive else none
  | .group .round [a,op,b] => do
      return .binary (← readOperator op) (← readExpression a) (← readExpression b)
  | .group .round [c,.atom ⟨"?",_⟩,a,.atom ⟨":",_⟩,b] => do
      return .select (← readExpression c) (← readExpression a) (← readExpression b)
  | _ => none
termination_by t => sizeOf t

theorem expression_readback (e : Expr) : readExpression (expression e) = some e.literalReadback := by
  induction e with
  | reference n =>
    simp only [expression,name,atom,readExpression,SystemVerilog.Name.parse_text,Option.map_some,Expr.literalReadback]
  | index n a ih => simp only [expression,readExpression,read_name,ih,Expr.literalReadback]; rfl
  | integer n =>
    simp only [expression,signed,atom,readExpression,Expr.literalReadback]
    exact read_signed (bits n+1) n (by omega)
  | literal w n h =>
    simp only [expression,signed,atom,readExpression,Expr.literalReadback]
    exact read_signed w (BitVec.ofInt w n).toNat h
  | bit b => cases b <;> simp only [expression,atom,readExpression,Expr.literalReadback,Bool.false_eq_true,↓reduceIte]
  | unsigned a ih => simp only [expression,atom,readExpression,ih,Expr.literalReadback]; rfl
  | cast w a h ih =>
    simp only [expression,atom,readExpression,read_natural,bind,Option.bind,dif_pos h,ih,Expr.literalReadback]
    rfl
  | binary op a b ha hb =>
    simp only [expression,readExpression,read_operator,ha,hb,Expr.literalReadback]
    rfl
  | select c a b hc ha hb =>
    simp only [expression,atom,readExpression,hc,ha,hb,Expr.literalReadback]
    rfl

def printExpression (e : Expr) : String := print [expression e]
def parseExpression (text : String) : Option Expr := do
  let [tree] ← parse text | none
  readExpression tree

theorem parse_printExpression (e : Expr) : parseExpression (printExpression e) = some e.literalReadback := by
  unfold parseExpression printExpression
  rw [parse_print]
  exact expression_readback e

/-- Text-to-semantics connection for every expression and every context.
The parsed expression is evaluated by the existing SV subset evaluator. -/
theorem printExpression_eval (e : Expr) (env : Environment) (context : Option IntegralType) :
    (parseExpression (printExpression e)).bind (fun parsed => parsed.eval env context) =
      e.eval env context := by
  rw [parse_printExpression]
  exact e.literalReadback_eval env context

end IRComparison.Circuit.SystemVerilog.Concrete
