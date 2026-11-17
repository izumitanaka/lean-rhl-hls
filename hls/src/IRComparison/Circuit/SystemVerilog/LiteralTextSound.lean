import IRComparison.Circuit.SystemVerilog.Lexical
import IRComparison.Circuit.SystemVerilog.Eval

namespace IRComparison.Circuit.SystemVerilog

/-- Interpretation of a signed decimal token, obtained solely from its text.
The type and payload are read back; neither the source literal nor a callback
to the printer is available to this function. -/
def signedTokenValue (text : String) (context : Option IntegralType) : Option Value := do
  let (width,payload) ← signedDecimal text
  let ty : IntegralType := ⟨width,true⟩
  return (Value.ofInt ty payload).inContext (ty.context context)

theorem signedTokenValue_print (w n : Nat) (positive : 0 < w) (context : Option IntegralType) :
    signedTokenValue (toString w ++ "'sd" ++ toString n) context =
      some ((Value.ofInt ⟨w,true⟩ n).inContext ((IntegralType.mk w true).context context)) := by
  unfold signedTokenValue
  rw [signedDecimal_print w n positive]
  rfl

theorem Value.ofInt_bits (w : Nat) (n : Int) :
    Value.ofInt ⟨w,true⟩ (BitVec.ofInt w n).toNat = Value.ofInt ⟨w,true⟩ n := by
  unfold Value.ofInt
  congr 1
  simp only [BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The printed decimal payload may be positive even when the source literal
is negative. Parsing must first recover the *width*, then interpret the bits
as signed; parsing the payload as an unbounded integer would be incorrect. -/
theorem literal_text_eval (w : Nat) (n : Int) (positive : 0 < w)
    (env : Environment) (context : Option IntegralType) :
    signedTokenValue (Expr.literal w n positive).text context =
      (Expr.literal w n positive).eval env context := by
  change signedTokenValue (toString w ++ "'sd" ++ toString (BitVec.ofInt w n).toNat) context = _
  rw [signedTokenValue_print _ _ positive,Value.ofInt_bits]
  rfl

theorem integer_text_eval (n : Nat) (env : Environment) (context : Option IntegralType) :
    signedTokenValue (Expr.integer n).text context = (Expr.integer n).eval env context := by
  change signedTokenValue (toString (bits n+1) ++ "'sd" ++ toString n) context = _
  rw [signedTokenValue_print _ _ (by omega)]
  rfl


/-- A parser reads the literal's width and bit pattern, not the unbounded
integer that happened to be used when constructing the source AST. This
representation records that information loss without changing evaluation. -/
def Expr.literalReadback : Expr → Expr
  | .reference n => .reference n
  | .index n a => .index n a.literalReadback
  | .integer n => .literal (bits n+1) n (by omega)
  | .literal w n h => .literal w (BitVec.ofInt w n).toNat h
  | .bit b => .bit b
  | .unsigned a => .unsigned a.literalReadback
  | .cast w a h => .cast w a.literalReadback h
  | .binary op a b => .binary op a.literalReadback b.literalReadback
  | .select c a b => .select c.literalReadback a.literalReadback b.literalReadback

theorem Expr.literalReadback_type (e : Expr) (env : Environment) :
    e.literalReadback.type env = e.type env := by
  induction e <;> simp only [literalReadback,Expr.type, *]

theorem Expr.literalReadback_eval (e : Expr) (env : Environment) (context : Option IntegralType) :
    e.literalReadback.eval env context = e.eval env context := by
  induction e generalizing env context with
  | reference n => rfl
  | index n a ih => simp only [literalReadback,Expr.eval,Expr.type,ih]
  | integer n => rfl
  | literal w n h =>
    simp only [literalReadback,Expr.eval,Expr.type,Value.ofInt_bits]
  | bit b => rfl
  | unsigned a ih => simp only [literalReadback,Expr.eval,Expr.type,literalReadback_type,ih]
  | cast w a h ih => simp only [literalReadback,Expr.eval,Expr.type,literalReadback_type,ih]
  | binary op a b ha hb => simp only [literalReadback,Expr.eval,Expr.type,literalReadback_type,ha,hb]
  | select c a b hc ha hb => simp only [literalReadback,Expr.eval,Expr.type,literalReadback_type,hc,ha,hb]

end IRComparison.Circuit.SystemVerilog
