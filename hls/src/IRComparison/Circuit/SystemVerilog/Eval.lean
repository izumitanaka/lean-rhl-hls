import IRComparison.Circuit.SystemVerilog.Syntax

namespace IRComparison.Circuit.SystemVerilog

/-- Two-state integral type. Declaration types and expression context are
kept separate: an unsigned assignment destination does not by itself change
the self-determined signedness of its RHS. -/
structure IntegralType where
  width : Nat
  signed : Bool
  deriving Repr, DecidableEq

structure Value where
  type : IntegralType
  bits : BitVec type.width
  deriving Repr

def Value.integer (v : Value) : Int := if v.type.signed then v.bits.toInt else v.bits.toNat

def Value.ofInt (t : IntegralType) (n : Int) : Value := ⟨t,BitVec.ofInt t.width n⟩

/-- Conversion of a context-determined operand: unsigned contexts zero extend;
sign extension is used only when both the operand and context are signed. -/
def Value.inContext (v : Value) (t : IntegralType) : Value :=
  .ofInt t (if v.type.signed && t.signed then v.bits.toInt else v.bits.toNat)

def IntegralType.join (a b : IntegralType) : IntegralType :=
  ⟨max a.width b.width,a.signed && b.signed⟩

def IntegralType.context (natural : IntegralType) (given : Option IntegralType) : IntegralType :=
  match given with
  | none => natural
  | some outer => ⟨max natural.width outer.width,outer.signed⟩

structure Environment where
  type : Name → IntegralType
  scalar : Name → Option Int
  cell : Name → Nat → Option Int

def Operator.comparison : Operator → Bool
  | .lt | .ge | .eq | .ne => true
  | _ => false

def Expr.type (env : Environment) : Expr → IntegralType
  | .reference n | .index n _ => env.type n
  | .integer n => ⟨bits n+1,true⟩
  | .literal w _ _ => ⟨w,true⟩
  | .bit _ => ⟨1,false⟩
  | .unsigned e => ⟨(e.type env).width+1,true⟩
  | .cast w _ _ => ⟨w,true⟩
  | .binary op a b => if op.comparison || op == .and then ⟨1,false⟩ else (a.type env).join (b.type env)
  | .select _ a b => (a.type env).join (b.type env)

def truth (v : Bool) : Value := .ofInt ⟨1,false⟩ (if v then 1 else 0)

def arithmetic (op : Operator) (a b : Int) : Option Int :=
  match op with
  | .add => some (a+b)
  | .sub => some (a-b)
  | .mul => some (a*b)
  | .div => if b = 0 then none else some (a.tdiv b)
  | .mod => if b = 0 then none else some (a.tmod b)
  | .lt => some (if a < b then 1 else 0)
  | .ge => some (if a ≥ b then 1 else 0)
  | .eq => some (if a = b then 1 else 0)
  | .ne => some (if a ≠ b then 1 else 0)
  | .and => some (if a ≠ 0 ∧ b ≠ 0 then 1 else 0)

/-- Expression evaluation with downward width/signedness propagation.
Undefined array reads and division by zero are outside the defined two-state
fragment; guarding them is a code-generation proof obligation. A missing
value is not silently converted to a successful zero result. -/
def Expr.eval (env : Environment) (context : Option IntegralType) (e : Expr) : Option Value := do
  let ty := (e.type env).context context
  match e with
  | .reference n => return (Value.ofInt (env.type n) (← env.scalar n)).inContext ty
  | .index n addressTerm =>
      let j := (← addressTerm.eval env none).integer
      if j < 0 then none else
        return (Value.ofInt (env.type n) (← env.cell n j.toNat)).inContext ty
  | .integer n => return (Value.ofInt (e.type env) n).inContext ty
  | .literal w n _ => return (Value.ofInt ⟨w,true⟩ n).inContext ty
  | .bit b => return (truth b).inContext ty
  | .unsigned a =>
      let v ← a.eval env none
      return (Value.ofInt (e.type env) v.bits.toNat).inContext ty
  | .cast w a _ =>
      let v ← a.eval env (some ⟨w,(a.type env).signed⟩)
      return (Value.ofInt ⟨w,true⟩ v.integer).inContext ty
  | .select c a b =>
      let condition ← c.eval env none
      if condition.integer != 0 then a.eval env (some ty) else b.eval env (some ty)
  | .binary op a b =>
      if op == .and then
        let av ← a.eval env none
        if av.integer = 0 then return (truth false).inContext ty
        let bv ← b.eval env none
        return (truth (bv.integer != 0)).inContext ty
      else if op.comparison then
        let operands := (a.type env).join (b.type env)
        let av ← a.eval env (some operands)
        let bv ← b.eval env (some operands)
        return (Value.ofInt ⟨1,false⟩ (← arithmetic op av.integer bv.integer)).inContext ty
      else
        let av ← a.eval env (some ty)
        let bv ← b.eval env (some ty)
        return Value.ofInt ty (← arithmetic op av.integer bv.integer)

/-- Destination width supplies a width context; its signedness does not
replace the RHS expression's signedness. Stored bits are then truncated. -/
def Expr.assignment (env : Environment) (width : Nat) (e : Expr) : Option (BitVec width) := do
  let v ← e.eval env (some ⟨width,(e.type env).signed⟩)
  return BitVec.ofInt width v.integer

end IRComparison.Circuit.SystemVerilog
