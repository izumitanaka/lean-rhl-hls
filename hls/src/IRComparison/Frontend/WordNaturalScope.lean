import IRComparison.Frontend.WordScalarSyntax

/-! Scope construction for the natural counter introduced by List.range.
The counter remains a Nat in the native function. Its retained scalar value
is checked at Word using the existing BitVec alias conversion. -/
namespace IRComparison.WordFrontend.NaturalScope
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic

def ofNatSignature : VExpr := .forallE natType
  (.forallE natType (.app (.const ``BitVec []) (.bvar 1)))

def index (n : VExpr) : VExpr := applications (.const ``BitVec.ofNat []) [width,n]
def nativeIndex (n : Lean.Expr) : Lean.Expr := app ``BitVec.ofNat [nativeWidth,n]

theorem index_represents (h : Represents n core) : Represents (nativeIndex n) (index core) :=
  .app (.app (.constant rfl) width_represents) h

theorem index_inferred (library : Arithmetic.Signatures env)
    (registered : env.constants ``BitVec.ofNat = some ⟨0,ofNatSignature⟩)
    (value : DirectTyping env 0 ctx n natType) :
    CastTyping env 0 Arithmetic.Casts ctx (index n) bitvecType := by
  have fn : CastTyping env 0 Arithmetic.Casts ctx (.const ``BitVec.ofNat []) ofNatSignature :=
    .constant registered (by simp) rfl
  have first := CastTyping.application fn (library.width_typed.withCasts _)
  simp only [ofNatSignature,natType,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ] at first
  have second := CastTyping.application first (value.withCasts _)
  simpa only [index,applications,bitvecType,VExpr.inst,VExpr.inst_lift, width_closed.instN_eq (Nat.zero_le _)] using second

theorem index_checked (library : Arithmetic.Signatures env)
    (registered : env.constants ``BitVec.ofNat = some ⟨0,ofNatSignature⟩)
    (value : DirectTyping env 0 ctx n natType) :
    CheckedTyping env 0 Arithmetic.Casts ctx (index n) wordType :=
  .converted (index_inferred library registered value) .bitvecValue

/-- Derive the complete locals-list typing when retaining a converted natural
counter; no parsing-success assumption or bound on the counter is needed. -/
def retain (inputs : InputsTyped env ctx p) (library : Arithmetic.Signatures env)
    (registered : env.constants ``BitVec.ofNat = some ⟨0,ofNatSignature⟩)
    (consDeclared : env.constants ``List.cons = some consSignature)
    (represented : Represents n core) (typed : DirectTyping env 0 ctx core natType) :
    InputsTyped env ctx {p with locals := nativeIndex n :: p.locals} :=
  inputs.withLocal (index_represents represented) (index_checked library registered typed)
    library.word consDeclared

def retainLocals (scope : ScalarSyntax.Locals env ctx p) (library : Arithmetic.Signatures env)
    (registered : env.constants ``BitVec.ofNat = some ⟨0,ofNatSignature⟩)
    (represented : Represents n core) (typed : DirectTyping env 0 ctx core natType) :
    ScalarSyntax.Locals env ctx {p with locals := nativeIndex n :: p.locals} :=
  scope.withLocal (index_represents represented) (index_checked library registered typed)

def forInParameters (p : Inputs) : Inputs :=
  {p.lift.lift with s := .bvar 0, locals := nativeIndex (.bvar 1) :: p.lift.lift.locals}

def foldParameters (p : Inputs) : Inputs :=
  {p.lift.lift with s := .bvar 1, locals := nativeIndex (.bvar 0) :: p.lift.lift.locals}

/-- These are the actual two binder orders used by forIn and foldlM. They
introduce neither an execution bound nor a new source-level variable. -/
def forInInputs (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    (library : Arithmetic.Signatures env)
    (registered : env.constants ``BitVec.ofNat = some ⟨0,ofNatSignature⟩)
    (consDeclared : env.constants ``List.cons = some consSignature) :
    InputsTyped env (stateType::natType::ctx) (forInParameters p) :=
  retain ((inputs.lift closed natType).nextState closed) library registered consDeclared
    .bvar (.bvar (.succ .zero))

def forInLocals (scope : ScalarSyntax.Locals env ctx p) (closed : ClosedConstantTypes env)
    (library : Arithmetic.Signatures env)
    (registered : env.constants ``BitVec.ofNat = some ⟨0,ofNatSignature⟩) :
    ScalarSyntax.Locals env (stateType::natType::ctx) (forInParameters p) :=
  retainLocals ((scope.lift closed natType).nextState closed) library registered
    .bvar (.bvar (.succ .zero))

def foldInputs (inputs : InputsTyped env ctx p) (closed : ClosedConstantTypes env)
    (library : Arithmetic.Signatures env)
    (registered : env.constants ``BitVec.ofNat = some ⟨0,ofNatSignature⟩)
    (consDeclared : env.constants ``List.cons = some consSignature) :
    InputsTyped env (natType::stateType::ctx) (foldParameters p) :=
  retain ((inputs.nextState closed).lift closed natType) library registered consDeclared
    .bvar (.bvar .zero)

def foldLocals (scope : ScalarSyntax.Locals env ctx p) (closed : ClosedConstantTypes env)
    (library : Arithmetic.Signatures env)
    (registered : env.constants ``BitVec.ofNat = some ⟨0,ofNatSignature⟩) :
    ScalarSyntax.Locals env (natType::stateType::ctx) (foldParameters p) :=
  retainLocals ((scope.nextState closed).lift closed natType) library registered
    .bvar (.bvar .zero)

end IRComparison.WordFrontend.NaturalScope
