import IRComparison.Frontend.WordArithmeticConversion


namespace IRComparison.WordFrontend.Arithmetic
open Lean4Lean LeanTyped LeanTypeInference Certificate

def binaryFirstPremise : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 8))
  (someValue wordType (.bvar 1))
def binarySecondPremise : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 7) (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 8))
  (someValue wordType (.bvar 1))
def Binary.result (op : Binary) : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 8) (.bvar 7) (.bvar 6) (.bvar 5) (.bvar 4)
    (applications (.const op.target []) [.bvar 10,.bvar 9]))
  (someValue wordType (applications op.header [.bvar 3,.bvar 2]))
def Binary.signature (op : Binary) : VExpr :=
  .forallE exprType (.forallE exprType (inputsType
    (.forallE wordType (.forallE wordType
      (.forallE binaryFirstPremise (.forallE binarySecondPremise op.result))))))

theorem Binary.header_inst (op : Binary) (arg : VExpr) (n : Nat) : op.header.inst arg n = op.header :=
  op.header_closed.instN_eq (Nat.zero_le n)

theorem binary_typed (inputs : InputsTyped env ctx p) [inputs.CastLocals casts]
    {a : Piece env ctx p u scalarExpected} {b : Piece env ctx p v scalarExpected}
    (left : ScalarCasts inputs a casts) (right : ScalarCasts inputs b casts) (op : Binary)
    (registered : env.constants op.fact = some ⟨0,op.signature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const op.fact [])
        ([a.represented.val,b.represented.val] ++ inputs.args ++
          [left.sourceCore.val,right.sourceCore.val,a.checked.proofCore.val,b.checked.proofCore.val]))
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val
          (applications (.const op.target []) [a.represented.val,b.represented.val]))
        (someValue wordType (applications op.header [left.sourceCore.val,right.sourceCore.val]))) := by
  have fact : CastTyping env 0 casts ctx (.const op.fact []) op.signature :=
    by
      have h := CastTyping.constant (casts := casts) (ctx := ctx) (U := 0) (levels := [])
        registered (by simp) rfl
      simpa [Binary.signature,Binary.result,Binary.header,Binary.dictionary,
        binaryFirstPremise,binarySecondPremise,inputsType,exprType,wordType,stateType,wordsType,
        equalValues,optionType,scalarValue,someValue,applications,VExpr.instL,
        VLevel.inst,width,natType,numeral] using h
  unfold Binary.signature at fact
  have a1 := CastTyping.application fact left.target
  simp only [inputsType,exprType,wordType,stateType,wordsType,VExpr.inst] at a1
  have a2 := CastTyping.application a1 right.target
  simp only [VExpr.inst] at a2
  have a3 := inputs.apply_casts a2
  simp only [InputsTyped.instantiate,binaryFirstPremise,binarySecondPremise,Binary.result,
    scalarValue,equalValues,optionType,wordType,someValue,applications,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ,Binary.header_inst] at a3
  have a4 := CastTyping.checkedApplication a3 left.value
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,Binary.header_inst] at a4
  have a5 := CastTyping.checkedApplication a4 right.value
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,Binary.header_inst] at a5
  have a6 := CastTyping.application a5 left.equality
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,Binary.header_inst] at a6
  simpa only [InputsTyped.args,applications,List.cons_append,List.nil_append,
    scalarValue,equalValues,optionType,wordType,someValue,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ,Binary.header_inst] using
    CastTyping.application a6 right.equality

/-- The exact certificate assembled by the production binary-expression branch.
The two child invariants compose for arbitrary subexpressions. -/
theorem binary_finish (inputs : InputsTyped env ctx p) [inputs.CastLocals casts]
    {a : Piece env ctx p u scalarExpected} {b : Piece env ctx p v scalarExpected}
    (left : ScalarCasts inputs a casts) (right : ScalarCasts inputs b casts) (op : Binary)
    (registered : env.constants op.fact = some ⟨0,op.signature⟩)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (scalarExpected p (app op.target [a.code,b.code]) (Lean.mkApp2 op.nativeHeader u v))
      (app op.target [a.code,b.code])
      (app op.fact ([a.code,b.code] ++ p.args ++ [u,v,a.checked.proof,b.checked.proof]))
      (a.checked.known.orElse b.checked.known) = some result ∧
      CastTyping env 0 casts ctx result.proofCore.val result.core.val ∧
      result.code = app op.target [a.code,b.code] ∧
      result.proof = app op.fact ([a.code,b.code] ++ p.args ++ [u,v,a.checked.proof,b.checked.proof]) := by
  have targetRep := app_represents (f := Lean.Expr.const op.target []) (.constant rfl)
    (.cons a.represented.property (.cons b.represented.property .nil))
  have sourceRep := Represents.app (Represents.app op.header_represents left.sourceCore.property)
    right.sourceCore.property
  have proofRep := app_represents (f := Lean.Expr.const op.fact []) (.constant rfl)
    (.cons a.represented.property (.cons b.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property (.cons left.sourceCore.property
          (.cons right.sourceCore.property (.cons a.checked.proofCore.property
            (.cons b.checked.proofCore.property .nil)))))))))))
  exact finish_cast_complete (scalarExpected_represents inputs targetRep sourceRep)
    proofRep (binary_typed inputs left right op registered)
    ((known_casts a.checked left.proof).orElse (known_casts b.checked right.proof)) coverage exposure _

theorem binary_value_typed (signatures : Signatures env) (op : Binary)
    (left : CheckedTyping env 0 Casts ctx u wordType) (right : CheckedTyping env 0 Casts ctx v wordType) :
    CastTyping env 0 Casts ctx (.app (.app op.header u) v) wordType := by
  have first := CastTyping.checkedApplication (signatures.header_typed op) left
  simp only [wordType,VExpr.inst] at first
  exact .checkedApplication first right

/-- The concrete converter, including nested Word/BitVec conversions, accepts
arbitrary well-typed operand derivations. There is no assumed conversion hit. -/
theorem binary_value_checked (setup : AliasSetup env) (signatures : Signatures env) (op : Binary)
    (left : CheckedTyping env 0 Casts ctx u wordType) (right : CheckedTyping env 0 Casts ctx v wordType)
    (coherent : KnownTypes.Casts known Casts) (exposure : Exposure env) :
    ∃ checked, checkWith env setup.conversion 0 ctx (.app (.app op.header u) v) wordType
      exposure known = some checked :=
  (binary_value_typed signatures op left right).check_complete coherent (setup.covers signatures) exposure


def literalSignature : VExpr := .forallE wordType (inputsType
  (equalValues (optionType wordType)
    (scalarValue (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0)
      (.app (.const ``HybridWord.Expr.lit []) (.bvar 5)))
    (someValue wordType (.bvar 5))))

theorem literal_typed (inputs : InputsTyped env ctx p) (signatures : Signatures env)
    (registered : env.constants ``WordFrontendFacts.literal = some ⟨0,literalSignature⟩) (n : Nat) :
    CastTyping env 0 Casts ctx
      (applications (.const ``WordFrontendFacts.literal []) (literalTerm n :: inputs.args))
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val
          (.app (.const ``HybridWord.Expr.lit []) (literalTerm n)))
        (someValue wordType (literalTerm n))) := by
  have fact : CastTyping env 0 Casts ctx (.const ``WordFrontendFacts.literal []) literalSignature :=
    .constant registered (by simp) rfl
  have first := CastTyping.application fact (signatures.literal_typed n)
  simp only [literalSignature,inputsType,wordType,stateType,wordsType,VExpr.inst] at first
  simpa only [InputsTyped.instantiate,scalarValue,equalValues,optionType,wordType,someValue,applications,
    Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ] using inputs.apply_casts first

theorem literal_finish (inputs : InputsTyped env ctx p) (signatures : Signatures env)
    (registered : env.constants ``WordFrontendFacts.literal = some ⟨0,literalSignature⟩) (n : Nat)
    (coverage : Conversion.Covers conv 0 Casts) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (scalarExpected p (app ``HybridWord.Expr.lit [nativeLiteral n]) (nativeLiteral n))
      (app ``HybridWord.Expr.lit [nativeLiteral n])
      (app ``WordFrontendFacts.literal (nativeLiteral n :: p.args)) = some result ∧
      CastTyping env 0 Casts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Expr.lit [nativeLiteral n] ∧
      result.proof = app ``WordFrontendFacts.literal (nativeLiteral n :: p.args) := by
  exact finish_cast_complete (scalarExpected_represents inputs
    (.app (.constant rfl) (literal_represents n)) (literal_represents n))
    (app_represents (.constant rfl) (.cons (literal_represents n) inputs.arguments))
    (literal_typed inputs signatures registered n)
    (known := noKnownTypes env 0) (by intro _ _ _ h; cases h) coverage exposure _

end IRComparison.WordFrontend.Arithmetic
