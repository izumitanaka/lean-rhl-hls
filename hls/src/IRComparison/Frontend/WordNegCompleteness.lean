import IRComparison.Frontend.WordArithmeticCompleteness

/-! Ordinary Lean BV32 negation: fixed library typing and certificate
construction. The conversion is the same Word/BitVec alias used by arithmetic. -/
namespace IRComparison.WordFrontend.Arithmetic
open Lean4Lean LeanTyped LeanTypeInference Certificate
set_option maxHeartbeats 1000000

def negPremise : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 6))
  (someValue wordType (.bvar 0))
def negResult : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 2)
    (.app (.const ``HybridWord.Expr.neg []) (.bvar 7)))
  (someValue wordType (.app negHeader (.bvar 1)))
def negSignature : VExpr := .forallE exprType (inputsType
  (.forallE wordType (.forallE negPremise negResult)))

theorem negHeader_inst (v : VExpr) (k : Nat) : negHeader.inst v k = negHeader :=
  negHeader_closed.instN_eq (Nat.zero_le k)

theorem neg_typed (inputs : InputsTyped env ctx p) [inputs.CastLocals casts]
    {a : Piece env ctx p v scalarExpected} (value : ScalarCasts inputs a casts)
    (registered : env.constants ``WordFrontendFacts.neg = some ⟨0,negSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordFrontendFacts.neg [])
        ([a.represented.val] ++ inputs.args ++ [value.sourceCore.val,a.checked.proofCore.val]))
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val
          (.app (.const ``HybridWord.Expr.neg []) a.represented.val))
        (someValue wordType (.app negHeader value.sourceCore.val))) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordFrontendFacts.neg []) negSignature := by
    have h := CastTyping.constant (casts := casts) (ctx := ctx) (U := 0) (levels := []) registered (by simp) rfl
    simpa [negSignature,negPremise,negResult,negHeader,width,natType,numeral,inputsType,
      exprType,wordType,stateType,wordsType,equalValues,optionType,scalarValue,someValue,
      applications,VExpr.instL,VLevel.inst] using h
  have a1 := CastTyping.application fact value.target
  simp only [negSignature,inputsType,exprType,wordType,stateType,wordsType,VExpr.inst] at a1
  have a2 := inputs.apply_casts a1
  simp only [InputsTyped.instantiate,negPremise,negResult,scalarValue,equalValues,optionType,
    wordType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,negHeader_inst] at a2
  have a3 := CastTyping.checkedApplication a2 value.value
  simp only [Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,negHeader_inst] at a3
  simpa only [InputsTyped.args,applications,List.cons_append,List.nil_append,scalarValue,
    equalValues,optionType,wordType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,
    VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,negHeader_inst] using
    CastTyping.application a3 value.equality

theorem neg_finish (inputs : InputsTyped env ctx p) [inputs.CastLocals casts]
    {a : Piece env ctx p v scalarExpected} (value : ScalarCasts inputs a casts)
    (registered : env.constants ``WordFrontendFacts.neg = some ⟨0,negSignature⟩)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env) :
    ∃ result, finish env conv exposure ctx
      (scalarExpected p (app ``HybridWord.Expr.neg [a.code]) (.app nativeNegHeader v))
      (app ``HybridWord.Expr.neg [a.code])
      (app ``WordFrontendFacts.neg ([a.code] ++ p.args ++ [v,a.checked.proof])) a.checked.known = some result ∧
      CastTyping env 0 casts ctx result.proofCore.val result.core.val ∧
      result.code = app ``HybridWord.Expr.neg [a.code] ∧
      result.proof = app ``WordFrontendFacts.neg ([a.code] ++ p.args ++ [v,a.checked.proof]) := by
  exact finish_cast_complete
    (scalarExpected_represents inputs (.app (.constant rfl) a.represented.property)
      (.app negHeader_represents value.sourceCore.property))
    (app_represents (.constant rfl) (.cons a.represented.property
      (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
        (.cons inputs.s.property (.cons inputs.ls.property
          (.cons value.sourceCore.property (.cons a.checked.proofCore.property .nil)))))))))
    (neg_typed inputs value registered) (known_casts a.checked value.proof) coverage exposure _

end IRComparison.WordFrontend.Arithmetic
