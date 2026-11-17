import IRComparison.Frontend.WordCertificateCompleteness

/-! Successful lookup and certificate construction for arbitrary in-scope
scalar bindings. The binding count is unrestricted. -/
namespace IRComparison.WordFrontend.Certificate
open Lean4Lean LeanTyped LeanTypeInference
set_option maxHeartbeats 800000

def wordCons (v vs : VExpr) : VExpr := applications (.const ``List.cons [.zero]) [wordType,v,vs]
def wordList (vs : List VExpr) : VExpr := vs.foldr wordCons (.app (.const ``List.nil [.zero]) wordType)
def localValue (n : VExpr) : VExpr := .app (.const ``HybridWord.Expr.local []) n

def localZeroResult : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 2) (wordCons (.bvar 1) (.bvar 0))
    (localValue (.const ``Nat.zero []))) (someValue wordType (.bvar 1))
def localZeroSignature : VExpr := .forallE wordType (.forallE wordType (.forallE wordType
  (.forallE stateType (.forallE wordType (.forallE wordsType localZeroResult)))))
def localSuccPremise : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 6) (.bvar 5) (.bvar 4) (.bvar 3) (.bvar 0)
    (localValue (.bvar 7))) (someValue wordType (.bvar 1))
def localSuccResult : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 7) (.bvar 6) (.bvar 5) (.bvar 4) (wordCons (.bvar 3) (.bvar 1))
    (localValue (.app (.const ``Nat.succ []) (.bvar 8)))) (someValue wordType (.bvar 2))
def localSuccSignature : VExpr := .forallE (.const ``Nat [])
  (.forallE wordType (.forallE wordType (.forallE wordType (.forallE stateType
    (.forallE wordType (.forallE wordType (.forallE wordsType
      (.forallE localSuccPremise localSuccResult))))))))

structure LocalSignatures (env : VEnv) : Prop where
  word : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩
  nil : env.constants ``List.nil = some nilSignature
  cons : env.constants ``List.cons = some consSignature
  localZero : env.constants ``WordFrontendFacts.localZero = some ⟨0,localZeroSignature⟩
  localSucc : env.constants ``WordFrontendFacts.localSucc = some ⟨0,localSuccSignature⟩
  constructor : env.constants ``HybridWord.Expr.local = some ⟨0,.forallE (.const ``Nat []) exprType⟩
  naturals : NatSignatures env

theorem wordCons_typed (signatures : LocalSignatures env)
    (value : CheckedTyping env 0 Arithmetic.Casts ctx v wordType) (tail : CastTyping env 0 Arithmetic.Casts ctx vs wordsType) :
    CastTyping env 0 Arithmetic.Casts ctx (wordCons v vs) wordsType := by
  have wt : CastTyping env 0 Arithmetic.Casts ctx wordType (.sort (.succ .zero)) :=
    .constant signatures.word (by simp) rfl
  have c : CastTyping env 0 Arithmetic.Casts ctx (.const ``List.cons [.zero]) (consSignature.type.instL [.zero]) :=
    .constant signatures.cons (by simp [VLevel.WF]) rfl
  have a1 := CastTyping.application c wt
  simp only [consSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,
    VExpr.instVar_succ,wordType,VExpr.lift,VExpr.liftN] at a1
  have a2 := CastTyping.checkedApplication a1 value
  simp only [VExpr.inst,wordType,VExpr.lift,VExpr.liftN] at a2
  exact .application a2 tail

theorem wordList_typed (signatures : LocalSignatures env)
    (typed : ∀ e ∈ vs, CheckedTyping env 0 Arithmetic.Casts ctx e wordType) :
    CastTyping env 0 Arithmetic.Casts ctx (wordList vs) wordsType := by
  induction vs with
  | nil =>
    have wt : CastTyping env 0 Arithmetic.Casts ctx wordType (.sort (.succ .zero)) :=
      .constant signatures.word (by simp) rfl
    have nt : CastTyping env 0 Arithmetic.Casts ctx (.const ``List.nil [.zero]) (nilSignature.type.instL [.zero]) :=
      .constant signatures.nil (by simp [VLevel.WF]) rfl
    exact .application nt wt
  | cons v vs ih =>
    exact wordCons_typed signatures (typed v (by simp)) (ih (by intro e h; exact typed e (by simp [h])))

theorem wordList_represents (represented : List.Forall₂ Represents xs vs) :
    Represents (xs.foldr consWord nilWords) (wordList vs) := by
  induction represented with
  | nil => exact .app (.constant rfl) (.constant rfl)
  | cons value tail ih => exact .app (.app (.app (.constant rfl) (.constant rfl)) value) ih

theorem localZero_typed (signatures : LocalSignatures env) (inputs : InputsTyped env ctx p)
    (value : CheckedTyping env 0 Arithmetic.Casts ctx v wordType) (tail : CastTyping env 0 Arithmetic.Casts ctx vs wordsType) :
    CastTyping env 0 Arithmetic.Casts ctx
      (applications (.const ``WordFrontendFacts.localZero [])
        [inputs.i.val,inputs.x.val,inputs.y.val,inputs.s.val,v,vs])
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val (wordCons v vs)
          (localValue (.const ``Nat.zero []))) (someValue wordType v)) := by
  have fact : CastTyping env 0 Arithmetic.Casts ctx (.const ``WordFrontendFacts.localZero []) localZeroSignature :=
    .constant signatures.localZero (by simp) rfl
  have a1 := CastTyping.application fact (inputs.hi.withCasts Arithmetic.Casts)
  simp only [localZeroSignature,localZeroResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a1
  have a2 := CastTyping.application a1 (inputs.hx.withCasts Arithmetic.Casts)
  simp only [localZeroSignature,localZeroResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a2
  have a3 := CastTyping.application a2 (inputs.hy.withCasts Arithmetic.Casts)
  simp only [localZeroSignature,localZeroResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a3
  have a4 := CastTyping.application a3 (inputs.hs.withCasts Arithmetic.Casts)
  simp only [localZeroSignature,localZeroResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a4
  have a5 := CastTyping.checkedApplication a4 value
  simp only [localZeroSignature,localZeroResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a5
  have a6 := CastTyping.application a5 tail
  simp only [localZeroSignature,localZeroResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a6
  exact a6

theorem localSucc_typed (signatures : LocalSignatures env) (inputs : InputsTyped env ctx p)
    (index : CastTyping env 0 Arithmetic.Casts ctx n (.const ``Nat []))
    (value : CheckedTyping env 0 Arithmetic.Casts ctx v wordType) (selected : CheckedTyping env 0 Arithmetic.Casts ctx w wordType)
    (tail : CastTyping env 0 Arithmetic.Casts ctx vs wordsType)
    (proof : CastTyping env 0 Arithmetic.Casts ctx h
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val vs (localValue n))
        (someValue wordType w))) :
    CastTyping env 0 Arithmetic.Casts ctx
      (applications (.const ``WordFrontendFacts.localSucc [])
        [n,inputs.i.val,inputs.x.val,inputs.y.val,inputs.s.val,v,w,vs,h])
      (equalValues (optionType wordType)
        (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val (wordCons v vs)
          (localValue (.app (.const ``Nat.succ []) n))) (someValue wordType w)) := by
  have fact : CastTyping env 0 Arithmetic.Casts ctx (.const ``WordFrontendFacts.localSucc []) localSuccSignature :=
    .constant signatures.localSucc (by simp) rfl
  have a1 := CastTyping.application fact index
  simp only [localSuccSignature,localSuccPremise,localSuccResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a1
  have a2 := CastTyping.application a1 (inputs.hi.withCasts Arithmetic.Casts)
  simp only [localSuccSignature,localSuccPremise,localSuccResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a2
  have a3 := CastTyping.application a2 (inputs.hx.withCasts Arithmetic.Casts)
  simp only [localSuccSignature,localSuccPremise,localSuccResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a3
  have a4 := CastTyping.application a3 (inputs.hy.withCasts Arithmetic.Casts)
  simp only [localSuccSignature,localSuccPremise,localSuccResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a4
  have a5 := CastTyping.application a4 (inputs.hs.withCasts Arithmetic.Casts)
  simp only [localSuccSignature,localSuccPremise,localSuccResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a5
  have a6 := CastTyping.checkedApplication a5 value
  simp only [localSuccSignature,localSuccPremise,localSuccResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a6
  have a7 := CastTyping.checkedApplication a6 selected
  simp only [localSuccSignature,localSuccPremise,localSuccResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a7
  have a8 := CastTyping.application a7 tail
  simp only [localSuccSignature,localSuccPremise,localSuccResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a8
  have a9 := CastTyping.application a8 proof
  simp only [localSuccSignature,localSuccPremise,localSuccResult,wordType,stateType,wordsType,wordCons,localValue,scalarValue,
    equalValues,optionType,someValue,applications,Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst,VExpr.inst_lift,
    VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] at a9
  exact a9

/-- Every selected local has the exact proof produced by `localFact`, and
that proof is well typed. No checker-success premise or binding-count bound. -/
theorem localFact_typed_complete (signatures : LocalSignatures env) (inputs : InputsTyped env ctx p)
    (represented : List.Forall₂ Represents xs vs)
    (typed : ∀ e ∈ vs, CheckedTyping env 0 Arithmetic.Casts ctx e wordType)
    (selected : xs[n]? = some value) :
    ∃ proof proofCore valueCore, localFact p n xs = some proof ∧
      Represents proof proofCore ∧ Represents value valueCore ∧
      CheckedTyping env 0 Arithmetic.Casts ctx valueCore wordType ∧
      CastTyping env 0 Arithmetic.Casts ctx proofCore
        (equalValues (optionType wordType)
          (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val (wordList vs)
            (localValue (ClosedTerm.bindingIndex n).represented.val)) (someValue wordType valueCore)) := by
  induction represented generalizing n with
  | nil => simp at selected
  | @cons x v xs vs headRep tailRep ih =>
    have valueTyped := typed v (by simp)
    have tailTyped : ∀ e ∈ vs, CheckedTyping env 0 Arithmetic.Casts ctx e wordType := by
      intro e h; exact typed e (by simp [h])
    have listTyped := wordList_typed signatures tailTyped
    have listRep := wordList_represents tailRep
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at selected
      subst value
      refine ⟨_,_,_,rfl,?_,headRep,valueTyped,localZero_typed signatures inputs valueTyped listTyped⟩
      exact app_represents (.constant rfl) (.cons inputs.i.property (.cons inputs.x.property
        (.cons inputs.y.property (.cons inputs.s.property (.cons headRep (.cons listRep .nil))))))
    | succ n =>
      simp only [List.getElem?_cons_succ] at selected
      obtain ⟨proof,pc,vc,parsed,proofRep,valueRep,valueTy,proofTy⟩ := ih tailTyped selected
      refine ⟨app ``WordFrontendFacts.localSucc
        [(ClosedTerm.bindingIndex n).val,p.i,p.x,p.y,p.s,x,value,xs.foldr consWord nilWords,proof],
        _,_,?_,?_,valueRep,valueTy,localSucc_typed signatures inputs
        ((ClosedTerm.bindingIndex_typed signatures.naturals n).withCasts _) valueTyped valueTy listTyped proofTy⟩
      · simp only [localFact,parsed,selected,bind,Option.bind,pure,Option.pure_def]
      · exact app_represents (.constant rfl) (.cons (ClosedTerm.bindingIndex n).represented.property
          (.cons inputs.i.property (.cons inputs.x.property (.cons inputs.y.property
          (.cons inputs.s.property (.cons headRep (.cons valueRep (.cons listRep (.cons proofRep .nil)))))))))

theorem forIn_prefix_done (before after : List α) (hit : α) (initial result : β)
    (step : α → β → Option (ForInStep β))
    (skips : ∀ a ∈ before, step a initial = some (.yield initial))
    (stops : step hit initial = some (.done result)) :
    forIn (before ++ hit::after) initial step = some result := by
  induction before with
  | nil => simp only [List.nil_append,List.forIn_cons,stops,bind,Option.bind,pure,Option.pure_def]
  | cons a before ih =>
    simp only [List.cons_append,List.forIn_cons,skips a (by simp),bind,Option.bind]
    exact ih (by intro x hx; exact skips x (by simp [hx]))

theorem forIn_range_hit (length n : Nat) (initial result : β)
    (step : Nat → β → Option (ForInStep β)) (bound : n < length)
    (skips : ∀ k < n, step k initial = some (.yield initial))
    (stops : step n initial = some (.done result)) :
    forIn (List.range length) initial step = some result := by
  have splitRange : List.range length = List.range n ++ n :: List.range' (n+1) (length-n-1) := by
    have total : length = n + (1 + (length-n-1)) := by omega
    calc
      List.range length = List.range (n + (1 + (length-n-1))) := congrArg List.range total
      _ = List.range n ++ n :: List.range' (n+1) (length-n-1) := by
        rw [List.range_eq_range',← List.range'_append]
        simp [Nat.add_comm 1,List.range'_succ,List.range_eq_range']
  rw [splitRange]
  exact forIn_prefix_done _ _ _ _ _ _ (by intro k hk; exact skips k (List.mem_range.mp hk)) stops

end IRComparison.WordFrontend.Certificate
