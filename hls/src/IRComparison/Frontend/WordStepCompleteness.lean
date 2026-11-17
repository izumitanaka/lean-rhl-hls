import IRComparison.Frontend.WordReturnCompleteness
import IRComparison.Frontend.WordBranchCompleteness

/-! Success of the existing normalization of Lean `for` bodies. `StepCasts`
records typing independently of running the parser; it is not another input
language or a successful-checker premise. -/
namespace IRComparison.WordFrontend.Certificate.Step
open Lean4Lean LeanTyped LeanTypeInference
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]
set_option maxHeartbeats 1000000

def stepState : VExpr := .app (.const ``ForInStep [.zero]) stateType
def lifted (plain : VExpr) : VExpr := .app (.const ``WordLoopFacts.lift []) plain
def expected (plain original : VExpr) : VExpr := equalValues (optionType stepState) (lifted plain) original

theorem expected_represents (plain : Represents p pc) (original : Represents s sc) :
    Represents (stepExpected p s) (expected pc sc) :=
  .app (.app (.app (.constant rfl) (.app (.constant rfl) (.app (.constant rfl) (.constant rfl))))
    (.app (.constant rfl) plain)) original

structure StepCasts (piece : StepPiece env ctx original) (casts : TypeCasts)
    (proofCasts : TypeCasts := casts) where
  sourceCore : {core // Represents original core}
  plainCore : {core // Represents piece.plain core}
  source : CastTyping env 0 casts ctx sourceCore.val (optionType stepState)
  plain : CastTyping env 0 casts ctx plainCore.val (optionType stateType)
  proof : CastTyping env 0 proofCasts ctx piece.checked.proofCore.val piece.checked.core.val

theorem StepCasts.equality {piece : StepPiece env ctx original} (typed : StepCasts piece casts proofCasts) :
    CastTyping env 0 proofCasts ctx piece.checked.proofCore.val (expected typed.plainCore.val typed.sourceCore.val) := by
  exact piece.checked.core.property.unique (expected_represents typed.plainCore.property typed.sourceCore.property) ▸ typed.proof

def StepCasts.inProofCasts {piece : StepPiece env ctx original} (typed : StepCasts piece casts proofCasts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b) : StepCasts piece proofCasts where
  sourceCore := typed.sourceCore
  plainCore := typed.plainCore
  source := typed.source.mono embeds
  plain := typed.plain.mono embeds
  proof := typed.proof

def StepCasts.mapProofs {piece : StepPiece env ctx original} (typed : StepCasts piece casts proofCasts)
    (embeds : ∀ scope a b, proofCasts scope a b → nextCasts scope a b) : StepCasts piece casts nextCasts where
  sourceCore := typed.sourceCore
  plainCore := typed.plainCore
  source := typed.source
  plain := typed.plain
  proof := typed.proof.mono embeds

def yieldSource (v : Lean.Expr) : Lean.Expr := Lean.mkApp4 (.const ``Pure.pure [.zero,.zero])
  (.const ``Option [.zero]) Return.nativePureInstance stepType (Lean.mkApp2 (.const ``ForInStep.yield [.zero]) state v)
def yieldValue (v : VExpr) : VExpr := .app (Return.Form.pure.headerFor stepState)
  (applications (.const ``ForInStep.yield [.zero]) [stateType,v])

theorem yield_represents (value : Represents v vc) : Represents (yieldSource v) (yieldValue vc) :=
  .app (.app (.app (.app (.constant rfl) (.constant rfl))
    (.app (.app (.constant rfl) (.constant rfl))
      (.app (.app (.constant rfl) (.constant rfl)) (.constant rfl))))
    (.app (.constant rfl) (.constant rfl))) (.app (.app (.constant rfl) (.constant rfl)) value)

def stepSignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))⟩
def yieldSignature : VConstant := ⟨1,.forallE (.sort (.succ (.param 0)))
  (.forallE (.bvar 0) (.app (.const ``ForInStep [.param 0]) (.bvar 1)))⟩
def liftSignature : VExpr := .forallE (optionType stateType) (optionType stepState)
def someYieldSignature : VExpr := .forallE stateType
  (expected (someValue stateType (.bvar 0)) (yieldValue (.bvar 0)))

structure Signatures (env : VEnv) extends Return.Signatures env : Prop where
  step : env.constants ``ForInStep = some stepSignature
  yieldDecl : env.constants ``ForInStep.yield = some yieldSignature
  liftDecl : env.constants ``WordLoopFacts.lift = some ⟨0,liftSignature⟩
  someYield : env.constants ``WordLoopFacts.someYield = some ⟨0,someYieldSignature⟩

theorem Signatures.step_typed (signatures : Signatures env) :
    DirectTyping env 0 ctx stepState (.sort (.succ .zero)) :=
  .application (.constant signatures.step (by simp [VLevel.WF]) rfl)
    (.constant signatures.state (by simp) rfl)

theorem yield_typed (signatures : Signatures env) (value : CastTyping env 0 casts ctx v stateType) :
    CastTyping env 0 casts ctx (yieldValue v) (optionType stepState) := by
  have ctor : DirectTyping env 0 ctx (.const ``ForInStep.yield [.zero]) (yieldSignature.type.instL [.zero]) :=
    .constant signatures.yieldDecl (by simp [VLevel.WF]) rfl
  have stateTyped : DirectTyping env 0 ctx stateType (.sort (.succ .zero)) :=
    .constant signatures.state (by simp) rfl
  have ctor1 := DirectTyping.application ctor stateTyped
  simp only [yieldSignature,VExpr.instL,VLevel.inst,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.lift,VExpr.liftN,stateType,Nat.reduceAdd,List.map_nil] at ctor1
  have ctor2 := CastTyping.application (ctor1.withCasts casts) value
  simp only [VExpr.inst,stateType] at ctor2
  have header := signatures.toSignatures.headerFor_typed .pure (ctx := ctx) signatures.step_typed (by trivial)
  exact .application (header.withCasts casts) ctor2

theorem yield_fact_typed (signatures : Signatures env) (value : CastTyping env 0 casts ctx v stateType) :
    CastTyping env 0 casts ctx (.app (.const ``WordLoopFacts.someYield []) v)
      (expected (someValue stateType v) (yieldValue v)) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordLoopFacts.someYield []) someYieldSignature :=
    .constant signatures.someYield (by simp) rfl
  simpa [someYieldSignature,expected,lifted,yieldValue,Return.Form.headerFor,Return.pureInstance,
    someValue,equalValues,applications,stepState,stateType,optionType,VExpr.inst,VExpr.instVar_zero] using
    CastTyping.application fact value

def nativeChoice (ty prop d a b : Lean.Expr) : Lean.Expr :=
  Lean.mkApp5 (.const ``ite [.succ .zero]) ty prop d a b

theorem nativeChoice_represents (tyRep : Represents ty tc) (propRep : Represents prop pc)
    (dRep : Represents d dc) (aRep : Represents a ac) (bRep : Represents b bc) :
    Represents (nativeChoice ty prop d a b) (Branch.iteValue tc pc dc ac bc) :=
  .app (.app (.app (.app (.app (.constant rfl) tyRep) propRep) dRep) aRep) bRep

def branchSignature : VExpr := .forallE (.sort .zero)
  (.forallE (.app (.const ``Decidable []) (.bvar 0))
    (.forallE (optionType stateType) (.forallE (optionType stateType)
      (.forallE (optionType stepState) (.forallE (optionType stepState)
        (.forallE (expected (.bvar 3) (.bvar 1)) (.forallE (expected (.bvar 3) (.bvar 1))
          (expected (Branch.iteValue (optionType stateType) (.bvar 7) (.bvar 6) (.bvar 5) (.bvar 4))
            (Branch.iteValue (optionType stepState) (.bvar 7) (.bvar 6) (.bvar 3) (.bvar 2))))))))))

theorem branch_fact_typed
    {a : StepPiece env ctx yes} (left : StepCasts a casts)
    {b : StepPiece env ctx no} (right : StepCasts b casts)
    (predicate : CastTyping env 0 casts ctx prop (.sort .zero))
    (decision : CastTyping env 0 casts ctx d (.app (.const ``Decidable []) prop))
    (registered : env.constants ``WordLoopFacts.branch = some ⟨0,branchSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordLoopFacts.branch []) [prop,d,left.plainCore.val,right.plainCore.val,
        left.sourceCore.val,right.sourceCore.val,a.checked.proofCore.val,b.checked.proofCore.val])
      (expected (Branch.iteValue (optionType stateType) prop d left.plainCore.val right.plainCore.val)
        (Branch.iteValue (optionType stepState) prop d left.sourceCore.val right.sourceCore.val)) := by
  have fact : CastTyping env 0 casts ctx (.const ``WordLoopFacts.branch []) branchSignature :=
    .constant registered (by simp) rfl
  have a1 := CastTyping.application fact predicate
  simp only [branchSignature,expected,lifted,Branch.iteValue,equalValues,applications,
    optionType,stateType,stepState,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.instVar_lower,Nat.reduceAdd] at a1
  have a2 := CastTyping.application a1 decision
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a2
  have a3 := CastTyping.application a2 left.plain
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a3
  have a4 := CastTyping.application a3 right.plain
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a4
  have a5 := CastTyping.application a4 left.source
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a5
  have a6 := CastTyping.application a5 right.source
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a6
  have a7 := CastTyping.application a6 left.equality
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a7
  simpa only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] using CastTyping.application a7 right.equality

def bindPremise (domain plain original : VExpr) : VExpr := .forallE domain
  (expected (.app plain.lift (.bvar 0)) (.app original.lift (.bvar 0)))
def bindSignature (domain : VExpr) : VExpr := .forallE (optionType domain)
  (.forallE (.forallE domain (optionType stateType))
    (.forallE (.forallE domain (optionType stepState))
      (.forallE (bindPremise domain (.bvar 1) (.bvar 0))
        (expected (applications (optionBindHeader domain stateType) [.bvar 3,.bvar 2])
          (applications (optionBindHeader domain stepState) [.bvar 3,.bvar 1])))))

theorem bind_fact_typed (domainClosed : domain.ClosedN 0)
    (firstTyped : CastTyping env 0 casts ctx first (optionType domain))
    (plainTyped : CastTyping env 0 casts ctx plain (.forallE domain (optionType stateType)))
    (originalTyped : CastTyping env 0 casts ctx original (.forallE domain (optionType stepState)))
    (proofTyped : CastTyping env 0 casts ctx proof actual)
    (beta : casts ctx actual (bindPremise domain plain original))
    (factTyped : CastTyping env 0 casts ctx (.const fact []) (bindSignature domain)) :
    CastTyping env 0 casts ctx (applications (.const fact []) [first,plain,original,proof])
      (expected (applications (optionBindHeader domain stateType) [first,plain])
        (applications (optionBindHeader domain stepState) [first,original])) := by
  have di (v : VExpr) (k : Nat) := domainClosed.instN_eq (e2 := v) (Nat.zero_le k)
  have a1 := CastTyping.application factTyped firstTyped
  simp only [bindSignature,bindPremise,expected,lifted,optionBindHeader,applications,equalValues,
    optionType,stateType,stepState,VExpr.inst,di,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.instVar_lower,Nat.reduceAdd,VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_true,ite_false] at a1
  have a2 := CastTyping.application a1 plainTyped
  simp only [VExpr.inst,di,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a2
  have a3 := CastTyping.application a2 originalTyped
  simp only [VExpr.inst,di,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a3
  have cast := beta
  simp only [bindPremise,expected,lifted,applications,equalValues,optionType,stateType,stepState] at cast
  simpa only [VExpr.inst,di,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] using CastTyping.convertedApplication a3 proofTyped cast

def letSignature : VExpr := .forallE (.sort (.succ .zero)) (.forallE (.bvar 0)
  (.forallE (.forallE (.bvar 1) (optionType stateType))
    (.forallE (.forallE (.bvar 2) (optionType stepState))
      (.forallE (bindPremise (.bvar 3) (.bvar 1) (.bvar 0))
        (expected (.app (.bvar 2) (.bvar 3)) (.app (.bvar 1) (.bvar 3)))))))

theorem let_fact_typed (domainClosed : domain.ClosedN 0)
    (domainTyped : DirectTyping env 0 ctx domain (.sort (.succ .zero)))
    (valueTyped : CastTyping env 0 casts ctx value domain)
    (plainTyped : CastTyping env 0 casts ctx plain (.forallE domain (optionType stateType)))
    (originalTyped : CastTyping env 0 casts ctx original (.forallE domain (optionType stepState)))
    (proofTyped : CastTyping env 0 casts ctx proof actual)
    (beta : casts ctx actual (bindPremise domain plain original))
    (registered : env.constants ``WordLoopFacts.letBinding = some ⟨0,letSignature⟩) :
    CastTyping env 0 casts ctx
      (applications (.const ``WordLoopFacts.letBinding []) [domain,value,plain,original,proof])
      (expected (.app plain value) (.app original value)) := by
  have dl (n k : Nat) := domainClosed.liftN_eq (n := n) (Nat.zero_le k)
  have di (v : VExpr) (k : Nat) := domainClosed.instN_eq (e2 := v) (Nat.zero_le k)
  have fact : CastTyping env 0 casts ctx (.const ``WordLoopFacts.letBinding []) letSignature :=
    .constant registered (by simp) rfl
  have a1 := CastTyping.application fact (domainTyped.withCasts casts)
  simp only [letSignature,bindPremise,expected,lifted,equalValues,optionType,stateType,stepState,applications,
    VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    VExpr.lift,dl,VExpr.liftN,liftVar,Nat.reduceLT,ite_true,ite_false] at a1
  have a2 := CastTyping.application a1 valueTyped
  simp only [VExpr.inst,di,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a2
  have a3 := CastTyping.application a2 plainTyped
  simp only [VExpr.inst,di,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a3
  have a4 := CastTyping.application a3 originalTyped
  simp only [VExpr.inst,di,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] at a4
  have cast := beta
  simp only [bindPremise,expected,lifted,applications,equalValues,optionType,stateType,stepState] at cast
  simpa only [VExpr.inst,di,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,Nat.reduceAdd,
    ← VExpr.lift_instN_lo,VExpr.inst_lift] using CastTyping.convertedApplication a4 proofTyped cast

end IRComparison.WordFrontend.Certificate.Step
