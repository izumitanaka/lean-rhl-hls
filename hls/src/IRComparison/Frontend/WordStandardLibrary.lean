import IRComparison.Frontend.WordNativeCompleteness

/-! Fixed signature interface for the actual BV32 frontend library. This
finite table is checked once; users do not build the Library record by hand.
Native provenance and dependency reachability are separate obligations. -/
namespace IRComparison.WordFrontend.StandardLibrary
open Lean4Lean LeanTypeInference
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

def entries : List (Lean.Name × VConstant) := [
  (``Bool, ⟨0,.sort (.succ .zero)⟩),
  (``Bool.true, ⟨0,Arithmetic.boolType⟩),
  (``Decidable, Arithmetic.decidableSignature),
  (``DecidableEq, Arithmetic.decEqSignature),
  (``bne, Certificate.Branch.bneSignature),
  (``instBEqOfDecidableEq, Certificate.Branch.beqInstanceSignature),
  (``instDecidableEqBitVec, Certificate.Branch.bitvecDecisionSignature),
  (``instDecidableEqBool, Certificate.Branch.boolDecisionSignature),
  (``HAdd, Arithmetic.Binary.add.heterogeneousSignature),
  (``HSub, Arithmetic.Binary.sub.heterogeneousSignature),
  (``HMul, Arithmetic.Binary.mul.heterogeneousSignature),
  (``HDiv, Arithmetic.Binary.div.heterogeneousSignature),
  (``Int.instAdd, ⟨0,Certificate.For.integerBinarySignature .add⟩),
  (``Int.instSub, ⟨0,Certificate.For.integerBinarySignature .sub⟩),
  (``Int.instMul, ⟨0,Certificate.For.integerBinarySignature .mul⟩),
  (``Int.instDiv, ⟨0,Certificate.For.integerBinarySignature .div⟩),
  (``Int, ⟨0,.sort (.succ .zero)⟩),
  (``instOfNat, ⟨0,Certificate.For.intOfNatSignature⟩),
  (``Int.instNegInt, ⟨0,Certificate.For.intNegSignature⟩),
  (`Neg, IRComparison.WordFrontend.Arithmetic.negClassSignature),
  (`BitVec.instNeg, { uvars := 0, type := IRComparison.WordFrontend.Arithmetic.negInstanceSignature }),
  (`Neg.neg, IRComparison.WordFrontend.Arithmetic.negMethodSignature),
  (`Nat, { uvars := 0, type := Lean4Lean.VExpr.sort Lean4Lean.VLevel.zero.succ }),
  (`IRComparison.HybridWord.Word, { uvars := 0, type := Lean4Lean.VExpr.sort Lean4Lean.VLevel.zero.succ }),
  (`Nat.zero, { uvars := 0, type := Lean4Lean.VExpr.const `Nat [] }),
  (`Nat.succ, { uvars := 0, type := (Lean4Lean.VExpr.const `Nat []).forallE (Lean4Lean.VExpr.const `Nat []) }),
  (`Nat.mul, { uvars := 0, type := (Lean4Lean.VExpr.const `Nat []).forallE ((Lean4Lean.VExpr.const `Nat []).forallE (Lean4Lean.VExpr.const `Nat [])) }),
  (`OfNat, IRComparison.WordFrontend.Arithmetic.ofNatClassSignature),
  (`BitVec.instOfNat, { uvars := 0, type := IRComparison.WordFrontend.Arithmetic.bitvecOfNatSignature }),
  (`OfNat.ofNat, IRComparison.WordFrontend.Arithmetic.ofNatSignature),
  (`instOfNatNat, { uvars := 0, type := IRComparison.WordFrontend.Arithmetic.natInstanceSignature }),
  (`BitVec, { uvars := 0, type := IRComparison.WordFrontend.Arithmetic.natType.forallE (Lean4Lean.VExpr.sort Lean4Lean.VLevel.zero.succ) }),
  (`Add, IRComparison.WordFrontend.Arithmetic.Binary.add.classSignature),
  (`Sub, IRComparison.WordFrontend.Arithmetic.Binary.sub.classSignature),
  (`Mul, IRComparison.WordFrontend.Arithmetic.Binary.mul.classSignature),
  (`Div, IRComparison.WordFrontend.Arithmetic.Binary.div.classSignature),
  (`BitVec.instAdd, { uvars := 0, type := IRComparison.WordFrontend.Arithmetic.Binary.add.instanceSignature }),
  (`BitVec.instSub, { uvars := 0, type := IRComparison.WordFrontend.Arithmetic.Binary.sub.instanceSignature }),
  (`BitVec.instMul, { uvars := 0, type := IRComparison.WordFrontend.Arithmetic.Binary.mul.instanceSignature }),
  (`BitVec.instDiv, { uvars := 0, type := IRComparison.WordFrontend.Arithmetic.Binary.div.instanceSignature }),
  (`instHAdd, IRComparison.WordFrontend.Arithmetic.Binary.add.liftedSignature),
  (`instHSub, IRComparison.WordFrontend.Arithmetic.Binary.sub.liftedSignature),
  (`instHMul, IRComparison.WordFrontend.Arithmetic.Binary.mul.liftedSignature),
  (`instHDiv, IRComparison.WordFrontend.Arithmetic.Binary.div.liftedSignature),
  (`HAdd.hAdd, IRComparison.WordFrontend.Arithmetic.Binary.add.methodSignature),
  (`HSub.hSub, IRComparison.WordFrontend.Arithmetic.Binary.sub.methodSignature),
  (`HMul.hMul, IRComparison.WordFrontend.Arithmetic.Binary.mul.methodSignature),
  (`HDiv.hDiv, IRComparison.WordFrontend.Arithmetic.Binary.div.methodSignature),
  (`IRComparison.WordFrontendFacts.neg, { uvars := 0, type := IRComparison.WordFrontend.Arithmetic.negSignature }),
  (`IRComparison.HybridWord.Expr.neg, { uvars := 0, type := IRComparison.WordFrontend.Certificate.exprType.forallE IRComparison.WordFrontend.Certificate.exprType }),
  (`ite, IRComparison.WordFrontend.Certificate.Branch.iteSignature),
  (`IRComparison.WordFrontendFacts.select, { uvars := 0, type := IRComparison.WordFrontend.Certificate.Branch.Select.signature }),
  (`IRComparison.HybridWord.Expr.select, { uvars := 0, type := IRComparison.WordFrontend.Certificate.Branch.Select.constructorSignature }),
  (`IRComparison.WordFrontendFacts.register, { uvars := 0, type := IRComparison.WordFrontend.Certificate.registerSignature }),
  (`IRComparison.HybridWord.State.regs, { uvars := 0, type := IRComparison.WordFrontend.Certificate.stateType.forallE ((Lean4Lean.VExpr.const `Nat []).forallE IRComparison.WordFrontend.Certificate.wordType) }),
  (`IRComparison.HybridWord.Expr.reg, { uvars := 0, type := (Lean4Lean.VExpr.const `Nat []).forallE IRComparison.WordFrontend.Certificate.exprType }),
  (`List.nil, IRComparison.WordFrontend.Certificate.nilSignature),
  (`List.cons, IRComparison.WordFrontend.Certificate.consSignature),
  (`IRComparison.WordFrontendFacts.localZero, { uvars := 0, type := IRComparison.WordFrontend.Certificate.localZeroSignature }),
  (`IRComparison.WordFrontendFacts.localSucc, { uvars := 0, type := IRComparison.WordFrontend.Certificate.localSuccSignature }),
  (`IRComparison.HybridWord.Expr.local, { uvars := 0, type := (Lean4Lean.VExpr.const `Nat []).forallE IRComparison.WordFrontend.Certificate.exprType }),
  (`IRComparison.WordFrontendFacts.left, { uvars := 0, type := IRComparison.WordFrontend.ScalarSyntax.Side.left.signature }),
  (`IRComparison.WordFrontendFacts.right, { uvars := 0, type := IRComparison.WordFrontend.ScalarSyntax.Side.right.signature }),
  (`IRComparison.HybridWord.Expr.left, { uvars := 0, type := IRComparison.WordFrontend.Certificate.exprType }),
  (`IRComparison.HybridWord.Expr.right, { uvars := 0, type := IRComparison.WordFrontend.Certificate.exprType }),
  (`IRComparison.WordFrontendFacts.index, { uvars := 0, type := IRComparison.WordFrontend.Certificate.indexSignature }),
  (`IRComparison.HybridWord.Expr.index, { uvars := 0, type := IRComparison.WordFrontend.Certificate.exprType }),
  (`IRComparison.WordFrontendFacts.literal, { uvars := 0, type := IRComparison.WordFrontend.Arithmetic.literalSignature }),
  (`IRComparison.HybridWord.Expr.lit, { uvars := 0, type := IRComparison.WordFrontend.Certificate.wordType.forallE IRComparison.WordFrontend.Certificate.exprType }),
  (`IRComparison.WordFrontendFacts.add, { uvars := 0, type := IRComparison.WordFrontend.Arithmetic.Binary.add.signature }),
  (`IRComparison.WordFrontendFacts.sub, { uvars := 0, type := IRComparison.WordFrontend.Arithmetic.Binary.sub.signature }),
  (`IRComparison.WordFrontendFacts.mul, { uvars := 0, type := IRComparison.WordFrontend.Arithmetic.Binary.mul.signature }),
  (`IRComparison.WordFrontendFacts.div, { uvars := 0, type := IRComparison.WordFrontend.Arithmetic.Binary.div.signature }),
  (`IRComparison.HybridWord.Expr.add, { uvars := 0, type := IRComparison.WordFrontend.Certificate.exprType.forallE (IRComparison.WordFrontend.Certificate.exprType.forallE IRComparison.WordFrontend.Certificate.exprType) }),
  (`IRComparison.HybridWord.Expr.sub, { uvars := 0, type := IRComparison.WordFrontend.Certificate.exprType.forallE (IRComparison.WordFrontend.Certificate.exprType.forallE IRComparison.WordFrontend.Certificate.exprType) }),
  (`IRComparison.HybridWord.Expr.mul, { uvars := 0, type := IRComparison.WordFrontend.Certificate.exprType.forallE (IRComparison.WordFrontend.Certificate.exprType.forallE IRComparison.WordFrontend.Certificate.exprType) }),
  (`IRComparison.HybridWord.Expr.div, { uvars := 0, type := IRComparison.WordFrontend.Certificate.exprType.forallE (IRComparison.WordFrontend.Certificate.exprType.forallE IRComparison.WordFrontend.Certificate.exprType) }),
  (`IRComparison.HybridWord.State, { uvars := 0, type := Lean4Lean.VExpr.sort Lean4Lean.VLevel.zero.succ }),
  (`Option, IRComparison.WordFrontend.Certificate.optionSignature),
  (`Option.some, IRComparison.WordFrontend.Certificate.Return.someSignature),
  (`Pure.pure, IRComparison.WordFrontend.Certificate.Return.pureSignature),
  (`Alternative.toApplicative, IRComparison.WordFrontend.Certificate.Return.projectionSignature `Alternative `Applicative),
  (`Applicative.toPure, IRComparison.WordFrontend.Certificate.Return.projectionSignature `Applicative `Pure),
  (`instAlternativeOption, IRComparison.WordFrontend.Certificate.Return.alternativeSignature),
  (`IRComparison.WordFrontendFacts.skip, { uvars := 0, type := IRComparison.WordFrontend.Certificate.Return.Form.some.signature }),
  (`IRComparison.WordFrontendFacts.skipPure, { uvars := 0, type := IRComparison.WordFrontend.Certificate.Return.Form.pure.signature }),
  (`IRComparison.HybridWord.Cmd.skip, { uvars := 0, type := IRComparison.WordFrontend.Certificate.cmdType }),
  (`IRComparison.WordFrontendFacts.store, { uvars := 0, type := IRComparison.WordFrontend.Certificate.storeSignature }),
  (`IRComparison.HybridWord.Cmd.store, { uvars := 0, type := IRComparison.WordFrontend.Certificate.storeConstructor }),
  (`IRComparison.WordFrontendFacts.assign, { uvars := 0, type := IRComparison.WordFrontend.Certificate.assignSignatureWith IRComparison.WordFrontend.Certificate.Return.Form.some.header }),
  (`IRComparison.WordFrontendFacts.assignPure, { uvars := 0, type := IRComparison.WordFrontend.Certificate.assignSignatureWith IRComparison.WordFrontend.Certificate.Return.Form.pure.header }),
  (`IRComparison.HybridWord.Cmd.assign, { uvars := 0, type := IRComparison.WordFrontend.Certificate.Return.assignConstructor }),
  (`IRComparison.HybridWord.State.set, { uvars := 0, type := IRComparison.WordFrontend.Certificate.Return.setterSignature }),
  (`IRComparison.HybridWord.State.write, { uvars := 0, type := IRComparison.WordFrontend.Certificate.writeSignature }),
  (`IRComparison.WordFrontendFacts.copy, { uvars := 0, type := IRComparison.WordFrontend.Certificate.copySignature }),
  (`IRComparison.HybridWord.Cmd.copy, { uvars := 0, type := IRComparison.WordFrontend.Certificate.copyConstructor }),
  (`IRComparison.HybridWord.State.copy, { uvars := 0, type := IRComparison.WordFrontend.Certificate.copySourceSignature }),
  (`IRComparison.WordFrontendFacts.branch, { uvars := 0, type := IRComparison.WordFrontend.Certificate.Branch.signature }),
  (`IRComparison.HybridWord.Cmd.branch, { uvars := 0, type := IRComparison.WordFrontend.Certificate.Branch.constructorSignature }),
  (`IRComparison.HybridWord.Expr.eval, { uvars := 0, type := IRComparison.WordFrontend.ScalarConversion.evalSignature }),
  (`Eq, IRComparison.WordFrontend.Certificate.eqSignature),
  (`IRComparison.HybridWord.Cmd.eval, { uvars := 0, type := IRComparison.WordFrontend.Certificate.evalSignature }),
  (`Bind.bind, IRComparison.WordFrontend.Certificate.bindSignature),
  (`Monad.toBind, IRComparison.WordFrontend.Certificate.monadBindSignature),
  (`instMonadOption, IRComparison.WordFrontend.Certificate.optionMonadSignature),
  (`IRComparison.WordFrontendFacts.sequence, { uvars := 0, type := IRComparison.WordFrontend.Certificate.sequenceSignature }),
  (`IRComparison.HybridWord.Cmd.seq, { uvars := 0, type := IRComparison.WordFrontend.Certificate.sequenceConstructor }),
  (`IRComparison.WordFrontendFacts.letValue, { uvars := 0, type := IRComparison.WordFrontend.Certificate.letValueSignature }),
  (`IRComparison.HybridWord.Cmd.letValue, { uvars := 0, type := IRComparison.WordFrontend.Certificate.bindValueConstructor }),
  (`IRComparison.WordFrontendFacts.letState, { uvars := 0, type := IRComparison.WordFrontend.Certificate.StateLet.signature }),
  (`IRComparison.WordFrontendFacts.letStateAlias, { uvars := 0, type := IRComparison.WordFrontend.Certificate.StateAlias.signature }),
  (`Array, IRComparison.WordFrontend.Read.arraySignature),
  (`Array.size, IRComparison.WordFrontend.Read.sizeSignature),
  (`LT.lt, IRComparison.WordFrontend.Read.lessSignature),
  (`instLTNat, { uvars := 0, type := (Lean4Lean.VExpr.const `LT [Lean4Lean.VLevel.zero]).app (Lean4Lean.VExpr.const `Nat []) }),
  (`GetElem?, IRComparison.WordFrontend.Read.getClassSignature),
  (`GetElem?.getElem?, IRComparison.WordFrontend.Read.getSignature),
  (`Array.instGetElem?NatLtSize, IRComparison.WordFrontend.Read.arrayInstanceSignature),
  (`IRComparison.HybridWord.State.arrays, { uvars := 0, type := IRComparison.WordFrontend.Read.arraysSignature }),
  (`BitVec.toNat, { uvars := 0, type := IRComparison.WordFrontend.Read.toNatSignature }),
  (`IRComparison.WordFrontendFacts.readNat, { uvars := 0, type := IRComparison.WordFrontend.Read.natSignature }),
  (`IRComparison.HybridWord.Expr.readNat, { uvars := 0, type := IRComparison.WordFrontend.Read.natConstructor }),
  (`IRComparison.WordFrontendFacts.read, { uvars := 0, type := IRComparison.WordFrontend.Read.wordSignature }),
  (`IRComparison.HybridWord.Expr.read, { uvars := 0, type := IRComparison.WordFrontend.Read.wordConstructor }),
  (`IRComparison.WordLoopFacts.letState, { uvars := 0, type := IRComparison.WordFrontend.StructuralStateLet.Loop.signature }),
  (`PUnit, IRComparison.WordFrontend.Certificate.UnitStep.unitSignature),
  (`PUnit.unit, IRComparison.WordFrontend.Certificate.UnitStep.valueSignature),
  (`IRComparison.WordFrontendFacts.unitSequence, { uvars := 0, type := IRComparison.WordFrontend.StructuralUnit.signature false }),
  (`IRComparison.WordLoopFacts.unitSequence, { uvars := 0, type := IRComparison.WordFrontend.StructuralUnit.signature true }),
  (`IRComparison.WordLoopFacts.letStateAlias, { uvars := 0, type := IRComparison.WordFrontend.StructuralStep.Alias.signature }),
  (`IRComparison.WordLoopFacts.letValue, { uvars := 0, type := IRComparison.WordFrontend.StructuralReadBind.letValueSignature }),
  (`IRComparison.WordLoopFacts.bindValue, { uvars := 0, type := IRComparison.WordFrontend.StructuralReadBind.bindValueSignature }),
  (`IRComparison.WordLoopFacts.branchCmd, { uvars := 0, type := IRComparison.WordFrontend.StructuralStep.Conditional.signature }),
  (`IRComparison.WordLoopFacts.sequence, { uvars := 0, type := IRComparison.WordFrontend.StructuralStep.sequenceSignature }),
  (`ForInStep, IRComparison.WordFrontend.Certificate.Step.stepSignature),
  (`ForInStep.yield, IRComparison.WordFrontend.Certificate.Step.yieldSignature),
  (`IRComparison.WordLoopFacts.lift, { uvars := 0, type := IRComparison.WordFrontend.Certificate.Step.liftSignature }),
  (`IRComparison.WordLoopFacts.someYield, { uvars := 0, type := IRComparison.WordFrontend.Certificate.Step.someYieldSignature }),
  (`IRComparison.WordLoopFacts.compose, { uvars := 0, type := IRComparison.WordFrontend.Certificate.For.composeSignature }),
  (`IRComparison.WordLoopFacts.forStatic, { uvars := 0, type := IRComparison.WordFrontend.Certificate.For.signature }),
  (`IRComparison.HybridWord.Cmd.forStatic, { uvars := 0, type := IRComparison.WordFrontend.Certificate.For.constructorSignature }),
  (`IRComparison.HybridWord.range, { uvars := 0, type := IRComparison.WordFrontend.Certificate.For.rangeSignature }),
  (`ForIn.forIn, IRComparison.WordFrontend.Certificate.For.Header.forInSignature),
  (`instForInOfForIn', IRComparison.WordFrontend.Certificate.For.Header.forInInstanceSignature),
  (`inferInstance, IRComparison.WordFrontend.Certificate.For.Header.inferInstanceSignature),
  (`List.instMembership, IRComparison.WordFrontend.Certificate.For.Header.membershipInstanceSignature),
  (`List.instForIn'InferInstanceMembershipOfMonad, IRComparison.WordFrontend.Certificate.For.Header.listInstanceSignature),
  (`List, IRComparison.WordFrontend.Certificate.For.Header.listSignature),
  (`Membership, IRComparison.WordFrontend.Certificate.For.Header.membershipSignature),
  (`BitVec.ofNat, { uvars := 0, type := IRComparison.WordFrontend.NaturalScope.ofNatSignature }),
  (`List.range, { uvars := 0, type := IRComparison.WordFrontend.NaturalLoop.rangeSignature }),
  (`List.foldlM, IRComparison.WordFrontend.NaturalLoop.foldSignature),
  (`IRComparison.WordLoopFacts.forIn, { uvars := 0, type := IRComparison.WordFrontend.NaturalLoop.Kind.forIn.signature }),
  (`IRComparison.WordFrontendFacts.forRange, { uvars := 0, type := IRComparison.WordFrontend.NaturalLoop.Kind.fold.signature }),
  (`IRComparison.HybridWord.Cmd.forRange, { uvars := 0, type := IRComparison.WordFrontend.NaturalLoop.constructorSignature }),
  (`IRComparison.WordFrontendFacts.bindValue, { uvars := 0, type := IRComparison.WordFrontend.Certificate.bindValueSignature })]

def model : VEnv where
  constants name := entries.lookup name
  defeqs _ := False

theorem library : ScopedSyntax.Library model := by
  repeat first
    | rfl
    | constructor
    | intro x; cases x

/-- The standard signature set is part of the fixed loading interface, even
when a particular source uses only a small part of the grammar. -/
theorem roots : ∀ pair ∈ entries, pair.1 ∈ WordFrontend.declarations := by
  decide

/-- Native signature provenance is a finite interface condition. Unlike
`Library`, it refers to actual declarations, not a second assumed type table. -/
def NativeEntries (native : Lean.Environment) (es : List (Lean.Name × VConstant)) : Prop :=
  ∀ pair ∈ es, ∃ d : LeanLibrary.Declaration native pair.1, pair.2 = d.signature

def checkEntries (native : Lean.Environment) : (es : List (Lean.Name × VConstant)) →
    Option (PLift (NativeEntries native es))
  | [] => some ⟨by intro p h; cases h⟩
  | (name, signature)::rest => do
    let d ← LeanLibrary.load native name
    if same : signature = d.signature then
      let tail ← checkEntries native rest
      return ⟨by
        intro p member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨d,same⟩
        · exact tail.down p member⟩
    else none

/-- This checker succeeds from the signature interface itself. Successful
parsing, typechecking, or compiler output is not an input condition. -/
theorem checkEntries_complete (valid : NativeEntries native es) :
    ∃ result, checkEntries native es = some result := by
  induction es with
  | nil => exact ⟨_,rfl⟩
  | cons pair rest ih =>
    obtain ⟨name,signature⟩ := pair
    obtain ⟨d,same⟩ := valid (name,signature) (by simp)
    obtain ⟨loaded,success⟩ := d.load_complete
    have eqn : signature = loaded.signature := same.trans (d.signature_unique loaded)
    obtain ⟨tail,done⟩ := ih (fun p hp => valid p (List.mem_cons_of_mem _ hp))
    simp only [checkEntries,success,bind,Option.bind,dif_pos eqn,done]
    exact ⟨_,rfl⟩

private theorem lookup_member {es : List (Lean.Name × VConstant)}
    (found : es.lookup name = some signature) : (name,signature) ∈ es := by
  induction es with
  | nil => cases found
  | cons p rest ih =>
    obtain ⟨n,s⟩ := p
    by_cases eqn : name = n
    · subst n
      simp only [List.lookup_cons,beq_self_eq_true,↓reduceIte,Option.some.injEq] at found
      subst s
      exact List.mem_cons_self
    · have ne : (name == n) = false := beq_eq_false_iff_ne.mpr eqn
      have tail : rest.lookup name = some signature := by simpa [List.lookup_cons,ne] using found
      exact List.mem_cons_of_mem _ (ih tail)

private def closureDecision : (e : VExpr) → (k : Nat) → Decidable (e.ClosedN k)
  | .bvar i, k => inferInstanceAs (Decidable (i < k))
  | .sort _, _ | .const _ _, _ => isTrue trivial
  | .app f a, k => @instDecidableAnd _ _ (closureDecision f k) (closureDecision a k)
  | .lam t b, k | .forallE t b, k => @instDecidableAnd _ _ (closureDecision t k) (closureDecision b (k+1))

private instance (e : VExpr) (k : Nat) : Decidable (e.ClosedN k) := closureDecision e k

/-- Closure of the fixed signature table is checked once, so binder typing
can be constructed in the ordinary source environment without user proofs. -/
theorem closed : ClosedConstantTypes model := by
  have allClosed : entries.all (fun pair => decide (pair.2.type.ClosedN 0)) = true := by decide +kernel
  intro name signature found
  exact of_decide_eq_true ((List.all_eq_true.mp allClosed) (name,signature) (lookup_member found))

/-- Construct the source table without hand-written provenance and
reachability proofs. Only the fixed native interface is inspected. -/
def sourceTable (valid : NativeEntries native entries) (name : Lean.Name) (value : Lean.Expr) :
    NativeCompleteness.SourceTable native name value where
  model := model
  declarations n signature found := valid (n,signature) (lookup_member found)
  reachable n signature found := .root (by
    have member := roots (n,signature) (lookup_member found)
    simp [libraryRoots,member])

/-- Ordinary environments obtain the table through a small proof-producing
check. The returned library proposition is the theorem above, not unchecked
native evaluation of a proposition. -/
def check (native : Lean.Environment) (name : Lean.Name) (value : Lean.Expr) :
    Option { table : NativeCompleteness.SourceTable native name value //
      ScopedSyntax.Library table.model } := do
  let valid ← checkEntries native entries
  return ⟨sourceTable valid.down name value,library⟩

theorem check_complete (valid : NativeEntries native entries) (name : Lean.Name) (value : Lean.Expr) :
    ∃ result, check native name value = some result := by
  obtain ⟨certificate,success⟩ := checkEntries_complete valid
  simp only [check,success,bind,Option.bind]
  exact ⟨_,rfl⟩

end IRComparison.WordFrontend.StandardLibrary
