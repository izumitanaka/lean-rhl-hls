import IRComparison.Frontend.LeanHLSCommand
import IRComparison.Frontend.WordLetCompleteness
import IRComparison.Frontend.WordLocalCompleteness
import IRComparison.Frontend.WordReturnCompleteness
import IRComparison.Frontend.WordUnitCompleteness
import IRComparison.Frontend.WordNativeCompleteness

namespace IRComparison.FrontendDepthExamples
open Lean Elab Command

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

private def literalZero : HybridWord.Word := 0
private def literalSmall : HybridWord.Word := 1
private def literalCompact : HybridWord.Word := 64
private def literalWrap : HybridWord.Word := 4294967297

-- The success lemmas use the actual fact signatures. Catch drift in the
-- library (including binder order and universe levels), rather than silently
-- proving success for declarations that the real frontend never installs.
run_cmd do
  let native ← getEnv
  let signatures : List (Name × Lean4Lean.VConstant) :=
    [(``WordLoopFacts.forIn, ⟨0, WordFrontend.NaturalLoop.Kind.forIn.signature⟩),
     (``WordFrontendFacts.forRange, ⟨0, WordFrontend.NaturalLoop.Kind.fold.signature⟩),
     (``List.foldlM, WordFrontend.NaturalLoop.foldSignature),
     (``List.range, ⟨0, WordFrontend.NaturalLoop.rangeSignature⟩),
     (``HybridWord.Cmd.forRange, ⟨0, WordFrontend.NaturalLoop.constructorSignature⟩),
     (``BitVec.ofNat, ⟨0, WordFrontend.NaturalScope.ofNatSignature⟩),
     (``PUnit, WordFrontend.Certificate.UnitStep.unitSignature),
     (``PUnit.unit, WordFrontend.Certificate.UnitStep.valueSignature),
     (``WordLoopFacts.bindUnit, ⟨0, WordFrontend.Certificate.UnitStep.signature⟩),
     (``WordFrontendFacts.letState, ⟨0, WordFrontend.Certificate.StateLet.signature⟩),
     (``WordFrontendFacts.letStateAlias, ⟨0, WordFrontend.Certificate.StateAlias.signature⟩),
     (``WordLoopFacts.forStatic, ⟨0, WordFrontend.Certificate.For.signature⟩),
     (``WordLoopFacts.compose, ⟨0, WordFrontend.Certificate.For.composeSignature⟩),
     (``HybridWord.Cmd.forStatic, ⟨0, WordFrontend.Certificate.For.constructorSignature⟩),
     (``HybridWord.range, ⟨0, WordFrontend.Certificate.For.rangeSignature⟩),
     (``Int, ⟨0, .sort (.succ .zero)⟩),
     (``instOfNat, ⟨0, WordFrontend.Certificate.For.intOfNatSignature⟩),
     (``Neg.neg, WordFrontend.Certificate.For.negSignature),
     (``Int.instNegInt, ⟨0, WordFrontend.Certificate.For.intNegSignature⟩),
     (``ForIn.forIn, WordFrontend.Certificate.For.Header.forInSignature),
     (``instForInOfForIn', WordFrontend.Certificate.For.Header.forInInstanceSignature),
     (``inferInstance, WordFrontend.Certificate.For.Header.inferInstanceSignature),
     (``List.instMembership, WordFrontend.Certificate.For.Header.membershipInstanceSignature),
     (``List.instForIn'InferInstanceMembershipOfMonad, WordFrontend.Certificate.For.Header.listInstanceSignature),
     (``List, WordFrontend.Certificate.For.Header.listSignature),
     (``Membership, WordFrontend.Certificate.For.Header.membershipSignature),
     (``WordFrontendFacts.index, ⟨0, WordFrontend.Certificate.indexSignature⟩),
     (``WordFrontendFacts.skip, ⟨0, WordFrontend.Certificate.skipSignature⟩),
     (``WordFrontendFacts.copy, ⟨0, WordFrontend.Certificate.copySignature⟩),
     (``WordFrontendFacts.assign, ⟨0, WordFrontend.Certificate.assignSignature⟩),
     (``WordFrontendFacts.store, ⟨0, WordFrontend.Certificate.storeSignature⟩),
     (``HybridWord.Cmd.store, ⟨0, WordFrontend.Certificate.storeConstructor⟩),
     (``HybridWord.State.write, ⟨0, WordFrontend.Certificate.writeSignature⟩),
     (``Option.some, WordFrontend.Certificate.Return.someSignature),
     (``Pure.pure, WordFrontend.Certificate.Return.pureSignature),
     (``Alternative.toApplicative, WordFrontend.Certificate.Return.projectionSignature ``Alternative ``Applicative),
     (``Applicative.toPure, WordFrontend.Certificate.Return.projectionSignature ``Applicative ``Pure),
     (``instAlternativeOption, WordFrontend.Certificate.Return.alternativeSignature),
     (``HybridWord.Cmd.copy, ⟨0, WordFrontend.Certificate.copyConstructor⟩),
     (``HybridWord.State.copy, ⟨0, WordFrontend.Certificate.copySourceSignature⟩),
     (``HybridWord.Cmd.assign, ⟨0, WordFrontend.Certificate.Return.assignConstructor⟩),
     (``HybridWord.State.set, ⟨0, WordFrontend.Certificate.Return.setterSignature⟩),
     (``WordFrontendFacts.assignPure, ⟨0, WordFrontend.Certificate.assignSignatureWith WordFrontend.Certificate.Return.Form.pure.header⟩),
     (``WordFrontendFacts.skipPure, ⟨0, WordFrontend.Certificate.Return.Form.pure.signature⟩),
     (``WordFrontendFacts.branch, ⟨0, WordFrontend.Certificate.Branch.signature⟩),
     (``HybridWord.Cmd.branch, ⟨0, WordFrontend.Certificate.Branch.constructorSignature⟩),
     (``WordFrontendFacts.select, ⟨0, WordFrontend.Certificate.Branch.Select.signature⟩),
     (``HybridWord.Expr.select, ⟨0, WordFrontend.Certificate.Branch.Select.constructorSignature⟩),
     (``ForInStep, WordFrontend.Certificate.Step.stepSignature),
     (``ForInStep.yield, WordFrontend.Certificate.Step.yieldSignature),
     (``WordLoopFacts.lift, ⟨0, WordFrontend.Certificate.Step.liftSignature⟩),
     (``WordLoopFacts.someYield, ⟨0, WordFrontend.Certificate.Step.someYieldSignature⟩),
     (``WordLoopFacts.branch, ⟨0, WordFrontend.Certificate.Step.branchSignature⟩),
     (``WordLoopFacts.bindState, ⟨0, WordFrontend.Certificate.Step.bindSignature WordFrontend.Certificate.stateType⟩),
     (``WordLoopFacts.letBinding, ⟨0, WordFrontend.Certificate.Step.letSignature⟩),
     (``WordLoopFacts.bindWord, ⟨0, WordFrontend.Certificate.Step.bindSignature WordFrontend.Certificate.wordType⟩),
     (``ite, WordFrontend.Certificate.Branch.iteSignature),
     (``HybridWord.Cmd.skip, ⟨0, WordFrontend.Certificate.cmdType⟩),
     (``WordFrontendFacts.localZero, ⟨0, WordFrontend.Certificate.localZeroSignature⟩),
     (``WordFrontendFacts.localSucc, ⟨0, WordFrontend.Certificate.localSuccSignature⟩),
     (``HybridWord.Expr.local, ⟨0, .forallE (.const ``Nat []) WordFrontend.Certificate.exprType⟩),
     (``WordFrontendFacts.letValue, ⟨0, WordFrontend.Certificate.letValueSignature⟩),
     (``WordFrontendFacts.bindValue, ⟨0, WordFrontend.Certificate.bindValueSignature⟩),
     (``HybridWord.Cmd.letValue, ⟨0, WordFrontend.Certificate.bindValueConstructor⟩),
     (``WordFrontendFacts.sequence, ⟨0, WordFrontend.Certificate.sequenceSignature⟩),
     (``HybridWord.Cmd.seq, ⟨0, WordFrontend.Certificate.sequenceConstructor⟩),
     (``Bind.bind, WordFrontend.Certificate.bindSignature),
     (``Monad.toBind, WordFrontend.Certificate.monadBindSignature),
     (``instMonadOption, WordFrontend.Certificate.optionMonadSignature),
     (``WordFrontendFacts.readNat, ⟨0, WordFrontend.Read.natSignature⟩),
     (``WordFrontendFacts.read, ⟨0, WordFrontend.Read.wordSignature⟩),
     (``Array, WordFrontend.Read.arraySignature),
     (``Array.size, WordFrontend.Read.sizeSignature),
     (``LT.lt, WordFrontend.Read.lessSignature),
     (``instLTNat, ⟨0, .app (.const ``LT [.zero]) (.const ``Nat [])⟩),
     (``GetElem?.getElem?, WordFrontend.Read.getSignature),
     (``Array.instGetElem?NatLtSize, WordFrontend.Read.arrayInstanceSignature),
     (``BitVec.toNat, ⟨0, WordFrontend.Read.toNatSignature⟩),
     (``HybridWord.State.arrays, ⟨0, WordFrontend.Read.arraysSignature⟩),
     (``HybridWord.Expr.readNat, ⟨0, WordFrontend.Read.natConstructor⟩),
     (``HybridWord.Expr.read, ⟨0, WordFrontend.Read.wordConstructor⟩),
     (``WordFrontendFacts.register, ⟨0, WordFrontend.Certificate.registerSignature⟩),
     (``HybridWord.State.regs, ⟨0, .forallE WordFrontend.Certificate.stateType
       (.forallE (.const ``Nat []) WordFrontend.Certificate.wordType)⟩),
     (``HybridWord.Expr.reg, ⟨0, .forallE (.const ``Nat []) WordFrontend.Certificate.exprType⟩),
     (``HybridWord.Cmd.eval, ⟨0, WordFrontend.Certificate.evalSignature⟩),
     (``Option, WordFrontend.Certificate.optionSignature),
     (``Eq, WordFrontend.Certificate.eqSignature),
     (``List.nil, WordFrontend.Certificate.nilSignature),
     (``List.cons, WordFrontend.Certificate.consSignature)]
  let arithmetic := [WordFrontend.Arithmetic.Binary.add, .sub, .mul, .div]
  let signatures := signatures ++
    [(``OfNat.ofNat, WordFrontend.Arithmetic.ofNatSignature),
     (``instOfNatNat, ⟨0, WordFrontend.Arithmetic.natInstanceSignature⟩),
     (``OfNat, WordFrontend.Arithmetic.ofNatClassSignature),
     (``BitVec.instOfNat, ⟨0, WordFrontend.Arithmetic.bitvecOfNatSignature⟩),
     (``WordFrontendFacts.literal, ⟨0, WordFrontend.Arithmetic.literalSignature⟩)] ++
    arithmetic.flatMap (fun op =>
      [(op.className, op.classSignature), (op.instanceName, ⟨0, op.instanceSignature⟩),
       (op.liftedInstance, op.liftedSignature), (op.method, op.methodSignature),
       (op.fact, ⟨0, op.signature⟩)])
  let some wd := LeanTypeReduction.load native ``HybridWord.Word
    | throwError "could not load the Word abbreviation"
  unless wd.declaration.levelParams.isEmpty &&
      wd.body.val.instL [] == WordFrontend.Arithmetic.bitvecType &&
      wd.type.val.instL [] == .sort (.succ .zero) do
    throwError "arithmetic success theorem has a mismatched Word abbreviation"
  for (name, expected) in signatures do
    let some declaration := LeanLibrary.load native name
      | throwError "could not load frontend fact {name}"
    unless declaration.signature == expected do
      throwError "frontend success theorem has a mismatched library signature: {name}"

-- Compare actual elaboration, including the compact-natural and BV32-wrap
-- boundaries, to the symbolic literal representation used by the theorem.
run_cmd do
  let native ← getEnv
  for (name,n) in [( ``literalZero,0),(``literalSmall,1),(``literalCompact,64),(``literalWrap,4294967297)] do
    let some declaration := LeanTypeReduction.load native name
      | throwError "could not load literal regression {name}"
    unless declaration.body.val == WordFrontend.Arithmetic.literalTerm n do
      throwError "literal success theorem does not describe actual Lean elaboration: {name}"

private def staticLower : Int := -3
private def staticUpper : Int := 64

run_cmd do
  let native ← getEnv
  for (name, expected) in [(``staticLower, WordFrontend.Certificate.For.negativeTerm
      (WordFrontend.Certificate.For.naturalTerm 3)),
      (``staticUpper, WordFrontend.Certificate.For.naturalTerm 64)] do
    let some declaration := LeanTypeReduction.load native name | throwError "could not load bound {name}"
    unless declaration.body.val == expected do
      throwError "static-bound theorem does not describe actual Lean elaboration: {name}"

/-- Construct a large ordinary Lean definition as regression data. This helper
is test-only: the public input remains `def`, with no new HLS source notation.
Each let only aliases the current State; it does not retain an old snapshot. -/
private def aliases : Nat → Lean.Expr
  | 0 => WordFrontend.someExpr WordFrontend.state (.bvar 0)
  | n+1 => .letE `current WordFrontend.state (.bvar 0) (aliases n) false

/-- Keep the first scalar alive across later bindings. Only testing references
to the newest variable would miss the numeric-representation boundary at 64. -/
private def oldLocal : Nat → Nat → Lean.Expr
  | 0,depth => WordFrontend.someExpr WordFrontend.state
      (WordFrontend.app ``HybridWord.State.set [.bvar (depth+1),.lit (.natVal 0),.bvar depth])
  | n+1,depth => .letE `unused WordFrontend.word
      (WordFrontend.app ``HybridWord.State.regs [.bvar (depth+1),.lit (.natVal 0)])
      (oldLocal n (depth+1)) false

run_cmd do
  let body := Lean.Expr.lam `s WordFrontend.state (aliases 80) .default
  liftCoreM <| addAndCompile (.defnDecl {
    name := `IRComparison.FrontendDepthExamples.deepAliases
    levelParams := [],type := .forallE `s WordFrontend.state
      (WordFrontend.option WordFrontend.state) .default,value := body,
    hints := .abbrev,safety := .safe })

run_cmd do
  let body := Lean.Expr.lam `s WordFrontend.state
    (.letE `first WordFrontend.word
      (WordFrontend.app ``HybridWord.State.regs [.bvar 0,.lit (.natVal 0)])
      (oldLocal 70 0) false) .default
  liftCoreM <| addAndCompile (.defnDecl {
    name := `IRComparison.FrontendDepthExamples.earlierScalar
    levelParams := [],type := .forallE `s WordFrontend.state
      (WordFrontend.option WordFrontend.state) .default,value := body,
    hints := .abbrev,safety := .safe })

def buffers : FixedMemory.Declarations := #[]
def annotated : CertifiedHLS.Program := fun s => some s
hls_fixed_program annotated using buffers as annotatedHLS
hls_fixed_program deepAliases using buffers as generated
hls_fixed_program earlierScalar using buffers as earlierScalarHLS

example (fuel : Nat) (strategy : Circuit.Pipelining.LoopStrategy) :
    ∃ compiled, generated.compile [] fuel strategy = .ok compiled :=
  generated.generates [] fuel strategy rfl

end IRComparison.FrontendDepthExamples
