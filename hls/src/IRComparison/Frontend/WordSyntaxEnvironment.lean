import IRComparison.Frontend.WordFunctionSyntax
import IRComparison.Frontend.WordScalarEnvironmentTransport

/-! Transport structured source judgments along signature installation. -/
namespace IRComparison.WordFrontend
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic

theorem StructuralSyntax.Form.install (form : StructuralSyntax.Form before ctx p e requirements)
    (installed : SignatureExtension before after) : StructuralSyntax.Form after ctx p e requirements := by
  induction form with
  | returns tag => exact .returns tag
  | write a i v => exact .write (a.install installed) (i.install installed) (v.install installed)
  | assign tag r v => exact .assign tag (r.install installed) (v.install installed)
  | copy d s n => exact .copy (d.install installed) (s.install installed) (n.install installed)
  | branch v d _ _ checked a b => exact .branch (v.install installed) (d.install installed) a b

def Certificate.For.Bound.install (value : For.Bound before ctx n)
    (installed : SignatureExtension before after) : For.Bound after ctx n :=
  ⟨value.represented,value.typed.install installed (fun _ _ _ h => h),value.closed⟩

theorem ScopedSyntax.ReadForm.install (form : ScopedSyntax.ReadForm before ctx p e)
    (installed : SignatureExtension before after) : ScopedSyntax.ReadForm after ctx p e := by
  cases form with
  | natural a n shape => exact .natural (a.install installed) (n.install installed) shape
  | bitsNatural a n shape => exact .bitsNatural (a.install installed) (n.install installed) shape
  | word a k => exact .word (a.install installed) (k.install installed)
  | bitsWord a k => exact .bitsWord (a.install installed) (k.install installed)

theorem ScopedSyntax.Syntax.install (form : ScopedSyntax.Syntax before mode ctx p e requirements)
    (installed : SignatureExtension before after) : ScopedSyntax.Syntax after mode ctx p e requirements := by
  induction form with
  | atom form => exact .atom (form.install installed)
  | write a i v => exact .write (a.install installed) (i.install installed) (v.install installed)
  | assign tag r v => exact .assign tag (r.install installed) (v.install installed)
  | branch v d _ _ checked a b => exact .branch (v.install installed) (d.install installed) a b
  | letValue annotation v _ name flag checked next => exact .letValue annotation (v.install installed) next name flag
  | sequence _ _ name info checked first next => exact .sequence first next name info
  | bindValue v _ name info checked next => exact .bindValue (v.install installed) next name info
  | bindBits v _ name info checked next => exact .bindBits (v.install installed) next name info
  | stateAlias _ name flag checked next => exact .stateAlias next name flag
  | stepBranch v d _ _ checked a b => exact .stepBranch (v.install installed) (d.install installed) a b
  | unitBody _ name info checked next => exact .unitBody next name info
  | unitLoop _ name info checked next => exact .unitLoop next name info
  | stateLet _ _ notAlias name flag checked value next => exact .stateLet value next notAlias name flag
  | stepStateLet _ _ notAlias name flag checked value next => exact .stepStateLet value next notAlias name flag
  | stepAlias _ name flag checked next => exact .stepAlias next name flag
  | stepLetValue annotation v _ name flag checked next => exact .stepLetValue annotation (v.install installed) next name flag
  | stepBindValue v _ name info checked next => exact .stepBindValue (v.install installed) next name info
  | stepBindBits v _ name info checked next => exact .stepBindBits (v.install installed) next name info
  | stepSequence _ _ name info checked first next => exact .stepSequence first next name info
  | valueCurrent => exact .valueCurrent
  | valueAssign r v => exact .valueAssign (r.install installed) (v.install installed)
  | yield _ checked ih => exact .yield ih
  | forStatic a b c _ kn tn ki ti checked body =>
    exact .forStatic (a.install installed) (b.install installed) (c.install installed) body kn tn ki ti
  | forRange kind count _ kn tn ki ti checked body => exact .forRange kind (count.install installed) body kn tn ki ti


/-- Function bindings are source data; signature installation changes only
their independent typing derivations. -/
theorem FunctionSyntax.Syntax.install (form : FunctionSyntax.Syntax before ctx p σ scope source requirements mode)
    (installed : SignatureExtension before after) : FunctionSyntax.Syntax after ctx p σ scope source requirements mode := by
  induction form with
  | plain body => exact .plain (body.install installed)
  | base head body => exact .base head (body.install installed)
  | valueCurrent current => exact .valueCurrent current
  | valueAssign register rn current value checked => exact .valueAssign register rn current (value.install installed)
  | yield value ih => exact .yield ih
  | unitBody next binder info ih => exact .unitBody ih binder info
  | unitLoop next binder info ih => exact .unitLoop ih binder info
  | stateAlias current next binder flag ih => exact .stateAlias current ih binder flag
  | stepAlias current next binder flag ih => exact .stepAlias current ih binder flag
  | stateLet value next notAlias binder flag ia ib => exact .stateLet ia ib notAlias binder flag
  | stepStateLet value next notAlias binder flag ia ib => exact .stepStateLet ia ib notAlias binder flag
  | stepSequence first next binder info ia ib => exact .stepSequence ia ib binder info
  | forStatic start stop stride current body kn tn ki ti checked ih => exact .forStatic (start.install installed) (stop.install installed) (stride.install installed) current ih kn tn ki ti
  | forRange kind count current body kn tn ki ti checked ih => exact .forRange kind (count.install installed) current ih kn tn ki ti
  | letValue annotation value next binder flag checked ih => exact .letValue annotation (value.install installed) ih binder flag
  | stepLetValue annotation value next binder flag checked ih => exact .stepLetValue annotation (value.install installed) ih binder flag
  | bindValue annotation value next binder info checked ih => exact .bindValue annotation (value.install installed) ih binder info
  | stepBindValue annotation value next binder info checked ih => exact .stepBindValue annotation (value.install installed) ih binder info
  | sequence first next binder info ia ib => exact .sequence ia ib binder info
  | branch value decision yes no checked ia ib => exact .branch (value.install installed) (decision.install installed) ia ib
  | booleanBranch value yes no checked ia ib => exact .booleanBranch (value.install installed) ia ib
  | stepBooleanBranch value yes no checked ia ib => exact .stepBooleanBranch (value.install installed) ia ib
  | annotatedBooleanBranch annotation operand value represented typed form yes no checked ia ib =>
    exact .annotatedBooleanBranch annotation operand (value.install installed) represented
      (typed.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed)) (form.install installed) ia ib
  | annotatedStepBooleanBranch annotation operand value represented typed form yes no checked ia ib =>
    exact .annotatedStepBooleanBranch annotation operand (value.install installed) represented
      (typed.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed)) (form.install installed) ia ib
  | retainedCall fn argument allowed binding coherent arguments next count dt bt ft ats tc pt rr sr ih =>
    exact .retainedCall fn argument allowed binding coherent (arguments.install installed) ih count
      (dt.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed))
      (bt.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed))
      (ft.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed))
      (ats.imp (fun _ _ h => h.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed))) tc
      (fun before after same nonempty => (pt before after same nonempty).install installed
        (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed)) rr sr
  | functionLet binder ty value next flag binding tail tr tt bt vt rr sr ih =>
    exact .functionLet binder ty value next flag binding ih tr
      (tt.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed))
      (bt.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed))
      (vt.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed)) rr sr
  | stepFunctionLet binder ty value next flag binding tail tr tt bt vt rr sr ih =>
    exact .stepFunctionLet binder ty value next flag binding ih tr
      (tt.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed))
      (bt.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed))
      (vt.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed)) rr sr

/-- Installing the declared signatures supplies every library field used by
syntax induction; no certificate-check success is assumed. -/
theorem ScopedSyntax.Library.install (library : ScopedSyntax.Library before)
    (installed : SignatureExtension before after) : ScopedSyntax.Library after :=
{
  scalars :=
    { negClass := installed `Neg Arithmetic.negClassSignature library.scalars.negClass,
      negInstance :=
        installed `BitVec.instNeg { uvars := 0, type := Arithmetic.negInstanceSignature } library.scalars.negInstance,
      negMethod := installed `Neg.neg Arithmetic.negMethodSignature library.scalars.negMethod,
      natural := installed `Nat { uvars := 0, type := VExpr.sort VLevel.zero.succ } library.scalars.natural,
      word :=
        installed `IRComparison.HybridWord.Word { uvars := 0, type := VExpr.sort VLevel.zero.succ }
          library.scalars.word,
      literals :=
        { zero := installed `Nat.zero { uvars := 0, type := VExpr.const `Nat [] } library.scalars.literals.zero,
          successor :=
            installed `Nat.succ { uvars := 0, type := (VExpr.const `Nat []).forallE (VExpr.const `Nat []) }
              library.scalars.literals.successor,
          multiply :=
            installed `Nat.mul
              { uvars := 0,
                type := (VExpr.const `Nat []).forallE ((VExpr.const `Nat []).forallE (VExpr.const `Nat [])) }
              library.scalars.literals.multiply },
      ofNatClass := installed `OfNat Arithmetic.ofNatClassSignature library.scalars.ofNatClass,
      bitvecOfNat :=
        installed `BitVec.instOfNat { uvars := 0, type := Arithmetic.bitvecOfNatSignature } library.scalars.bitvecOfNat,
      ofNat := installed `OfNat.ofNat Arithmetic.ofNatSignature library.scalars.ofNat,
      natInstance :=
        installed `instOfNatNat { uvars := 0, type := Arithmetic.natInstanceSignature } library.scalars.natInstance,
      bitvec :=
        installed `BitVec { uvars := 0, type := Arithmetic.natType.forallE (VExpr.sort VLevel.zero.succ) }
          library.scalars.bitvec,
      classes := fun op => installed op.className op.classSignature (library.scalars.classes op),
      instances := fun op =>
        installed op.instanceName { uvars := 0, type := op.instanceSignature } (library.scalars.instances op),
      lifted := fun op => installed op.liftedInstance op.liftedSignature (library.scalars.lifted op),
      methods := fun op => installed op.method op.methodSignature (library.scalars.methods op),
      heterogeneous := fun op => installed _ _ (library.scalars.heterogeneous op),
      negFact :=
        installed `IRComparison.WordFrontendFacts.neg { uvars := 0, type := Arithmetic.negSignature }
          library.scalars.negFact,
      negConstructor :=
        installed `IRComparison.HybridWord.Expr.neg
          { uvars := 0, type := Certificate.exprType.forallE Certificate.exprType } library.scalars.negConstructor,
      ite := installed `ite Certificate.Branch.iteSignature library.scalars.ite,
      selectFact :=
        installed `IRComparison.WordFrontendFacts.select { uvars := 0, type := Certificate.Branch.Select.signature }
          library.scalars.selectFact,
      selectConstructor :=
        installed `IRComparison.HybridWord.Expr.select
          { uvars := 0, type := Certificate.Branch.Select.constructorSignature } library.scalars.selectConstructor,
      registerFact :=
        installed `IRComparison.WordFrontendFacts.register { uvars := 0, type := Certificate.registerSignature }
          library.scalars.registerFact,
      registerAccessor :=
        installed `IRComparison.HybridWord.State.regs
          { uvars := 0, type := Certificate.stateType.forallE ((VExpr.const `Nat []).forallE Certificate.wordType) }
          library.scalars.registerAccessor,
      registerConstructor :=
        installed `IRComparison.HybridWord.Expr.reg
          { uvars := 0, type := (VExpr.const `Nat []).forallE Certificate.exprType }
          library.scalars.registerConstructor,
      localLibrary :=
        {
          word :=
            installed `IRComparison.HybridWord.Word { uvars := 0, type := VExpr.sort VLevel.zero.succ }
              library.scalars.localLibrary.word,
          nil := installed `List.nil Certificate.nilSignature library.scalars.localLibrary.nil,
          cons := installed `List.cons Certificate.consSignature library.scalars.localLibrary.cons,
          localZero :=
            installed `IRComparison.WordFrontendFacts.localZero { uvars := 0, type := Certificate.localZeroSignature }
              library.scalars.localLibrary.localZero,
          localSucc :=
            installed `IRComparison.WordFrontendFacts.localSucc { uvars := 0, type := Certificate.localSuccSignature }
              library.scalars.localLibrary.localSucc,
          constructor :=
            installed `IRComparison.HybridWord.Expr.local
              { uvars := 0, type := (VExpr.const `Nat []).forallE Certificate.exprType }
              library.scalars.localLibrary.constructor,
          naturals :=
            {
              zero :=
                installed `Nat.zero { uvars := 0, type := VExpr.const `Nat [] }
                  library.scalars.localLibrary.naturals.zero,
              successor :=
                installed `Nat.succ { uvars := 0, type := (VExpr.const `Nat []).forallE (VExpr.const `Nat []) }
                  library.scalars.localLibrary.naturals.successor,
              multiply :=
                installed `Nat.mul
                  { uvars := 0,
                    type := (VExpr.const `Nat []).forallE ((VExpr.const `Nat []).forallE (VExpr.const `Nat [])) }
                  library.scalars.localLibrary.naturals.multiply } },
      sideFact := fun side =>
        installed side.fact { uvars := 0, type := side.signature } (library.scalars.sideFact side),
      sideConstructor := fun side =>
        installed side.target { uvars := 0, type := Certificate.exprType } (library.scalars.sideConstructor side),
      indexFact :=
        installed `IRComparison.WordFrontendFacts.index { uvars := 0, type := Certificate.indexSignature }
          library.scalars.indexFact,
      indexConstructor :=
        installed `IRComparison.HybridWord.Expr.index { uvars := 0, type := Certificate.exprType }
          library.scalars.indexConstructor,
      literalFact :=
        installed `IRComparison.WordFrontendFacts.literal { uvars := 0, type := Arithmetic.literalSignature }
          library.scalars.literalFact,
      literalConstructor :=
        installed `IRComparison.HybridWord.Expr.lit
          { uvars := 0, type := Certificate.wordType.forallE Certificate.exprType } library.scalars.literalConstructor,
      binaryFact := fun op => installed op.fact { uvars := 0, type := op.signature } (library.scalars.binaryFact op),
      binaryConstructor := fun op =>
        installed op.target
          { uvars := 0, type := Certificate.exprType.forallE (Certificate.exprType.forallE Certificate.exprType) }
          (library.scalars.binaryConstructor op) },
  returns :=
    {
      state :=
        installed `IRComparison.HybridWord.State { uvars := 0, type := VExpr.sort VLevel.zero.succ }
          library.returns.state,
      option := installed `Option Certificate.optionSignature library.returns.option,
      someDecl := installed `Option.some Certificate.Return.someSignature library.returns.someDecl,
      pureDecl := installed `Pure.pure Certificate.Return.pureSignature library.returns.pureDecl,
      applicative :=
        installed `Alternative.toApplicative (Certificate.Return.projectionSignature `Alternative `Applicative)
          library.returns.applicative,
      projectPure :=
        installed `Applicative.toPure (Certificate.Return.projectionSignature `Applicative `Pure)
          library.returns.projectPure,
      alternative :=
        installed `instAlternativeOption Certificate.Return.alternativeSignature library.returns.alternative },
  returnFact := fun form => installed form.fact { uvars := 0, type := form.signature } (library.returnFact form),
  skipConstructor :=
    installed `IRComparison.HybridWord.Cmd.skip { uvars := 0, type := Certificate.cmdType } library.skipConstructor,
  storeFact :=
    installed `IRComparison.WordFrontendFacts.store { uvars := 0, type := Certificate.storeSignature }
      library.storeFact,
  storeConstructor :=
    installed `IRComparison.HybridWord.Cmd.store { uvars := 0, type := Certificate.storeConstructor }
      library.storeConstructor,
  assignFact := fun form =>
    installed form.assignFact { uvars := 0, type := Certificate.assignSignatureWith form.header }
      (library.assignFact form),
  assignConstructor :=
    installed `IRComparison.HybridWord.Cmd.assign { uvars := 0, type := Certificate.Return.assignConstructor }
      library.assignConstructor,
  setter :=
    installed `IRComparison.HybridWord.State.set { uvars := 0, type := Certificate.Return.setterSignature }
      library.setter,
  writer :=
    installed `IRComparison.HybridWord.State.write { uvars := 0, type := Certificate.writeSignature } library.writer,
  copyFact :=
    installed `IRComparison.WordFrontendFacts.copy { uvars := 0, type := Certificate.copySignature } library.copyFact,
  copyConstructor :=
    installed `IRComparison.HybridWord.Cmd.copy { uvars := 0, type := Certificate.copyConstructor }
      library.copyConstructor,
  copier :=
    installed `IRComparison.HybridWord.State.copy { uvars := 0, type := Certificate.copySourceSignature }
      library.copier,
  branchFact :=
    installed `IRComparison.WordFrontendFacts.branch { uvars := 0, type := Certificate.Branch.signature }
      library.branchFact,
  branchConstructor :=
    installed `IRComparison.HybridWord.Cmd.branch { uvars := 0, type := Certificate.Branch.constructorSignature }
      library.branchConstructor,
  ite := installed `ite Certificate.Branch.iteSignature library.ite,
  scalarEval :=
    installed `IRComparison.HybridWord.Expr.eval { uvars := 0, type := ScalarConversion.evalSignature }
      library.scalarEval,
  cons := installed `List.cons Certificate.consSignature library.cons,
  eq := installed `Eq Certificate.eqSignature library.eq,
  eval := installed `IRComparison.HybridWord.Cmd.eval { uvars := 0, type := Certificate.evalSignature } library.eval,
  bind :=
    { option := installed `Option Certificate.optionSignature library.bind.option,
      bind := installed `Bind.bind Certificate.bindSignature library.bind.bind,
      projector := installed `Monad.toBind Certificate.monadBindSignature library.bind.projector,
      instanceOption := installed `instMonadOption Certificate.optionMonadSignature library.bind.instanceOption },
  sequence :=
    installed `IRComparison.WordFrontendFacts.sequence { uvars := 0, type := Certificate.sequenceSignature }
      library.sequence,
  sequenceConstructor :=
    installed `IRComparison.HybridWord.Cmd.seq { uvars := 0, type := Certificate.sequenceConstructor }
      library.sequenceConstructor,
  letValue :=
    installed `IRComparison.WordFrontendFacts.letValue { uvars := 0, type := Certificate.letValueSignature }
      library.letValue,
  letValueConstructor :=
    installed `IRComparison.HybridWord.Cmd.letValue { uvars := 0, type := Certificate.bindValueConstructor }
      library.letValueConstructor,
  stateLet :=
    installed `IRComparison.WordFrontendFacts.letState { uvars := 0, type := Certificate.StateLet.signature }
      library.stateLet,
  stateAlias :=
    installed `IRComparison.WordFrontendFacts.letStateAlias { uvars := 0, type := Certificate.StateAlias.signature }
      library.stateAlias,
  reads :=
    {
      word :=
        installed `IRComparison.HybridWord.Word { uvars := 0, type := VExpr.sort VLevel.zero.succ } library.reads.word,
      natural := installed `Nat { uvars := 0, type := VExpr.sort VLevel.zero.succ } library.reads.natural,
      array := installed `Array Read.arraySignature library.reads.array,
      size := installed `Array.size Read.sizeSignature library.reads.size,
      less := installed `LT.lt Read.lessSignature library.reads.less,
      instanceLess :=
        installed `instLTNat { uvars := 0, type := (VExpr.const `LT [VLevel.zero]).app (VExpr.const `Nat []) }
          library.reads.instanceLess,
      getClass := installed `GetElem? Read.getClassSignature library.reads.getClass,
      getter := installed `GetElem?.getElem? Read.getSignature library.reads.getter,
      instanceArray := installed `Array.instGetElem?NatLtSize Read.arrayInstanceSignature library.reads.instanceArray,
      arrays :=
        installed `IRComparison.HybridWord.State.arrays { uvars := 0, type := Read.arraysSignature }
          library.reads.arrays,
      toNat := installed `BitVec.toNat { uvars := 0, type := Read.toNatSignature } library.reads.toNat },
  readNatFact :=
    installed `IRComparison.WordFrontendFacts.readNat { uvars := 0, type := Read.natSignature } library.readNatFact,
  readNatConstructor :=
    installed `IRComparison.HybridWord.Expr.readNat { uvars := 0, type := Read.natConstructor }
      library.readNatConstructor,
  readFact :=
    installed `IRComparison.WordFrontendFacts.read { uvars := 0, type := Read.wordSignature } library.readFact,
  readConstructor :=
    installed `IRComparison.HybridWord.Expr.read { uvars := 0, type := Read.wordConstructor } library.readConstructor,
  stepStateLet :=
    installed `IRComparison.WordLoopFacts.letState { uvars := 0, type := StructuralStateLet.Loop.signature }
      library.stepStateLet,
  units :=
    { typeDecl := installed `PUnit Certificate.UnitStep.unitSignature library.units.typeDecl,
      valueDecl := installed `PUnit.unit Certificate.UnitStep.valueSignature library.units.valueDecl },
  unitFact := fun isStep =>
    installed (StructuralUnit.factName isStep) { uvars := 0, type := StructuralUnit.signature isStep }
      (library.unitFact isStep),
  stepAlias :=
    installed `IRComparison.WordLoopFacts.letStateAlias { uvars := 0, type := StructuralStep.Alias.signature }
      library.stepAlias,
  stepLetValue :=
    installed `IRComparison.WordLoopFacts.letValue { uvars := 0, type := StructuralReadBind.letValueSignature }
      library.stepLetValue,
  stepBindValue :=
    installed `IRComparison.WordLoopFacts.bindValue { uvars := 0, type := StructuralReadBind.bindValueSignature }
      library.stepBindValue,
  stepBranch :=
    installed `IRComparison.WordLoopFacts.branchCmd { uvars := 0, type := StructuralStep.Conditional.signature }
      library.stepBranch,
  stepSequence :=
    installed `IRComparison.WordLoopFacts.sequence { uvars := 0, type := StructuralStep.sequenceSignature }
      library.stepSequence,
  steps :=
    {
      state :=
        installed `IRComparison.HybridWord.State { uvars := 0, type := VExpr.sort VLevel.zero.succ }
          library.steps.state,
      option := installed `Option Certificate.optionSignature library.steps.option,
      someDecl := installed `Option.some Certificate.Return.someSignature library.steps.someDecl,
      pureDecl := installed `Pure.pure Certificate.Return.pureSignature library.steps.pureDecl,
      applicative :=
        installed `Alternative.toApplicative (Certificate.Return.projectionSignature `Alternative `Applicative)
          library.steps.applicative,
      projectPure :=
        installed `Applicative.toPure (Certificate.Return.projectionSignature `Applicative `Pure)
          library.steps.projectPure,
      alternative := installed `instAlternativeOption Certificate.Return.alternativeSignature library.steps.alternative,
      step := installed `ForInStep Certificate.Step.stepSignature library.steps.step,
      yieldDecl := installed `ForInStep.yield Certificate.Step.yieldSignature library.steps.yieldDecl,
      liftDecl :=
        installed `IRComparison.WordLoopFacts.lift { uvars := 0, type := Certificate.Step.liftSignature }
          library.steps.liftDecl,
      someYield :=
        installed `IRComparison.WordLoopFacts.someYield { uvars := 0, type := Certificate.Step.someYieldSignature }
          library.steps.someYield },
  compose :=
    installed `IRComparison.WordLoopFacts.compose { uvars := 0, type := Certificate.For.composeSignature }
      library.compose,
  forFact :=
    installed `IRComparison.WordLoopFacts.forStatic { uvars := 0, type := Certificate.For.signature } library.forFact,
  forConstructor :=
    installed `IRComparison.HybridWord.Cmd.forStatic { uvars := 0, type := Certificate.For.constructorSignature }
      library.forConstructor,
  range :=
    installed `IRComparison.HybridWord.range { uvars := 0, type := Certificate.For.rangeSignature } library.range,
  decisions := {
    boolean := installed _ _ library.decisions.boolean
    truth := installed _ _ library.decisions.truth
    equality := installed _ _ library.decisions.equality
    decidable := installed _ _ library.decisions.decidable
    decidableEq := installed _ _ library.decisions.decidableEq
    bneMethod := installed _ _ library.decisions.bneMethod
    beqInstance := installed _ _ library.decisions.beqInstance
    bitvecInstance := installed _ _ library.decisions.bitvecInstance
    boolInstance := installed _ _ library.decisions.boolInstance }
  bounds := {
    natural := {
      zero := installed _ _ library.bounds.natural.zero
      successor := installed _ _ library.bounds.natural.successor
      multiply := installed _ _ library.bounds.natural.multiply }
    integer := installed _ _ library.bounds.integer
    ofNat := installed _ _ library.bounds.ofNat
    intOfNat := installed _ _ library.bounds.intOfNat
    negate := installed _ _ library.bounds.negate
    intNeg := installed _ _ library.bounds.intNeg
    intBinary := fun op => installed _ _ (library.bounds.intBinary op) }
  forHeader :=
    {
      word :=
        installed `IRComparison.HybridWord.Word { uvars := 0, type := VExpr.sort VLevel.zero.succ }
          library.forHeader.word,
      state :=
        installed `IRComparison.HybridWord.State { uvars := 0, type := VExpr.sort VLevel.zero.succ }
          library.forHeader.state,
      option := installed `Option Certificate.optionSignature library.forHeader.option,
      monad := installed `instMonadOption Certificate.optionMonadSignature library.forHeader.monad,
      forIn := installed `ForIn.forIn Certificate.For.Header.forInSignature library.forHeader.forIn,
      forInInstance :=
        installed `instForInOfForIn' Certificate.For.Header.forInInstanceSignature library.forHeader.forInInstance,
      inferInstanceDecl :=
        installed `inferInstance Certificate.For.Header.inferInstanceSignature library.forHeader.inferInstanceDecl,
      membershipInstance :=
        installed `List.instMembership Certificate.For.Header.membershipInstanceSignature
          library.forHeader.membershipInstance,
      listInstance :=
        installed `List.instForIn'InferInstanceMembershipOfMonad Certificate.For.Header.listInstanceSignature
          library.forHeader.listInstance,
      list := installed `List Certificate.For.Header.listSignature library.forHeader.list,
      membership := installed `Membership Certificate.For.Header.membershipSignature library.forHeader.membership },
  naturalLoops :=
    { ofNat := installed `BitVec.ofNat { uvars := 0, type := NaturalScope.ofNatSignature } library.naturalLoops.ofNat,
      range := installed `List.range { uvars := 0, type := NaturalLoop.rangeSignature } library.naturalLoops.range,
      fold := installed `List.foldlM NaturalLoop.foldSignature library.naturalLoops.fold,
      fact := fun kind => installed kind.fact { uvars := 0, type := kind.signature } (library.naturalLoops.fact kind),
      constructor :=
        installed `IRComparison.HybridWord.Cmd.forRange { uvars := 0, type := NaturalLoop.constructorSignature }
          library.naturalLoops.constructor },
  bindValueFact :=
    installed `IRComparison.WordFrontendFacts.bindValue { uvars := 0, type := Certificate.bindValueSignature }
      library.bindValueFact }

end IRComparison.WordFrontend
