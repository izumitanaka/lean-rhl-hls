import IRComparison.Frontend.WordHelperCompleteness
import IRComparison.Frontend.WordStructuralUnit
import IRComparison.Frontend.WordLexicalScalarSyntax
import IRComparison.Frontend.WordNaturalLoop
import IRComparison.Frontend.WordAnnotatedStepLet
import IRComparison.Frontend.WordAnnotatedStepRead
import IRComparison.Frontend.WordReadElementCompleteness

/-! Context-indexed source syntax and simultaneous success/typing induction.
The constructors describe ordinary elaborated Lean terms, not parser runs.
The runtime input is unchanged; this is a proof-side judgment. -/
namespace IRComparison.WordFrontend.ScopedSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate
open StructuralSyntax StructuralBody
set_option maxHeartbeats 1800000

structure Library (env : VEnv) : Prop extends StructuralSyntax.Library env where
  scalarEval : env.constants ``HybridWord.Expr.eval = some ⟨0,ScalarConversion.evalSignature⟩
  cons : env.constants ``List.cons = some consSignature
  eq : env.constants ``Eq = some eqSignature
  eval : env.constants ``HybridWord.Cmd.eval = some ⟨0,evalSignature⟩
  bind : BindSignatures env
  sequence : env.constants ``WordFrontendFacts.sequence = some ⟨0,sequenceSignature⟩
  sequenceConstructor : env.constants ``HybridWord.Cmd.seq = some ⟨0,Certificate.sequenceConstructor⟩
  letValue : env.constants ``WordFrontendFacts.letValue = some ⟨0,letValueSignature⟩
  letValueConstructor : env.constants ``HybridWord.Cmd.letValue = some ⟨0,bindValueConstructor⟩
  stateLet : env.constants ``WordFrontendFacts.letState = some ⟨0,StateLet.signature⟩
  stateAlias : env.constants ``WordFrontendFacts.letStateAlias = some ⟨0,StateAlias.signature⟩
  reads : Read.Signatures env
  readNatFact : env.constants ``WordFrontendFacts.readNat = some ⟨0,Read.natSignature⟩
  readNatConstructor : env.constants ``HybridWord.Expr.readNat = some ⟨0,Read.natConstructor⟩
  readFact : env.constants ``WordFrontendFacts.read = some ⟨0,Read.wordSignature⟩
  readConstructor : env.constants ``HybridWord.Expr.read = some ⟨0,Read.wordConstructor⟩
  stepStateLet : env.constants ``WordLoopFacts.letState = some ⟨0,StructuralStateLet.Loop.signature⟩
  units : UnitStep.Signatures env
  unitFact : ∀ isStep, env.constants (StructuralUnit.factName isStep) = some ⟨0,StructuralUnit.signature isStep⟩
  stepAlias : env.constants ``WordLoopFacts.letStateAlias = some ⟨0,StructuralStep.Alias.signature⟩
  stepLetValue : env.constants ``WordLoopFacts.letValue = some ⟨0,StructuralReadBind.letValueSignature⟩
  stepBindValue : env.constants ``WordLoopFacts.bindValue = some ⟨0,StructuralReadBind.bindValueSignature⟩
  stepBranch : env.constants ``WordLoopFacts.branchCmd = some ⟨0,StructuralStep.Conditional.signature⟩
  stepSequence : env.constants ``WordLoopFacts.sequence = some ⟨0,StructuralStep.sequenceSignature⟩
  steps : Step.Signatures env
  compose : env.constants ``WordLoopFacts.compose = some ⟨0,For.composeSignature⟩
  forFact : env.constants ``WordLoopFacts.forStatic = some ⟨0,For.signature⟩
  forConstructor : env.constants ``HybridWord.Cmd.forStatic = some ⟨0,For.constructorSignature⟩
  range : env.constants ``HybridWord.range = some ⟨0,For.rangeSignature⟩
  decisions : Branch.BooleanLibrary env
  bounds : For.BoundSignatures env
  forHeader : For.Header.Signatures env
  naturalLoops : NaturalLoop.Signatures env
  bindValueFact : env.constants ``WordFrontendFacts.bindValue = some ⟨0,bindValueSignature⟩


def Library.scalarCertificates (library : Library env) : ScalarConversion.Signatures env :=
  ⟨library.scalars.word,library.returns.option,library.returns.someDecl,library.eq,library.scalarEval⟩

/-- The final named-source checks use the same declarations already required
by syntax induction, so their signature assumptions are not supplied twice. -/
def Library.connection (library : Library env) : ConnectionSignatures env :=
  ⟨library.scalars.word,library.returns.state,library.scalars.localLibrary.nil,
    library.eval,library.returns.option,library.eq⟩

theorem Library.stepOption_typed (library : Library env) :
    DirectTyping env 0 ctx (optionType Step.stepState) (.sort (.succ .zero)) := by
  have optionHead : DirectTyping env 0 ctx (.const ``Option [.zero])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .constant library.steps.option (by simp [VLevel.WF]) rfl
  exact DirectTyping.application optionHead library.steps.step_typed


/-- Library-head separation from the finite alias rules, independently of
any attempt to parse or normalize a source body. -/
structure Fresh (setup : Arithmetic.AliasSetup env) : Prop where
  scalar : ∀ n ∈ LexicalScalarSyntax.valueHeads, ∀ r ∈ setup.rules, n ≠ r.name
  condition : ∀ n ∈ [``bne,``Decidable,``instDecidableEqBool], ∀ r ∈ setup.rules, n ≠ r.name
  state : ∀ r ∈ setup.rules, ``HybridWord.State ≠ r.name
  eq : ∀ r ∈ setup.rules, ``Eq ≠ r.name
  unit : ∀ r ∈ setup.rules, ``PUnit ≠ r.name
  lift : ∀ r ∈ setup.rules, ``WordLoopFacts.lift ≠ r.name
  nat : ∀ r ∈ setup.rules, ``Nat ≠ r.name
  option : ∀ r ∈ setup.rules, ``Option ≠ r.name
  read : ∀ r ∈ setup.rules, ``GetElem?.getElem? ≠ r.name
  readAux : ∀ n ∈ [``Array.instGetElem?NatLtSize,``HybridWord.State.arrays,``BitVec.toNat,``ForInStep],
    ∀ r ∈ setup.rules, n ≠ r.name
  value : ∀ n ∈ [``Option.some,``Pure.pure,``HybridWord.State.write,
      ``HybridWord.State.copy,``ite,``Bind.bind,``ForIn.forIn,``List.foldlM], ∀ r ∈ setup.rules, n ≠ r.name

theorem represented_head (represented : Represents source core)
    (head : source.getAppFn = .const name levels) :
    ∃ vs, LeanTypeReduction.constantHead core = some (name,vs) := by
  induction represented with
  | bvar | sort | lam | forallE | letE | metadata | natural => cases head
  | constant h => cases head; exact ⟨_,rfl⟩
  | app f a ihf iha => exact ihf head

theorem head_form (fresh : Fresh setup) (represented : Represents source core)
    (head : source.getAppFn = .const name levels)
    (member : name ∈ [``Option.some,``Pure.pure,``HybridWord.State.write,
      ``HybridWord.State.copy,``ite,``Bind.bind,``ForIn.forIn,``List.foldlM]) :
    Arithmetic.ValueForm setup ctx core ty := by
  obtain ⟨vs,h⟩ := represented_head represented head
  exact .constant h (fresh.value _ member) (by simp only [List.mem_cons,List.mem_nil_iff,or_false] at member; rcases member with h|h|h|h|h|h|h|h <;> subst name <;> decide)

private theorem base_form (fresh : Fresh setup) (form : StructuralSyntax.Form env ctx p source requirements)
    (represented : Represents source core) : Arithmetic.ValueForm setup ctx core ty := by
  cases form with
  | returns tag => cases tag <;> exact head_form fresh represented rfl (by simp)
  | write => exact head_form fresh represented rfl (by simp)
  | assign tag => cases tag <;> exact head_form fresh represented rfl (by simp)
  | copy => exact head_form fresh represented rfl (by simp)
  | branch => exact head_form fresh represented rfl (by simp)

/-- Source syntax supplies scalar success; certificate transports are embedded
into the same proof relation used for enclosing structured commands. -/
theorem scalar_complete (setup : Arithmetic.AliasSetup env) (library : Library env)
    (closed : ClosedConstantTypes env) (fresh : Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p)
    (form : LexicalScalarSyntax.Form env ctx p [] source) :
    ∃ piece, ScalarEnvironment.parse env setup.conversion exposure ctx p source = some piece ∧
      Nonempty (ScalarCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup)) := by
  have someFresh := fresh.value ``Option.some (by simp)
  obtain ⟨piece,parsed,⟨typed⟩⟩ := LexicalScalarSyntax.parse_complete setup library.scalars
    library.scalarCertificates library.decisions fresh.condition closed fresh.eq someFresh fresh.scalar exposure inputs locals form
  exact ⟨piece,parsed,⟨typed.mapProofs
    (fun _ _ _ h => For.Casts.scalar library.scalarCertificates someFresh h)⟩⟩

/-- Array reads have statically declared array identifiers and either natural
literal indices or scalar BV32 indices. Source syntax is independent of readStep. -/
inductive ReadForm (env : VEnv) (ctx : List VExpr) (p : Inputs) : Lean.Expr → Prop where
  | natural (array : NatArgument env ctx a) (index : NatArgument env ctx n)
      (form : Read.NaturalIndex n) : ReadForm env ctx p (Read.source p.s a n)
  | word (array : NatArgument env ctx a) (index : LexicalScalarSyntax.Form env ctx p [] k) :
      ReadForm env ctx p (Read.wordSource p.s a k)
  | bitsNatural (array : NatArgument env ctx a) (index : NatArgument env ctx n)
      (form : Read.NaturalIndex n) : ReadForm env ctx p (Read.bitsSource p.s a n)
  | bitsWord (array : NatArgument env ctx a) (index : LexicalScalarSyntax.Form env ctx p [] k) :
      ReadForm env ctx p (Read.bitsSource p.s a (Read.wordIndex k))

theorem natural_value_form (setup : Arithmetic.AliasSetup env) (fresh : Fresh setup)
    (form : Read.NaturalIndex source) (represented : Represents source core) :
    Arithmetic.ValueForm setup ctx core Arithmetic.natType := by
  rcases form with raw | head
  · cases source <;> try cases raw
    rename_i literal
    cases literal with
    | strVal => cases raw
    | natVal n =>
      rw [represented.unique Represents.natural]
      apply LeanTyped.numeral_induction (fun e => Arithmetic.ValueForm setup ctx e Arithmetic.natType)
      · exact .constant rfl (setup.irreducibleNumeral _ (by simp)) (by decide)
      · intro a _; exact .constant rfl (setup.irreducibleNumeral _ (by simp)) (by decide)
      · intro a _; exact .constant rfl (setup.irreducibleNumeral _ (by simp)) (by decide)
  · have named : ∃ levels, source.getAppFn = .const ``OfNat.ofNat levels := by
      cases h : source.getAppFn <;> simp only [h,Lean.Expr.constName?] at head <;> try contradiction
      rename_i name levels
      cases Option.some.inj head
      exact ⟨levels,rfl⟩
    obtain ⟨levels,h⟩ := named
    obtain ⟨levels,head⟩ := represented_head represented h
    exact .constant head (fresh.scalar _ (by simp [LexicalScalarSyntax.valueHeads])) (by decide)

theorem read_complete (setup : Arithmetic.AliasSetup env) (library : Library env)
    (closed : ClosedConstantTypes env) (fresh : Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p)
    (form : ReadForm env ctx p source) :
    ∃ piece, readStep env setup.conversion exposure ctx p
      (ScalarEnvironment.parse env setup.conversion exposure ctx p) source = some piece ∧
      Nonempty (Read.ReadCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup)) := by
  have liftProof {value} {piece : Piece env ctx p value readExpected}
      (typed : Read.ReadCasts inputs piece (Arithmetic.SourceCasts env)) :
      Read.ReadCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup) :=
    ⟨typed.sourceCore,typed.value,typed.target,typed.proof.mono (fun _ _ _ h => .base (.base (.source h)))⟩
  cases form with
  | natural array index form =>
    obtain ⟨piece,parsed,⟨typed⟩⟩ := Read.nat_step_invariant_complete library.reads inputs array index form
      library.readNatFact library.readNatConstructor setup.conversion exposure
      (setup.covers_source library.scalars.toSignatures closed) _
    exact ⟨piece,parsed,⟨liftProof typed⟩⟩
  | bitsNatural array index form =>
    exact Read.bits_nat_complete setup library.scalars.toSignatures library.reads library.scalarCertificates inputs
      array index form (natural_value_form setup fresh form index.represented.property)
      fresh.read (fresh.readAux _ (by simp)) (fresh.readAux _ (by simp))
      library.readNatFact library.readNatConstructor
      (For.Casts.covered setup library.scalars.toSignatures library.steps closed
        library.cons library.eq library.eval fresh.state fresh.eq fresh.lift) exposure _
  | bitsWord array index =>
    obtain ⟨k,hk,⟨tk⟩⟩ := scalar_complete setup library closed fresh exposure inputs locals index
    exact Read.bits_word_complete setup library.scalars.toSignatures library.reads library.scalarCertificates
      inputs array tk fresh.read (fresh.readAux _ (by simp)) (fresh.readAux _ (by simp))
      (fresh.readAux _ (by simp)) library.readFact library.readConstructor
      (For.Casts.covered setup library.scalars.toSignatures library.steps closed
        library.cons library.eq library.eval fresh.state fresh.eq fresh.lift) exposure _ hk
  | word array index =>
    obtain ⟨k,hk,⟨tk⟩⟩ := scalar_complete setup library closed fresh exposure inputs locals index
    obtain ⟨piece,parsed,⟨typed⟩⟩ := Read.word_step_split_complete library.reads library.scalars.toSignatures
      inputs array tk
      library.readFact library.readConstructor (fun _ _ _ h => .base (.base (.source h)))
      (For.Casts.covered setup library.scalars.toSignatures library.steps closed
        library.cons library.eq library.eval fresh.state fresh.eq fresh.lift) exposure _ hk
    exact ⟨piece,parsed,⟨typed⟩⟩

theorem ReadForm.valueForm (form : ReadForm env ctx p source) (fresh : Fresh setup)
    (represented : Represents source core) : Arithmetic.ValueForm setup ctx core ty := by
  have head : source.getAppFn = .const ``GetElem?.getElem? [.zero,.zero,.zero] := by
    cases form <;> rfl
  obtain ⟨levels,h⟩ := represented_head represented head
  exact .constant h fresh.read (by decide)

/-- Scope changes are explicit indices of the syntax judgment. In particular,
a State continuation exposes only the latest State, while a value let retains
all earlier scalar locals. There is no parser-success premise. -/
inductive Syntax (env : VEnv) : Mode → List VExpr → Inputs → Lean.Expr →
    (requirements : Lean.Expr → Prop := fun _ => True) → Prop where
  | atom (form : StructuralSyntax.Form env ctx p (requirements := requirements) source)
      (checked : requirements source := by trivial) :
      Syntax env (requirements := requirements) .body ctx p source
  | write (array : NatArgument env ctx a) (index : LexicalScalarSyntax.Form env ctx p [] k)
      (value : LexicalScalarSyntax.Form env ctx p [] v)
      (checked : requirements (app ``HybridWord.State.write [p.s,a,k,v]) := by trivial) :
      Syntax env (requirements := requirements) .body ctx p (app ``HybridWord.State.write [p.s,a,k,v])
  | assign (tag : Return.Form) (register : NatArgument env ctx r)
      (value : LexicalScalarSyntax.Form env ctx p [] v)
      (checked : requirements (tag.source (app ``HybridWord.State.set [p.s,r,v])) := by trivial) :
      Syntax env (requirements := requirements) .body ctx p (tag.source (app ``HybridWord.State.set [p.s,r,v]))
  | branch (value : LexicalScalarSyntax.Form env ctx p [] v) (decision : Decision env ctx v d)
      (yes : Syntax env (requirements := requirements) .body ctx p a) (no : Syntax env (requirements := requirements) .body ctx p b)
      (checked : requirements (Branch.source v d a b) := by trivial) :
      Syntax env (requirements := requirements) .body ctx p (Branch.source v d a b)
  | letValue (annotation : WordBinder.Annotation) (value : LexicalScalarSyntax.Form env ctx p [] v)
      (next : Syntax env (requirements := requirements) .body (annotation.core::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} b)
      (binder : Lean.Name) (flag : Bool)
      (checked : requirements (WordBinder.letSource annotation binder v b flag) := by trivial) :
      Syntax env (requirements := requirements) .body ctx p (WordBinder.letSource annotation binder v b flag)
  | sequence (first : Syntax env (requirements := requirements) .body ctx p a)
      (next : Syntax env (requirements := requirements) .body (stateType::ctx) {p.lift with s := .bvar 0} b)
      (binder : Lean.Name) (info : Lean.BinderInfo)
      (checked : requirements (sequenceSource a (.lam binder state b info)) := by trivial) :
      Syntax env (requirements := requirements) .body ctx p (sequenceSource a (.lam binder state b info))
  | bindValue (value : ReadForm env ctx p v)
      (next : Syntax env (requirements := requirements) .body (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} b)
      (binder : Lean.Name) (info : Lean.BinderInfo)
      (checked : requirements (bindValueSource v (.lam binder word b info)) := by trivial) :
      Syntax env (requirements := requirements) .body ctx p (bindValueSource v (.lam binder word b info))
  | bindBits (value : ReadForm env ctx p v)
      (next : Syntax env (requirements := requirements) .body (Arithmetic.bitvecType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} b)
      (binder : Lean.Name) (info : Lean.BinderInfo)
      (checked : requirements (WordBinder.readSource .bitvec v
        (.lam binder WordBinder.Annotation.bitvec.native b info)) := by trivial) :
      Syntax env (requirements := requirements) .body ctx p (WordBinder.readSource .bitvec v
        (.lam binder WordBinder.Annotation.bitvec.native b info))
  | stateAlias (next : Syntax env (requirements := requirements) .body (stateType::ctx) {p.lift with s := .bvar 0} b)
      (binder : Lean.Name) (flag : Bool)
      (checked : requirements (.letE binder state p.s b flag) := by trivial) :
      Syntax env (requirements := requirements) .body ctx p (.letE binder state p.s b flag)
  | stepBranch (value : LexicalScalarSyntax.Form env ctx p [] v) (decision : Decision env ctx v d)
      (yes : Syntax env (requirements := requirements) .step ctx p a) (no : Syntax env (requirements := requirements) .step ctx p b)
      (checked : requirements (StructuralStep.Conditional.source v d a b) := by trivial) :
      Syntax env (requirements := requirements) .step ctx p (StructuralStep.Conditional.source v d a b)
  | unitBody (next : Syntax env (requirements := requirements) .body (UnitStep.unitType::ctx) p.lift b)
      (binder : Lean.Name) (info : Lean.BinderInfo)
      (checked : requirements (StructuralUnit.source false binder b info) := by trivial) :
      Syntax env (requirements := requirements) .body ctx p (StructuralUnit.source false binder b info)
  | unitLoop (next : Syntax env (requirements := requirements) .step (UnitStep.unitType::ctx) p.lift b)
      (binder : Lean.Name) (info : Lean.BinderInfo)
      (checked : requirements (StructuralUnit.source true binder b info) := by trivial) :
      Syntax env (requirements := requirements) .step ctx p (StructuralUnit.source true binder b info)
  | stateLet (value : Syntax env (requirements := requirements) .value ctx p v)
      (next : Syntax env (requirements := requirements) .body (stateType::ctx) {p.lift with s := .bvar 0} b)
      (notAlias : sameTerm v p.s = false) (binder : Lean.Name) (flag : Bool)
      (checked : requirements (StateLet.source binder v b flag) := by trivial) :
      Syntax env (requirements := requirements) .body ctx p (StateLet.source binder v b flag)
  | stepStateLet (value : Syntax env (requirements := requirements) .value ctx p v)
      (next : Syntax env (requirements := requirements) .step (stateType::ctx) {p.lift with s := .bvar 0} b)
      (notAlias : sameTerm v p.s = false) (binder : Lean.Name) (flag : Bool)
      (checked : requirements (StructuralStateLet.Loop.source binder v b flag) := by trivial) :
      Syntax env (requirements := requirements) .step ctx p (StructuralStateLet.Loop.source binder v b flag)
  | stepAlias (next : Syntax env (requirements := requirements) .step (stateType::ctx) {p.lift with s := .bvar 0} b)
      (binder : Lean.Name) (flag : Bool)
      (checked : requirements (.letE binder state p.s b flag) := by trivial) :
      Syntax env (requirements := requirements) .step ctx p (.letE binder state p.s b flag)
  | stepLetValue (annotation : WordBinder.Annotation) (value : LexicalScalarSyntax.Form env ctx p [] v)
      (next : Syntax env (requirements := requirements) .step (annotation.core::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} b)
      (binder : Lean.Name) (flag : Bool)
      (checked : requirements (WordBinder.letSource annotation binder v b flag) := by trivial) :
      Syntax env (requirements := requirements) .step ctx p (WordBinder.letSource annotation binder v b flag)
  | stepBindValue (value : ReadForm env ctx p v)
      (next : Syntax env (requirements := requirements) .step (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} b)
      (binder : Lean.Name) (info : Lean.BinderInfo)
      (checked : requirements (StructuralReadBind.bindValueSource v (.lam binder word b info)) := by trivial) :
      Syntax env (requirements := requirements) .step ctx p (StructuralReadBind.bindValueSource v (.lam binder word b info))
  | stepBindBits (value : ReadForm env ctx p v)
      (next : Syntax env (requirements := requirements) .step (Arithmetic.bitvecType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} b)
      (binder : Lean.Name) (info : Lean.BinderInfo)
      (checked : requirements (WordBinder.stepReadSource .bitvec v
        (.lam binder WordBinder.Annotation.bitvec.native b info)) := by trivial) :
      Syntax env (requirements := requirements) .step ctx p (WordBinder.stepReadSource .bitvec v
        (.lam binder WordBinder.Annotation.bitvec.native b info))
  | stepSequence (first : Syntax env (requirements := requirements) .body ctx p a)
      (next : Syntax env (requirements := requirements) .step (stateType::ctx) {p.lift with s := .bvar 0} b)
      (binder : Lean.Name) (info : Lean.BinderInfo)
      (checked : requirements (StructuralStep.sequenceSource a (.lam binder state b info)) := by trivial) :
      Syntax env (requirements := requirements) .step ctx p (StructuralStep.sequenceSource a (.lam binder state b info))
  | valueCurrent
      (checked : requirements p.s := by trivial) :
      Syntax env (requirements := requirements) .value ctx p p.s
  | valueAssign (register : NatArgument env ctx r) (value : LexicalScalarSyntax.Form env ctx p [] v)
      (checked : requirements (app ``HybridWord.State.set [p.s,r,v]) := by trivial) :
      Syntax env (requirements := requirements) .value ctx p (app ``HybridWord.State.set [p.s,r,v])
  | yield (value : Syntax env (requirements := requirements) .value ctx p v)
      (checked : requirements (Step.yieldSource v) := by trivial) :
      Syntax env (requirements := requirements) .step ctx p (Step.yieldSource v)
  | forStatic (start : For.Bound env ctx a) (stop : For.Bound env ctx b) (stride : For.Bound env ctx c)
      (body : Syntax env (requirements := requirements) .step (stateType::wordType::ctx) (For.parameters p) original)
      (kn tn : Lean.Name) (ki ti : Lean.BinderInfo)
      (checked : requirements (For.source a b c p.s (.lam kn word (.lam tn state original ti) ki)) := by trivial) :
      Syntax env (requirements := requirements) .body ctx p (For.source a b c p.s (.lam kn word (.lam tn state original ti) ki))
  | forRange (kind : NaturalLoop.Kind)
      (count : LexicalScalarSyntax.Form env ctx p [] n)
      (body : Syntax env (requirements := requirements) kind.mode (kind.context ctx) (kind.parameters p) original)
      (kn tn : Lean.Name) (ki ti : Lean.BinderInfo)
      (checked : requirements (kind.source n p.s (kind.nativeLambda kn tn ki ti original)) := by trivial) :
      Syntax env (requirements := requirements) .body ctx p (kind.source n p.s (kind.nativeLambda kn tn ki ti original))


abbrev Form (env : VEnv) (ctx : List VExpr) (p : Inputs) (source : Lean.Expr)
    (requirements : Lean.Expr → Prop := fun _ => True) := Syntax env .body ctx p source requirements

/-- All modes refer to the same structural traversal. Only the return type
and the command-certificate proposition differ. -/
def Outcome (setup : Arithmetic.AliasSetup env) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (mode : Mode) (source : Lean.Expr) : Prop :=
  match mode with
  | .body => ∃ piece, StructuralBody.bodyRetained env setup.conversion exposure ctx p source = some piece ∧
      ∃ typed : BodyCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType stateType)
  | .value => ∃ piece, visit env setup.conversion exposure source ctx p .value .identity (fun _ => none) = some piece ∧
      Nonempty (StructuralLoop.ValueCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup))
  | .step => ∃ piece, visit env setup.conversion exposure source ctx p .step .identity (fun _ => none) = some piece ∧
      ∃ typed : StructuralLoop.StepCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState)

theorem syntax_complete (setup : Arithmetic.AliasSetup env) (library : Library env)
    (closed : ClosedConstantTypes env) (fresh : Fresh setup) (exposure : Exposure env)
    (form : Syntax env mode ctx p source requirements) :
    ∀ (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p),
      Outcome setup exposure inputs mode source := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have embed : ∀ scope a b, Arithmetic.SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  induction form with
  | atom form =>
    intro inputs locals
    obtain ⟨piece,parsed,⟨typed⟩⟩ := StructuralSyntax.complete inputs library.toLibrary locals
      (setup.covers library.scalars.toSignatures) exposure form
    let lifted : BodyCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup) := (typed.mapSource (fun _ _ _ h => Arithmetic.SourceCasts.arithmetic h)).mapProofs
      (fun _ _ _ h => For.Casts.base (.base (.source (Arithmetic.SourceCasts.arithmetic h))))
    exact ⟨piece,parsed,lifted,base_form fresh form typed.sourceCore.property⟩
  | write array index value =>
    intro inputs locals
    obtain ⟨j,hj,⟨tj⟩⟩ := scalar_complete setup library closed fresh exposure inputs locals index
    obtain ⟨v,hv,⟨tv⟩⟩ := scalar_complete setup library closed fresh exposure inputs locals value
    obtain ⟨piece,parsed,⟨typed⟩⟩ := store_step_invariant_complete inputs array tj tv
      library.storeFact library.storeConstructor library.writer embed coverage exposure _ _ _ _ hj hv
    exact ⟨piece,by rw [store_leaf inputs]; exact parsed,typed,
      head_form fresh typed.sourceCore.property rfl (by simp)⟩
  | assign tag register value =>
    intro inputs locals
    obtain ⟨v,hv,⟨tv⟩⟩ := scalar_complete setup library closed fresh exposure inputs locals value
    obtain ⟨piece,parsed,⟨typed⟩⟩ := Return.assign_step_split_complete library.returns inputs tag register tv
      (library.assignFact tag) library.assignConstructor library.setter embed coverage exposure _ _ _ _ hv
    refine ⟨piece,by rw [assign_node tag]; exact parsed,typed,?_⟩
    cases tag <;> exact head_form fresh typed.sourceCore.property rfl (by simp)
  | branch value decision _ _ checked ihYes ihNo =>
    intro inputs locals
    obtain ⟨v,hv,⟨tv⟩⟩ := scalar_complete setup library closed fresh exposure inputs locals value
    obtain ⟨a,ha,ta,fa⟩ := ihYes inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ihNo inputs locals
    obtain ⟨vc,dc,vr,dr,pt,dt⟩ := decision.typing
    rw [← tv.sourceCore.property.unique vr] at pt dt
    obtain ⟨piece,parsed,⟨typed⟩⟩ := Branch.branch_step_split_complete inputs
      tv ta tb dr
      (pt.mono (fun _ _ _ h => Arithmetic.SourceCasts.arithmetic h))
      (dt.mono (fun _ _ _ h => Arithmetic.SourceCasts.arithmetic h))
      library.toLibrary.option_typed library.ite library.branchFact library.branchConstructor
      embed coverage exposure _ _ _ _ hv ha hb
    exact ⟨piece,by rw [branch_node]; exact parsed,typed,head_form fresh typed.sourceCore.property rfl (by simp)⟩
  | letValue annotation value next binder flag checked ih =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩⟩ := scalar_complete setup library closed fresh exposure inputs locals value
    obtain ⟨b,hb,tb,fb⟩ := ih
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (annotation.nextLocals locals closed)
    exact WordBinder.let_complete annotation setup library.scalars.toSignatures inputs closed library.cons
      library.returns.state library.returns.option library.eq library.eval library.letValue library.letValueConstructor
      fresh.option coverage exposure ta tb fb ha hb binder flag
  | sequence first next binder info checked ihFirst ihNext =>
    intro inputs locals
    obtain ⟨a,ha,ta,fa⟩ := ihFirst inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ihNext (inputs.nextState closed) (locals.nextState closed)
    obtain ⟨target,_,_⟩ := sequence_next_typed inputs closed Arithmetic.SourceCasts.closed library.returns.state tb
    obtain ⟨piece,parsed,⟨typed⟩⟩ := sequence_step_complete inputs closed Arithmetic.SourceCasts.closed
      embed library.returns.state ta tb (.base (.base (.stateContinuation inputs target tb.value fb)))
      library.sequence library.sequenceConstructor coverage exposure library.bind binder info _ _ _ _ ha hb
    exact ⟨piece,by rw [sequence_node]; exact parsed,typed,head_form fresh typed.sourceCore.property rfl (by simp)⟩
  | bindValue value next binder info checked ih =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩⟩ := read_complete setup library closed fresh exposure inputs locals value
    obtain ⟨b,hb,tb,fb⟩ := ih (inputs.nextWord closed library.scalars.word library.cons) (locals.nextWord closed)
    obtain ⟨target,_,_⟩ := bindValue_next_typed inputs closed Arithmetic.SourceCasts.closed
      library.scalars.word library.cons tb
    obtain ⟨piece,parsed,⟨typed⟩⟩ := bindValue_step_complete inputs closed Arithmetic.SourceCasts.closed
      embed library.scalars.word library.cons ta tb
      (.base (.base (.valueContinuation inputs target tb.value fb))) library.bindValueFact library.letValueConstructor
      coverage exposure library.bind library.returns.state binder info
      (ScalarEnvironment.parse env setup.conversion exposure)
      (fun ctx p => readStep env setup.conversion exposure ctx p (ScalarEnvironment.parse env setup.conversion exposure ctx p))
      (fun _ _ => none) (StructuralBody.bodyRetained env setup.conversion exposure) ha hb
    exact ⟨piece,by rw [bindValue_node]; exact parsed,typed,
      head_form fresh typed.sourceCore.property rfl (by simp)⟩
  | bindBits value next binder info checked ih =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩⟩ := read_complete setup library closed fresh exposure inputs locals value
    obtain ⟨b,hb,tb,fb⟩ := ih
      (WordBinder.Annotation.bitvec.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (WordBinder.Annotation.bitvec.nextLocals locals closed)
    exact WordBinder.bind_bits_complete setup library.scalars.toSignatures library.bind inputs closed
      library.cons library.returns.state library.eq library.eval library.bindValueFact library.letValueConstructor
      fresh.state (fresh.value _ (by simp)) coverage exposure ta (value.valueForm fresh ta.sourceCore.property)
      tb fb ha hb binder info
  | stateAlias next binder flag checked ih =>
    intro inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ih (inputs.nextState closed) (locals.nextState closed)
    obtain ⟨target,_,_⟩ := sequence_next_typed inputs closed Arithmetic.SourceCasts.closed library.returns.state tb
    obtain ⟨piece,parsed,⟨typed⟩,_⟩ := StateAlias.alias_step_complete inputs closed Arithmetic.SourceCasts.closed
      embed library.returns.state tb (.base (.base (.stateContinuation inputs target tb.value fb)))
      library.stateAlias coverage exposure binder flag _ _ _ _ hb
    have same := typed.sourceCore.property.unique
      (Represents.letE (Represents.constant rfl) inputs.s.property tb.sourceCore.property)
    refine ⟨piece,by rw [alias_node inputs]; exact parsed,typed,?_⟩
    rw [same]
    exact .beta tb.value
  | stepBranch value decision _ _ checked ihYes ihNo =>
    intro inputs locals
    obtain ⟨v,hv,⟨tv⟩⟩ := scalar_complete setup library closed fresh exposure inputs locals value
    obtain ⟨a,ha,ta,fa⟩ := ihYes inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ihNo inputs locals
    obtain ⟨vc,dc,vr,dr,pt,dt⟩ := decision.typing
    rw [← tv.sourceCore.property.unique vr] at pt dt
    obtain ⟨piece,parsed,⟨typed⟩⟩ := StructuralStep.Conditional.split_complete inputs
      tv ta tb dr
      (pt.mono (fun _ _ _ h => Arithmetic.SourceCasts.arithmetic h))
      (dt.mono (fun _ _ _ h => Arithmetic.SourceCasts.arithmetic h))
      library.stepOption_typed library.ite library.stepBranch library.branchConstructor embed coverage exposure hv ha hb
    exact ⟨piece,parsed,typed,head_form fresh typed.sourceCore.property rfl (by simp)⟩
  | stepLetValue annotation value next binder flag checked ih =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩⟩ := scalar_complete setup library closed fresh exposure inputs locals value
    obtain ⟨b,hb,tb,fb⟩ := ih
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (annotation.nextLocals locals closed)
    exact WordBinder.step_let_complete annotation setup library.scalars.toSignatures inputs closed library.cons
      library.steps library.eq library.eval library.stepLetValue library.letValueConstructor
      fresh.option coverage exposure ta tb fb ha hb binder flag
  | @stepBindValue ctx p v b requirements value next binder info checked ih =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩⟩ := read_complete setup library closed fresh exposure inputs locals value
    obtain ⟨b,hb,tb,fb⟩ := ih (inputs.nextWord closed library.scalars.word library.cons) (locals.nextWord closed)
    have eval := eval_cast_typed (inputs.nextWord closed library.scalars.word library.cons) library.eval tb.target
    have beta := For.Casts.directContinuation (setup := setup) .word eval tb.value fb
    have codeClosed := b.represented.property.closed 0 b.closed
    have cast : For.Casts setup ctx
        (StructuralReadBind.bindValueNextActual inputs b.represented.val tb.sourceCore.val)
        (StructuralReadBind.bindValueContinuationType inputs b.represented.val (.lam wordType tb.sourceCore.val)) := by
      simpa only [StructuralReadBind.bindValueNextActual,StructuralReadBind.bindValueContinuationType,
        InputsTyped.nextWord,InputsTyped.lift,Step.Binder.core,Arithmetic.continuationValue,
        VExpr.lift,VExpr.liftN,wordType,codeClosed.liftN_eq (Nat.zero_le _)] using beta
    obtain ⟨piece,parsed,⟨typed⟩⟩ := StructuralReadBind.complete inputs closed Arithmetic.SourceCasts.closed
      embed library.scalars.word library.cons ta tb cast library.stepBindValue library.letValueConstructor
      coverage exposure library.bind library.steps binder info ha hb
    exact ⟨piece,parsed,typed,head_form fresh typed.sourceCore.property rfl (by simp)⟩
  | unitBody next binder info checked ih =>
    intro inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ih (inputs.lift closed UnitStep.unitType) (locals.lift closed UnitStep.unitType)
    have eval := eval_cast_typed (inputs.lift closed UnitStep.unitType) library.eval tb.target
    have beta := For.Casts.unitContinuation (setup := setup) library.units false eval tb.value fb fresh.unit
    have codeClosed := b.represented.property.closed 0 b.closed
    obtain ⟨piece,parsed,⟨typed⟩⟩ := StructuralUnit.complete false inputs closed Arithmetic.SourceCasts.closed
      embed library.units library.steps library.bind
      ⟨tb.sourceCore,tb.value,tb.target,tb.proof⟩
      (by simpa only [StructuralUnit.continuationType,StructuralUnit.lhs,For.unitRequired,
        InputsTyped.lift,Arithmetic.continuationValue,VExpr.lift,VExpr.liftN,UnitStep.unitType,
        codeClosed.liftN_eq (Nat.zero_le _)] using beta)
      (library.unitFact false) coverage exposure binder info hb
    exact ⟨piece,parsed,⟨typed.sourceCore,typed.value,typed.target,typed.proof⟩,
      head_form fresh typed.sourceCore.property rfl (by simp)⟩
  | unitLoop next binder info checked ih =>
    intro inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ih (inputs.lift closed UnitStep.unitType) (locals.lift closed UnitStep.unitType)
    have eval := eval_cast_typed (inputs.lift closed UnitStep.unitType) library.eval tb.target
    have beta := For.Casts.unitContinuation (setup := setup) library.units true eval tb.value fb fresh.unit
    have codeClosed := b.represented.property.closed 0 b.closed
    obtain ⟨piece,parsed,⟨typed⟩⟩ := StructuralUnit.complete true inputs closed Arithmetic.SourceCasts.closed
      embed library.units library.steps library.bind
      ⟨tb.sourceCore,tb.value,tb.target,tb.proof⟩
      (by simpa only [StructuralUnit.continuationType,StructuralUnit.lhs,For.unitRequired,
        InputsTyped.lift,Arithmetic.continuationValue,VExpr.lift,VExpr.liftN,UnitStep.unitType,
        codeClosed.liftN_eq (Nat.zero_le _)] using beta)
      (library.unitFact true) coverage exposure binder info hb
    exact ⟨piece,parsed,⟨typed.sourceCore,typed.value,typed.target,typed.proof⟩,
      head_form fresh typed.sourceCore.property rfl (by simp)⟩
  | stateLet value next notAlias binder flag checked ihValue ihNext =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩⟩ := ihValue inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ihNext (inputs.nextState closed) (locals.nextState closed)
    obtain ⟨target,_,_⟩ := sequence_next_typed inputs closed Arithmetic.SourceCasts.closed library.returns.state tb
    obtain ⟨piece,parsed,⟨typed⟩⟩ := StructuralStateLet.complete inputs closed Arithmetic.SourceCasts.closed
      embed library.returns.state ta library.returns tb
      (.base (.base (.stateContinuation inputs target tb.value fb))) library.stateLet library.sequenceConstructor
      coverage exposure binder flag notAlias ha hb
    have same := typed.sourceCore.property.unique
      (Represents.letE (Represents.constant rfl) ta.sourceCore.property tb.sourceCore.property)
    refine ⟨piece,parsed,typed,?_⟩
    rw [same]
    exact .beta tb.value
  | @stepStateLet ctx p v requirements b value next notAlias binder flag checked ihValue ihNext =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩⟩ := ihValue inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ihNext (inputs.nextState closed) (locals.nextState closed)
    have eval := eval_cast_typed (inputs.nextState closed) library.eval tb.target
    have beta := For.Casts.directContinuation (setup := setup) .state eval tb.value fb
    have codeClosed := b.represented.property.closed 0 b.closed
    have cast : For.Casts setup ctx
        (StructuralStep.sequenceNextActual inputs b.represented.val tb.sourceCore.val)
        (StructuralStep.sequenceContinuationType inputs b.represented.val (.lam stateType tb.sourceCore.val)) := by
      simpa only [StructuralStep.sequenceNextActual,StructuralStep.sequenceContinuationType,
        InputsTyped.nextState,InputsTyped.lift,Step.Binder.core,Arithmetic.continuationValue,
        VExpr.lift,VExpr.liftN,stateType,codeClosed.liftN_eq (Nat.zero_le _)] using beta
    obtain ⟨piece,parsed,⟨typed⟩⟩ := StructuralStateLet.Loop.complete inputs closed Arithmetic.SourceCasts.closed
      embed library.returns.state ta library.returns tb cast library.stepStateLet library.sequenceConstructor
      coverage exposure binder flag notAlias ha hb
    have same := typed.sourceCore.property.unique
      (Represents.letE (Represents.constant rfl) ta.sourceCore.property tb.sourceCore.property)
    refine ⟨piece,parsed,typed,?_⟩
    rw [same]
    exact .beta tb.value
  | @stepAlias ctx b requirements p next binder flag checked ihNext =>
    intro inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ihNext (inputs.nextState closed) (locals.nextState closed)
    have eval := eval_cast_typed (inputs.nextState closed) library.eval tb.target
    have beta := For.Casts.directContinuation (setup := setup) .state eval tb.value fb
    have codeClosed := b.represented.property.closed 0 b.closed
    have cast : For.Casts setup ctx
        (StructuralStep.sequenceNextActual inputs b.represented.val tb.sourceCore.val)
        (StructuralStep.sequenceContinuationType inputs b.represented.val (.lam stateType tb.sourceCore.val)) := by
      simpa only [StructuralStep.sequenceNextActual,StructuralStep.sequenceContinuationType,
        InputsTyped.nextState,InputsTyped.lift,Step.Binder.core,Arithmetic.continuationValue,
        VExpr.lift,VExpr.liftN,stateType,codeClosed.liftN_eq (Nat.zero_le _)] using beta
    obtain ⟨piece,parsed,⟨typed⟩,_⟩ := StructuralStep.Alias.alias_step_complete inputs closed Arithmetic.SourceCasts.closed
      embed library.returns.state tb cast library.stepAlias coverage exposure binder flag hb
    have same := typed.sourceCore.property.unique
      (Represents.letE (Represents.constant rfl) inputs.s.property tb.sourceCore.property)
    refine ⟨piece,parsed,typed,?_⟩
    rw [same]
    exact .beta tb.value
  | stepBindBits value next binder info checked ih =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩⟩ := read_complete setup library closed fresh exposure inputs locals value
    obtain ⟨b,hb,tb,fb⟩ := ih
      (WordBinder.Annotation.bitvec.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (WordBinder.Annotation.bitvec.nextLocals locals closed)
    exact WordBinder.step_bind_bits_complete setup library.scalars.toSignatures library.bind inputs closed
      library.cons library.steps library.eq library.eval library.stepBindValue library.letValueConstructor
      (fresh.readAux _ (by simp)) (fresh.value _ (by simp)) coverage exposure ta
      (value.valueForm fresh ta.sourceCore.property) tb fb ha hb binder info
  | @stepSequence ctx p a requirements b first next binder info checked ihFirst ihNext =>
    intro inputs locals
    obtain ⟨a,ha,ta,fa⟩ := ihFirst inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ihNext (inputs.nextState closed) (locals.nextState closed)
    have eval := eval_cast_typed (inputs.nextState closed) library.eval tb.target
    have beta := For.Casts.directContinuation (setup := setup) .state eval tb.value fb
    have codeClosed := b.represented.property.closed 0 b.closed
    have cast : For.Casts setup ctx
        (StructuralStep.sequenceNextActual inputs b.represented.val tb.sourceCore.val)
        (StructuralStep.sequenceContinuationType inputs b.represented.val (.lam stateType tb.sourceCore.val)) := by
      simpa only [StructuralStep.sequenceNextActual,StructuralStep.sequenceContinuationType,
        InputsTyped.nextState,InputsTyped.lift,Step.Binder.core,Arithmetic.continuationValue,
        VExpr.lift,VExpr.liftN,stateType,codeClosed.liftN_eq (Nat.zero_le _)] using beta
    obtain ⟨piece,parsed,⟨typed⟩⟩ := StructuralStep.sequence_complete inputs closed Arithmetic.SourceCasts.closed
      embed library.returns.state ta tb cast library.stepSequence library.sequenceConstructor coverage exposure
      library.bind library.steps binder info ha hb
    exact ⟨piece,parsed,typed,head_form fresh typed.sourceCore.property rfl (by simp)⟩
  | valueCurrent =>
    intro inputs locals
    obtain ⟨piece,parsed,⟨typed⟩⟩ := StructuralLoop.value_skip_complete inputs (library.returnFact .some)
      library.skipConstructor setup.conversion exposure (Arithmetic.SourceCasts env)
      (setup.covers_source library.scalars.toSignatures closed)
    exact ⟨piece,parsed,⟨⟨typed.sourceCore,typed.value,typed.target,typed.proof.mono embed⟩⟩⟩
  | valueAssign register value =>
    intro inputs locals
    obtain ⟨v,hv,⟨tv⟩⟩ := scalar_complete setup library closed fresh exposure inputs locals value
    obtain ⟨piece,parsed,⟨typed⟩⟩ := StructuralLoop.value_assign_split_complete inputs register
      tv
      (library.assignFact .some) library.assignConstructor library.setter
      embed coverage exposure hv
    exact ⟨piece,parsed,⟨typed⟩⟩
  | yield value checked ih =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩⟩ := ih inputs locals
    obtain ⟨piece,parsed,⟨typed⟩⟩ := StructuralLoop.yield_complete inputs library.steps
      library.eval library.compose embed ta coverage exposure ha
    exact ⟨piece,parsed,typed,head_form fresh typed.sourceCore.property rfl (by simp)⟩
  | forStatic start stop stride body kn tn ki ti checked ih =>
    intro inputs locals
    obtain ⟨b,hb,tb,fb⟩ := ih (For.nextInputs inputs closed library.scalars.word library.cons)
      ((locals.nextWord closed).nextState closed)
    obtain ⟨target,_,_⟩ := StructuralLoop.next_typed inputs closed Arithmetic.SourceCasts.closed
      library.scalars.word library.returns.state library.cons tb
    obtain ⟨piece,parsed,⟨typed⟩⟩ := StructuralLoop.body_forStatic_complete inputs closed Arithmetic.SourceCasts.closed
      embed start stop stride library.scalars.word library.returns.state library.cons tb
      (.continuation inputs target (b.represented.property.closed 0 b.closed) tb.value fb)
      library.forFact library.forConstructor library.range library.forHeader.header_typed
      coverage exposure kn tn ki ti hb
    exact ⟨piece,parsed,typed,head_form fresh typed.sourceCore.property rfl (by simp)⟩
  | @forRange ctx p n original requirements kind count _ kn tn ki ti checked ih =>
    intro inputs locals
    obtain ⟨c,hc,⟨tc⟩⟩ := scalar_complete setup library closed fresh exposure inputs locals count
    let nextInputs := kind.nextInputs inputs closed library.scalars.toSignatures library.naturalLoops library.cons
    let nextLocals := kind.nextLocals locals closed library.scalars.toSignatures library.naturalLoops
    have child : ∃ b, visit env setup.conversion exposure original (kind.context ctx) (kind.parameters p)
        kind.mode .identity (fun _ => none) = some b ∧
        ∃ typed : NaturalLoop.ChildCasts kind nextInputs b (Arithmetic.SourceCasts env) (For.Casts setup),
          Arithmetic.ValueForm setup (kind.context ctx) typed.sourceCore.val (optionType kind.result) := by
      cases kind with
      | forIn => exact ih nextInputs nextLocals
      | fold => exact ih nextInputs nextLocals
    obtain ⟨b,hb,tb,fb⟩ := child
    have beta := NaturalLoop.continuation_cast setup inputs kind closed library.scalars.toSignatures
      library.naturalLoops library.steps library.cons library.eval fresh.nat fresh.state tb fb
    obtain ⟨piece,parsed,⟨typed⟩⟩ := NaturalLoop.body_forRange_complete inputs kind closed embed
      library.scalars.toSignatures library.naturalLoops library.forHeader library.reads library.steps.state
      library.cons tc tb beta coverage exposure kn tn ki ti hc hb
    refine ⟨piece,parsed,typed,?_⟩
    cases kind <;> exact head_form fresh typed.sourceCore.property rfl (by simp)


theorem complete (setup : Arithmetic.AliasSetup env) (library : Library env)
    (closed : ClosedConstantTypes env) (fresh : Fresh setup) (exposure : Exposure env)
    (form : Form env ctx p source requirements) :
    ∀ (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p),
    ∃ piece, StructuralBody.bodyRetained env setup.conversion exposure ctx p source = some piece ∧
      ∃ typed : BodyCasts inputs piece (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType stateType) :=
  syntax_complete setup library closed fresh exposure form

/-- Named-source connection for the contextual induction. Body success,
continuation conversion coverage and closure of imported constant types are
conclusions, not successful-parser/checker premises. Loading and the remaining
source constructors are separate obligations. -/
theorem compile_of_parser_rule_with_code
    (parseBody : (env : VEnv) → Conversion env → Exposure env →
      (ctx : List VExpr) → (p : Inputs) → (source : Lean.Expr) →
      Option (Piece env ctx p source bodyExpected))
    (lib : LeanEntryEnvironment.Loaded native name)
    (loaded : WordFrontend.load native name = some lib)
    (library : Library lib.model)
    (closed : ClosedConstantTypes lib.model)
    (wordShape : Arithmetic.WordDeclaration native) (decEqShape : Arithmetic.DecEqDeclaration native)
    (freshWord : ``HybridWord.Word ≠ name) (freshBitVec : ``BitVec ≠ name)
    (freshOfNat : ``OfNat ≠ name)
    (freshNumerals : ∀ n ∈ [``Nat.zero,``Nat.succ,``Nat.mul], n ≠ name)
    (freshClasses : ∀ op : Arithmetic.Binary, op.className ≠ name)
    (freshHeterogeneous : ∀ op : Arithmetic.Binary, op.heterogeneous ≠ name)
    (freshNeg : ``Neg ≠ name)
    (freshScalarHeads : ∀ n ∈ LexicalScalarSyntax.valueHeads, n ≠ name)
    (freshHeads : ∀ n ∈ [``HybridWord.State,``Eq,``Option.some,``Pure.pure,
      ``HybridWord.State.write,``HybridWord.State.copy,``ite,``Bind.bind,``ForIn.forIn,``WordLoopFacts.lift,``PUnit,``Nat,``List.foldlM,``Option,``GetElem?.getElem?,``GetElem?,``Array.instGetElem?NatLtSize,``HybridWord.State.arrays,``BitVec.toNat,``ForInStep,``bne,``Decidable,``instDecidableEqBool], n ≠ name)
    (monomorphic : lib.source.declaration.levelParams = [])
    (shape : LeanSourceEntry.strip lib.source.declaration.value =
      .lam ni word (.lam nx word (.lam ny word (.lam ns state original bs) byInfo) bx) bi)
    (sourceType : lib.source.type.val = sourceFunctionType)
    (property : Lean.Expr → Prop)
    (bodyRule : ∀ (setup : Arithmetic.AliasSetup lib.model), Fresh setup →
      ∃ piece, parseBody lib.model setup.conversion lib.exposure context parameters original = some piece ∧
        ∃ typed : BodyCasts (initialInputs library.connection.word library.connection.nilWords) piece
          (Arithmetic.SourceCasts lib.model) (For.Casts setup), property piece.code) :
    ∃ result, compileWith parseBody native name = some result ∧ result.CodeTyped ∧ property result.code := by
  obtain ⟨setup,converter,exposer,rules⟩ := Arithmetic.loaded_alias_setup loaded wordShape decEqShape
    freshWord freshBitVec freshOfNat freshNumerals freshClasses freshHeterogeneous freshNeg (freshHeads _ (by simp)) (freshHeads _ (by simp))
  have member (r : LeanTypeReduction.Rule lib.model) (h : r ∈ setup.rules) :
      r.name ∈ [name,``HybridWord.Word,``DecidableEq,``optParam] := by
    rw [← rules]
    exact List.mem_map.mpr ⟨r,h,rfl⟩
  have separated (n : Lean.Name)
      (hn : n ∈ [``HybridWord.State,``Eq,``Option.some,``Pure.pure,
        ``HybridWord.State.write,``HybridWord.State.copy,``ite,``Bind.bind,``ForIn.forIn,``WordLoopFacts.lift,``PUnit,``Nat,``List.foldlM,``Option,``GetElem?.getElem?,``GetElem?,``Array.instGetElem?NatLtSize,``HybridWord.State.arrays,``BitVec.toNat,``ForInStep,``bne,``Decidable,``instDecidableEqBool]) :
      ∀ r ∈ setup.rules, n ≠ r.name := by
    intro r hr
    have hm := member r hr
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hm
    rcases hm with h | h | h | h
    · rw [h]; exact freshHeads n hn
    all_goals simp only [List.mem_cons,List.mem_nil_iff,or_false] at hn
    all_goals rcases hn with hn|hn|hn|hn|hn|hn|hn|hn|hn|hn|hn|hn|hn|hn|hn|hn|hn|hn|hn|hn|hn|hn|hn <;> subst n <;> rw [h] <;> decide
  have scalarSeparated : ∀ n ∈ LexicalScalarSyntax.valueHeads, ∀ r ∈ setup.rules, n ≠ r.name := by
    intro n hn r hr
    have hm := member r hr
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hm
    rcases hm with h | h | h | h
    · rw [h]; exact freshScalarHeads n hn
    all_goals simp only [LexicalScalarSyntax.valueHeads,List.mem_cons,List.mem_nil_iff,or_false] at hn
    all_goals rcases hn with hn|hn|hn|hn|hn|hn|hn|hn|hn <;> subst n <;> rw [h] <;> decide
  have fresh : Fresh setup :=
    ⟨scalarSeparated,(fun n hn => separated n (by simp only [List.mem_cons,List.mem_nil_iff,or_false] at hn; rcases hn with rfl|rfl|rfl <;> simp)),separated _ (by simp),separated _ (by simp),separated _ (by simp),separated _ (by simp),separated _ (by simp),separated _ (by simp),separated _ (by simp),
      (fun n hn => separated n (by simp only [List.mem_cons,List.mem_nil_iff,or_false] at hn; rcases hn with rfl|rfl|rfl|rfl <;> simp)),
      fun n hn => separated n (by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hn ⊢
      rcases hn with h|h|h|h|h|h|h|h <;> simp [h])⟩
  obtain ⟨piece,parsed,typed,hasProperty⟩ := bodyRule setup fresh
  rw [converter] at parsed
  have coverage := setup.covers_source library.scalars.toSignatures closed
  rw [converter] at coverage
  obtain ⟨result,success,typed,sameCode⟩ := compile_of_cast_body parseBody lib loaded library.connection closed Arithmetic.SourceCasts.closed
    coverage monomorphic shape sourceType typed.sourceCore.property typed.value piece parsed typed.target
  exact ⟨result,success,typed,sameCode.symm ▸ hasProperty⟩


end IRComparison.WordFrontend.ScopedSyntax
