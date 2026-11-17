import IRComparison.Frontend.WordFixedCopyCompleteness

/-! Static source conditions through read binding to the existing total RTL
backend. Array/register/index values and numeral spellings are arbitrary.
This component is not a replacement for the remaining structured static
source induction. No successful parser or generated Entry is an assumption. -/
namespace IRComparison.WordFrontend.FixedReadCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 1800000

def program (array index register : Nat) (s : HybridWord.State) : Option HybridWord.State := do
  let value : BitVec 32 ← (s.arrays array)[index]?
  pure (s.set register value)

def continuation (register : Nat) (rn : NatNotation) (p : Inputs := parameters) : Lean.Expr :=
  Return.Form.pure.source (app ``HybridWord.State.set [p.lift.s,rn.native register,.bvar 0])

def original (array index register : Nat) (an nn rn : NatNotation)
    (binder : Lean.Name) (info : Lean.BinderInfo) (p : Inputs := parameters) : Lean.Expr :=
  WordBinder.readSource .bitvec (Read.bitsSource p.s (an.native array) (nn.native index))
    (.lam binder WordBinder.Annotation.bitvec.native (continuation register rn p) info)

def quotedCode (array index register : Nat) (an nn rn : NatNotation) : Lean.Expr :=
  app ``HybridWord.Cmd.letValue [app ``HybridWord.Expr.readNat [an.native array,nn.native index],
    app ``HybridWord.Cmd.assign [rn.native register,app ``HybridWord.Expr.local [(ClosedTerm.bindingIndex 0).val]]]

/-- Source-shape evidence records only ordinary Lean syntax and its static
arguments. It neither invokes the parser nor contains a generated Entry. -/
structure Source (value : Lean.Expr) where
  array : Nat
  index : Nat
  register : Nat
  an : NatNotation
  nn : NatNotation
  rn : NatNotation
  binder : Lean.Name
  info : Lean.BinderInfo
  shape : value = original array index register an nn rn binder info

/-- A newly bound scalar is distinct from every lifted enclosing input.
This is derived from the binding representation; callers do not provide
per-variable dispatch tests. -/
private theorem fresh_local (represented : Represents source core) :
    sameTerm (.bvar 0) (LeanBindings.rename Nat.succ source) = false := by
  obtain ⟨lifted,translated,same⟩ := represented.lift.translate_complete
  have different : VExpr.bvar 0 ≠ core.lift := by
    cases core <;> simp [VExpr.lift,VExpr.liftN,liftVar]
    omega
  simp only [sameTerm,translate,translated,same]
  exact decide_eq_false different

theorem source_syntax_at (library : ScopedSyntax.Library env) (inputs : InputsTyped env ctx p)
    (array index register : Nat) (an nn rn : NatNotation) (binder : Lean.Name) (info : Lean.BinderInfo) :
    ScopedSyntax.Form env ctx p (original array index register an nn rn binder info p) := by
  apply ScopedSyntax.Syntax.bindBits
  · apply ScopedSyntax.ReadForm.bitsNatural (an.argument library.scalars.toSignatures array)
      (nn.argument library.scalars.toSignatures index)
    cases nn with
    | raw => exact Or.inl rfl
    | elaborated => exact Or.inr rfl
  · apply ScopedSyntax.Syntax.assign .pure (rn.argument library.scalars.toSignatures register)
    exact .localValue (.variable 0) 0 rfl (fresh_local inputs.i.property)
      (fresh_local inputs.x.property) (fresh_local inputs.y.property) (by intro j h; omega)
  · trivial

theorem source_syntax (library : ScopedSyntax.Library env) (array index register : Nat)
    (an nn rn : NatNotation) (binder : Lean.Name) (info : Lean.BinderInfo) :
    ScopedSyntax.Form env context parameters (original array index register an nn rn binder info) :=
  source_syntax_at library (initialInputs library.connection.word library.connection.nilWords)
    array index register an nn rn binder info

/-- The same constructor proof supplies both typing and the exact command.
Static array conditions can therefore be applied to the command actually
produced, instead of to an unrelated assumed backend entry. -/
theorem body_complete_at (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p)
    (array index register : Nat) (an nn rn : NatNotation) (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ piece, StructuralBody.bodyRetained env setup.conversion exposure ctx p
        (original array index register an nn rn binder info p) = some piece ∧
      ∃ typed : BodyCasts inputs piece
        (SourceCasts env) (For.Casts setup), piece.code = quotedCode array index register an nn rn := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have embed : ∀ scope a b, SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  let aa := an.argument (ctx := ctx) library.scalars.toSignatures array
  let na := nn.argument (ctx := ctx) library.scalars.toSignatures index
  have natural : Read.NaturalIndex (nn.native index) := by
    cases nn with
    | raw => exact Or.inl rfl
    | elaborated => exact Or.inr rfl
  obtain ⟨a,ha,⟨ta⟩,aCode⟩ := Read.bits_nat_complete_code setup library.scalars.toSignatures library.reads
    library.scalarCertificates inputs aa na natural
    (ScopedSyntax.natural_value_form setup fresh natural na.represented.property)
    fresh.read (fresh.readAux _ (by simp)) (fresh.readAux _ (by simp))
    library.readNatFact library.readNatConstructor coverage exposure
    (ScalarEnvironment.parse env setup.conversion exposure ctx p)
  let nextInputs := WordBinder.Annotation.bitvec.nextInputs inputs closed library.scalars.toSignatures library.cons
  let nextLocals := WordBinder.Annotation.bitvec.nextLocals locals closed
  obtain ⟨v,hv,⟨tv⟩,vCode⟩ := ScalarSyntax.local_visit_complete_code
    (casts := SourceCasts env) (proofCasts := For.Casts setup) nextInputs library.scalars []
    (ScalarEnvironment.BindingTypes.empty nextInputs (SourceCasts env)) nextLocals
    setup.conversion exposure coverage (.variable 0) (n := 0) rfl (fresh_local inputs.i.property) (fresh_local inputs.x.property)
    (fresh_local inputs.y.property) (by intro j h; omega)
  have scalarParsed : ScalarEnvironment.parse env setup.conversion exposure _ _ (.bvar 0) = some v := hv
  obtain ⟨b,hb,⟨tb⟩,bCode⟩ := Return.assign_step_split_complete_code library.returns nextInputs .pure
    (rn.argument library.scalars.toSignatures register) tv (library.assignFact .pure)
    library.assignConstructor library.setter embed coverage exposure
    (ScalarEnvironment.parse env setup.conversion exposure) (fun _ _ _ => none)
    (fun _ _ => none) (fun _ _ _ => none) scalarParsed
  have bodyParsed : StructuralBody.bodyRetained env setup.conversion exposure _ _ (continuation register rn p) = some b := by
    exact (StructuralSyntax.assign_node
      (p := {p.lift with locals := .bvar 0::p.lift.locals})
      (r := rn.native register) (v := .bvar 0) .pure).trans hb
  obtain ⟨piece,parsed,typed,_,code⟩ := WordBinder.bind_bits_complete_code setup library.scalars.toSignatures
    library.bind inputs closed library.cons library.returns.state library.eq library.eval
    library.bindValueFact library.letValueConstructor fresh.state (fresh.value _ (by simp))
    coverage exposure ta
    ((ScopedSyntax.ReadForm.bitsNatural aa na natural).valueForm fresh ta.sourceCore.property)
    tb (ScopedSyntax.head_form fresh tb.sourceCore.property rfl (by simp)) ha bodyParsed binder info
  refine ⟨piece,parsed,typed,?_⟩
  rw [code,aCode,bCode,vCode (.empty _)]
  rfl

theorem body_complete (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (array index register : Nat) (an nn rn : NatNotation) (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ piece, StructuralBody.bodyRetained env setup.conversion exposure context parameters
        (original array index register an nn rn binder info) = some piece ∧
      ∃ typed : BodyCasts (initialInputs library.connection.word library.connection.nilWords) piece
        (SourceCasts env) (For.Casts setup), piece.code = quotedCode array index register an nn rn :=
  body_complete_at setup library closed fresh exposure
    (initialInputs library.connection.word library.connection.nilWords) (.empty rfl)
    array index register an nn rn binder info

end IRComparison.WordFrontend.FixedReadCompleteness
