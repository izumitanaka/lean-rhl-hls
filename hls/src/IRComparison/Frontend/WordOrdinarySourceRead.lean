import IRComparison.Frontend.WordOrdinarySourceScalar

/-! Interpret original array-read syntax using the common scalar induction.
Array declaration conditions are obtained from the original read, not supplied
again for a substituted expression or a generated command. -/
namespace IRComparison.WordFrontend.OrdinarySource
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody ScalarSyntax
set_option maxHeartbeats 2400000

private theorem readNatural_demands (annotation : WordBinder.Annotation) (an nn : NatNotation) :
    stateVariables Γ (FixedReadSourceCompleteness.naturalSource annotation st (an.native a) (nn.native n)) =
      stateVariables Γ st := by
  cases annotation <;> cases an <;> cases nn <;>
    simp [FixedReadSourceCompleteness.naturalSource,IRComparison.WordFrontend.Read.source,IRComparison.WordFrontend.Read.bitsSource,
      IRComparison.WordFrontend.Read.nativeHeader,IRComparison.WordFrontend.Read.nativeBitsHeader,
      IRComparison.WordFrontend.Read.nativeArray,IRComparison.WordFrontend.Read.nativeValidity,
      WordBinder.Annotation.native,nativeWidth,NatNotation.native,stateVariables,freeVariables,app,word,state,
      Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB]

private theorem readWord_demands (annotation : WordBinder.Annotation) (an : NatNotation) :
    stateVariables Γ (FixedReadSourceCompleteness.wordSource annotation st (an.native a) k) =
      stateVariables Γ st ++ stateVariables Γ k := by
  cases annotation <;> cases an <;>
    simp [FixedReadSourceCompleteness.wordSource,FixedReadSourceCompleteness.naturalSource,
      IRComparison.WordFrontend.Read.source,IRComparison.WordFrontend.Read.bitsSource,IRComparison.WordFrontend.Read.wordIndex,
      IRComparison.WordFrontend.Read.nativeHeader,IRComparison.WordFrontend.Read.nativeBitsHeader,
      IRComparison.WordFrontend.Read.nativeArray,IRComparison.WordFrontend.Read.nativeValidity,
      WordBinder.Annotation.native,nativeWidth,NatNotation.native,stateVariables,freeVariables,app,word,state,
      Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,List.filter_append]

private theorem mapReadNatural (σ : Substitution) (annotation : WordBinder.Annotation) (an nn : NatNotation) :
    σ.apply (FixedReadSourceCompleteness.naturalSource annotation st (an.native a) (nn.native n)) =
      FixedReadSourceCompleteness.naturalSource annotation (σ.apply st) (an.native a) (nn.native n) := by
  cases σ <;> cases annotation <;> cases an <;> cases nn <;> rfl

private theorem mapReadWord (σ : Substitution) (annotation : WordBinder.Annotation) (an : NatNotation) :
    σ.apply (FixedReadSourceCompleteness.wordSource annotation st (an.native a) k) =
      FixedReadSourceCompleteness.wordSource annotation (σ.apply st) (an.native a) (σ.apply k) := by
  cases σ <;> cases annotation <;> cases an <;> rfl

/-- Both index spellings and both scalar annotations use the same original
read rule. Nested scalar lets and selections are covered by Scalar.forms. -/
theorem Read.forms (source : Read ds Γ raw annotation) (related : Context.Related Γ Δ)
    (frame : ScalarFrame env Δ ctx p σ τ) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (inputs : InputsTyped env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p) (references : ReferenceScope p)
    (current : CurrentMapping σ p (stateVariables Γ raw)) :
    ScopedSyntax.ReadForm env ctx p (σ.apply raw) ∧
      FixedReadSourceCompleteness.Conditions ds (σ.apply raw) := by
  cases source with
  | natural annotation state array index an nn declared =>
    rw [readNatural_demands] at current
    have same := state.current current
    obtain ⟨position,ref⟩ := state.mappedReference related frame
    have ps : p.s = .bvar position := same.symm.trans ref
    rw [mapReadNatural,same]
    have ni : IRComparison.WordFrontend.Read.NaturalIndex (nn.native index) := by
      cases nn with | raw => exact .inl rfl | elaborated => exact .inr rfl
    refine ⟨?_,?_⟩
    · cases annotation with
      | word =>
        exact .natural (an.argument library.scalars.toSignatures array)
            (nn.argument library.scalars.toSignatures index) ni
      | bitvec =>
        exact .bitsNatural (an.argument library.scalars.toSignatures array)
            (nn.argument library.scalars.toSignatures index) ni
    · constructor
      · rw [ps]; cases annotation <;> cases an <;> cases nn <;> trivial
      · intro other st a n equal
        cases annotation <;> cases other <;>
          simp only [FixedReadSourceCompleteness.naturalSource,IRComparison.WordFrontend.Read.source,IRComparison.WordFrontend.Read.bitsSource,
            Lean.mkApp2,Lean.mkApp,Lean.mkAppB,app,List.foldl_cons,List.foldl_nil,Lean.Expr.app.injEq] at equal
        all_goals first | contradiction | exact ⟨array,an,equal.1.2.2.symm,declared⟩
      · intro other st a n equal natural
        cases annotation <;> cases other <;>
          simp only [FixedReadSourceCompleteness.naturalSource,IRComparison.WordFrontend.Read.source,IRComparison.WordFrontend.Read.bitsSource,
            Lean.mkApp2,Lean.mkApp,Lean.mkAppB,app,List.foldl_cons,List.foldl_nil,Lean.Expr.app.injEq] at equal
        all_goals first | contradiction | exact ⟨⟨index,nn,equal.2.symm⟩⟩
  | word annotation state array an declared index =>
    rw [readWord_demands] at current
    have same := state.current current.left
    obtain ⟨position,ref⟩ := state.mappedReference related frame
    have ps : p.s = .bvar position := same.symm.trans ref
    obtain ⟨form,static⟩ := index.forms related frame library closed inputs typing references current.right
    rw [mapReadWord,same]
    refine ⟨?_,FixedReadSourceCompleteness.Conditions.word annotation array an declared ?_⟩
    · cases annotation with
      | word => exact .word (an.argument library.scalars.toSignatures array) form
      | bitvec => exact .bitsWord (an.argument library.scalars.toSignatures array) form
    · rw [ps]; cases annotation <;> cases an <;> exact ⟨⟨by trivial,by trivial⟩,⟨by trivial,static⟩⟩

/-- Register update substitution preserves the original operands. -/
theorem mapStateSet (σ : Substitution) (rn : NatNotation) :
    σ.apply (app ``HybridWord.State.set [st,rn.native r,v]) =
      app ``HybridWord.State.set [σ.apply st,rn.native r,σ.apply v] := by
  cases σ <;> cases rn <;> rfl

/-- Original State values derive the internal value rule and its fixed-array
requirements. In particular, scalar operands use the shared source induction. -/
theorem StateValue.forms (source : StateValue Γ raw) (related : Context.Related Γ Δ)
    (frame : ScalarFrame env Δ ctx p σ τ) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (inputs : InputsTyped env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p) (references : ReferenceScope p)
    (current : CurrentMapping σ p (stateVariables Γ raw)) :
    FunctionSyntax.Syntax env (mode := .value) ctx p σ scope raw
      (FixedSequenceCompleteness.InputConditions ds) ∧
      LexicalScalarSyntax.StaticRegisters (σ.apply raw) := by
  cases source with
  | reference state =>
    have same := state.current current
    obtain ⟨position,ref⟩ := state.mappedReference related frame
    exact ⟨.valueCurrent same,by rw [ref]; trivial⟩
  | @set st v annotation state register rn value =>
    have same := state.current current.appLeft.appLeft.appRight
    obtain ⟨position,ref⟩ := state.mappedReference related frame
    have ps : p.s = .bvar position := same.symm.trans ref
    obtain ⟨vf,vs⟩ := value.forms related frame library closed inputs typing references current.appRight
    have static : LexicalScalarSyntax.StaticRegisters (σ.apply (app ``HybridWord.State.set [st,rn.native register,v])) := by
      rw [mapStateSet,same,ps]
      cases rn <;> exact ⟨⟨⟨by trivial,by trivial⟩,by trivial⟩,vs⟩
    refine ⟨.valueAssign register rn same vf ?_,static⟩
    rw [mapStateSet] at static ⊢
    exact FixedSequenceCompleteness.InputConditions.valueAssign rn register static

/-- A return wraps the same original State-value rule. No transformed-body
judgment or generated-code property is needed at this source boundary. -/
theorem StateValue.returnSyntax (source : StateValue Γ raw) (tag : Return.Form)
    (related : Context.Related Γ Δ) (frame : ScalarFrame env Δ ctx p σ τ)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p) (current : CurrentMapping σ p (stateVariables Γ raw)) :
    FunctionSyntax.Syntax env ctx p σ scope (tag.source raw)
      (FixedSequenceCompleteness.InputConditions ds) := by
  cases source with
  | reference state =>
    have same := state.current current
    obtain ⟨position,ref⟩ := state.mappedReference related frame
    have ps : p.s = .bvar position := same.symm.trans ref
    apply FunctionSyntax.Syntax.base (.returns tag same)
    rw [StructuralSyntax.substitute_return, same]
    have conditions : FixedSequenceCompleteness.InputConditions ds (tag.source p.s) := by
      rw [ps]; exact FixedSequenceCompleteness.InputConditions.returnVariable tag position
    exact .atom (.returns tag conditions) conditions
  | @set st v annotation state register rn value =>
    have same := state.current current.appLeft.appLeft.appRight
    obtain ⟨position,ref⟩ := state.mappedReference related frame
    have ps : p.s = .bvar position := same.symm.trans ref
    obtain ⟨vf,vs⟩ := value.forms related frame library closed inputs typing references current.appRight
    apply FunctionSyntax.Syntax.base (.assign tag same)
    rw [StructuralSyntax.substitute_return,mapStateSet,same]
    refine ScopedSyntax.Syntax.assign tag (rn.argument library.scalars.toSignatures register) vf ?_
    apply FixedSequenceCompleteness.InputConditions.assign tag rn register
    rw [ps]
    cases tag <;> cases rn <;> exact ⟨by trivial,⟨⟨⟨by trivial,by trivial⟩,by trivial⟩,vs⟩⟩

end IRComparison.WordFrontend.OrdinarySource
