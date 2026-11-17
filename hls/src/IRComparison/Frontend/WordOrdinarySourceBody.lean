import IRComparison.Frontend.WordOrdinarySourceRead

/-! Compositional interpretation of original command bindings. The child
Syntax arguments below are induction hypotheses, never constructors of the
public source judgment. Original static notation is transported by the shared
binding proof instead of being demanded again after substitution. -/
namespace IRComparison.WordFrontend.OrdinarySource
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody ScalarSyntax
set_option maxHeartbeats 2400000

private theorem letConditions {body : Lean.Expr} (static : LexicalScalarSyntax.StaticRegisters (.letE binder ty value body flag)) :
    FixedSequenceCompleteness.InputConditions ds (.letE binder ty value body flag) := by
  constructor
  · exact static
  · intro tag st r v h; cases tag <;> cases h
  · intro st r v h; cases h
  · intro st a k v h; simp [app] at h
  · intro st d o n h; simp [app] at h
  · intro annotation v fn h; cases annotation <;> cases h
  · intro annotation v fn h; cases annotation <;> cases h
  · intro a b c st fn h; cases h

private theorem readConditions (result : Result) (annotation : WordBinder.Annotation)
    (read : FixedReadSourceCompleteness.Conditions ds value)
    (static : LexicalScalarSyntax.StaticRegisters (readBind result annotation value fn)) :
    FixedSequenceCompleteness.InputConditions ds (readBind result annotation value fn) := by
  cases result with
  | body => exact FixedSequenceCompleteness.InputConditions.readBind annotation read static
  | step =>
    constructor
    · exact static
    · intro tag st r v h; cases tag <;> cases annotation <;> cases h
    · intro st r v h; cases annotation <;> cases h
    · intro st a k v h; cases annotation <;> cases h
    · intro st d o n h; cases annotation <;> cases h
    · intro other v f h; cases annotation <;> cases other <;> cases h
    · intro other v f h
      cases annotation <;> cases other <;>
        simp only [readBind,Result.native,WordBinder.stepReadSource,bindHead,
          Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,Lean.Expr.app.injEq] at h
      all_goals first | contradiction | exact h.1.2 ▸ read
    · intro a b c st f h; cases annotation <;> cases h

/-- The original scalar initializer is interpreted once. The continuation
uses its original binder; the existing letValue rule retains the value. -/
theorem scalarLetSyntax (value : Scalar Γ v actual) (result : Result) (annotation : WordBinder.Annotation)
    (related : Context.Related Γ Δ) (frame : ScalarFrame env Δ ctx p σ τ)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p) (current : CurrentMapping σ p (stateVariables Γ v))
    (registers : RegisterMapping σ) (bodyStatic : LexicalScalarSyntax.StaticRegisters b)
    (next : FunctionSyntax.Syntax env (mode := result.mode)
      (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
      (under σ) (.push none scope) b (FixedSequenceCompleteness.InputConditions ds))
    (binder : Lean.Name) (flag : Bool) :
    FunctionSyntax.Syntax env (mode := result.mode) ctx p σ scope
      (WordBinder.letSource annotation binder v b flag) (FixedSequenceCompleteness.InputConditions ds) := by
  obtain ⟨form,static⟩ := value.forms related frame library closed inputs typing references current
  have conditions : FixedSequenceCompleteness.InputConditions ds
      (σ.apply (WordBinder.letSource annotation binder v b flag)) := by
    rw [FunctionSyntax.substitute_annotated_let]
    exact letConditions ⟨static,registers.under.substitute bodyStatic⟩
  cases result with
  | body => exact .letValue annotation form next binder flag conditions
  | step => exact .stepLetValue annotation form next binder flag conditions

/-- State aliases and updates select their existing internal rules from the
original State expression. No alias test is a source-level premise. -/
theorem stateLetSyntax (value : StateValue Γ v) (result : Result)
    (related : Context.Related Γ Δ) (frame : ScalarFrame env Δ ctx p σ τ)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p) (current : CurrentMapping σ p (stateVariables Γ v))
    (next : FunctionSyntax.Syntax env (mode := result.mode)
      (stateType::ctx) {p.lift with s := .bvar 0}
      (under σ) (.push none scope) b (FixedSequenceCompleteness.InputConditions ds))
    (binder : Lean.Name) (flag : Bool) :
    FunctionSyntax.Syntax env (mode := result.mode) ctx p σ scope
      (StateLet.source binder v b flag) (FixedSequenceCompleteness.InputConditions ds) := by
  obtain ⟨valueSyntax,_⟩ := value.forms related frame library closed inputs typing references current
  cases value with
  | reference state =>
    have same := state.current current
    cases result with
    | body => exact .stateAlias same next binder flag
    | step => exact .stepAlias same next binder flag
  | @set st value annotation state register rn scalar =>
    have same := state.current current.appLeft.appLeft.appRight
    obtain ⟨position,ref⟩ := state.mappedReference related frame
    have ps : p.s = .bvar position := same.symm.trans ref
    have apart : sameTerm (σ.apply (app ``HybridWord.State.set [st,rn.native register,value])) p.s = false := by
      rw [mapStateSet,ps]
      exact sameTerm_application_variable _ _ position
    cases result with
    | body => exact .stateLet valueSyntax next apart binder flag
    | step => exact .stepStateLet valueSyntax next apart binder flag

/-- The same binding step handles Word and BitVec reads in both ordinary
bodies and iterator continuations. -/
theorem readBindSyntax (read : Read ds Γ v actual) (result : Result) (annotation : WordBinder.Annotation)
    (related : Context.Related Γ Δ) (frame : ScalarFrame env Δ ctx p σ τ)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p) (current : CurrentMapping σ p (stateVariables Γ v))
    (registers : RegisterMapping σ) (bodyStatic : LexicalScalarSyntax.StaticRegisters b)
    (next : FunctionSyntax.Syntax env (mode := result.mode)
      (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
      (under σ) (.push none scope) b (FixedSequenceCompleteness.InputConditions ds))
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    FunctionSyntax.Syntax env (mode := result.mode) ctx p σ scope
      (readBind result annotation v (.lam binder annotation.native b info))
      (FixedSequenceCompleteness.InputConditions ds) := by
  obtain ⟨form,conditions⟩ := read.forms related frame library closed inputs typing references current
  have mapped : σ.apply (readBind result annotation v (.lam binder annotation.native b info)) =
      readBind result annotation (σ.apply v) (.lam binder annotation.native ((under σ).apply b) info) := by
    cases σ <;> cases result <;> cases annotation <;> rfl
  have checks : FixedSequenceCompleteness.InputConditions ds
      (σ.apply (readBind result annotation v (.lam binder annotation.native b info))) := by
    rw [mapped]
    apply readConditions result annotation conditions
    have child := registers.under.substitute bodyStatic
    cases result <;> cases annotation <;>
      exact ⟨⟨by trivial,conditions.registers⟩,child⟩
  cases result with
  | body => exact .bindValue annotation form next binder info checks
  | step => exact .stepBindValue annotation form next binder info checks

/-- Choice operands obtain their inferred Word/BV32 type from the original
scalar judgment. Both branches remain ordinary recursive Syntax hypotheses. -/
theorem branchSyntax (guard : Scalar Γ v actual) (result : Result) (annotation : WordBinder.Annotation)
    (related : Context.Related Γ Δ) (frame : ScalarFrame env Δ ctx p σ τ)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p) (current : CurrentMapping σ p (stateVariables Γ v))
    (registers : RegisterMapping σ)
    (static : LexicalScalarSyntax.StaticRegisters (branch result annotation v a b))
    (yes : FunctionSyntax.Syntax env (mode := result.mode) ctx p σ scope a
      (FixedSequenceCompleteness.InputConditions ds))
    (no : FunctionSyntax.Syntax env (mode := result.mode) ctx p σ scope b
      (FixedSequenceCompleteness.InputConditions ds)) :
    FunctionSyntax.Syntax env (mode := result.mode) ctx p σ scope
      (branch result annotation v a b) (FixedSequenceCompleteness.InputConditions ds) := by
  obtain ⟨form,_⟩ := guard.forms related frame library closed inputs typing references current
  obtain ⟨core,inferred,rep,typed,shape⟩ := frame.evidence guard related library closed
  have mapped : σ.apply (branch result annotation v a b) =
      branch result annotation (σ.apply v) (σ.apply a) (σ.apply b) := by
    cases σ <;> cases result <;> cases annotation <;> rfl
  have conditions : FixedSequenceCompleteness.InputConditions ds
      (σ.apply (branch result annotation v a b)) := by
    have moved := registers.substitute static
    rw [mapped] at moved ⊢
    cases result <;> exact FixedSequenceCompleteness.InputConditions.choice moved
  cases result with
  | body => exact .annotatedBooleanBranch annotation inferred form rep typed shape yes no conditions
  | step => exact .annotatedStepBooleanBranch annotation inferred form rep typed shape yes no conditions

/-- A static range bound is a closed source arithmetic expression. Changing
lexical environments does not require normalizing it or imposing a budget. -/
theorem staticBoundMapped (bound : FixedSequenceCompleteness.StaticBound raw n) (σ : Substitution) :
    σ.apply raw = raw := by
  rw [Substitution.apply_eq]
  induction bound with
  | natural n => rfl
  | negative value ih =>
    simp only [For.nativeNegative,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,LeanBindings.substitute,ih]
  | binary op left right il ir =>
    cases op <;> simp only [For.nativeBinary,For.nativeBinaryHeader,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,app,List.foldl_cons,List.foldl_nil,
      LeanBindings.substitute,il,ir]

theorem staticRangeSyntax (state : StateRef Γ st)
    (start : FixedSequenceCompleteness.StaticBound a startValue)
    (stop : FixedSequenceCompleteness.StaticBound b stopValue)
    (stride : FixedSequenceCompleteness.StaticBound c strideValue)
    (library : ScopedSyntax.Library env) (current : CurrentMapping σ p (stateVariables Γ st))
    (registers : RegisterMapping σ)
    (static : LexicalScalarSyntax.StaticRegisters (For.source a b c st (.lam kn word (.lam tn WordFrontend.state raw ti) ki)))
    (next : FunctionSyntax.Syntax env (mode := .step)
      (stateType::wordType::ctx) (For.parameters p) (under (under σ)) (.push none (.push none scope)) raw
      (FixedSequenceCompleteness.InputConditions ds)) :
    FunctionSyntax.Syntax env ctx p σ scope
      (For.source a b c st (.lam kn word (.lam tn WordFrontend.state raw ti) ki))
      (FixedSequenceCompleteness.InputConditions ds) := by
  have sa := staticBoundMapped start σ
  have sb := staticBoundMapped stop σ
  have sc := staticBoundMapped stride σ
  obtain ⟨ab⟩ := start.typed (ctx := ctx) library.bounds library.scalars.toSignatures
  obtain ⟨bb⟩ := stop.typed (ctx := ctx) library.bounds library.scalars.toSignatures
  obtain ⟨cb⟩ := stride.typed (ctx := ctx) library.bounds library.scalars.toSignatures
  refine .forStatic (sa.symm ▸ ab) (sb.symm ▸ bb) (sc.symm ▸ cb) (state.current current) next kn tn ki ti ?_
  have mapped : σ.apply (For.source a b c st (.lam kn word (.lam tn WordFrontend.state raw ti) ki)) =
      For.source (σ.apply a) (σ.apply b) (σ.apply c) (σ.apply st)
        (.lam kn word (.lam tn WordFrontend.state ((under (under σ)).apply raw) ti) ki) := by
    cases σ <;> rfl
  have moved := registers.substitute static
  rw [mapped,sa,sb,sc] at moved ⊢
  exact FixedSequenceCompleteness.InputConditions.forStatic start stop stride moved

theorem naturalRangeSyntax (state : StateRef Γ st) (count : Scalar Γ n actual) (kind : NaturalLoop.Kind)
    (related : Context.Related Γ Δ) (frame : ScalarFrame env Δ ctx p σ τ)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p) (stateCurrent : CurrentMapping σ p (stateVariables Γ st))
    (countCurrent : CurrentMapping σ p (stateVariables Γ n)) (registers : RegisterMapping σ)
    (static : LexicalScalarSyntax.StaticRegisters (kind.source n st (kind.nativeLambda kn tn ki ti raw)))
    (next : FunctionSyntax.Syntax env (mode := kind.mode)
      (kind.context ctx) (kind.parameters p) (under (under σ)) (.push none (.push none scope)) raw
      (FixedSequenceCompleteness.InputConditions ds)) :
    FunctionSyntax.Syntax env ctx p σ scope
      (kind.source n st (kind.nativeLambda kn tn ki ti raw)) (FixedSequenceCompleteness.InputConditions ds) := by
  obtain ⟨form,_⟩ := count.forms related frame library closed inputs typing references countCurrent
  refine .forRange kind form (state.current stateCurrent) next kn tn ki ti ?_
  have mapped : σ.apply (kind.source n st (kind.nativeLambda kn tn ki ti raw)) =
      kind.source (σ.apply n) (σ.apply st) (kind.nativeLambda kn tn ki ti ((under (under σ)).apply raw)) := by
    cases σ <;> cases kind <;> rfl
  have moved := registers.substitute static
  rw [mapped] at moved ⊢
  exact FixedSequenceCompleteness.InputConditions.forRange kind moved

/-- Array writes obtain declaration and scalar obligations from the original
source operands. No generated command or parser success is supplied. -/
theorem writeSyntax (state : StateRef Γ st) (array : Nat) (an : NatNotation)
    (declared : (FixedMemory.lookup ds array).isSome = true)
    (index : Scalar Γ k ka) (value : Scalar Γ v va)
    (related : Context.Related Γ Δ) (frame : ScalarFrame env Δ ctx p σ τ)
    (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p)
    (current : CurrentMapping σ p (stateVariables Γ st ++ stateVariables Γ k ++ stateVariables Γ v)) :
    FunctionSyntax.Syntax env ctx p σ scope
      (app ``HybridWord.State.write [st,an.native array,k,v]) (FixedSequenceCompleteness.InputConditions ds) := by
  have same := state.current current.left.left
  obtain ⟨position,ref⟩ := state.mappedReference related frame
  have ps : p.s = .bvar position := same.symm.trans ref
  obtain ⟨kf,ks⟩ := index.forms related frame library closed inputs typing references current.left.right
  obtain ⟨vf,vs⟩ := value.forms related frame library closed inputs typing references current.right
  have mapped : σ.apply (app ``HybridWord.State.write [st,an.native array,k,v]) =
      app ``HybridWord.State.write [p.s,an.native array,σ.apply k,σ.apply v] := by
    have eq : σ.apply (app ``HybridWord.State.write [st,an.native array,k,v]) =
        app ``HybridWord.State.write [σ.apply st,an.native array,σ.apply k,σ.apply v] := by
      cases σ <;> cases an <;> rfl
    rw [eq,same]
  apply FunctionSyntax.Syntax.base (.store same)
  rw [mapped]
  refine ScopedSyntax.Syntax.write (an.argument library.scalars.toSignatures array) kf vf ?_
  constructor
  · rw [ps]; cases an <;> exact ⟨⟨⟨⟨by trivial,by trivial⟩,by trivial⟩,ks⟩,vs⟩
  · intro tag st r v h; cases tag <;> cases h
  · intro st r v h; cases h
  · intro st a k v h
    simp only [app,List.foldl_cons,List.foldl_nil,Lean.Expr.app.injEq] at h
    exact ⟨array,an,h.1.1.2.symm,declared⟩
  · intro st d o n h; simp [app] at h
  · intro annotation v fn h; cases annotation <;> cases h
  · intro annotation v fn h; cases annotation <;> cases h
  · intro a b c st fn h; cases h

/-- Whole-array copying retains the original equality of declared capacities. -/
theorem copySyntax (state : StateRef Γ st) (destination origin count : Nat) (dn sn cn : NatNotation)
    (target : FixedMemory.lookup ds destination = some count)
    (source : FixedMemory.lookup ds origin = some count)
    (related : Context.Related Γ Δ) (frame : ScalarFrame env Δ ctx p σ τ)
    (library : ScopedSyntax.Library env) (current : CurrentMapping σ p (stateVariables Γ st)) :
    FunctionSyntax.Syntax env ctx p σ scope
      (app ``HybridWord.State.copy [st,dn.native destination,sn.native origin,cn.native count])
      (FixedSequenceCompleteness.InputConditions ds) := by
  have same := state.current current
  obtain ⟨position,ref⟩ := state.mappedReference related frame
  have ps : p.s = .bvar position := same.symm.trans ref
  have mapped : σ.apply (app ``HybridWord.State.copy [st,dn.native destination,sn.native origin,cn.native count]) =
      app ``HybridWord.State.copy [p.s,dn.native destination,sn.native origin,cn.native count] := by
    have eq : σ.apply (app ``HybridWord.State.copy [st,dn.native destination,sn.native origin,cn.native count]) =
        app ``HybridWord.State.copy [σ.apply st,dn.native destination,sn.native origin,cn.native count] := by
      cases σ <;> cases dn <;> cases sn <;> cases cn <;> rfl
    rw [eq,same]
  apply FunctionSyntax.Syntax.base (.copy same)
  rw [mapped]
  have conditions : FixedSequenceCompleteness.InputConditions ds
      (app ``HybridWord.State.copy [p.s,dn.native destination,sn.native origin,cn.native count]) := by
    constructor
    · rw [ps]; cases dn <;> cases sn <;> cases cn <;> trivial
    · intro tag st r v h; cases tag <;> cases h
    · intro st r v h; cases h
    · intro st a k v h; simp [app] at h
    · intro st d o n h
      simp only [app,List.foldl_cons,List.foldl_nil,Lean.Expr.app.injEq] at h
      exact ⟨destination,origin,count,dn,sn,cn,h.1.1.2.symm,h.1.2.symm,h.2.symm,target,source⟩
    · intro annotation v fn h; cases annotation <;> cases h
    · intro annotation v fn h; cases annotation <;> cases h
    · intro a b c st fn h; cases h
  exact .atom (.copy (dn.argument library.scalars.toSignatures destination)
    (sn.argument library.scalars.toSignatures origin) (cn.argument library.scalars.toSignatures count) conditions) conditions

/-- The command-body induction uses the same State binder in either result
mode; only the existing sequencing constructor changes. -/
theorem stateBindSyntax (result : Result)
    (first : FunctionSyntax.Syntax env ctx p σ scope a requirements)
    (next : FunctionSyntax.Syntax env (mode := result.mode)
      (stateType::ctx) {p.lift with s := .bvar 0} (under σ) (.push none scope) b requirements)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    FunctionSyntax.Syntax env (mode := result.mode) ctx p σ scope
      (sequence result a (.lam binder state b info)) requirements := by
  cases result with
  | body => exact .sequence first next binder info
  | step => exact .stepSequence first next binder info

theorem unitBindSyntax (result : Result)
    (next : FunctionSyntax.Syntax env (mode := result.mode)
      (UnitStep.unitType::ctx) p.lift (under σ) (.push none scope) b requirements)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    FunctionSyntax.Syntax env (mode := result.mode) ctx p σ scope
      (StructuralUnit.source (result == .step) binder b info) requirements := by
  cases result with
  | body => exact .unitBody next binder info
  | step => exact .unitLoop next binder info

end IRComparison.WordFrontend.OrdinarySource
