import IRComparison.Frontend.WordStructuralBody
import IRComparison.Frontend.WordScalarSyntax
import IRComparison.Frontend.WordReturnCompleteness
import IRComparison.Frontend.WordBranchCompleteness
import IRComparison.Frontend.WordLetCompleteness
import IRComparison.Frontend.WordStateAliasCompleteness

/-! Syntax-directed completeness of the structural body traversal.
This file connects existing constructor typing proofs to the new traversal;
it does not yet cover the entire accepted ordinary-Lean grammar. -/
namespace IRComparison.WordFrontend.StructuralSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate
open StructuralBody
set_option maxHeartbeats 1200000

/-- Both existing Lean return spellings select the same leaf as before.
No recursive call or fuel adequacy is involved in this leaf equation. -/
theorem return_leaf (inputs : InputsTyped env ctx p) (form : Return.Form) :
    StructuralBody.bodyRetained env conv exposure ctx p (form.source p.s) =
      bodyStep env conv exposure (fun _ _ _ => none) (fun _ _ _ => none)
        (fun _ _ => none) (fun _ _ _ => none) ctx p (form.source p.s) := by
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have modeStep : (Mode.body == Mode.step) = false := rfl
  have same := sameTerm_complete inputs.s.property inputs.s.property
  unfold StructuralBody.bodyRetained
  rw [StructuralBody.visit]
  have args : (form.source p.s).getAppArgs.back? = some p.s := by cases form <;> rfl
  cases form <;>
    simp [StructuralBody.node,bodyValue,modeStep,same,args,Lean.Expr.getAppFn,Lean.Expr.constName?,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      Substitution.apply,ScalarEnvironment.arguments,ScalarEnvironment.below,Return.Form.source,Return.Form.nativeHeader,
      Mode.expected,bodyStep,leadingLet]
  all_goals simp only [Return.Form.source,Return.Form.nativeHeader] at args
  all_goals simp only [args,Option.bind_some,same,ite_true]
  all_goals rfl

/-- The write constructor uses the structural scalar callback. Its typing
proof is shared with the legacy traversal through store_step_complete. -/
theorem store_leaf (inputs : InputsTyped env ctx p) :
    StructuralBody.bodyRetained env conv exposure ctx p (app ``HybridWord.State.write [p.s,a,k,v]) =
      bodyStep env conv exposure (ScalarEnvironment.parse env conv exposure)
        (fun _ _ _ => none) (fun _ _ => none) (fun _ _ _ => none)
        ctx p (app ``HybridWord.State.write [p.s,a,k,v]) := by
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have modeBody : (Mode.body != Mode.body) = false := rfl
  have args : (app ``HybridWord.State.write [p.s,a,k,v]).getAppArgs.toList = [p.s,a,k,v] := rfl
  have same := sameTerm_complete inputs.s.property inputs.s.property
  unfold StructuralBody.bodyRetained
  rw [StructuralBody.visit]
  simp [StructuralBody.node,bodyValue,same,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
    Substitution.apply,ScalarEnvironment.arguments,ScalarEnvironment.below,
    modeBody,Mode.expected,bodyStep,leadingLet,app,Lean.Expr.getAppFn,Lean.Expr.constName?]
  simp only [app,List.foldl_cons,List.foldl_nil] at args
  simp only [args,same,Bool.true_eq_false,ite_false]
  rfl

/-- The copy leaf has no recursive syntax call. -/
theorem copy_leaf (inputs : InputsTyped env ctx p) :
    StructuralBody.bodyRetained env conv exposure ctx p (app ``HybridWord.State.copy [p.s,d,s,n]) =
      bodyStep env conv exposure (fun _ _ _ => none) (fun _ _ _ => none)
        (fun _ _ => none) (fun _ _ _ => none) ctx p (app ``HybridWord.State.copy [p.s,d,s,n]) := by
  have same := sameTerm_complete inputs.s.property inputs.s.property
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have bodyBody : (Mode.body != Mode.body) = false := rfl
  have args : (app ``HybridWord.State.copy [p.s,d,s,n]).getAppArgs.toList = [p.s,d,s,n] := rfl
  unfold StructuralBody.bodyRetained
  rw [StructuralBody.visit]
  simp [StructuralBody.node,bodyValue,bodyBody,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
    Substitution.apply,ScalarEnvironment.arguments,ScalarEnvironment.below,
    Mode.expected,bodyStep,leadingLet,app,Lean.Expr.getAppFn,Lean.Expr.constName?,same]
  simp only [app,List.foldl_cons,List.foldl_nil] at args
  simp only [args,same,Bool.true_eq_false,ite_false]
  rfl

/-- Recursive branches use the structural traversal for both arms. -/
theorem branch_node :
    StructuralBody.bodyRetained env conv exposure ctx p (Branch.source v d yes no) =
      bodyStep env conv exposure (ScalarEnvironment.parse env conv exposure)
        (fun _ _ _ => none) (fun _ _ => none) (StructuralBody.bodyRetained env conv exposure)
        ctx p (Branch.source v d yes no) := by
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have bodyStep : (Mode.body == Mode.step) = false := rfl
  have args : (Branch.source v d yes no).getAppArgs.toList =
      [option state,Branch.nativeCondition v,d,yes,no] := rfl
  have test : nonzeroValue (Branch.nativeCondition v) = some v := rfl
  unfold StructuralBody.bodyRetained
  rw [StructuralBody.visit]
  simp [StructuralBody.node,bodyValue,bodyStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
    Substitution.apply,ScalarEnvironment.arguments,ScalarEnvironment.below,
    Mode.expected,WordFrontend.bodyStep,leadingLet,Branch.source,Lean.mkApp5,Lean.mkApp4,
    Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,List.map_cons,List.map_nil,
    Lean.Expr.getAppFn,Lean.Expr.constName?,StructuralBody.arguments]
  simp only [Branch.source,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at args
  simp only [args,test,Option.bind_some]
  rfl

/-- State updates inside either return spelling use the same scalar parser. -/
theorem assign_node (form : Return.Form) :
    StructuralBody.bodyRetained env conv exposure ctx p
      (form.source (app ``HybridWord.State.set [p.s,r,v])) =
      bodyStep env conv exposure (ScalarEnvironment.parse env conv exposure)
        (fun _ _ _ => none) (fun _ _ => none) (fun _ _ _ => none)
        ctx p (form.source (app ``HybridWord.State.set [p.s,r,v])) := by
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have bodyStep : (Mode.body == Mode.step) = false := rfl
  unfold StructuralBody.bodyRetained
  rw [StructuralBody.visit]
  have args : (form.source (app ``HybridWord.State.set [p.s,r,v])).getAppArgs.back? =
      some (app ``HybridWord.State.set [p.s,r,v]) := by cases form <;> rfl
  cases form <;>
    simp [StructuralBody.node,bodyValue,bodyStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      Substitution.apply,ScalarEnvironment.arguments,ScalarEnvironment.below,Mode.expected,
      WordFrontend.bodyStep,leadingLet,Return.Form.source,Return.Form.nativeHeader,
      Lean.Expr.getAppFn,Lean.Expr.constName?,StructuralBody.arguments]
  all_goals simp only [Return.Form.source,Return.Form.nativeHeader] at args
  all_goals try simp only [args,Option.bind_some]
  all_goals rfl

private theorem empty_functions : underFunctions (fun _ => (none : Option (Continuation env))) =
    (fun _ => none) := by funext n; cases n <;> rfl

theorem letValue_node :
    StructuralBody.bodyRetained env conv exposure ctx p (letValueSource binder value next flag) =
      bodyStep env conv exposure (ScalarEnvironment.parse env conv exposure)
        (fun _ _ _ => none) (fun _ _ => none) (StructuralBody.bodyRetained env conv exposure)
        ctx p (letValueSource binder value next flag) := by
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have bodyStep : (Mode.body == Mode.step) = false := rfl
  have ws : sameTerm word state = false := rfl
  have ww : compatible env conv ctx word word = true :=
    compatible_same (Represents.constant rfl) (Represents.constant rfl) env conv ctx
  have wt : translate word = some ⟨wordType,Represents.constant rfl⟩ := rfl
  unfold StructuralBody.bodyRetained
  rw [StructuralBody.visit]
  simp [StructuralBody.node,bodyValue,bodyStep,letParts,letValueSource,Substitution.apply,
    under,empty_functions,ws,ww,wt,WordFrontend.bodyStep]
  rfl

theorem alias_node (inputs : InputsTyped env ctx p) :
    StructuralBody.bodyRetained env conv exposure ctx p (.letE binder state p.s next flag) =
      bodyStep env conv exposure (ScalarEnvironment.parse env conv exposure)
        (fun _ _ _ => none) (fun _ _ => none) (StructuralBody.bodyRetained env conv exposure)
        ctx p (.letE binder state p.s next flag) := by
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have bodyStep : (Mode.body == Mode.step) = false := rfl
  have ss : sameTerm state state = true := sameTerm_complete (Represents.constant rfl) (Represents.constant rfl)
  have same := sameTerm_complete inputs.s.property inputs.s.property
  have st : translate state = some ⟨stateType,Represents.constant rfl⟩ := rfl
  unfold StructuralBody.bodyRetained
  rw [StructuralBody.visit]
  simp [StructuralBody.node,bodyValue,bodyStep,letParts,Substitution.apply,under,
    empty_functions,ss,same,st,WordFrontend.bodyStep]
  rfl

theorem sequence_node :
    StructuralBody.bodyRetained env conv exposure ctx p (sequenceSource first (.lam binder state next info)) =
      bodyStep env conv exposure (ScalarEnvironment.parse env conv exposure)
        (fun _ _ _ => none) (fun _ _ => none) (StructuralBody.bodyRetained env conv exposure)
        ctx p (sequenceSource first (.lam binder state next info)) := by
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have bodyStep : (Mode.body == Mode.step) = false := rfl
  have ss : sameTerm state state = true := sameTerm_complete (Represents.constant rfl) (Represents.constant rfl)
  have sc : compatible env conv ctx state state = true :=
    compatible_same (Represents.constant rfl) (Represents.constant rfl) env conv ctx
  have st : translate state = some ⟨stateType,Represents.constant rfl⟩ := rfl
  have su : sameTerm state (.const ``PUnit [.succ .zero]) = false := rfl
  have args : (sequenceSource first (.lam binder state next info)).getAppArgs =
    #[.const ``Option [.zero],Lean.mkAppN (.const ``Monad.toBind [.zero,.zero])
      #[.const ``Option [.zero],.const ``instMonadOption [.zero]],state,state,first,.lam binder state next info] := rfl
  unfold StructuralBody.bodyRetained
  rw [StructuralBody.visit]
  simp [StructuralBody.node,bodyValue,bodyStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
    Substitution.apply,ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,under,
    empty_functions,ss,sc,st,WordFrontend.bodyStep,leadingLet,sequenceSource,Lean.mkApp,Lean.mkApp2,
    Lean.mkAppB,Lean.Expr.getAppFn,Lean.Expr.constName?,bindHead,stateBindHeader,optionBindHeader,Lean.mkAppN,List.map_cons,List.map_nil]
  simp only [sequenceSource,Lean.mkApp,Lean.mkApp2,Lean.mkAppB,bindHead,Lean.mkAppN] at args
  simp only [List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,
    Function.comp_apply,List.length_cons,List.length_nil,Nat.reduceAdd,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.unattach_some,
    args,Array.getElem?_eq_getElem,List.length_cons,List.length_nil,Array.back?,
    su,ss,sc,st,Option.bind_some,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true]
  rfl

theorem bindValue_node :
    StructuralBody.bodyRetained env conv exposure ctx p (bindValueSource first (.lam binder word next info)) =
      bodyStep env conv exposure (ScalarEnvironment.parse env conv exposure)
        (fun ctx p => readStep env conv exposure ctx p (ScalarEnvironment.parse env conv exposure ctx p)) (fun _ _ => none) (StructuralBody.bodyRetained env conv exposure)
        ctx p (bindValueSource first (.lam binder word next info)) := by
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have bodyStep : (Mode.body == Mode.step) = false := rfl
  have ss : sameTerm word state = false := rfl
  have sc : compatible env conv ctx word word = true :=
    compatible_same (Represents.constant rfl) (Represents.constant rfl) env conv ctx
  have st : translate word = some ⟨wordType,Represents.constant rfl⟩ := rfl
  have su : sameTerm word (.const ``PUnit [.succ .zero]) = false := rfl
  have args : (bindValueSource first (.lam binder word next info)).getAppArgs =
    #[.const ``Option [.zero],Lean.mkAppN (.const ``Monad.toBind [.zero,.zero])
      #[.const ``Option [.zero],.const ``instMonadOption [.zero]],word,state,first,.lam binder word next info] := rfl
  unfold StructuralBody.bodyRetained
  rw [StructuralBody.visit]
  simp [StructuralBody.node,bodyValue,bodyStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
    Substitution.apply,ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,under,
    empty_functions,ss,sc,st,WordFrontend.bodyStep,leadingLet,bindValueSource,Lean.mkApp,Lean.mkApp2,
    Lean.mkAppB,Lean.Expr.getAppFn,Lean.Expr.constName?,bindHead,stateBindHeader,optionBindHeader,Lean.mkAppN,List.map_cons,List.map_nil]
  simp only [bindValueSource,Lean.mkApp,Lean.mkApp2,Lean.mkAppB,bindHead,Lean.mkAppN] at args
  simp only [List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append,
    Function.comp_apply,List.length_cons,List.length_nil,Nat.reduceAdd,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.unattach_some,
    args,Array.getElem?_eq_getElem,List.length_cons,List.length_nil,Array.back?,
    su,ss,sc,st,Option.bind_some,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true]
  rfl

structure Library (env : VEnv) : Prop where
  scalars : ScalarSyntax.Library env
  returns : Return.Signatures env
  returnFact : ∀ form : Return.Form, env.constants form.fact = some ⟨0,form.signature⟩
  skipConstructor : env.constants ``HybridWord.Cmd.skip = some ⟨0,cmdType⟩
  storeFact : env.constants ``WordFrontendFacts.store = some ⟨0,storeSignature⟩
  storeConstructor : env.constants ``HybridWord.Cmd.store = some ⟨0,Certificate.storeConstructor⟩
  assignFact : ∀ form : Return.Form, env.constants form.assignFact = some ⟨0,assignSignatureWith form.header⟩
  assignConstructor : env.constants ``HybridWord.Cmd.assign = some ⟨0,Return.assignConstructor⟩
  setter : env.constants ``HybridWord.State.set = some ⟨0,Return.setterSignature⟩
  writer : env.constants ``HybridWord.State.write = some ⟨0,writeSignature⟩
  copyFact : env.constants ``WordFrontendFacts.copy = some ⟨0,copySignature⟩
  copyConstructor : env.constants ``HybridWord.Cmd.copy = some ⟨0,Certificate.copyConstructor⟩
  copier : env.constants ``HybridWord.State.copy = some ⟨0,copySourceSignature⟩
  branchFact : env.constants ``WordFrontendFacts.branch = some ⟨0,Branch.signature⟩
  branchConstructor : env.constants ``HybridWord.Cmd.branch = some ⟨0,Branch.constructorSignature⟩
  ite : env.constants ``ite = some Branch.iteSignature

abbrev Decision := ScalarSyntax.Decision

theorem Library.option_typed (library : Library env) :
    DirectTyping env 0 ctx (optionType stateType) (.sort (.succ .zero)) := by
  have o : DirectTyping env 0 ctx (.const ``Option [.zero])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .constant library.returns.option (by simp [VLevel.WF]) rfl
  have st : DirectTyping env 0 ctx stateType (.sort (.succ .zero)) :=
    .constant library.returns.state (by simp) rfl
  exact .application o st

/-- The first body constructors connected to structural completeness.
This fragment is not a replacement for the broader supported input language.
In particular, sequence/branch/binder/loop completeness remains to be joined. -/
inductive Form (env : VEnv) (ctx : List VExpr) (p : Inputs) :
    Lean.Expr → (requirements : Lean.Expr → Prop := fun _ => True) → Prop where
  | returns (form : Return.Form)
      (checked : requirements (form.source p.s) := by trivial) :
      Form env ctx p (requirements := requirements) (form.source p.s)
  | write (array : NatArgument env ctx a) (index : ScalarSyntax.Form env ctx p k)
      (value : ScalarSyntax.Form env ctx p v)
      (checked : requirements (app ``HybridWord.State.write [p.s,a,k,v]) := by trivial) :
      Form env ctx p (requirements := requirements) (app ``HybridWord.State.write [p.s,a,k,v])
  | assign (form : Return.Form) (register : NatArgument env ctx r) (value : ScalarSyntax.Form env ctx p v)
      (checked : requirements (form.source (app ``HybridWord.State.set [p.s,r,v])) := by trivial) :
      Form env ctx p (requirements := requirements) (form.source (app ``HybridWord.State.set [p.s,r,v]))
  | copy (destination : NatArgument env ctx d) (origin : NatArgument env ctx s)
      (count : NatArgument env ctx n)
      (checked : requirements (app ``HybridWord.State.copy [p.s,d,s,n]) := by trivial) :
      Form env ctx p (requirements := requirements) (app ``HybridWord.State.copy [p.s,d,s,n])
  | branch (value : ScalarSyntax.Form env ctx p v) (decision : Decision env ctx v d)
      (yes : Form env ctx p (requirements := requirements) a) (no : Form env ctx p (requirements := requirements) b)
      (checked : requirements (Branch.source v d a b) := by trivial) :
      Form env ctx p (requirements := requirements) (Branch.source v d a b)


theorem complete (inputs : InputsTyped env ctx p) (library : Library env)
    (locals : ScalarSyntax.Locals env ctx p)
    (coverage : Conversion.Covers conv 0 Arithmetic.Casts) (exposure : Exposure env)
    (form : Form env ctx p source requirements) :
    ∃ piece, StructuralBody.bodyRetained env conv exposure ctx p source = some piece ∧
      Nonempty (BodyCasts inputs piece Arithmetic.Casts) := by
  induction form with
  | returns tag =>
    rw [return_leaf inputs tag]
    exact Return.body_skip_invariant_complete library.returns inputs tag
      (library.returnFact tag) library.skipConstructor conv exposure Arithmetic.Casts coverage
  | write array index value =>
    obtain ⟨j,hj,⟨tj⟩⟩ := ScalarSyntax.complete inputs library.scalars locals coverage exposure index
    obtain ⟨e,he,⟨te⟩⟩ := ScalarSyntax.complete inputs library.scalars locals coverage exposure value
    rw [store_leaf inputs]
    exact store_step_complete inputs array tj te library.storeFact library.storeConstructor
      library.writer coverage exposure _ _ _ _ hj he
  | assign tag register value =>
    obtain ⟨v,hv,⟨tv⟩⟩ := ScalarSyntax.complete inputs library.scalars locals coverage exposure value
    rw [assign_node tag]
    exact Return.assign_step_complete library.returns inputs tag register tv (library.assignFact tag)
      library.assignConstructor library.setter coverage exposure _ _ _ _ hv
  | copy destination origin count =>
    rw [copy_leaf inputs]
    exact body_copy_invariant_complete inputs destination origin count library.copyFact
      library.copyConstructor library.copier conv exposure Arithmetic.Casts coverage
  | branch value decision _ _ checked ihYes ihNo =>
    obtain ⟨v,hv,⟨tv⟩⟩ := ScalarSyntax.complete inputs library.scalars locals coverage exposure value
    obtain ⟨a,ha,⟨ta⟩⟩ := ihYes
    obtain ⟨b,hb,⟨tb⟩⟩ := ihNo
    obtain ⟨vc,dc,vr,dr,pt,dt⟩ := decision.typing
    rw [← tv.sourceCore.property.unique vr] at pt dt
    rw [branch_node]
    exact Branch.branch_step_complete inputs tv ta tb dr pt dt library.option_typed library.ite
      library.branchFact library.branchConstructor (fun _ _ _ h => h) coverage exposure _ _ _ _ hv ha hb

end IRComparison.WordFrontend.StructuralSyntax
