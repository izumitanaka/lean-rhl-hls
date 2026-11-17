import IRComparison.Frontend.WordClosureEnvironment
import IRComparison.Frontend.WordStructuralSyntax

/-! Connect source-syntax rules to a helper's captured binding environment.
The runtime still traverses the original children. These equations permit
reuse of the existing constructor certificates at the substituted scope. -/
namespace IRComparison.WordFrontend.StructuralSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate StructuralBody
set_option maxHeartbeats 1200000

private theorem finish_congr (same : source = target) (code : ClosedTerm) (proof : Lean.Expr)
    (known : KnownTypes env 0 := noKnownTypes env 0) :
    HEq (finishBody env conv exposure ctx p mode source code proof known)
      (finishBody env conv exposure ctx p mode target code proof known) := by
  cases same
  rfl

private theorem none_congr {mode : Mode} (same : source = target) :
    HEq (none : Option (Piece env ctx p source mode.expected))
      (none : Option (Piece env ctx p target mode.expected)) := by
  cases same
  rfl

theorem substitute_return (σ : Substitution) (form : Return.Form) (s : Lean.Expr) :
    σ.apply (form.source s) = form.source (σ.apply s) := by
  simp only [Substitution.apply_eq]
  cases form <;> rfl

/-- Returning the current state is independent of the function environment.
In particular a helper parameter may stand for the latest state. -/
theorem mapped_return (same : sameTerm p.s p.s = true) (form : Return.Form)
    (current : σ.apply original = p.s) :
    HEq (visit env conv exposure (form.source original) ctx p .body σ fs)
      (StructuralBody.bodyRetained env conv exposure ctx p (form.source p.s)) := by
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have modeStep : (Mode.body == Mode.step) = false := rfl
  have mapped := substitute_return σ form original
  rw [current] at mapped
  unfold StructuralBody.bodyRetained
  rw [visit,visit]
  cases σ <;> cases form <;>
    simp [node,bodyValue,modeStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      Substitution.apply,LeanBindings.substitute,ScalarEnvironment.arguments,
      ScalarEnvironment.below,Return.Form.source,Return.Form.nativeHeader,
      Return.nativePureInstance,state,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
      Mode.expected,Lean.Expr.getAppFn,Lean.Expr.constName?] at current mapped ⊢
  all_goals simp only [current,same,ite_true]
  all_goals apply finish_congr; rw [current]

theorem substitute_app (σ : Substitution) (name : Lean.Name) (args : List Lean.Expr) :
    σ.apply (app name args) = app name (args.map σ.apply) := by
  simp only [Substitution.apply_eq,app]
  generalize fEq : Lean.Expr.const name [] = f
  have mapFold (f : Lean.Expr) :
      LeanBindings.substitute σ.reference (args.foldl Lean.Expr.app f) =
        (args.map (LeanBindings.substitute σ.reference)).foldl Lean.Expr.app
          (LeanBindings.substitute σ.reference f) := by
    induction args generalizing f with
    | nil => rfl
    | cons a as ih => exact ih (.app f a)
  subst f
  have eq : σ.apply = LeanBindings.substitute σ.reference := funext (σ.apply_eq)
  rw [eq]
  exact mapFold (.const name [])

theorem mapped_copy (same : sameTerm p.s p.s = true)
    (current : σ.apply original = p.s) :
    HEq (visit env conv exposure (app ``HybridWord.State.copy [original,d,s,n]) ctx p .body σ fs)
      (StructuralBody.bodyRetained env conv exposure ctx p
        (app ``HybridWord.State.copy [p.s,σ.apply d,σ.apply s,σ.apply n])) := by
  have sourceSame : σ.apply (app ``HybridWord.State.copy [original,d,s,n]) =
      app ``HybridWord.State.copy [p.s,σ.apply d,σ.apply s,σ.apply n] := by
    rw [substitute_app]
    simp only [List.map_cons,List.map_nil,current]
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have bodyBody : (Mode.body != Mode.body) = false := rfl
  have originalArgs : (app ``HybridWord.State.copy [original,d,s,n]).getAppArgs.toList = [original,d,s,n] := rfl
  have mappedArgs : (app ``HybridWord.State.copy [p.s,σ.apply d,σ.apply s,σ.apply n]).getAppArgs.toList =
      [p.s,σ.apply d,σ.apply s,σ.apply n] := rfl
  unfold StructuralBody.bodyRetained
  rw [visit,visit]
  simp [node,bodyValue,bodyBody,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
    ScalarEnvironment.arguments,ScalarEnvironment.below,Substitution.apply_eq,
    app,LeanBindings.substitute,Lean.Expr.getAppFn,Lean.Expr.constName?]
  simp only [Substitution.apply_eq] at current originalArgs mappedArgs
  simp only [app,List.foldl_cons,List.foldl_nil] at originalArgs mappedArgs
  simp only [originalArgs,mappedArgs,current,same,Bool.true_eq_false,ite_false,
    bind,Option.bind]
  have identityRef : Substitution.identity.reference = Lean.Expr.bvar := rfl
  simp only [identityRef,LeanBindings.substitute_id,same,Bool.true_eq_false,ite_false]
  cases hd : closedTerm (LeanBindings.substitute σ.reference d) <;>
    cases hs : closedTerm (LeanBindings.substitute σ.reference s) <;>
    cases hn : closedTerm (LeanBindings.substitute σ.reference n) <;>
    try simp only [hd,hs,hn,Option.bind_none,Option.bind_some]
  all_goals first | exact none_congr (env := env) (ctx := ctx) (p := p) (mode := .body) sourceSame | exact finish_congr sourceSame _ _

theorem substitute_branch (σ : Substitution) :
    σ.apply (Branch.source v d yes no) =
      Branch.source (σ.apply v) (σ.apply d) (σ.apply yes) (σ.apply no) := by
  cases σ <;> rfl

/-- Branches preserve the captured environment in both children. The two
recursive equalities are supplied by the source-structure induction. -/
theorem mapped_branch
    (left : HEq (visit env conv exposure yes ctx p .body σ fs)
      (StructuralBody.bodyRetained env conv exposure ctx p (σ.apply yes)))
    (right : HEq (visit env conv exposure no ctx p .body σ fs)
      (StructuralBody.bodyRetained env conv exposure ctx p (σ.apply no))) :
    HEq (visit env conv exposure (Branch.source v d yes no) ctx p .body σ fs)
      (StructuralBody.bodyRetained env conv exposure ctx p
        (Branch.source (σ.apply v) (σ.apply d) (σ.apply yes) (σ.apply no))) := by
  have leftEq := eq_of_heq left
  have rightEq := eq_of_heq right
  dsimp only [StructuralBody.bodyRetained] at leftEq rightEq
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have bodyStep : (Mode.body == Mode.step) = false := rfl
  conv => lhs; rw [visit]
  conv => rhs; unfold StructuralBody.bodyRetained; rw [visit]
  have identityApply (e : Lean.Expr) : Substitution.identity.apply e = e := rfl
  simp [node,bodyValue,bodyStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
    ScalarEnvironment.arguments,ScalarEnvironment.below,
    identityApply,
    Branch.source,Branch.nativeCondition,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,
    Lean.mkApp,Lean.mkAppB,Lean.Expr.getAppFn,Lean.Expr.constName?]
  have test : nonzeroValue (Branch.nativeCondition v) = some v := rfl
  have mappedTest : nonzeroValue (Branch.nativeCondition (σ.apply v)) =
      some (σ.apply v) := rfl
  simp only [Branch.nativeCondition,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at test mappedTest
  simp only [test,mappedTest,Option.bind_some,leftEq,rightEq]
  have scalarIdentity : ScalarEnvironment.parse env conv exposure ctx p (Substitution.identity.apply (σ.apply v)) =
      ScalarEnvironment.parse env conv exposure ctx p (σ.apply v) := rfl
  simp only [scalarIdentity]
  cases he : ScalarEnvironment.parse env conv exposure ctx p (σ.apply v) <;>
    cases ha : visit env conv exposure (σ.apply yes) ctx p .body .identity (fun _ => none) <;>
    cases hb : visit env conv exposure (σ.apply no) ctx p .body .identity (fun _ => none) <;>
    try simp only [he,ha,hb,Option.bind_none,Option.bind_some]
  all_goals first
    | exact none_congr (env := env) (ctx := ctx) (p := p) (mode := .body) (substitute_branch σ)
    | exact finish_congr (substitute_branch σ) _ _ _

theorem mapped_store (same : sameTerm p.s p.s = true)
    (current : σ.apply original = p.s) :
    HEq (visit env conv exposure (app ``HybridWord.State.write [original,a,j,e]) ctx p .body σ fs)
      (StructuralBody.bodyRetained env conv exposure ctx p
        (app ``HybridWord.State.write [p.s,σ.apply a,σ.apply j,σ.apply e])) := by
  have sourceSame : σ.apply (app ``HybridWord.State.write [original,a,j,e]) =
      app ``HybridWord.State.write [p.s,σ.apply a,σ.apply j,σ.apply e] := by
    rw [substitute_app]; simp only [List.map_cons,List.map_nil,current]
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have bodyBody : (Mode.body != Mode.body) = false := rfl
  have identityApply (e : Lean.Expr) : Substitution.identity.apply e = e := rfl
  conv => lhs; rw [visit]
  conv => rhs; unfold StructuralBody.bodyRetained; rw [visit]
  simp [node,bodyValue,bodyBody,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
    ScalarEnvironment.arguments,ScalarEnvironment.below,identityApply,
    app,Lean.Expr.getAppFn,Lean.Expr.constName?,current,same]
  have scalarIdentity (v : Lean.Expr) :
      ScalarEnvironment.parse env conv exposure ctx p (Substitution.identity.apply v) =
        ScalarEnvironment.parse env conv exposure ctx p v := rfl
  try simp only [scalarIdentity]
  cases ha : closedTerm (σ.apply a) <;>
    cases hj : ScalarEnvironment.parse env conv exposure ctx p (σ.apply j) <;>
    cases he : ScalarEnvironment.parse env conv exposure ctx p (σ.apply e) <;>
    try simp only [ha,hj,he,Option.bind_none,Option.bind_some]
  all_goals first
    | exact none_congr (env := env) (ctx := ctx) (p := p) (mode := .body) sourceSame
    | exact finish_congr sourceSame _ _ _

theorem mapped_assign (same : sameTerm p.s p.s = true) (form : Return.Form)
    (current : σ.apply original = p.s) :
    HEq (visit env conv exposure (form.source (app ``HybridWord.State.set [original,r,v]))
      ctx p .body σ fs)
      (StructuralBody.bodyRetained env conv exposure ctx p
        (form.source (app ``HybridWord.State.set [p.s,σ.apply r,σ.apply v]))) := by
  have updateSame : σ.apply (app ``HybridWord.State.set [original,r,v]) =
      app ``HybridWord.State.set [p.s,σ.apply r,σ.apply v] := by
    rw [substitute_app]; simp only [List.map_cons,List.map_nil,current]
  have sourceSame := (substitute_return σ form (app ``HybridWord.State.set [original,r,v])).trans
    (congrArg form.source updateSame)
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have bodyStep : (Mode.body == Mode.step) = false := rfl
  have identityApply (e : Lean.Expr) : Substitution.identity.apply e = e := rfl
  have originalArgs : (app ``HybridWord.State.set [original,r,v]).getAppArgs.toList = [original,r,v] := rfl
  have mappedArgs : (app ``HybridWord.State.set [p.s,σ.apply r,σ.apply v]).getAppArgs.toList =
      [p.s,σ.apply r,σ.apply v] := rfl
  have scalarIdentity (e : Lean.Expr) :
      ScalarEnvironment.parse env conv exposure ctx p (Substitution.identity.apply e) =
        ScalarEnvironment.parse env conv exposure ctx p e := rfl
  simp only [app,List.foldl_cons,List.foldl_nil] at originalArgs mappedArgs
  conv => lhs; rw [visit]
  conv => rhs; unfold StructuralBody.bodyRetained; rw [visit]
  cases form <;>
    simp [node,bodyValue,bodyStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      ScalarEnvironment.arguments,ScalarEnvironment.below,identityApply,
      Return.Form.source,Return.Form.nativeHeader,Return.nativePureInstance,
      Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
      app,Lean.Expr.getAppFn,Lean.Expr.constName?,current,same]
  all_goals simp only [app,List.foldl_cons,List.foldl_nil] at updateSame
  all_goals simp only [updateSame]
  all_goals cases test : sameTerm (app ``HybridWord.State.set [p.s,σ.apply r,σ.apply v]) p.s
  all_goals simp only [app,List.foldl_cons,List.foldl_nil] at test
  all_goals simp only [test,Bool.false_eq_true,ite_false,ite_true]
  all_goals try simp only [originalArgs,mappedArgs,current,same,Bool.true_eq_false,ite_false,scalarIdentity]
  all_goals
    cases hr : closedTerm (σ.apply r) <;>
      cases hv : ScalarEnvironment.parse env conv exposure ctx p (σ.apply v) <;>
      try simp only [hr,hv,Option.bind_none,Option.bind_some]
  all_goals first
    | exact none_congr (env := env) (ctx := ctx) (p := p) (mode := .body) sourceSame
    | exact finish_congr sourceSame _ _ _

theorem substitute_sequence (σ : Substitution) :
    σ.apply (sequenceSource first (.lam binder state next info)) =
      sequenceSource (σ.apply first) (.lam binder state ((under σ).apply next) info) := by
  cases σ <;> rfl

theorem mapped_sequence
    (firstEq : HEq (visit env conv exposure first ctx p .body σ fs)
      (StructuralBody.bodyRetained env conv exposure ctx p (σ.apply first)))
    (nextEq : HEq (visit env conv exposure next (stateType::ctx) {p.lift with s := .bvar 0}
      .body (under σ) (underFunctions fs))
      (StructuralBody.bodyRetained env conv exposure (stateType::ctx) {p.lift with s := .bvar 0}
        ((under σ).apply next))) :
    HEq (visit env conv exposure (sequenceSource first (.lam binder state next info)) ctx p .body σ fs)
      (StructuralBody.bodyRetained env conv exposure ctx p
        (sequenceSource (σ.apply first) (.lam binder state ((under σ).apply next) info))) := by
  have firstSame := eq_of_heq firstEq
  have nextSame := eq_of_heq nextEq
  dsimp only [StructuralBody.bodyRetained] at firstSame nextSame
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have bodyStep : (Mode.body == Mode.step) = false := rfl
  have identityApply (e : Lean.Expr) : Substitution.identity.apply e = e := rfl
  have stateApply : σ.apply state = state := by cases σ <;> rfl
  have ss : sameTerm state state = true :=
    sameTerm_complete (Represents.constant rfl) (Represents.constant rfl)
  have su : sameTerm state (.const ``PUnit [.succ .zero]) = false := rfl
  have st : translate state = some ⟨stateType,Represents.constant rfl⟩ := rfl
  have stMapped : (translate (σ.apply state)).unattach = some stateType := by rw [stateApply]; rfl
  have compatibleState : compatible env conv ctx state state = true :=
    compatible_same (Represents.constant rfl) (Represents.constant rfl) env conv ctx
  have underIdentity : under .identity = .identity := rfl
  have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
    funext n; cases n <;> rfl
  conv => lhs; rw [visit]
  conv => rhs; unfold StructuralBody.bodyRetained; rw [visit]
  simp [node,bodyValue,bodyStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
    ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,identityApply,stateApply,
    sequenceSource,bindHead,Lean.mkAppN,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
    Lean.Expr.getAppFn,Lean.Expr.constName?,ss,su,st,underIdentity,empty]
  simp only [List.map_append,List.map_cons,List.map_nil,Function.comp_apply,
    List.cons_append,List.nil_append,List.length_cons,List.length_nil,Nat.reduceAdd,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.unattach_some,
    stMapped,compatibleState,ite_true,Option.bind_some,firstSame,nextSame]
  have firstArg (a b : Lean.Expr) :
      ((ScalarEnvironment.arguments (sequenceSource a (.lam binder state b info)))[4]?).unattach = some a := rfl
  dsimp only [List.map,List.append,List.length,Function.comp_apply,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.unattach]
  try simp only [firstArg,Option.bind_some,firstSame,nextSame]
  change HEq ((some first).bind _) ((some (σ.apply first)).bind _)
  simp only [Option.bind_some,firstSame,nextSame]
  have stIdentity : (translate (Substitution.identity.apply state)).map Subtype.val = some stateType := rfl
  have lambdaSame : σ.apply (.lam binder state next info) =
      .lam binder state ((under σ).apply next) info := by cases σ <;> rfl
  simp only [stIdentity,Option.bind_some,underIdentity,lambdaSame]
  have nextIdentity :
      visit env conv exposure ((under σ).apply next) (stateType::ctx) {p.lift with s := .bvar 0}
        .body (under .identity) (fun _ => none) =
      visit env conv exposure ((under σ).apply next) (stateType::ctx) {p.lift with s := .bvar 0}
        .body .identity (fun _ => none) := rfl
  simp only [nextIdentity]
  cases ha : visit env conv exposure (σ.apply first) ctx p .body .identity (fun _ => none) <;>
    cases hb : visit env conv exposure ((under σ).apply next) (stateType::ctx)
      {p.lift with s := .bvar 0} .body .identity (fun _ => none) <;>
    try simp only [ha,hb,Option.bind_none,Option.bind_some]
  all_goals first
    | exact none_congr (env := env) (ctx := ctx) (p := p) (mode := .body) (substitute_sequence σ)
    | exact finish_congr (substitute_sequence σ) _ _ _

/-- A captured helper may read an array before continuing. Only the
continuation extends the scope; the read expression is checked in the current
captured scope, exactly as in the runtime traversal. -/
theorem substitute_bindValue (σ : Substitution) :
    σ.apply (bindValueSource first (.lam binder word next info)) =
      bindValueSource (σ.apply first) (.lam binder word ((under σ).apply next) info) := by
  cases σ <;> rfl

theorem mapped_bindValue
    (nextEq : HEq (visit env conv exposure next (wordType::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} .body (under σ) (underFunctions fs))
      (StructuralBody.bodyRetained env conv exposure (wordType::ctx)
        {p.lift with locals := .bvar 0::p.lift.locals} ((under σ).apply next))) :
    HEq (visit env conv exposure (bindValueSource first (.lam binder word next info)) ctx p .body σ fs)
      (StructuralBody.bodyRetained env conv exposure ctx p
        (bindValueSource (σ.apply first) (.lam binder word ((under σ).apply next) info))) := by
  have nextSame := eq_of_heq nextEq
  dsimp only [StructuralBody.bodyRetained] at nextSame
  have bodyValue : (Mode.body == Mode.value) = false := rfl
  have bodyStep : (Mode.body == Mode.step) = false := rfl
  have identityApply (e : Lean.Expr) : Substitution.identity.apply e = e := rfl
  have wordApply : σ.apply word = word := by cases σ <;> rfl
  have ws : sameTerm word state = false := rfl
  have ww : sameTerm word word = true := rfl
  have wu : sameTerm word (.const ``PUnit [.succ .zero]) = false := rfl
  have wt : translate word = some ⟨wordType,Represents.constant rfl⟩ := rfl
  have wtMapped : (translate (σ.apply word)).unattach = some wordType := by rw [wordApply]; rfl
  have compatibleWord : compatible env conv ctx word word = true :=
    compatible_same (Represents.constant rfl) (Represents.constant rfl) env conv ctx
  have underIdentity : under .identity = .identity := rfl
  have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
    funext n; cases n <;> rfl
  conv => lhs; rw [visit]
  conv => rhs; unfold StructuralBody.bodyRetained; rw [visit]
  simp [node,bodyValue,bodyStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
    ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,identityApply,wordApply,
    bindValueSource,bindHead,Lean.mkAppN,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
    Lean.Expr.getAppFn,Lean.Expr.constName?,ws,ww,wu,wt,underIdentity,empty]
  simp only [List.map_append,List.map_cons,List.map_nil,Function.comp_apply,
    List.cons_append,List.nil_append,List.length_cons,List.length_nil,Nat.reduceAdd,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.unattach_some,
    wtMapped,compatibleWord,ite_true,Option.bind_some,nextSame]
  dsimp only [List.map,List.append,List.length,Function.comp_apply,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.unattach]
  change HEq ((some first).bind _) ((some (σ.apply first)).bind _)
  simp only [Option.bind_some,nextSame]
  have lambdaSame : σ.apply (.lam binder word next info) =
      .lam binder word ((under σ).apply next) info := by cases σ <;> rfl
  have wtIdentity : (translate (Substitution.identity.apply word)).map Subtype.val = some wordType := rfl
  simp only [wtIdentity,Option.bind_some,underIdentity,lambdaSame]
  change HEq ((readStep env conv exposure ctx p (ScalarEnvironment.parse env conv exposure ctx p) (σ.apply first)).bind _)
    ((readStep env conv exposure ctx p (ScalarEnvironment.parse env conv exposure ctx p) (σ.apply first)).bind _)
  have nextIdentity : visit env conv exposure ((under σ).apply next) (wordType::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} .body (under .identity) (fun _ => none) =
      visit env conv exposure ((under σ).apply next) (wordType::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} .body .identity (fun _ => none) := rfl
  simp only [nextIdentity]
  cases ha : readStep env conv exposure ctx p (ScalarEnvironment.parse env conv exposure ctx p) (σ.apply first) <;>
    cases hb : visit env conv exposure ((under σ).apply next) (wordType::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} .body .identity (fun _ => none) <;>
    try simp only [wordApply,identityApply,wt,Option.map_some,underIdentity,nextSame,ha,hb,Option.bind]
  all_goals first
    | exact none_congr (env := env) (ctx := ctx) (p := p) (mode := .body) (substitute_bindValue σ)
    | exact finish_congr (substitute_bindValue σ) _ _ _

/-- Scalar lets in captured helpers extend the scalar scope rather than
instantiating and reparsing the original body. -/
theorem substitute_letValue (σ : Substitution) :
    σ.apply (letValueSource binder value next flag) =
      letValueSource binder (σ.apply value) ((under σ).apply next) flag := by
  cases σ <;> rfl

theorem mapped_letValue
    (nextEq : HEq (visit env conv exposure next (wordType::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} .body (under σ) (underFunctions fs))
      (StructuralBody.bodyRetained env conv exposure (wordType::ctx)
        {p.lift with locals := .bvar 0::p.lift.locals} ((under σ).apply next))) :
    HEq (visit env conv exposure (letValueSource binder value next flag) ctx p .body σ fs)
      (StructuralBody.bodyRetained env conv exposure ctx p
        (letValueSource binder (σ.apply value) ((under σ).apply next) flag)) := by
  cases σ with
  | identity =>
    let σ := Substitution.identity
    have nextSame := eq_of_heq nextEq
    dsimp only [StructuralBody.bodyRetained] at nextSame
    have bodyValue : (Mode.body == Mode.value) = false := rfl
    have bodyStep : (Mode.body == Mode.step) = false := rfl
    have identityApply (e : Lean.Expr) : Substitution.identity.apply e = e := rfl
    have wordApply : σ.apply word = word := by cases σ <;> rfl
    have ws : sameTerm word state = false := rfl
    have wt : translate word = some ⟨wordType,Represents.constant rfl⟩ := rfl
    have compatibleWord : compatible env conv ctx word word = true :=
      compatible_same (Represents.constant rfl) (Represents.constant rfl) env conv ctx
    have underIdentity : under .identity = .identity := rfl
    have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
      funext n; cases n <;> rfl
    conv => lhs; rw [visit]
    conv => rhs; unfold StructuralBody.bodyRetained; rw [visit]
    simp only [node,bodyValue,bodyStep,letParts,letValueSource,identityApply,wordApply,
      ws,compatibleWord,wt,underIdentity,empty,Bool.false_eq_true,Bool.not_false,
      Bool.true_and,Bool.false_and,ite_true,ite_false,Option.bind_some,Option.map_some]
    change HEq ((ScalarEnvironment.parse env conv exposure ctx p (σ.apply value)).bind (fun a =>
        (visit env conv exposure next (wordType::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
          .body (under σ) (underFunctions fs)).bind _))
      ((ScalarEnvironment.parse env conv exposure ctx p (σ.apply value)).bind (fun a =>
        (visit env conv exposure ((under σ).apply next) (wordType::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
          .body .identity (fun _ => none)).bind _))
    rw [nextSame]
    cases ha : ScalarEnvironment.parse env conv exposure ctx p (σ.apply value) <;>
      cases hb : visit env conv exposure ((under σ).apply next) (wordType::ctx)
        {p.lift with locals := .bvar 0::p.lift.locals} .body .identity (fun _ => none) <;>
      try simp only [nextSame,ha,hb,Option.bind_none,Option.bind_some,bind,pure,Option.pure_def,Option.bind_fun_some]
    all_goals first
      | exact none_congr (env := env) (ctx := ctx) (p := p) (mode := .body) (substitute_letValue σ)
      | exact finish_congr (substitute_letValue σ) _ _ _
  | bindings reference =>
    let σ := Substitution.bindings reference
    have nextSame := eq_of_heq nextEq
    dsimp only [StructuralBody.bodyRetained] at nextSame
    have bodyValue : (Mode.body == Mode.value) = false := rfl
    have bodyStep : (Mode.body == Mode.step) = false := rfl
    have identityApply (e : Lean.Expr) : Substitution.identity.apply e = e := rfl
    have wordApply : σ.apply word = word := by cases σ <;> rfl
    have ws : sameTerm word state = false := rfl
    have wt : translate word = some ⟨wordType,Represents.constant rfl⟩ := rfl
    have compatibleWord : compatible env conv ctx word word = true :=
      compatible_same (Represents.constant rfl) (Represents.constant rfl) env conv ctx
    have underIdentity : under .identity = .identity := rfl
    have empty : underFunctions (fun _ => (none : Option (Continuation env))) = (fun _ => none) := by
      funext n; cases n <;> rfl
    conv => lhs; rw [visit]
    conv => rhs; unfold StructuralBody.bodyRetained; rw [visit]
    simp only [node,bodyValue,bodyStep,letParts,letValueSource,identityApply,wordApply,
      ws,compatibleWord,wt,underIdentity,empty,Bool.false_eq_true,Bool.not_false,
      Bool.true_and,Bool.false_and,ite_true,ite_false,Option.bind_some,Option.map_some]
    change HEq ((ScalarEnvironment.parse env conv exposure ctx p (σ.apply value)).bind (fun a =>
        (visit env conv exposure next (wordType::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
          .body (under σ) (underFunctions fs)).bind _))
      ((ScalarEnvironment.parse env conv exposure ctx p (σ.apply value)).bind (fun a =>
        (visit env conv exposure ((under σ).apply next) (wordType::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
          .body .identity (fun _ => none)).bind _))
    rw [nextSame]
    cases ha : ScalarEnvironment.parse env conv exposure ctx p (σ.apply value) <;>
      cases hb : visit env conv exposure ((under σ).apply next) (wordType::ctx)
        {p.lift with locals := .bvar 0::p.lift.locals} .body .identity (fun _ => none) <;>
      try simp only [nextSame,ha,hb,Option.bind_none,Option.bind_some,bind,pure,Option.pure_def,Option.bind_fun_some]
    all_goals first
      | exact none_congr (env := env) (ctx := ctx) (p := p) (mode := .body) (substitute_letValue σ)
      | exact finish_congr (substitute_letValue σ) _ _ _

/- The remaining structured constructors are connected below this judgment
as their binder environments are accounted for. This is a dispatch-stability
condition, not a replacement for ScopedSyntax or the public source language. -/
inductive HeadForm : Substitution → Inputs → Lean.Expr → Prop where
  | returns (tag : Return.Form) (current : σ.apply st = p.s) : HeadForm σ p (tag.source st)
  | copy (current : σ.apply st = p.s) :
      HeadForm σ p (app ``HybridWord.State.copy [st,d,s,n])
  | store (current : σ.apply st = p.s) :
      HeadForm σ p (app ``HybridWord.State.write [st,a,j,e])
  | assign (tag : Return.Form) (current : σ.apply st = p.s) :
      HeadForm σ p (tag.source (app ``HybridWord.State.set [st,r,v]))
  | branch (yes : HeadForm σ p a) (no : HeadForm σ p b) :
      HeadForm σ p (Branch.source v d a b)
  | letValue (next : HeadForm (under σ) {p.lift with locals := .bvar 0::p.lift.locals} b)
      (binder : Lean.Name) (flag : Bool) :
      HeadForm σ p (letValueSource binder v b flag)
  | bindValue (next : HeadForm (under σ) {p.lift with locals := .bvar 0::p.lift.locals} b)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      HeadForm σ p (bindValueSource a (.lam binder word b info))
  | sequence (first : HeadForm σ p a)
      (next : HeadForm (under σ) {p.lift with s := .bvar 0} b)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      HeadForm σ p (sequenceSource a (.lam binder state b info))

private theorem body_congr (same : source = target) :
    HEq (StructuralBody.bodyRetained env conv exposure ctx p source)
      (StructuralBody.bodyRetained env conv exposure ctx p target) := by cases same; rfl

private theorem sameTerm_lift_self {e : Lean.Expr} (self : sameTerm e e = true) :
    sameTerm (LeanBindings.rename Nat.succ e) (LeanBindings.rename Nat.succ e) = true := by
  unfold sameTerm at self
  cases h : translate e with
  | none => simp [h] at self
  | some core => exact sameTerm_complete core.property.lift core.property.lift

/-- Source-constructor induction connects the captured-environment traversal
to the existing structured parser. The equivalence holds even when parsing
fails, so it cannot conceal a success premise in the syntax judgment. -/
theorem HeadForm.parser_congr (form : HeadForm σ p source) (self : sameTerm p.s p.s = true) :
    HEq (visit env conv exposure source ctx p .body σ fs)
      (StructuralBody.bodyRetained env conv exposure ctx p (σ.apply source)) := by
  revert self
  induction form generalizing ctx fs with
  | returns tag current =>
    intro self
    exact (mapped_return self tag current).trans (body_congr
      ((substitute_return _ tag _).trans (congrArg tag.source current)).symm)
  | copy current =>
    intro self
    apply (mapped_copy self current).trans
    apply body_congr
    symm
    rw [substitute_app]
    simp only [List.map_cons,List.map_nil,current]
  | store current =>
    intro self
    apply (mapped_store self current).trans
    apply body_congr
    symm
    rw [substitute_app]
    simp only [List.map_cons,List.map_nil,current]
  | assign tag current =>
    intro self
    apply (mapped_assign self tag current).trans
    apply body_congr
    symm
    rw [substitute_return,substitute_app]
    simp only [List.map_cons,List.map_nil,current]
  | branch _ _ yes no =>
    intro self
    exact (mapped_branch (yes self) (no self)).trans (body_congr (substitute_branch _).symm)
  | letValue _ binder flag next =>
    intro self
    exact (mapped_letValue (binder := binder) (flag := flag) (next (sameTerm_lift_self self))).trans
      (body_congr (substitute_letValue _).symm)
  | bindValue _ binder info next =>
    intro self
    exact (mapped_bindValue (binder := binder) (info := info) (next (sameTerm_lift_self self))).trans
      (body_congr (substitute_bindValue _).symm)
  | sequence _ _ binder info first next =>
    intro self
    exact (mapped_sequence (binder := binder) (info := info) (first self) (next rfl)).trans
      (body_congr (substitute_sequence _).symm)


end IRComparison.WordFrontend.StructuralSyntax
