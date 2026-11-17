import IRComparison.Frontend.WordHelperCompleteness
import IRComparison.Frontend.WordScopedSyntax
import Lean4Lean.Verify.Expr

/-! Lexical helper descriptions for the source judgment. These are binding
contexts used only by the completeness proof, not a new runtime IR or input
language. Their interpretation is the existing continuation environment. -/
namespace IRComparison.WordFrontend.FunctionSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate StructuralBody StructuralSyntax
set_option maxHeartbeats 1500000

mutual
inductive Scope where
  | empty
  | push (value : Option Closure) (tail : Scope)
inductive Closure where
  | captured (depth : Nat) (bindings : Substitution) (arity : Nat)
      (body : Lean.Expr) (functions : Scope)
end

mutual
def Scope.runtime (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (scope : Scope) : Continuations env :=
  match scope with
  | .empty => fun _ => none
  | .push none tail => letContinuations (tail.runtime env conv exposure ) none
  | .push (some value) tail => letContinuations (tail.runtime env conv exposure )
      (some (value.runtime env conv exposure ))
def Closure.runtime (env : VEnv) (conv : Conversion env) (exposure : Exposure env)
    (closure : Closure) : Continuation env :=
  match closure with
  | .captured depth bindings arity body functions =>
    ⟨fun ctx p mode args => do
      if args.length != arity then none else do
        let substitution := closureSubstitution depth ctx.length bindings args
        let fs := closureFunctions (functions.runtime env conv exposure ) args.length
        let parsed ← visit env conv exposure body ctx p mode substitution fs 
        return ⟨substitution.apply body,parsed⟩⟩
end

def Scope.lookup : Scope → Nat → Option Closure
  | .empty,_ => none
  | .push value _,0 => value
  | .push _ tail,n+1 => tail.lookup n

def Scope.parameters : Nat → Scope → Scope
  | 0,scope => scope
  | n+1,scope => .push none (scope.parameters n)

theorem Scope.runtime_lookup (scope : Scope) (n : Nat) :
    scope.runtime env conv exposure  n = (scope.lookup n).map (fun c => c.runtime env conv exposure ) := by
  induction n generalizing scope with
  | zero => cases scope with
    | empty => rfl
    | push value tail => cases value <;> rfl
  | succ n ih => cases scope with
    | empty => rfl
    | push value tail => cases value <;> exact ih tail

theorem Scope.runtime_parameters (scope : Scope) (n : Nat) :
    (scope.parameters n).runtime env conv exposure  = closureFunctions (scope.runtime env conv exposure ) n := by
  funext k
  induction n generalizing k with
  | zero => simp [Scope.parameters,closureFunctions]
  | succ n ih =>
    cases k with
    | zero => simp [Scope.parameters,Scope.runtime,letContinuations,closureFunctions]
    | succ k =>
      simpa only [Scope.parameters,Scope.runtime,letContinuations,Option.map_none,
        closureFunctions,Nat.succ_lt_succ_iff,Nat.succ_sub_succ_eq_sub] using ih k

/-- Construct the runtime function binding from its source lambda chain. -/
theorem capture_runtime {body : Lean.Expr} (scope : Scope) (value : Child raw)
    (shape : LambdaSource value.val domains body) :
    makeContinuation (fun ctx p mode bindings functions child =>
      visit env conv exposure child.val ctx p mode bindings functions)
      depth σ (scope.runtime env conv exposure ) value =
      some ((Closure.captured depth σ domains.length body scope).runtime env conv exposure ) := by
  obtain ⟨child,same,found⟩ := shape.capture
    (fun ctx p mode bindings functions child => visit env conv exposure child.val ctx p mode bindings functions)
    (captureDepth := depth) (σ := σ) (fs := scope.runtime env conv exposure )
  subst body
  exact found

/-- Function definitions and aliases have the same lexical binding rule. -/
inductive BindingValue : Scope → Nat → Substitution → Lean.Expr → Closure → Prop where
  | lambda {body : Lean.Expr} (shape : LambdaSource value domains body) :
      BindingValue scope depth σ value (.captured depth σ domains.length body scope)
  | reuse (bound : scope.lookup index = some closure) :
      BindingValue scope depth σ (.bvar index) closure

theorem BindingValue.construct (value : Child raw)
    (binding : BindingValue scope depth σ value.val closure) :
    makeContinuation (fun ctx p mode bindings functions child =>
      visit env conv exposure child.val ctx p mode bindings functions)
      depth σ (scope.runtime env conv exposure ) value =
      some (closure.runtime env conv exposure ) := by
  generalize sourceSame : value.val = source at binding
  cases binding with
  | lambda shape => exact capture_runtime scope value (sourceSame.symm ▸ shape)
  | reuse bound =>
    apply makeContinuation_cached sourceSame
    rw [Scope.runtime_lookup,bound]
    rfl

/-- Reopening a closure at its capture depth introduces no renaming. -/
theorem closureSubstitution_at_capture (depth : Nat) (σ : Substitution) (value : Lean.Expr) :
    (closureSubstitution depth depth σ []).apply value = σ.apply value := by
  rw [Substitution.apply_eq,Substitution.apply_eq]
  congr 1
  funext n
  simp only [closureSubstitution,Substitution.reference,closureReference,List.reverse_nil,
    List.getElem?_nil,List.length_nil,Nat.sub_self,Nat.sub_zero,Nat.add_zero]
  exact LeanBindings.rename_id _

/-- Only lexical depth, not run-time iteration count, shifts a captured value. -/
theorem closureSubstitution_shift_empty (bound : capture ≤ target) (shift : Nat)
    (σ : Substitution) (value : Lean.Expr) :
    (closureSubstitution capture (target+shift) σ []).apply value =
      LeanBindings.rename (·+shift) ((closureSubstitution capture target σ []).apply value) := by
  simp only [Substitution.apply,closureSubstitution,LeanBindings.rename_substitute]
  congr 1
  funext n
  simp only [closureReference,List.reverse_nil,List.getElem?_nil,List.length_nil,Nat.sub_zero,
    LeanBindings.rename_comp]
  congr 1
  funext k
  simp only [Function.comp_apply]
  omega

/-- Eliminating one retained scalar slot commutes with reopening an arbitrary
closure body. Captured variables lose exactly that slot; actual arguments
are instantiated in their existing order. This equation is independent of
the body's commands and does not assume that parsing succeeds. -/
theorem closureSubstitution_instantiate (bound : capture ≤ target)
    (σ : Substitution) (args : List Lean.Expr) (value body : Lean.Expr) :
    LeanBindings.instantiate value
      ((closureSubstitution capture (target+1) σ args).apply body) =
      (closureSubstitution capture target σ
        (args.map (LeanBindings.instantiate value))).apply body := by
  simp only [Substitution.apply,closureSubstitution,LeanBindings.instantiate,
    LeanBindings.substitute_comp]
  congr 1
  funext n
  simp only [closureReference,← List.map_reverse,List.getElem?_map,List.length_map]
  cases found : args.reverse[n]? with
  | some argument => rfl
  | none =>
    simp only [found,Option.map_none,LeanBindings.substitute_rename]
    rw [← LeanBindings.substitute_bvars]
    congr 1
    funext k
    have shifted : k + (target+1-capture) = (k + (target-capture))+1 := by omega
    simp only [Function.comp_apply,shifted]

/-- The scalar argument bound by letValue can be substituted back without
changing the previously saved arguments, later arguments or captured scope.
The same equation applies to State/read bindings anywhere in the body. -/
theorem closureSubstitution_retain_actual (bound : capture ≤ target)
    (σ : Substitution) (saved rest : List Lean.Expr) (value body : Lean.Expr) :
    LeanBindings.instantiate value
      ((closureSubstitution capture (target+1) σ
        ((saved.map (LeanBindings.rename Nat.succ) ++ [.bvar 0]) ++
          rest.map (LeanBindings.rename Nat.succ))).apply body) =
      (closureSubstitution capture target σ (saved ++ value::rest)).apply body := by
  rw [closureSubstitution_instantiate bound]
  have cancel (e : Lean.Expr) :
      LeanBindings.instantiate value (LeanBindings.rename Nat.succ e) = e := by
    simpa only [LeanBindings.instantiate,LeanBindings.substitute_rename,Function.comp_def]
      using LeanBindings.substitute_id e
  simp only [List.map_append,List.map_map,List.map_cons,List.map_nil,
    LeanBindings.instantiate_zero,Function.comp_def,cancel,List.map_id,
    List.append_assoc,List.singleton_append]
  simp

/-- Independent lexical correspondence between the existing closure record
and its source function value. No generated code or successful check occurs
here. The original LambdaSource is retained only as a proposition. -/
def Closure.SourceAt : Closure → Nat → Lean.Expr → Prop
  | .captured capture σ arity body functions,target,source =>
    capture ≤ target ∧ ∃ value domains, LambdaSource value domains body ∧
      domains.length = arity ∧ source = (closureSubstitution capture target σ []).apply value

/-- The two existing lexical environments describe the same function values.
This is a scope invariant, not another source language or parsing judgment. -/
def Scope.Coherent (scope : Scope) (depth : Nat) (σ : Substitution) : Prop :=
  ∀ index closure, scope.lookup index = some closure → closure.SourceAt depth (σ.reference index)

theorem Scope.coherent_empty (depth : Nat) (σ : Substitution) : Scope.Coherent .empty depth σ := by
  intro index closure found
  cases found

theorem Closure.SourceAt.shift {closure : Closure} (value : closure.SourceAt depth source) (amount : Nat) :
    closure.SourceAt (depth+amount) (LeanBindings.rename (·+amount) source) := by
  cases closure with
  | captured capture σ arity body functions =>
    obtain ⟨bound,value,domains,shape,length,same⟩ := value
    exact ⟨by omega,value,domains,shape,length,by rw [same,closureSubstitution_shift_empty bound]⟩

/-- Source correspondence for a freshly captured lambda or a reused helper
follows from the binding rule and the existing scope invariant. -/
theorem BindingValue.sourceAt (binding : BindingValue scope depth σ value closure)
    (coherent : scope.Coherent depth σ) : closure.SourceAt depth (σ.apply value) := by
  cases binding with
  | lambda shape => exact ⟨Nat.le_refl _,_,_,shape,rfl,(closureSubstitution_at_capture _ _ _).symm⟩
  | reuse found =>
    have h := coherent _ _ found
    simpa only [Substitution.apply_eq,LeanBindings.substitute] using h

/-- A function let extends both environments together. Aliases use the same
proof as lambda definitions; no call-site capture equation is added. -/
theorem Scope.Coherent.functionLet (coherent : scope.Coherent depth σ)
    (binding : BindingValue scope depth σ value closure) :
    (Scope.push (some closure) scope).Coherent depth (letSubstitution σ value) := by
  intro index foundClosure found
  cases index with
  | zero =>
    have same : closure = foundClosure := Option.some.inj found
    subst foundClosure
    exact binding.sourceAt coherent
  | succ index => exact coherent index foundClosure found

/-- Scalar and State bindings preserve captured functions by one lexical
shift. This also supplies each binder in a structured loop continuation. -/
theorem Scope.Coherent.under (coherent : scope.Coherent depth σ) :
    (Scope.push none scope).Coherent (depth+1) (StructuralBody.under σ) := by
  intro index closure found
  cases index with
  | zero => cases found
  | succ index =>
    have value := (coherent index closure found).shift 1
    simpa only [under_reference,LeanBindings.underSubst] using value

/-- Parameter slots shadow helper names; the remaining scope is unchanged. -/
theorem Scope.lookup_parameters (scope : Scope) (count index : Nat) :
    (scope.parameters count).lookup index =
      if index < count then none else scope.lookup (index-count) := by
  induction count generalizing index with
  | zero => simp [Scope.parameters]
  | succ count ih =>
    cases index with
    | zero => simp [Scope.parameters,Scope.lookup]
    | succ index => simpa [Scope.parameters,Scope.lookup] using ih index

/-- Applying actual arguments preserves the capture invariant for any arity.
Arguments shadow names; surviving helper values are shifted by lexical depth. -/
theorem Scope.Coherent.applyArguments {scope : Scope} {capture target : Nat}
    (coherent : scope.Coherent capture σ)
    (bound : capture ≤ target) (args : List Lean.Expr) :
    (scope.parameters args.length).Coherent target (closureSubstitution capture target σ args) := by
  intro index closure found
  rw [Scope.lookup_parameters] at found
  split at found
  · cases found
  · rename_i outside
    have value := (coherent _ _ found).shift (target-capture)
    have missing : args.reverse[index]? = none := List.getElem?_eq_none (by simpa using Nat.le_of_not_gt outside)
    simpa only [Nat.add_sub_of_le bound,closureSubstitution,Substitution.reference,
      closureReference,missing] using value

/-- Substitution distributes over an application spine once, independently
of argument count and of the parser's representation of applications. -/
theorem substitution_applications (σ : Substitution) (args : List Lean.Expr) (head : Lean.Expr) :
    σ.apply (args.foldl Lean.Expr.app head) =
      (args.map σ.apply).foldl Lean.Expr.app (σ.apply head) := by
  induction args generalizing head with
  | nil => rfl
  | cons arg args ih =>
    simp only [List.foldl_cons,List.map_cons,ih]
    cases σ <;> rfl

theorem substitute_annotated_let (σ : Substitution) (annotation : WordBinder.Annotation) :
    σ.apply (WordBinder.letSource annotation binder value next flag) =
      WordBinder.letSource annotation binder (σ.apply value) ((under σ).apply next) flag := by
  cases σ with
  | identity => rfl
  | bindings substitution =>
    simp only [WordBinder.letSource,Substitution.apply,under,LeanBindings.substitute,
      WordBinder.Annotation.substitute_native]

/-- A closure's arguments occupy the innermost positions in reverse order.
Appending an argument adds exactly one binder, independently of captures. -/
theorem closureReference_append (depth target : Nat) (σ : Substitution)
    (args : List Lean.Expr) (argument : Lean.Expr) :
    closureReference depth target σ (args ++ [argument]) =
      fun | 0 => argument | n+1 => closureReference depth target σ args n := by
  funext n
  cases n with
  | zero => simp [closureReference,List.reverse_append]
  | succ n =>
    simp only [closureReference,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.cons_append,List.getElem?_cons_succ,List.length_append,List.length_singleton]
    split
    · rfl
    · congr 2
      omega

/-- Extend the captured substitution by one actual argument. The open body
uses the same existing environment, with its newest binder retained. -/
theorem closureSubstitution_append (depth target : Nat) (σ : Substitution)
    (args : List Lean.Expr) (argument body : Lean.Expr) :
    (closureSubstitution depth target σ (args ++ [argument])).apply body =
      LeanBindings.instantiate argument
        ((under (closureSubstitution depth target σ args)).apply body) := by
  rw [Substitution.apply_eq,Substitution.apply_eq,under_reference]
  simp only [closureSubstitution,Substitution.reference,closureReference_append,
    LeanBindings.instantiate,LeanBindings.substitute_comp]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [LeanBindings.underSubst,LeanBindings.substitute_rename]
    exact (LeanBindings.substitute_id _).symm

/-- The same binder equation transports representation evidence for a call.
Neither a parser result nor a target certificate is an assumption. -/
theorem closureSubstitution_append_represents {body : Lean.Expr}
    (bodyRep : Represents ((under (closureSubstitution depth target σ args)).apply body) core)
    (argumentRep : Represents argument argumentCore) :
    Represents ((closureSubstitution depth target σ (args ++ [argument])).apply body)
      (core.inst argumentCore) := by
  rw [closureSubstitution_append]
  exact bodyRep.instantiate argumentRep

/-- Scope of the substituted function and actuals suffices for its body.
The same lambda-spine induction used for representations handles all arities. -/
theorem lambdaSource_apply_scoped {body : Lean.Expr}
    (shape : LambdaSource value domains body)
    (scope_ok : LeanScalar.wellScoped bound
      ((closureSubstitution depth target σ done).apply value) = true)
    (arguments : ∀ a ∈ actuals, LeanScalar.wellScoped bound a = true)
    (length : actuals.length = domains.length) :
    LeanScalar.wellScoped bound
      ((closureSubstitution depth target σ (done ++ actuals)).apply body) = true := by
  have instantiateScoped (argument inner : Lean.Expr)
      (a : LeanScalar.wellScoped bound argument = true)
      (b : LeanScalar.wellScoped (bound+1) inner = true) :
      LeanScalar.wellScoped bound (LeanBindings.instantiate argument inner) = true := by
    apply LeanBindings.substitute_wellScoped inner (bound+1) bound b
    intro n hn
    cases n with
    | zero => exact a
    | succ n => simpa only [LeanScalar.wellScoped,decide_eq_true_eq] using (show n < bound by omega)
  induction shape generalizing done actuals with
  | @last name ty body info notLambda =>
    cases actuals with
    | nil => simp at length
    | cons a rest =>
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using length)
      subst rest
      change LeanScalar.wellScoped bound (.lam name _ _ info) = true at scope_ok
      rw [closureSubstitution_append]
      exact instantiateScoped _ _ (arguments _ (by simp)) (Bool.and_eq_true_iff.mp scope_ok).2
  | @next name ty inner info domains body tail ih =>
    cases actuals with
    | nil => simp at length
    | cons a rest =>
      change LeanScalar.wellScoped bound (.lam name _ _ info) = true at scope_ok
      have applied : LeanScalar.wellScoped bound
          ((closureSubstitution depth target σ (done ++ [a])).apply inner) = true := by
        rw [closureSubstitution_append]
        exact instantiateScoped _ _ (arguments _ (by simp)) (Bool.and_eq_true_iff.mp scope_ok).2
      simpa only [List.append_assoc,List.singleton_append] using ih applied
        (fun x hx => arguments x (by simp [hx])) (by simpa using length)

/-- Apply a whole lambda spine to represented actual arguments. The closure
may already contain arguments and arbitrary captured substitutions. This is
one induction on the existing lambda syntax, not one proof per call arity. -/
theorem lambdaSource_apply_represents {body : Lean.Expr}
    (shape : LambdaSource value domains body)
    (arguments : List.Forall₂ Represents actuals cores)
    (length : actuals.length = domains.length)
    (represented : Represents ((closureSubstitution depth target σ done).apply value) functionCore) :
    Represents ((closureSubstitution depth target σ (done ++ actuals)).apply body)
      (cores.foldl LeanTypeReduction.applyReduced functionCore) := by
  induction shape generalizing done actuals cores functionCore with
  | @last name ty body info notLambda =>
    cases arguments with
    | nil => simp at length
    | @cons a ac rest cs ar restRep =>
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using length)
      subst rest
      cases restRep
      change Represents (.lam name _ _ info) functionCore at represented
      cases represented with
      | lam typeRep bodyRep =>
        exact closureSubstitution_append_represents bodyRep ar
  | @next name ty inner info domains body tail ih =>
    cases arguments with
    | nil => simp at length
    | @cons a ac rest cs ar restRep =>
      change Represents (.lam name _ _ info) functionCore at represented
      cases represented with
      | lam typeRep bodyRep =>
        have applied := closureSubstitution_append_represents bodyRep ar
        have result := ih restRep (by simpa using length) applied
        simpa only [List.foldl_cons,List.append_assoc,List.singleton_append] using result

/-- Both source-side representations of an arbitrary-arity closure call.
The sole enclosing shape condition identifies the function and actuals;
post-substitution correspondence follows from the lambda-spine induction. -/
theorem closureCall_representations {body : Lean.Expr}
    (shape : LambdaSource value domains body)
    (arguments : List.Forall₂ Represents actuals cores)
    (length : actuals.length = domains.length)
    (functionRep : Represents ((closureSubstitution depth target σ []).apply value) functionCore)
    (callShape : source = actuals.foldl Lean.Expr.app
      ((closureSubstitution depth target σ []).apply value)) :
    Represents ((closureSubstitution depth target σ actuals).apply body)
      (cores.foldl LeanTypeReduction.applyReduced functionCore) ∧
      Represents source (applications functionCore cores) := by
  constructor
  · simpa only [List.nil_append] using
      lambdaSource_apply_represents shape arguments length functionRep
  · rw [callShape]
    exact app_represents functionRep arguments

/-- The actual Lean application-array accessor reconstructs its source.
Reuse lean4lean's verified array/list connection rather than assume a
call-site equation or add a second application parser. -/
theorem application_spine (raw : Lean.Expr) :
    raw.getAppArgs.toList.foldl Lean.Expr.app raw.getAppFn = raw := by
  have spine (raw : Lean.Expr) (tail : List Lean.Expr) :
      (raw.getAppArgsList tail).foldl Lean.Expr.app raw.getAppFn =
        tail.foldl Lean.Expr.app raw := by
    induction raw using Lean.Expr.recOn generalizing tail <;>
      simp only [Lean.Expr.getAppArgsList,Lean.Expr.getAppFn]
    rename_i fn argument ih other
    simpa only [List.foldl_cons] using ih (argument::tail)
  rw [Lean.Expr.getAppArgs_toList]
  exact spine raw []

/-- Scope of the actual application decomposes into its head and arguments.
It uses the same application spine as the executable frontend. -/
theorem application_spine_scoped (raw : Lean.Expr) (σ : Substitution)
    (scope_ok : LeanScalar.wellScoped bound (σ.apply raw) = true) :
    LeanScalar.wellScoped bound (σ.apply raw.getAppFn) = true ∧
      ∀ a ∈ raw.getAppArgs.toList.map σ.apply, LeanScalar.wellScoped bound a = true := by
  have folded (args : List Lean.Expr) (head : Lean.Expr)
      (h : LeanScalar.wellScoped bound (args.foldl Lean.Expr.app head) = true) :
      LeanScalar.wellScoped bound head = true ∧ ∀ a ∈ args, LeanScalar.wellScoped bound a = true := by
    induction args generalizing head with
    | nil => exact ⟨h,by simp⟩
    | cons a rest ih =>
      obtain ⟨ha,hr⟩ := ih (.app head a) h
      obtain ⟨headScope,argScope⟩ := Bool.and_eq_true_iff.mp ha
      exact ⟨headScope,by intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact argScope; exact hr x hx⟩
  apply folded
  rw [← substitution_applications,application_spine]
  exact scope_ok

/-- Call-site correspondence follows from lexical coherence. The original
captured lambda and its substitution equation are obtained from the scope;
clients provide only the raw application spine and representations of its
immediate subexpressions. -/
theorem BindingValue.call_representations {body : Lean.Expr} {actuals : List Lean.Expr}
    (binding : BindingValue scope target σ head (.captured capture captured arity body functions))
    (coherent : scope.Coherent target σ)
    (spine : raw = actuals.foldl Lean.Expr.app head)
    (arguments : List.Forall₂ Represents (actuals.map σ.apply) cores)
    (length : actuals.length = arity)
    (headRep : Represents (σ.apply head) functionCore) :
    Represents ((closureSubstitution capture target captured (actuals.map σ.apply)).apply body)
      (cores.foldl LeanTypeReduction.applyReduced functionCore) ∧
      Represents (σ.apply raw) (applications functionCore cores) := by
  obtain ⟨bound,value,domains,shape,arityEq,headEq⟩ := binding.sourceAt coherent
  apply closureCall_representations shape arguments
    (by simpa only [List.length_map,arityEq] using length)
  · simpa only [← headEq] using headRep
  · rw [spine,substitution_applications,headEq]

/-- A binding is a lambda spine or an alias, so the call head and singleton
argument list are derived from the binding, rather than restated by clients. -/
theorem BindingValue.application_parts (binding : BindingValue scope depth σ value closure)
    (argument : Lean.Expr) :
    value.getAppFn = value ∧ (Lean.Expr.app value argument).getAppArgs.toList = [argument] := by
  cases binding with
  | lambda shape => cases shape <;> exact ⟨rfl,rfl⟩
  | reuse found => exact ⟨rfl,rfl⟩

/-- Removing a retained function binder is ordinary capture-avoiding
substitution, also when surrounding scalar/function bindings are captured. -/
theorem letSubstitution_apply (σ : Substitution) (value body : Lean.Expr) :
    (letSubstitution σ value).apply body =
      LeanBindings.instantiate (σ.apply value) ((under σ).apply body) := by
  rw [Substitution.apply_eq,Substitution.apply_eq (under σ),under_reference]
  simp only [LeanBindings.instantiate,LeanBindings.substitute_comp]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [letSubstitution,Substitution.reference,LeanBindings.underSubst,
      LeanBindings.substitute_rename]
    exact (LeanBindings.substitute_id _).symm

/-- Build both enclosing representations from the three source subterms.
This proof is shared by ordinary bodies and ForInStep-valued loop bodies. -/
theorem let_representations {sourceBody functionValue type : VExpr}
    (typeRep : Represents (σ.apply ty) type)
    (valueRep : Represents (σ.apply value) functionValue)
    (bodyRep : Represents ((under σ).apply next) sourceBody)
    (binder : Lean.Name) (flag : Bool) :
    Represents ((letSubstitution σ value).apply next) (sourceBody.inst functionValue) ∧
      Represents (σ.apply (.letE binder ty value next flag))
        (.app (.lam type sourceBody) functionValue) := by
  constructor
  · rw [letSubstitution_apply]
    exact bodyRep.instantiate valueRep
  · have shape : σ.apply (.letE binder ty value next flag) =
        .letE binder (σ.apply ty) (σ.apply value) ((under σ).apply next) flag := by
      cases σ <;> rfl
    rw [shape]
    exact .letE typeRep valueRep bodyRep

/-- Instantiation crosses a static lambda telescope without changing its
parameter annotations. The index moves once for each remaining binder. -/
private theorem instantiate_lambdas (domains : List VExpr)
    (closed : ∀ d ∈ domains, d.ClosedN 0) (body argument : VExpr) (index : Nat) :
    (domains.foldr VExpr.lam body).inst argument index =
      domains.foldr VExpr.lam (body.inst argument (index + domains.length)) := by
  induction domains generalizing index with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldr_cons,VExpr.inst,List.length_cons]
    rw [(closed d (by simp)).instN_eq (Nat.zero_le index),
      ih (fun t ht => closed t (by simp [ht]))]
    have indexEq : index + 1 + ds.length = index + (ds.length + 1) := by omega
    rw [indexEq]

/-- Once a parameter has been applied, its annotation has disappeared from
the reduced source term. This equation does not assert that mixed Word/BV32
arguments have identical inferred types. -/
theorem lambda_prefix_retag (arguments before after suffix : List VExpr)
    (leftLength : before.length = arguments.length)
    (rightLength : after.length = arguments.length)
    (closed : ∀ d ∈ before ++ after ++ suffix, d.ClosedN 0) (body : VExpr) :
    arguments.foldl LeanTypeReduction.applyReduced ((before ++ suffix).foldr VExpr.lam body) =
      arguments.foldl LeanTypeReduction.applyReduced ((after ++ suffix).foldr VExpr.lam body) := by
  induction arguments generalizing before after body with
  | nil =>
    have l : before = [] := List.eq_nil_of_length_eq_zero leftLength
    have r : after = [] := List.eq_nil_of_length_eq_zero rightLength
    subst before; subst after; rfl
  | cons arg args ih =>
    cases before with
    | nil => simp at leftLength
    | cons d ds =>
      cases after with
      | nil => simp at rightLength
      | cons e es =>
        have len : ds.length = es.length := by simp at leftLength rightLength; omega
        simp only [List.cons_append,List.foldr_cons,List.foldl_cons,LeanTypeReduction.applyReduced]
        rw [instantiate_lambdas (ds ++ suffix) (by intro t ht; exact closed t (by simp only [List.mem_append,List.mem_cons] at ht ⊢; rcases ht with h | h <;> simp_all)),
          instantiate_lambdas (es ++ suffix) (by intro t ht; exact closed t (by simp only [List.mem_append,List.mem_cons] at ht ⊢; rcases ht with h | h <;> simp_all))]
        simp only [List.length_append,Nat.zero_add,len]
        exact ih ds es (by simpa using leftLength) (by simpa using rightLength)
          (by
            intro t ht
            apply closed t
            simp only [List.mem_append,List.mem_cons] at ht ⊢
            rcases ht with (h | h) | h
            · exact Or.inl (Or.inl (Or.inr h))
            · exact Or.inl (Or.inr (Or.inr h))
            · exact Or.inr h) _

/-- Type a static lambda telescope once from the original body's typing.
This is shared by source reconstruction and mixed-argument prefix typing. -/
theorem lambdaTelescope_typed {body : VExpr} (domains : List VExpr) (closed : ClosedConstantTypes env)
    (parameters : ∀ d ∈ domains, ∃ u, CastTyping env 0 (Arithmetic.SourceCasts env) [] d (.sort u))
    (bodyTyped : CastTyping env 0 (Arithmetic.SourceCasts env) (domains.reverse ++ ctx) body resultType) :
    CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (domains.foldr VExpr.lam body) (domains.foldr VExpr.forallE resultType) := by
  induction domains generalizing ctx with
  | nil => simpa using bodyTyped
  | cons d ds ih =>
    obtain ⟨u,typed⟩ := parameters d (by simp)
    exact .lambda (typed.in_context closed Arithmetic.SourceCasts.closed (by trivial) ctx)
      (ih (fun t ht => parameters t (by simp [ht]))
        (by simpa [List.reverse_cons,List.append_assoc] using bodyTyped))

/-- Binding transport and typing reuse the same lambda-spine representation. -/
theorem lambdaSource_represents {body : Lean.Expr} (shape : LambdaSource value domains body)
    (represented : List.Forall₂ Represents domains cores) (bodyRep : Represents body bodyCore) :
    Represents value (cores.foldr VExpr.lam bodyCore) := by
  induction shape generalizing cores with
  | last notLambda =>
    cases represented with
    | cons rep tail => cases tail; exact .lam rep bodyRep
  | next tail ih =>
    cases represented with
    | cons rep rest => exact .lam rep (ih rest bodyRep)

/-- Reconstruct the type and representation of an arbitrary lambda spine
from its final body's source evidence. Reuse LambdaSource rather than define
another function grammar. Parameter types are checked once in the empty scope. -/
theorem lambdaSource_typed {body : Lean.Expr} (shape : LambdaSource value domains body)
    (represented : List.Forall₂ Represents domains cores)
    (closed : ClosedConstantTypes env)
    (parameters : ∀ d ∈ cores, ∃ u, CastTyping env 0 (Arithmetic.SourceCasts env) [] d (.sort u))
    (bodyRep : Represents body bodyCore)
    (bodyTyped : CastTyping env 0 (Arithmetic.SourceCasts env) (cores.reverse ++ ctx) bodyCore resultType) :
    Represents value (cores.foldr VExpr.lam bodyCore) ∧
      CastTyping env 0 (Arithmetic.SourceCasts env) ctx
        (cores.foldr VExpr.lam bodyCore) (cores.foldr VExpr.forallE resultType) := by
  exact ⟨lambdaSource_represents shape represented bodyRep,
    lambdaTelescope_typed cores closed parameters bodyTyped⟩

/-- Function types for the same list of static parameter types are well formed
without a separate hand-written derivation per arity. -/
theorem functionType_typed (cores : List VExpr) (closed : ClosedConstantTypes env)
    (parameters : ∀ d ∈ cores, ∃ u, CastTyping env 0 (Arithmetic.SourceCasts env) [] d (.sort u))
    (resultTyped : CastTyping env 0 (Arithmetic.SourceCasts env) [] resultType (.sort resultLevel)) :
    ∃ u, CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (cores.foldr VExpr.forallE resultType) (.sort u) := by
  induction cores generalizing ctx with
  | nil => exact ⟨_,resultTyped.in_context closed Arithmetic.SourceCasts.closed (by trivial) ctx⟩
  | cons d rest ih =>
    obtain ⟨u,domainTyped⟩ := parameters d (by simp)
    obtain ⟨v,codomainTyped⟩ := ih (fun t ht => parameters t (by simp [ht])) (ctx := d::ctx)
    exact ⟨_,.forallType
      (domainTyped.in_context closed Arithmetic.SourceCasts.closed (by trivial) ctx) codomainTyped⟩

/-- Closed parameter and result declarations imply closure of every suffix
of the helper telescope. Callers do not prove closure per partial application. -/
theorem functionType_suffix_closed (domains : List VExpr) (closed : ClosedConstantTypes env)
    (parameters : ∀ d ∈ domains, ∃ u, CastTyping env 0 (Arithmetic.SourceCasts env) [] d (.sort u))
    (resultTyped : CastTyping env 0 (Arithmetic.SourceCasts env) [] resultType (.sort resultLevel)) :
    ∀ n, ((domains.drop n).foldr VExpr.forallE resultType).ClosedN 0 := by
  intro n
  obtain ⟨u,typed⟩ := functionType_typed (domains.drop n) closed
    (fun d hd => parameters d (List.mem_of_mem_drop hd)) resultTyped (ctx := [])
  exact typed.closed_term

/-- All partial-application types follow from typing the *original* helper
body under the parameter annotations of the supplied arguments. No reduced
term, parser success or generated certificate is a premise. In particular,
a Word/BV32 spelling change is handled before exact typed substitution. -/
theorem lambdaPrefixesFromBody {body : VExpr}
    (domains actual args : List VExpr) (arity : domains.length = args.length)
    (arguments : List.Forall₂ (fun ty arg => CastTyping env 0 (Arithmetic.SourceCasts env) ctx arg ty) actual args)
    (closed : ClosedConstantTypes env)
    (parameters : ∀ d ∈ domains ++ actual, ∃ u, CastTyping env 0 (Arithmetic.SourceCasts env) [] d (.sort u))
    (resultTyped : CastTyping env 0 (Arithmetic.SourceCasts env) [] resultType (.sort resultLevel))
    (bodyTyped : ∀ n, n ≤ args.length → CastTyping env 0 (Arithmetic.SourceCasts env)
      ((actual.take n ++ domains.drop n).reverse ++ ctx) body resultType) :
    ∀ before after, args = before ++ after →
      CastTyping env 0 (Arithmetic.SourceCasts env) ctx
        (before.foldl LeanTypeReduction.applyReduced (domains.foldr VExpr.lam body))
        ((domains.drop before.length).foldr VExpr.forallE resultType) := by
  have actualLength : actual.length = args.length := by
    clear arity parameters bodyTyped
    induction arguments with
    | nil => rfl
    | cons _ _ ih => simpa using congrArg Nat.succ ih
  have takeArguments : ∀ n, List.Forall₂ (fun ty arg => CastTyping env 0 (Arithmetic.SourceCasts env) ctx arg ty)
      (actual.take n) (args.take n) := by
    intro n
    clear arity parameters bodyTyped actualLength
    induction arguments generalizing n with
    | nil => simp
    | cons typed rest ih =>
      cases n with
      | zero => exact .nil
      | succ n => exact .cons typed (ih n)
  intro before after split
  have bound : before.length ≤ args.length := by rw [split,List.length_append]; omega
  have prefixArguments : List.Forall₂ (fun ty arg => CastTyping env 0 (Arithmetic.SourceCasts env) ctx arg ty)
      (actual.take before.length) before := by
    simpa only [split,List.take_left] using takeArguments before.length
  have param : ∀ d ∈ actual.take before.length ++ domains.drop before.length,
      ∃ u, CastTyping env 0 (Arithmetic.SourceCasts env) [] d (.sort u) := by
    intro d member
    apply parameters d
    rcases List.mem_append.mp member with h | h
    · exact List.mem_append_right _ (List.mem_of_mem_take h)
    · exact List.mem_append_left _ (List.mem_of_mem_drop h)
  have suffixTyped := functionType_typed (domains.drop before.length) closed
    (fun d hd => parameters d (List.mem_append_left _ (List.mem_of_mem_drop hd))) resultTyped (ctx := [])
  obtain ⟨suffixLevel,suffixTyped⟩ := suffixTyped
  have typesClosed := functionType_suffix_closed (actual.take before.length) closed
    (fun d hd => parameters d (List.mem_append_right _ (List.mem_of_mem_take hd))) suffixTyped
  have originalTyped := lambdaTelescope_typed (actual.take before.length ++ domains.drop before.length)
    closed param (bodyTyped before.length bound)
  have retyped := LeanTypeReduction.exact_spine_prefix_typed prefixArguments typesClosed closed
    Arithmetic.SourceCasts.closed (by simpa only [List.foldr_append] using originalTyped)
    before [] (by simp)
  have erased := lambda_prefix_retag before (domains.take before.length) (actual.take before.length)
    (domains.drop before.length)
    (by simp only [List.length_take,arity,Nat.min_eq_left bound])
    (by simp only [List.length_take,actualLength,Nat.min_eq_left bound])
    (by
      intro d member
      have member' : d ∈ domains ++ actual := by
        simp only [List.mem_append] at member ⊢
        rcases member with (h | h) | h
        · exact Or.inl (List.mem_of_mem_take h)
        · exact Or.inr (List.mem_of_mem_take h)
        · exact Or.inl (List.mem_of_mem_drop h)
      obtain ⟨_,typed⟩ := parameters d member'
      exact typed.closed_term) body
  rw [List.take_append_drop] at erased
  rw [erased]
  simpa only [List.foldr_append,List.drop_take,Nat.sub_self,List.take_zero,List.foldr_nil] using retyped

/-- Discharge the whole argument-spine condition from element typing.
This concerns static, closed parameter types; mixed Word/BV32 argument
conversion is not silently assumed to be an exact typing derivation. -/
theorem functionArguments_typed
    (arguments : List.Forall₂ (fun domain argument =>
      CastTyping env 0 (Arithmetic.SourceCasts env) ctx argument domain) domains values)
    (closed : ClosedConstantTypes env)
    (parameters : ∀ d ∈ domains, ∃ u, CastTyping env 0 (Arithmetic.SourceCasts env) [] d (.sort u))
    (resultTyped : CastTyping env 0 (Arithmetic.SourceCasts env) [] resultType (.sort resultLevel)) :
    LeanTypeReduction.ArgumentsCasts env 0 (Arithmetic.SourceCasts env) ctx
      (domains.foldr VExpr.forallE resultType) values resultType := by
  induction arguments with
  | nil => exact .nil
  | @cons domain argument domains values typed rest ih =>
    have tailTypes := fun d (hd : d ∈ domains) => parameters d (by simp [hd])
    obtain ⟨u,formed⟩ := functionType_typed domains closed tailTypes resultTyped (ctx := [])
    apply LeanTypeReduction.ArgumentsCasts.cons typed
    simpa only [formed.closed_term.instN_eq (Nat.zero_le _)] using ih tailTypes

/-- A scalar binding extends the value context and preserves captured helper
bindings. Certificate construction is shared with the ordinary body rule. -/
theorem letValue_complete_code (annotation : WordBinder.Annotation)
    (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p (σ.apply first) scalarExpected}
    (left : ScalarCasts inputs a (Arithmetic.SourceCasts env) (For.Casts setup))
    {b : Piece env (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
      ((under σ).apply next) bodyExpected}
    (right : BodyCasts (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons) b
      (Arithmetic.SourceCasts env) (For.Casts setup))
    (rightForm : Arithmetic.ValueForm setup (annotation.core::ctx) right.sourceCore.val (optionType stateType))
    (ha : ScalarEnvironment.parse env setup.conversion exposure ctx p (σ.apply first) = some a)
    (hb : visit env setup.conversion exposure next (annotation.core::ctx)
      {p.lift with locals := .bvar 0::p.lift.locals} .body (under σ) (underFunctions fs) = some b)
    (binder : Lean.Name) (flag : Bool) :
    ∃ result, visit env setup.conversion exposure (WordBinder.letSource annotation binder first next flag)
        ctx p .body σ fs = some result ∧
      ∃ typed : BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType stateType) ∧
        result.code = app ``HybridWord.Cmd.letValue [a.code,b.code] := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have assembled := WordBinder.let_certificate annotation setup library.scalars.toSignatures inputs closed
    library.cons library.steps.state library.steps.option library.eq library.eval library.letValue
    library.letValueConstructor fresh.option coverage exposure left right rightForm binder flag
  have sourceSame := substitute_annotated_let (binder := binder) (value := first) (next := next) (flag := flag) σ annotation
  rw [← sourceSame] at assembled
  obtain ⟨artifact,checked,typed,form⟩ := assembled
  let code := ClosedTerm.app ``HybridWord.Cmd.letValue [a.closedTerm,b.closedTerm]
  let result : Piece env ctx p (σ.apply (WordBinder.letSource annotation binder first next flag)) bodyExpected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  refine ⟨result,?_,typed,form,rfl⟩
  have annotationApply : σ.apply annotation.native = annotation.native := by
    rw [Substitution.apply_eq,annotation.substitute_native]
  have compatible := annotation.compatible setup library.scalars.toSignatures (ctx := ctx)
  have notState : sameTerm annotation.native state = false := by cases annotation <;> rfl
  obtain ⟨tc,translated,same⟩ := annotation.represented.translate_complete
  have translatedExact : translate annotation.native = some ⟨annotation.core,annotation.represented⟩ := by
    cases tc with | mk val prop => dsimp only at same; subst val; exact translated
  have modeValue : (Mode.body == Mode.value) = false := rfl
  have modeStep : (Mode.body == Mode.step) = false := rfl
  cases annotation <;> cases σ
  all_goals
    rw [visit]
    simp only [node,WordBinder.letSource,letParts,Substitution.apply,LeanBindings.substitute,
      WordBinder.Annotation.native,WordBinder.Annotation.core,WordFrontend.word,Arithmetic.nativeWidth,app,List.foldl_cons,List.foldl_nil,
      Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,under] at compatible notState translatedExact ha hb checked ⊢
    simp only [notState,compatible,modeValue,modeStep,Bool.false_eq_true,ite_false,
      Bool.false_and,Bool.not_false,Bool.true_and,ite_true,translatedExact,bind,Option.bind,pure,Option.pure_def]
    rw [ha]
    dsimp only
    rw [hb]
    dsimp only
    simp only [finishBody,Mode.expected,ClosedTerm.app,Piece.closedTerm,WordBinder.letSource,
      Substitution.apply,LeanBindings.substitute,WordBinder.Annotation.native,WordBinder.Annotation.core,WordFrontend.word,
      Arithmetic.nativeWidth,app,List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil,
      Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked ⊢
    rw [checked]
    rfl

/-- Branch certificates compose already-derived children in their captured
lexical environment; neither arm is reparsed after substitution. -/
theorem branch_typed_complete_code (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p)
    {e : Piece env ctx p (σ.apply v) scalarExpected}
    (value : ScalarCasts inputs e (Arithmetic.SourceCasts env) (For.Casts setup))
    {a : Piece env ctx p (σ.apply yes) bodyExpected}
    (left : BodyCasts inputs a (Arithmetic.SourceCasts env) (For.Casts setup))
    {b : Piece env ctx p (σ.apply no) bodyExpected}
    (right : BodyCasts inputs b (Arithmetic.SourceCasts env) (For.Casts setup))
    (decisionRep : Represents (σ.apply d) dc)
    (predicateTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (Branch.condition value.sourceCore.val) (.sort .zero))
    (decisionTyped : CastTyping env 0 (Arithmetic.SourceCasts env) ctx dc
      (.app (.const ``Decidable []) (Branch.condition value.sourceCore.val)))
    (he : ScalarEnvironment.parse env setup.conversion exposure ctx p (σ.apply v) = some e)
    (ha : visit env setup.conversion exposure yes ctx p .body σ fs = some a)
    (hb : visit env setup.conversion exposure no ctx p .body σ fs = some b) :
    ∃ result, visit env setup.conversion exposure (Branch.source v d yes no) ctx p .body σ fs = some result ∧
      ∃ typed : BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType stateType) ∧ result.code = app ``HybridWord.Cmd.branch [e.code,a.code,b.code] := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have embed : ∀ scope a b, Arithmetic.SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  have assembled := Branch.finish_complete inputs
    (value.inProofCasts embed) (left.inProofCasts embed) (right.inProofCasts embed) decisionRep
    (decisionTyped.mono embed) library.branchFact coverage exposure
  let code := ClosedTerm.app ``HybridWord.Cmd.branch [e.closedTerm,a.closedTerm,b.closedTerm]
  have represented := Branch.source_represents value.sourceCore.property decisionRep left.sourceCore.property right.sourceCore.property
  have sourceSame := substitute_branch (v := v) (d := d) (yes := yes) (no := no) σ
  rw [← sourceSame] at represented assembled
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := assembled
  let result : Piece env ctx p (σ.apply (Branch.source v d yes no)) bodyExpected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  have target : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (applications (.const ``HybridWord.Cmd.branch []) [e.represented.val,a.represented.val,b.represented.val]) cmdType := by
    have h : CastTyping env 0 (Arithmetic.SourceCasts env) ctx (.const ``HybridWord.Cmd.branch []) Branch.constructorSignature :=
      .constant library.branchConstructor (by simp) rfl
    exact .application (.application (.application h value.target) left.target) right.target
  let typed : BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup) :=
    ⟨⟨_,represented⟩,Branch.choice_typed library.toLibrary.option_typed predicateTyped decisionTyped
      left.value right.value library.ite,target,proofTyped⟩
  refine ⟨result,?_,typed,?_,rfl⟩
  · rw [visit]
    have bodyValue : (Mode.body == Mode.value) = false := rfl
    have bodyStep : (Mode.body == Mode.step) = false := rfl
    simp only [node,bodyValue,bodyStep]
    simp [letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      ScalarEnvironment.arguments,ScalarEnvironment.below,Branch.source,Branch.nativeCondition,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
      Lean.Expr.getAppFn,Lean.Expr.constName?]
    have test : nonzeroValue (Branch.nativeCondition v) = some v := rfl
    simp only [Branch.nativeCondition,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at test
    simp only [test,Option.bind_some,he,ha,hb]
    refine ⟨v,rfl,e,he,a,rfl,b,rfl,?_⟩
    simp only [finishBody,bind,Option.bind,pure,Option.pure_def]
    simp only [Mode.expected,ClosedTerm.app,ClosedTerm.const,Piece.closedTerm,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append,Branch.source,Branch.nativeCondition,Lean.mkApp5,Lean.mkApp4,
      Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked ⊢
    rw [checked]
    rfl
  · change Arithmetic.ValueForm setup ctx _ _
    exact .constant rfl (fresh.value _ (by simp)) (by decide)

theorem branch_complete_code (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p)
    {e : Piece env ctx p (σ.apply v) scalarExpected}
    (value : ScalarCasts inputs e (Arithmetic.SourceCasts env) (For.Casts setup))
    {a : Piece env ctx p (σ.apply yes) bodyExpected}
    (left : BodyCasts inputs a (Arithmetic.SourceCasts env) (For.Casts setup))
    {b : Piece env ctx p (σ.apply no) bodyExpected}
    (right : BodyCasts inputs b (Arithmetic.SourceCasts env) (For.Casts setup))
    (decision : ScalarSyntax.Decision env ctx (σ.apply v) (σ.apply d))
    (he : ScalarEnvironment.parse env setup.conversion exposure ctx p (σ.apply v) = some e)
    (ha : visit env setup.conversion exposure yes ctx p .body σ fs = some a)
    (hb : visit env setup.conversion exposure no ctx p .body σ fs = some b) :
    ∃ result, visit env setup.conversion exposure (Branch.source v d yes no) ctx p .body σ fs = some result ∧
      ∃ typed : BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType stateType) ∧ result.code = app ``HybridWord.Cmd.branch [e.code,a.code,b.code] := by
  obtain ⟨vc,dc,vr,dr,pt,dt⟩ := decision.typing
  rw [← value.sourceCore.property.unique vr] at pt dt
  exact branch_typed_complete_code setup library closed fresh exposure inputs value left right dr
    (pt.mono (fun _ _ _ h => Arithmetic.SourceCasts.arithmetic h))
    (dt.mono (fun _ _ _ h => Arithmetic.SourceCasts.arithmetic h)) he ha hb

theorem branch_complete (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p)
    {e : Piece env ctx p (σ.apply v) scalarExpected}
    (value : ScalarCasts inputs e (Arithmetic.SourceCasts env) (For.Casts setup))
    {a : Piece env ctx p (σ.apply yes) bodyExpected}
    (left : BodyCasts inputs a (Arithmetic.SourceCasts env) (For.Casts setup))
    {b : Piece env ctx p (σ.apply no) bodyExpected}
    (right : BodyCasts inputs b (Arithmetic.SourceCasts env) (For.Casts setup))
    (decision : ScalarSyntax.Decision env ctx (σ.apply v) (σ.apply d))
    (he : ScalarEnvironment.parse env setup.conversion exposure ctx p (σ.apply v) = some e)
    (ha : visit env setup.conversion exposure yes ctx p .body σ fs = some a)
    (hb : visit env setup.conversion exposure no ctx p .body σ fs = some b) :
    ∃ result, visit env setup.conversion exposure (Branch.source v d yes no) ctx p .body σ fs = some result ∧
      ∃ typed : BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType stateType) := by
  obtain ⟨result,parsed,typed,form,_⟩ := branch_complete_code setup library closed fresh exposure inputs value left right decision he ha hb
  exact ⟨result,parsed,typed,form⟩

/-- Sequential State continuations preserve the captured helper environment
under the new State binder, and compose the existing sequence certificate. -/
theorem sequence_complete_code (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p (σ.apply first) bodyExpected}
    (left : BodyCasts inputs a (Arithmetic.SourceCasts env) (For.Casts setup))
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} ((under σ).apply next) bodyExpected}
    (right : BodyCasts (inputs.nextState closed) b (Arithmetic.SourceCasts env) (For.Casts setup))
    (rightForm : Arithmetic.ValueForm setup (stateType::ctx) right.sourceCore.val (optionType stateType))
    (ha : visit env setup.conversion exposure first ctx p .body σ fs = some a)
    (hb : visit env setup.conversion exposure next (stateType::ctx) {p.lift with s := .bvar 0}
      .body (under σ) (underFunctions fs) = some b)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ result, visit env setup.conversion exposure (sequenceSource first (.lam binder state next info))
        ctx p .body σ fs = some result ∧
      ∃ typed : BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType stateType) ∧ result.code = app ``HybridWord.Cmd.seq [a.code,b.code] := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have embed : ∀ scope a b, Arithmetic.SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  obtain ⟨target,nextTyped,_⟩ := sequence_next_typed inputs closed Arithmetic.SourceCasts.closed library.steps.state right
  have beta : For.Casts setup ctx (sequenceNextActual inputs b.represented.val right.sourceCore.val)
      (sequenceContinuationType inputs b.represented.val (.lam stateType right.sourceCore.val)) :=
    .base (.base (.stateContinuation inputs target right.value rightForm))
  have assembled := sequence_finish inputs closed Arithmetic.SourceCasts.closed embed library.steps.state
    left right beta library.sequence coverage exposure binder info
  have sourceSame := substitute_sequence (first := first) (next := next) (binder := binder) (info := info) σ
  rw [← sourceSame] at assembled
  obtain ⟨artifact,checked,proofTyped,_,_⟩ := assembled
  let code := ClosedTerm.app ``HybridWord.Cmd.seq [a.closedTerm,b.closedTerm]
  let result : Piece env ctx p (σ.apply (sequenceSource first (.lam binder state next info))) bodyExpected :=
    ⟨code.val,artifact,code.closed,code.represented⟩
  have src : Represents (σ.apply (sequenceSource first (.lam binder state next info)))
      (.app (.app stateBindHeader left.sourceCore.val) (.lam stateType right.sourceCore.val)) := by
    rw [sourceSame]
    exact .app (.app stateBind_represents left.sourceCore.property) (.lam (.constant rfl) right.sourceCore.property)
  have applied := CastTyping.application ((library.bind.state_header_typed library.steps.state).withCasts (Arithmetic.SourceCasts env)) left.value
  simp only [optionType,stateType,VExpr.inst] at applied
  have sourceTyped := CastTyping.application applied nextTyped
  have constructor : CastTyping env 0 (Arithmetic.SourceCasts env) ctx
      (.const ``HybridWord.Cmd.seq []) sequenceConstructor := .constant library.sequenceConstructor (by simp) rfl
  have targetTyped := CastTyping.application (CastTyping.application constructor left.target) target
  let typed : BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup) :=
    ⟨⟨_,src⟩,sourceTyped,targetTyped,proofTyped⟩
  refine ⟨result,?_,typed,?_,rfl⟩
  · have bodyValue : (Mode.body == Mode.value) = false := rfl
    have bodyStep : (Mode.body == Mode.step) = false := rfl
    have stateApply : σ.apply state = state := by cases σ <;> rfl
    have ss : sameTerm state state = true := sameTerm_complete (Represents.constant rfl) (Represents.constant rfl)
    have su : sameTerm state (.const ``PUnit [.succ .zero]) = false := rfl
    have st : translate state = some ⟨stateType,Represents.constant rfl⟩ := rfl
    have stMapped : (translate (σ.apply state)).unattach = some stateType := by rw [stateApply]; rfl
    have sc : compatible env setup.conversion ctx state state = true :=
      compatible_same (Represents.constant rfl) (Represents.constant rfl) env setup.conversion ctx
    rw [visit]
    simp [node,bodyValue,bodyStep,letParts,applicationHead,makeContinuation,continuationParts,lambdaChain,
      ScalarEnvironment.arguments,ScalarEnvironment.below,lambdaParts,stateApply,
      sequenceSource,bindHead,Lean.mkAppN,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
      Lean.Expr.getAppFn,Lean.Expr.constName?,ss,su,st]
    simp only [List.map_append,List.map_cons,List.map_nil,Function.comp_apply,
      List.cons_append,List.nil_append,List.length_cons,List.length_nil,Nat.reduceAdd,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.unattach_some,
      stMapped,sc,ite_true,Option.bind_some,ha,hb]
    dsimp only [List.map,List.append,List.length,Function.comp_apply,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.unattach]
    try simp only [ha,hb,Option.bind_some]
    have lambdaSame : σ.apply (.lam binder state next info) = .lam binder state ((under σ).apply next) info := by cases σ <;> rfl
    simp only [lambdaSame,finishBody,bind,Option.bind,pure,Option.pure_def]
    refine ⟨first,rfl,stateType,rfl,trivial,a,ha,b,hb,?_⟩
    simp only [Mode.expected,ClosedTerm.app,Piece.closedTerm,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append,sequenceSource,bindHead,Lean.mkAppN,Lean.mkApp4,
      Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked ⊢
    rw [checked]
    rfl
  · exact .constant rfl (fresh.value _ (by simp)) (by decide)

theorem sequence_complete (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p)
    {a : Piece env ctx p (σ.apply first) bodyExpected}
    (left : BodyCasts inputs a (Arithmetic.SourceCasts env) (For.Casts setup))
    {b : Piece env (stateType::ctx) {p.lift with s := .bvar 0} ((under σ).apply next) bodyExpected}
    (right : BodyCasts (inputs.nextState closed) b (Arithmetic.SourceCasts env) (For.Casts setup))
    (rightForm : Arithmetic.ValueForm setup (stateType::ctx) right.sourceCore.val (optionType stateType))
    (ha : visit env setup.conversion exposure first ctx p .body σ fs = some a)
    (hb : visit env setup.conversion exposure next (stateType::ctx) {p.lift with s := .bvar 0}
      .body (under σ) (underFunctions fs) = some b)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    ∃ result, visit env setup.conversion exposure (sequenceSource first (.lam binder state next info))
        ctx p .body σ fs = some result ∧
      ∃ typed : BodyCasts inputs result (Arithmetic.SourceCasts env) (For.Casts setup),
        Arithmetic.ValueForm setup ctx typed.sourceCore.val (optionType stateType) := by
  obtain ⟨result,parsed,typed,form,_⟩ := sequence_complete_code setup library closed fresh exposure inputs left right rightForm ha hb binder info
  exact ⟨result,parsed,typed,form⟩

end IRComparison.WordFrontend.FunctionSyntax

namespace IRComparison.WordFrontend.FunctionSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate StructuralBody StructuralSyntax
set_option maxHeartbeats 2400000

/-- Source parameter references after opening a whole telescope. This is
proof-side binding bookkeeping, not a new program representation. -/
def openArguments : Nat → List Lean.Expr → List Lean.Expr
  | 0, saved => saved
  | n+1, saved => openArguments n (saved.map (LeanBindings.rename Nat.succ) ++ [.bvar 0])

@[simp] theorem openArguments_length (n : Nat) (saved : List Lean.Expr) :
    (openArguments n saved).length = saved.length+n := by
  induction n generalizing saved with
  | zero => simp [openArguments]
  | succ n ih => simp [openArguments,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Opening one more formal argument agrees with entering its source binder,
including when other parameters or captures already occupy the environment. -/
theorem closureSubstitution_open_next (bound : capture ≤ target)
    (captured : Substitution) (saved : List Lean.Expr) (body : Lean.Expr) :
    (closureSubstitution capture (target+1) captured
      (saved.map (LeanBindings.rename Nat.succ) ++ [.bvar 0])).apply body =
      (under (closureSubstitution capture target captured saved)).apply body := by
  rw [Substitution.apply_eq,Substitution.apply_eq]
  congr 1
  funext n
  cases n with
  | zero => simp [closureSubstitution,Substitution.reference,closureReference,under,LeanBindings.underSubst]
  | succ n =>
    simp only [closureSubstitution,Substitution.reference,closureReference,List.reverse_append,
      List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append,← List.map_reverse,
      List.getElem?_cons_succ,List.getElem?_map,List.length_append,List.length_map,
      List.length_cons,List.length_nil,Nat.add_sub_add_right,under,LeanBindings.underSubst]
    cases found : saved.reverse[n]? with
    | some v => rfl
    | none =>
      simp only [found,Option.map_none,LeanBindings.rename_comp]
      congr 1
      funext k
      simp only [Function.comp_apply,Nat.succ_eq_add_one]
      omega

private theorem lambda_nonempty {body : Lean.Expr} (shape : LambdaSource value domains body) : domains ≠ [] := by
  cases shape <;> simp

/-- Compare the source lambda body with the captured body opened at all
parameters. The induction visits only the lambda spine, never the body. -/
theorem lambdaSource_opened {body functionBody : Lean.Expr}
    (original : LambdaSource value domains body)
    (bound : capture ≤ target)
    (shape : LambdaSource ((closureSubstitution capture target captured saved).apply value) nativeDomains functionBody)
    (length : domains.length = nativeDomains.length) :
    (closureSubstitution capture (target+domains.length) captured
      (openArguments domains.length saved)).apply body = functionBody := by
  induction original generalizing target saved nativeDomains functionBody with
  | @last name ty body info notLambda =>
    change LambdaSource (.lam name _ ((under (closureSubstitution capture target captured saved)).apply body) info) nativeDomains functionBody at shape
    cases shape with
    | last =>
      simpa only [List.length_cons,List.length_nil,openArguments] using
        closureSubstitution_open_next bound captured saved body
    | next tail =>
      have empty : _ = ([] : List Lean.Expr) := List.eq_nil_of_length_eq_zero (by simpa using length.symm)
      exact False.elim (lambda_nonempty tail empty)
  | @next name ty inner info domains body tail ih =>
    change LambdaSource (.lam name _ ((under (closureSubstitution capture target captured saved)).apply inner) info) nativeDomains functionBody at shape
    cases shape with
    | last =>
      have empty : domains = [] := List.eq_nil_of_length_eq_zero (by simpa using length)
      exact False.elim (lambda_nonempty tail empty)
    | next nextShape =>
      rw [← closureSubstitution_open_next bound captured saved inner] at nextShape
      have result := ih (target := target+1) (by omega) nextShape (by simpa using length)
      simpa only [List.length_cons,openArguments,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

/-- Arbitrary arity counterpart of openedScalar, with arbitrary captures. -/
theorem BindingValue.openedArguments {body functionBody : Lean.Expr}
    (binding : BindingValue scope target σ head (.captured capture captured arity body functions))
    (coherent : scope.Coherent target σ)
    (shape : LambdaSource (σ.apply head) domains functionBody)
    (length : domains.length = arity) :
    (closureSubstitution capture (target+arity) captured (openArguments arity [])).apply body = functionBody := by
  obtain ⟨bound,value,originalDomains,original,count,same⟩ := binding.sourceAt coherent
  rw [same] at shape
  simpa only [count] using lambdaSource_opened original bound shape (count.trans length.symm)

/-- Singleton compatibility rule, derived from general telescope opening. -/
theorem closureSubstitution_open_scalar (bound : capture ≤ target)
    (captured : Substitution) (body : Lean.Expr) :
    (closureSubstitution capture (target+1) captured [.bvar 0]).apply body =
      (under (closureSubstitution capture target captured [])).apply body := by
  simpa only [List.map_nil,List.nil_append] using closureSubstitution_open_next bound captured [] body

/-- Singleton compatibility rule; no separate lambda-spine induction. -/
theorem BindingValue.openedScalar {body functionBody : Lean.Expr}
    (binding : BindingValue scope target σ head (.captured capture captured 1 body functions))
    (coherent : scope.Coherent target σ)
    (shape : LambdaSource (σ.apply head) [annotation] functionBody) :
    (closureSubstitution capture (target+1) captured [.bvar 0]).apply body = functionBody := by
  simpa only [openArguments,List.map_nil,List.nil_append] using binding.openedArguments coherent shape rfl

end IRComparison.WordFrontend.FunctionSyntax
