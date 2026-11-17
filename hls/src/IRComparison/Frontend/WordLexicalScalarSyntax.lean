import IRComparison.Frontend.WordScalarSyntax
import IRComparison.Frontend.WordAnnotatedSelectSyntax

/-! Source-only lexical syntax. The list below contains ordinary Lean values,
not parse results or certificates. The success induction constructs the
runtime environment and its typing invariant from this source description. -/
namespace IRComparison.WordFrontend.LexicalScalarSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarEnvironment ScalarSyntax
set_option maxHeartbeats 1800000
variable {env : VEnv} {ctx : List VExpr} {p : Inputs} {bindings : Bindings env ctx p}

def sourceReference (values : List Lean.Expr) (n : Nat) : Lean.Expr :=
  match values[n]? with
  | some value => value
  | none => .bvar (n - values.length)

def expand (values : List Lean.Expr) (source : Lean.Expr) : Lean.Expr :=
  LeanBindings.substitute (sourceReference values) source

def under (values : List Lean.Expr) (source : Lean.Expr) : Lean.Expr :=
  LeanBindings.substitute (LeanBindings.underSubst (sourceReference values)) source

/-- This relates the source-only scope to the runtime cache, and is preserved
when the induction constructs one new value. -/
def Matches (values : List Lean.Expr) (bindings : Bindings env ctx p) : Prop :=
  bindings.map Binding.source = values

theorem aligned_nil : Matches [] ([] : Bindings env ctx p) := rfl

theorem Matches.reference (aligned : Matches values bindings) : ScalarEnvironment.reference bindings = sourceReference values := by
  subst values
  funext n
  simp only [ScalarEnvironment.reference,sourceReference,List.getElem?_map,List.length_map]
  cases bindings[n]? <;> rfl

theorem Matches.materialize (aligned : Matches values bindings) (e : Lean.Expr) :
    ScalarEnvironment.materialize bindings e = expand values e := by
  rw [materialize_eq_substitute,aligned.reference]
  rfl

theorem Matches.under (aligned : Matches values bindings) (e : Lean.Expr) :
    LeanBindings.substitute (LeanBindings.underSubst (ScalarEnvironment.reference bindings)) e = under values e := by
  rw [aligned.reference]
  rfl

theorem Matches.cons (aligned : Matches values bindings)
    {piece : Piece env ctx p (ScalarEnvironment.materialize bindings value) scalarExpected} :
    Matches (expand values value :: values) (⟨ScalarEnvironment.materialize bindings value,piece⟩ :: bindings) := by
  simp only [Matches,List.map_cons,aligned.materialize]
  exact congrArg (List.cons _) aligned

@[simp] theorem expand_nil (e : Lean.Expr) : expand [] e = e := by
  have ref : sourceReference [] = Lean.Expr.bvar := by funext n; simp [sourceReference]
  simp [expand,ref,LeanBindings.substitute_id]

/-- The same source substitution law is used by syntax construction and
code-indexed source evidence. It does not refer to parser caches. -/
theorem expand_cons (value : Lean.Expr) (values : List Lean.Expr) (body : Lean.Expr) :
    expand (value::values) body = LeanBindings.instantiate value (under values body) := by
  simp only [expand,under,LeanBindings.instantiate,LeanBindings.substitute_comp]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [sourceReference,List.getElem?_cons_succ,List.length_cons,
      Nat.add_sub_add_right,LeanBindings.underSubst,LeanBindings.substitute_rename]
    exact (LeanBindings.substitute_id _).symm

/-- Heads of value expressions in the accepted scalar syntax, independently
of the installed type-conversion rules. -/
def valueHeads : List Lean.Name :=
  [``OfNat.ofNat,``HAdd.hAdd,``HSub.hSub,``HMul.hMul,``HDiv.hDiv,
    ``Neg.neg,``HybridWord.State.regs,``ite,``BitVec.ofNat]

inductive ValueShape (env : VEnv) (ctx : List VExpr) : VExpr → VExpr → Prop where
  | bound : ValueShape env ctx (.bvar n) ty
  | constant (head : LeanTypeReduction.constantHead e = some (name,levels))
      (allowed : name ∈ valueHeads) : ValueShape env ctx e ty
  | beta {body arg : VExpr} (annotation resultAnnotation : WordBinder.Annotation)
      (typed : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core) :
      ValueShape env ctx (.app (.lam annotation.core body) arg) resultAnnotation.core

theorem ValueShape.toValueForm (shape : ValueShape env ctx e ty) (setup : AliasSetup env)
    (fresh : ∀ n ∈ valueHeads, ∀ r ∈ setup.rules, n ≠ r.name) :
    ValueForm setup ctx e ty := by
  cases shape with
  | bound => exact .bound
  | constant head allowed =>
    exact .constant head (fresh _ allowed) (by
      simp only [valueHeads,List.mem_cons,List.mem_nil_iff,or_false] at allowed
      rcases allowed with h|h|h|h|h|h|h|h|h <;> subst_vars <;> decide)
  | beta annotation resultAnnotation typed =>
    simpa only [resultAnnotation.closed.instN_eq (Nat.zero_le _)] using
      (ValueForm.beta (setup := setup) (arg := _) typed)

/-- The type and scope side conditions mention source terms only. In
particular, a lexical constructor never assumes a successful parser run. -/
inductive Form (env : VEnv) (ctx : List VExpr) (p : Inputs) :
    List Lean.Expr → Lean.Expr → Prop where
  | reference (selected : values[n]? = some value) : Form env ctx p values (.bvar n)
  | parameter (side : Side) (shape : LocalOccurrence raw)
      (same : expand values raw = side.source p)
      (notIndex : sameTerm (side.source p) p.i = false)
      (notLeft : side = .right → sameTerm (side.source p) p.x = false) : Form env ctx p values raw
  | index (shape : LocalOccurrence raw) (same : expand values raw = p.i) : Form env ctx p values raw
  | localValue (shape : LocalOccurrence raw) (k : Nat)
      (selected : p.locals[k]? = some (expand values raw))
      (notIndex : sameTerm (expand values raw) p.i = false)
      (notLeft : sameTerm (expand values raw) p.x = false)
      (notRight : sameTerm (expand values raw) p.y = false)
      (first : ∀ j < k, (p.locals[j]?.map (sameTerm (expand values raw))).getD false = false) :
      Form env ctx p values raw
  | literal (n : Nat) (scope : Separated p (nativeLiteral n)) : Form env ctx p values (nativeLiteral n)
  | binary (op : Binary) (left : Form env ctx p values a) (right : Form env ctx p values b)
      (scope : Separated p (expand values (Lean.mkApp2 op.nativeHeader a b))) :
      Form env ctx p values (Lean.mkApp2 op.nativeHeader a b)
  | neg (value : Form env ctx p values v)
      (scope : Separated p (expand values (.app nativeNegHeader v))) :
      Form env ctx p values (.app nativeNegHeader v)
  | register (stateSame : expand values st = p.s)
      (register : NatArgument env ctx (expand values r))
      (scope : Separated p (expand values (app ``HybridWord.State.regs [st,r]))) :
      Form env ctx p values (app ``HybridWord.State.regs [st,r])
  | select (value : Form env ctx p values v)
      (decision : Decision env ctx (expand values v) (expand values d) (SourceCasts env))
      (yes : Form env ctx p values a) (no : Form env ctx p values b)
      (scope : Separated p (expand values (Branch.Select.source v d a b))) :
      Form env ctx p values (Branch.Select.source v d a b)
  | annotatedLiteral (annotation : WordBinder.Annotation) (n : Nat)
      (scope : Separated p (AnnotatedLiteral.native annotation n)) :
      Form env ctx p values (AnnotatedLiteral.native annotation n)
  | annotatedBinary {leftCore rightCore : VExpr} (op : Binary)
      (aa ab ac ad oa ob : WordBinder.Annotation)
      (left : Form env ctx p values a)
      (right : Form env ctx p values b)
      (leftRep : Represents (expand values a) leftCore) (rightRep : Represents (expand values b) rightCore)
      (leftTyped : CastTyping env 0 (SourceCasts env) ctx leftCore oa.core)
      (rightTyped : CastTyping env 0 (SourceCasts env) ctx rightCore ob.core)
      (leftShape : LexicalScalarSyntax.ValueShape env ctx leftCore oa.core)
      (rightShape : LexicalScalarSyntax.ValueShape env ctx rightCore ob.core)
      (scope : Separated p (expand values (Lean.mkApp2 (AnnotatedBinary.nativeHeader op aa ab ac ad) a b))) :
      Form env ctx p values (Lean.mkApp2 (AnnotatedBinary.nativeHeader op aa ab ac ad) a b)
  | annotatedNeg {valueCore : VExpr} (annotation operand : WordBinder.Annotation)
      (value : Form env ctx p values v)
      (represented : Represents (expand values v) valueCore)
      (typed : CastTyping env 0 (SourceCasts env) ctx valueCore operand.core)
      (form : LexicalScalarSyntax.ValueShape env ctx valueCore operand.core)
      (scope : Separated p (expand values (.app (AnnotatedNeg.nativeHeader annotation) v))) :
      Form env ctx p values (.app (AnnotatedNeg.nativeHeader annotation) v)
  | annotatedSelect {valueCore leftCore rightCore : VExpr}
      (resultAnnotation annotation operand oa ob : WordBinder.Annotation)
      (value : Form env ctx p values v)
      (yes : Form env ctx p values a) (no : Form env ctx p values b)
      (vr : Represents (expand values v) valueCore) (ar : Represents (expand values a) leftCore) (br : Represents (expand values b) rightCore)
      (vt : CastTyping env 0 (SourceCasts env) ctx valueCore operand.core)
      (typedLeft : CastTyping env 0 (SourceCasts env) ctx leftCore oa.core)
      (bt : CastTyping env 0 (SourceCasts env) ctx rightCore ob.core)
      (vf : LexicalScalarSyntax.ValueShape env ctx valueCore operand.core)
      (af : LexicalScalarSyntax.ValueShape env ctx leftCore oa.core)
      (bf : LexicalScalarSyntax.ValueShape env ctx rightCore ob.core)
      (scope : Separated p (expand values (AnnotatedCondition.scalarSource resultAnnotation annotation v
        (AnnotatedCondition.nativeDecision annotation v) a b))) :
      Form env ctx p values (AnnotatedCondition.scalarSource resultAnnotation annotation v (AnnotatedCondition.nativeDecision annotation v) a b)
  | letValue {body arg : VExpr} (annotation resultAnnotation : WordBinder.Annotation) (value : Form env ctx p values v)
      (tail : Form env ctx p (expand values v :: values) next)
      (argument : Represents (expand values v) arg)
      (representedBody : Represents (under values next) body)
      (bodyTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core)
      (form : ∃ actual : WordBinder.Annotation, ValueShape env ctx (body.inst arg) actual.core)
      (binder : Lean.Name) (flag : Bool) :
      Form env ctx p values (.letE binder annotation.native v next flag)
  | beta {body arg : VExpr} (annotation resultAnnotation : WordBinder.Annotation) (value : Form env ctx p values v)
      (tail : Form env ctx p (expand values v :: values) next)
      (argument : Represents (expand values v) arg)
      (representedBody : Represents (under values next) body)
      (bodyTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core)
      (form : ∃ actual : WordBinder.Annotation, ValueShape env ctx (body.inst arg) actual.core)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Form env ctx p values (.app (.lam binder annotation.native next info) v)

theorem expand_renameCache (refs : ∀ n, sourceReference target (ρ n) = sourceReference values n) (raw : Lean.Expr) :
    expand target (LeanBindings.rename ρ raw) = expand values raw := by
  unfold expand
  rw [LeanBindings.substitute_rename]
  congr 1
  exact funext refs

theorem under_renameCache (refs : ∀ n, sourceReference target (ρ n) = sourceReference values n) (raw : Lean.Expr) :
    under target (LeanBindings.rename (LeanBindings.underRename ρ) raw) = under values raw := by
  unfold under
  rw [LeanBindings.substitute_rename]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [Function.comp_apply,LeanBindings.underRename,LeanBindings.underSubst,refs]

private theorem cons_refs (refs : ∀ n, sourceReference target (ρ n) = sourceReference values n) (v : Lean.Expr) :
    ∀ n, sourceReference (v::target) (LeanBindings.underRename ρ n) = sourceReference (v::values) n := by
  intro n
  cases n with
  | zero => rfl
  | succ n => simpa only [LeanBindings.underRename,sourceReference,List.getElem?_cons_succ,List.length_cons,Nat.add_sub_add_right] using refs n

private theorem cons_lookup (lookup : ∀ n, target[ρ n]? = values[n]?) (v : Lean.Expr) :
    ∀ n, (v::target)[LeanBindings.underRename ρ n]? = (v::values)[n]? := by
  intro n
  cases n with
  | zero => rfl
  | succ n => exact lookup n

private theorem rename_annotation (a : WordBinder.Annotation) (ρ : Nat → Nat) :
    LeanBindings.rename ρ a.native = a.native := by cases a <;> rfl

private theorem occurrence_rename (shape : LocalOccurrence raw) (ρ : Nat → Nat) :
    LocalOccurrence (LeanBindings.rename ρ raw) := by
  cases raw with
  | letE name ty v body flag => exact False.elim (shape.notLet name ty v body flag rfl)
  | app f a =>
    cases f with
    | lam name ty body info => exact False.elim (shape.notBeta name ty body info a rfl)
    | _ => exact ⟨by intros; simp [LeanBindings.rename], by intros; simp [LeanBindings.rename]⟩
  | _ => exact ⟨by intros; simp [LeanBindings.rename], by intros; simp [LeanBindings.rename]⟩

/-- Re-index the source-only cache without changing any expanded term.
The map may identify slots holding the same value. -/
theorem Form.renameCache (form : Form env ctx p values raw)
    (lookup : ∀ n, target[ρ n]? = values[n]?)
    (refs : ∀ n, sourceReference target (ρ n) = sourceReference values n) :
    Form env ctx p target (LeanBindings.rename ρ raw) := by
  induction form generalizing target ρ with
  | reference found => exact .reference ((lookup _).trans found)
  | index shape same => exact .index (occurrence_rename shape ρ) ((expand_renameCache refs _).trans same)
  | parameter side shape same ni nl => exact .parameter side (occurrence_rename shape ρ) ((expand_renameCache refs _).trans same) ni nl
  | localValue shape k selected ni nl nr first =>
    exact .localValue (occurrence_rename shape ρ) k
      (by rwa [expand_renameCache refs]) (by rwa [expand_renameCache refs])
      (by rwa [expand_renameCache refs]) (by rwa [expand_renameCache refs])
      (by simpa only [expand_renameCache refs] using first)
  | literal n separated => exact .literal n separated
  | annotatedLiteral a n separated =>
    simpa only [AnnotatedLiteral.native,Lean.mkApp3,Lean.mkApp2,LeanBindings.rename,rename_annotation] using
      Form.annotatedLiteral (values := target) a n separated
  | @register values st r same reg separated =>
    apply Form.register (st := LeanBindings.rename ρ st) (r := LeanBindings.rename ρ r)
    · exact (expand_renameCache refs _).trans same
    · simpa only [expand_renameCache refs] using reg
    · simpa only [← expand_renameCache refs,app,LeanBindings.rename] using separated
  | @binary values a b op left right separated il ir =>
    have children := Form.binary op (il lookup refs) (ir lookup refs)
    cases op <;> apply children <;> simpa only [← expand_renameCache refs,Binary.nativeHeader,Lean.mkApp2,LeanBindings.rename] using separated
  | neg child separated ih =>
    apply Form.neg (ih lookup refs)
    simpa only [← expand_renameCache refs,LeanBindings.rename] using separated
  | select child decision yes no separated iv ia ib =>
    refine Form.select (iv lookup refs) (d := LeanBindings.rename ρ _) ?_ (ia lookup refs) (ib lookup refs) ?_
    · simpa only [expand_renameCache refs] using decision
    · simpa only [← expand_renameCache refs,Branch.Select.source,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,LeanBindings.rename] using separated
  | annotatedBinary op aa ab ac ad oa ob left right lr rr lt rt lf rf separated il ir =>
    have nh := fun (a : WordBinder.Annotation) => rename_annotation a ρ
    have head : LeanBindings.rename ρ (AnnotatedBinary.nativeHeader op aa ab ac ad) = AnnotatedBinary.nativeHeader op aa ab ac ad := by
      simp only [AnnotatedBinary.nativeHeader,AnnotatedBinary.nativeDictionary,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,app,LeanBindings.rename,nh]
      rfl
    simp only [Lean.mkApp2,LeanBindings.rename,head]
    apply Form.annotatedBinary op aa ab ac ad oa ob (il lookup refs) (ir lookup refs)
      (by simpa only [expand_renameCache refs] using lr) (by simpa only [expand_renameCache refs] using rr) lt rt lf rf
    simpa only [← expand_renameCache refs,Lean.mkApp2,LeanBindings.rename,head] using separated
  | annotatedNeg a operand child vr vt vf separated ih =>
    have head : LeanBindings.rename ρ (AnnotatedNeg.nativeHeader a) = AnnotatedNeg.nativeHeader a := by cases a <;> rfl
    simp only [LeanBindings.rename,head]
    apply Form.annotatedNeg a operand (ih lookup refs) (by simpa only [expand_renameCache refs] using vr) vt vf
    simpa only [← expand_renameCache refs,LeanBindings.rename,head] using separated
  | @annotatedSelect values v a b vc ac bc ra ca oa ob oc child yes no vr ar br vt at_ bt vf af bf separated iv ia ib =>
    have renamed : LeanBindings.rename ρ (AnnotatedCondition.scalarSource ra ca v (AnnotatedCondition.nativeDecision ca v) a b) =
        AnnotatedCondition.scalarSource ra ca (LeanBindings.rename ρ v) (AnnotatedCondition.nativeDecision ca (LeanBindings.rename ρ v)) (LeanBindings.rename ρ a) (LeanBindings.rename ρ b) := by cases ra <;> cases ca <;> rfl
    rw [renamed]
    apply Form.annotatedSelect ra ca oa ob oc (iv lookup refs) (ia lookup refs) (ib lookup refs)
      (by simpa only [expand_renameCache refs] using vr) (by simpa only [expand_renameCache refs] using ar)
      (by simpa only [expand_renameCache refs] using br) vt at_ bt vf af bf
    simpa only [← expand_renameCache refs,renamed] using separated
  | @letValue values v rest bodyCore argCore annotation result fv next ar br typed shape binder flag iv ib
  | @beta values v rest bodyCore argCore annotation result fv next ar br typed shape binder flag iv ib =>
    have next := ib (cons_lookup lookup (expand values v)) (cons_refs refs (expand values v))
    have ar' : Represents (expand target (LeanBindings.rename ρ v)) argCore := by simpa only [expand_renameCache refs] using ar
    have br' : Represents (under target (LeanBindings.rename (LeanBindings.underRename ρ) rest)) bodyCore := by simpa only [under_renameCache refs] using br
    rw [← expand_renameCache refs v] at next
    simp only [LeanBindings.rename,rename_annotation]
    first
    | exact .letValue annotation result (iv lookup refs) next ar' br' typed shape binder flag
    | exact .beta annotation result (iv lookup refs) next ar' br' typed shape binder flag

/-- General source induction, including repeated uses and shadowing. It
produces both parser success and the invariant needed by parent expressions. -/
theorem complete (setup : AliasSetup env) (library : ScalarSyntax.Library env)
    (scalarLibrary : ScalarConversion.Signatures env) (decisions : Branch.BooleanLibrary env)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (freshConditions : ∀ n ∈ [``bne,``Decidable,``instDecidableEqBool], ∀ r ∈ setup.rules, n ≠ r.name)
    (freshHeads : ∀ n ∈ valueHeads, ∀ r ∈ setup.rules, n ≠ r.name)
    (inputs : InputsTyped env ctx p) (locals : Locals env ctx p)
    (coverage : Conversion.Covers conv 0 (ScalarConversion.Casts setup)) (exposure : Exposure env)
    (form : Form env ctx p values source) :
    ∀ bindings : Bindings env ctx p, Matches values bindings →
      BindingTypes inputs (SourceCasts env) bindings (ScalarConversion.Casts setup) →
      ∃ piece, visit env conv exposure ctx p source bindings = some piece ∧
        Nonempty (ScalarCasts inputs piece (SourceCasts env) (ScalarConversion.Casts setup)) := by
  have embeds : ∀ scope a b, (SourceCasts env) scope a b → ScalarConversion.Casts setup scope a b :=
    fun _ _ _ h => .source h
  induction form with
  | @reference values n value selected =>
    intro bindings aligned types
    have selectedRuntime : (bindings.map Binding.source)[n]? = some value := by rw [aligned]; exact selected
    simp only [List.getElem?_map] at selectedRuntime
    cases h : bindings[n]? with
    | none => simp [h] at selectedRuntime
    | some bound => exact reference_complete types h conv exposure
  | parameter side shape same notIndex notLeft =>
    intro bindings aligned types
    have expanded := (aligned.materialize _).trans same
    exact parameter_visit_complete inputs library bindings types side conv exposure coverage shape
      (expanded.symm ▸ (side.representation inputs).property)
      (expanded.symm ▸ notIndex) (fun h => expanded.symm ▸ notLeft h)
  | index shape same =>
    intro bindings aligned types
    have expanded := (aligned.materialize _).trans same
    exact index_visit_complete inputs library bindings types conv exposure coverage shape (expanded.symm ▸ inputs.i.property)
  | @localValue raw values shape k selected notIndex notLeft notRight first =>
    intro bindings aligned types
    have mat := aligned.materialize raw
    exact local_visit_complete inputs library bindings types locals conv exposure coverage shape
      (mat.symm ▸ selected) (mat.symm ▸ notIndex) (mat.symm ▸ notLeft) (mat.symm ▸ notRight)
      (fun j hj => mat.symm ▸ first j hj)
  | literal n scope =>
    intro bindings aligned types
    exact literal_visit_complete inputs library types embeds coverage exposure scope
  | binary op left right scope ihLeft ihRight =>
    intro bindings aligned types
    obtain ⟨a,ha,⟨ta⟩⟩ := ihLeft bindings aligned types
    obtain ⟨b,hb,⟨tb⟩⟩ := ihRight bindings aligned types
    exact binary_visit_complete inputs library types embeds ta tb op coverage exposure ha hb
      ((aligned.materialize _).symm ▸ scope)
  | neg value scope ih =>
    intro bindings aligned types
    obtain ⟨a,ha,⟨ta⟩⟩ := ih bindings aligned types
    exact neg_visit_complete inputs library types embeds ta coverage exposure ha ((aligned.materialize _).symm ▸ scope)
  | @register values st r stateSame register scope =>
    intro bindings aligned types
    have stateRep : Represents (materialize bindings st) inputs.s.val := by
      rw [aligned.materialize,stateSame]
      exact inputs.s.property
    exact register_visit_complete inputs library types stateRep
      ((aligned.materialize _).symm ▸ register) conv exposure coverage ((aligned.materialize _).symm ▸ scope)
  | select value decision yes no scope ihValue ihYes ihNo =>
    intro bindings aligned types
    obtain ⟨v,hv,⟨tv⟩⟩ := ihValue bindings aligned types
    obtain ⟨a,ha,⟨ta⟩⟩ := ihYes bindings aligned types
    obtain ⟨b,hb,⟨tb⟩⟩ := ihNo bindings aligned types
    obtain ⟨vc,dc,vr,dr,pt,dt⟩ := decision.typing
    have same := tv.sourceCore.property.unique ((aligned.materialize _).symm ▸ vr)
    rw [← same] at pt dt
    exact select_visit_complete inputs types embeds tv ta tb ((aligned.materialize _).symm ▸ dr)
      pt dt (.constant library.word (by simp) rfl) library.ite library.selectFact library.selectConstructor
      coverage exposure hv ha hb ((aligned.materialize _).symm ▸ scope)
  | annotatedLiteral annotation n scope =>
    intro bindings aligned types
    obtain ⟨piece,parsed,typed,_⟩ := AnnotatedLiteral.visit_complete inputs library annotation n embeds coverage exposure scope
    exact ⟨piece,parsed,typed⟩
  | annotatedBinary op aa ab ac ad oa ob left right lr rr lt rt lf rf scope il ir =>
    intro bindings aligned types
    obtain ⟨a,ha,⟨ta⟩⟩ := il bindings aligned types
    obtain ⟨b,hb,⟨tb⟩⟩ := ir bindings aligned types
    have leftSame := ta.sourceCore.property.unique (by rw [aligned.materialize]; exact lr)
    have rightSame := tb.sourceCore.property.unique (by rw [aligned.materialize]; exact rr)
    obtain ⟨piece,parsed,typed,q⟩ := AnnotatedBinary.visit_complete_code setup scalarLibrary inputs library types ta tb
      op aa ab ac ad oa ob (leftSame.symm ▸ lt) (rightSame.symm ▸ rt)
      (leftSame.symm ▸ lf.toValueForm setup freshHeads) (rightSame.symm ▸ rf.toValueForm setup freshHeads)
      (freshHeads op.method (by cases op <;> simp [Binary.method,LexicalScalarSyntax.valueHeads]))
      coverage exposure ha hb (by rw [aligned.materialize]; exact scope)
    exact ⟨piece,parsed,typed⟩
  | annotatedNeg annotation operand value represented typed form scope ih =>
    intro bindings aligned types
    obtain ⟨a,ha,⟨ta⟩⟩ := ih bindings aligned types
    have same := ta.sourceCore.property.unique (by rw [aligned.materialize]; exact represented)
    obtain ⟨piece,parsed,result,q⟩ := AnnotatedNeg.visit_complete_code setup scalarLibrary inputs library types ta
      annotation operand (same.symm ▸ typed) (same.symm ▸ form.toValueForm setup freshHeads)
      (freshHeads ``Neg.neg (by simp [LexicalScalarSyntax.valueHeads])) coverage exposure ha
      (by rw [aligned.materialize]; exact scope)
    exact ⟨piece,parsed,result⟩
  | @annotatedSelect values rawValue rawYes rawNo valueCore leftCore rightCore
      resultAnnotation annotation operand oa ob value yes no vr ar br vt typedLeft bt vf af bf scope iv ia ib =>
    intro bindings aligned types
    obtain ⟨v,hv,⟨tv⟩⟩ := iv bindings aligned types
    obtain ⟨a,ha,⟨ta⟩⟩ := ia bindings aligned types
    obtain ⟨b,hb,⟨tb⟩⟩ := ib bindings aligned types
    have sv := tv.sourceCore.property.unique (by rw [aligned.materialize]; exact vr)
    have sa := ta.sourceCore.property.unique (by rw [aligned.materialize]; exact ar)
    have sb := tb.sourceCore.property.unique (by rw [aligned.materialize]; exact br)
    rw [← sv] at vt vf
    rw [← sa] at typedLeft af
    rw [← sb] at bt bf
    obtain ⟨_,dt⟩ := AnnotatedCondition.condition_typed decisions library.toSignatures annotation tv.value
    have dr : Represents (materialize bindings (AnnotatedCondition.nativeDecision annotation rawValue))
        (AnnotatedCondition.decision annotation tv.sourceCore.val) := by
      have mapped : materialize bindings (AnnotatedCondition.nativeDecision annotation rawValue) =
          AnnotatedCondition.nativeDecision annotation (materialize bindings rawValue) := by cases bindings <;> cases annotation <;> rfl
      rw [mapped]
      exact AnnotatedCondition.decision_represents annotation tv.sourceCore.property
    have df : ValueForm setup ctx (AnnotatedCondition.decision annotation tv.sourceCore.val)
        (.app (.const ``Decidable []) (AnnotatedCondition.condition annotation tv.sourceCore.val)) :=
      .constant rfl (freshConditions _ (by simp)) (by decide)
    have premises : AnnotatedCondition.ScalarConditions setup ctx tv.sourceCore.val
        (AnnotatedCondition.decision annotation tv.sourceCore.val) ta.sourceCore.val tb.sourceCore.val annotation :=
      ⟨decisions,operand,oa,ob,vt,vf.toValueForm setup freshHeads,dt,df,typedLeft,bt,
        af.toValueForm setup freshHeads,bf.toValueForm setup freshHeads,library.ite,
        freshConditions _ (by simp),freshHeads _ (by simp [LexicalScalarSyntax.valueHeads]),
        freshConditions _ (by simp),freshHeads _ (by simp [LexicalScalarSyntax.valueHeads])⟩
    obtain ⟨piece,parsed,typed,q⟩ := AnnotatedSelect.visit_complete_code setup library scalarLibrary inputs
      resultAnnotation annotation types tv ta tb dr premises freshEq coverage exposure hv ha hb
      (by rw [aligned.materialize]; exact scope)
    exact ⟨piece,parsed,typed⟩
  | letValue annotation resultAnnotation value next argument body bodyTyped form binder flag ihValue ihNext =>
    intro bindings aligned types
    obtain ⟨a,ha,⟨ta⟩⟩ := ihValue bindings aligned types
    obtain ⟨b,hb,⟨tb⟩⟩ := ihNext _ aligned.cons (types.cons ta)
    have argSame := ta.sourceCore.property.unique ((aligned.materialize _).symm ▸ argument)
    rw [← argSame] at form
    exact ScalarConversion.let_visit_complete annotation resultAnnotation setup library.toSignatures scalarLibrary inputs bindings ta tb
      ((aligned.under _).symm ▸ body) bodyTyped (by obtain ⟨actual,shape⟩ := form; exact ⟨actual,shape.toValueForm setup freshHeads⟩) coverage exposure ha hb binder flag
  | beta annotation resultAnnotation value next argument body bodyTyped form binder info ihValue ihNext =>
    intro bindings aligned types
    obtain ⟨a,ha,⟨ta⟩⟩ := ihValue bindings aligned types
    obtain ⟨b,hb,⟨tb⟩⟩ := ihNext _ aligned.cons (types.cons ta)
    have argSame := ta.sourceCore.property.unique ((aligned.materialize _).symm ▸ argument)
    rw [← argSame] at form
    exact ScalarConversion.beta_visit_complete annotation resultAnnotation setup library.toSignatures scalarLibrary inputs bindings ta tb
      ((aligned.under _).symm ▸ body) bodyTyped (by obtain ⟨actual,shape⟩ := form; exact ⟨actual,shape.toValueForm setup freshHeads⟩) coverage exposure ha hb binder info

theorem parse_complete (setup : AliasSetup env) (library : ScalarSyntax.Library env)
    (scalarLibrary : ScalarConversion.Signatures env) (decisions : Branch.BooleanLibrary env)
    (freshConditions : ∀ n ∈ [``bne,``Decidable,``instDecidableEqBool], ∀ r ∈ setup.rules, n ≠ r.name)
    (closed : ClosedConstantTypes env)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (freshSome : ∀ r ∈ setup.rules, ``Option.some ≠ r.name)
    (freshHeads : ∀ n ∈ valueHeads, ∀ r ∈ setup.rules, n ≠ r.name)
    (exposure : Exposure env) (inputs : InputsTyped env ctx p) (locals : Locals env ctx p) (form : Form env ctx p [] source) :
    ∃ piece, parse env setup.conversion exposure ctx p source = some piece ∧
      Nonempty (ScalarCasts inputs piece (SourceCasts env) (ScalarConversion.Casts setup)) :=
  complete setup library scalarLibrary decisions freshEq freshConditions freshHeads inputs locals
    (ScalarConversion.Casts.covered setup library.toSignatures scalarLibrary closed freshEq freshSome)
    exposure form [] aligned_nil (BindingTypes.empty inputs (SourceCasts env))

end IRComparison.WordFrontend.LexicalScalarSyntax
