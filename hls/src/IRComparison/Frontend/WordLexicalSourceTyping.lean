import IRComparison.Frontend.WordLexicalScalarCode

/-! Source typing is derived compositionally, independently of the parser.
This supplies the annotation/shape premises of the existing success induction;
no successful parse or target certificate occurs in these conditions. -/
namespace IRComparison.WordFrontend.LexicalScalarCode
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarSyntax
set_option maxHeartbeats 1800000

def Evidence (env : VEnv) (ctx : List VExpr) (raw : Lean.Expr) : Prop :=
  ∃ (core : VExpr) (annotation : WordBinder.Annotation), Represents raw core ∧
    CastTyping env 0 (SourceCasts env) ctx core annotation.core ∧
    LexicalScalarSyntax.ValueShape env ctx core annotation.core

/-- Only source values occur in this invariant. Entering a scalar let extends
it with the evidence derived for that let's initializer. -/
def ValuesTyped (env : VEnv) (ctx : List VExpr) (vs : List Value) : Prop :=
  ∀ v ∈ vs, Evidence env ctx v.source

structure ScopeTyped (env : VEnv) (ctx : List VExpr) (p : Inputs) : Prop where
  index : Evidence env ctx p.i
  left : Evidence env ctx p.x
  right : Evidence env ctx p.y
  locals : ∀ e ∈ p.locals, Evidence env ctx e

private theorem expand_literal (vs : List Value) (annotation : WordBinder.Annotation) (n : Nat) :
    expand vs (AnnotatedLiteral.native annotation n) = AnnotatedLiteral.native annotation n := by
  cases annotation <;> rfl

private theorem expand_selection (vs : List Value) (ra ca : WordBinder.Annotation) (v a b : Lean.Expr) :
    expand vs (AnnotatedCondition.scalarSource ra ca v (AnnotatedCondition.nativeDecision ca v) a b) =
      AnnotatedCondition.scalarSource ra ca (expand vs v) (AnnotatedCondition.nativeDecision ca (expand vs v))
        (expand vs a) (expand vs b) := by
  cases ra <;> cases ca <;> rfl

/-- All scalar constructors produce a value with an ordinary Word/BV32 type.
The proof follows source syntax, including lexical bindings, not a parser run. -/
theorem Source.evidence (source : Source env ctx p vs raw native code quotation)
    (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (scope : ScopeTyped env ctx p)
    (values : ValuesTyped env ctx vs) : Evidence env ctx (expand vs raw) := by
  induction source with
  | @reference vs n bound selected =>
    have eq : expand vs (.bvar n) = bound.source := by
      simp [expand,LexicalScalarSyntax.expand,LexicalScalarSyntax.sourceReference,sources,List.getElem?_map,selected,LeanBindings.substitute]
    rw [eq]
    exact values _ (List.mem_of_getElem? selected)
  | index _ same _ => exact same ▸ scope.index
  | parameter side _ same _ _ _ =>
    cases side with
    | left => exact same ▸ scope.left
    | right => exact same ▸ scope.right
  | localValue _ k _ selected _ _ _ _ => exact scope.locals _ (List.mem_of_getElem? selected)
  | literal n _ =>
    exact ⟨_,.word,by simpa only [AnnotatedLiteral.native,WordBinder.Annotation.native] using AnnotatedLiteral.represented .word n,
      AnnotatedLiteral.annotation_typed library.toSignatures .word n,
      .constant rfl (by simp [LexicalScalarSyntax.valueHeads])⟩
  | annotatedLiteral annotation n _ =>
    rw [expand_literal]
    exact ⟨_,annotation,AnnotatedLiteral.represented annotation n,
      AnnotatedLiteral.annotation_typed library.toSignatures annotation n,
      .constant rfl (by simp [LexicalScalarSyntax.valueHeads])⟩
  | @register vs st number r rn stateSame numberSame _ =>
    have same : expand vs (app ``HybridWord.State.regs [st,number]) =
        app ``HybridWord.State.regs [p.s,rn.native r] := by
      change app ``HybridWord.State.regs [expand _ _,expand _ _] = _
      rw [stateSame,numberSame]
    rw [same]
    have fn : CastTyping env 0 (SourceCasts env) ctx (.const ``HybridWord.State.regs [])
        (.forallE stateType (.forallE (.const ``Nat []) wordType)) :=
      .constant library.registerAccessor (by simp) rfl
    have a := CastTyping.application fn (inputs.hs.withCasts _)
    simp only [wordType,VExpr.inst] at a
    have result := CastTyping.application a ((rn.argument (ctx := ctx) library.toSignatures r).typed.withCasts _)
    refine ⟨_,.word,app_represents (.constant rfl) (.cons inputs.s.property (.cons (rn.argument (ctx := ctx) library.toSignatures r).represented.property .nil)),?_,.constant rfl (by simp [LexicalScalarSyntax.valueHeads])⟩
    simpa only [WordBinder.Annotation.core,wordType,VExpr.inst] using result
  | binary op left right _ il ir =>
    obtain ⟨u,ua,ur,ut,uf⟩ := (il values)
    obtain ⟨v,va,vr,vt,vf⟩ := (ir values)
    have fn := CastTyping.checkedApplication (AnnotatedBinary.header_typed library.toSignatures op .word .word .word .word) (ua.result ut)
    simp only [WordBinder.Annotation.core,wordType,VExpr.inst] at fn
    have t := CastTyping.checkedApplication fn (va.result vt)
    refine ⟨_,.word,.app (.app (AnnotatedBinary.represented op .word .word .word .word) ur) vr,?_,?_⟩
    · simpa only [WordBinder.Annotation.core,wordType,VExpr.inst] using t
    · cases op <;> exact .constant rfl (by simp [LexicalScalarSyntax.valueHeads,Binary.method])
  | @annotatedBinary vs a f lc lq b g rc rq leftCore rightCore op aa ab ac ad oa ob left right lr rr lt rt lf rf _ il ir =>
    have fn := CastTyping.checkedApplication (AnnotatedBinary.header_typed library.toSignatures op aa ab ac ad) (aa.argument (oa.result lt))
    simp only [VExpr.inst,ab.closed.instN_eq (Nat.zero_le _),ac.closed.instN_eq (Nat.zero_le _)] at fn
    have t := CastTyping.checkedApplication fn (ab.argument (ob.result rt))
    refine ⟨(.app (.app (AnnotatedBinary.header op aa ab ac ad) leftCore) rightCore),ac,?_,?_,?_⟩
    · simpa only [expand,LexicalScalarSyntax.expand,AnnotatedBinary.nativeHeader,AnnotatedBinary.nativeDictionary,
        Lean.mkApp2,Lean.mkApp4,Lean.mkApp,Lean.mkAppB,LeanBindings.substitute,WordBinder.Annotation.substitute_native,
        app,nativeWidth,List.foldl_cons,List.foldl_nil,Lean.mkApp3] using
        (Represents.app (Represents.app (AnnotatedBinary.represented op aa ab ac ad) lr) rr)
    · simpa only [VExpr.inst,ac.closed.instN_eq (Nat.zero_le _)] using t
    · cases op <;> exact .constant rfl (by simp [LexicalScalarSyntax.valueHeads,Binary.method])
  | neg value _ ih =>
    obtain ⟨v,va,vr,vt,vf⟩ := (ih values)
    have t := CastTyping.checkedApplication (AnnotatedNeg.header_typed library.toSignatures .word) (va.result vt)
    refine ⟨_,.word,.app (AnnotatedNeg.represented .word) vr,?_,.constant rfl (by simp [LexicalScalarSyntax.valueHeads])⟩
    simpa only [VExpr.inst,WordBinder.Annotation.core,wordType] using t
  | @annotatedNeg vs v f vc vq valueCore annotation operand value rep typed form _ ih =>
    have t := CastTyping.checkedApplication (AnnotatedNeg.header_typed library.toSignatures annotation)
      (annotation.argument (operand.result typed))
    refine ⟨.app (AnnotatedNeg.header annotation) valueCore,annotation,?_,?_,.constant rfl (by simp [LexicalScalarSyntax.valueHeads])⟩
    · cases annotation
      · exact .app (AnnotatedNeg.represented .word) rep
      · exact .app (AnnotatedNeg.represented .bitvec) rep
    · simpa only [VExpr.inst,annotation.closed.instN_eq (Nat.zero_le _)] using t
  | select value decision yes no _ iv ia ib =>
    obtain ⟨v,va,vr,vt,vf⟩ := (iv values)
    obtain ⟨a,aa,ar,at_,af⟩ := (ia values)
    obtain ⟨b,ba,br,bt,bf⟩ := (ib values)
    obtain ⟨vc,dc,vrep,drep,ct,dt⟩ := decision.typing
    have eq := vrep.unique vr
    subst vc
    have t := Branch.ite_typed (.constant library.word (by simp) rfl) (by trivial)
      ct dt
      (aa.result at_) (ba.result bt) library.ite
    exact ⟨_,.word,Branch.Select.source_represents vr drep ar br,t,
      .constant rfl (by simp [LexicalScalarSyntax.valueHeads])⟩
  | booleanSelect value yes no _ iv ia ib =>
    obtain ⟨v,va,vr,vt,vf⟩ := (iv values)
    obtain ⟨a,aa,ar,at_,af⟩ := (ia values)
    obtain ⟨b,ba,br,bt,bf⟩ := (ib values)
    obtain ⟨ct,dt⟩ := decisions.condition_typed library.toSignatures (va.result vt)
    have t := Branch.ite_typed (.constant library.word (by simp) rfl) (by trivial) ct dt
      (aa.result at_) (ba.result bt) library.ite
    exact ⟨_,.word,Branch.Select.source_represents vr (Branch.booleanDecision_represents vr) ar br,t,
      .constant rfl (by simp [LexicalScalarSyntax.valueHeads])⟩
  | annotatedSelect resultAnnotation annotation operand oa ob value yes no vr ar br vt at_ bt vf af bf _ iv ia ib =>
    obtain ⟨ct,dt⟩ := AnnotatedCondition.condition_typed decisions library.toSignatures annotation (operand.result vt)
    have t := Branch.ite_typed (resultAnnotation.type_typed library.toSignatures) resultAnnotation.closed ct dt
      (resultAnnotation.argument (oa.result at_)) (resultAnnotation.argument (ob.result bt)) library.ite
    refine ⟨_,resultAnnotation,?_,t,.constant rfl (by simp [LexicalScalarSyntax.valueHeads])⟩
    rw [expand_selection]
    exact AnnotatedCondition.scalarSource_represents resultAnnotation annotation vr (AnnotatedCondition.decision_represents annotation vr) ar br
  | letValue annotation resultAnnotation value next argument body bodyTyped form binder flag iv ib
  | beta annotation resultAnnotation value next argument body bodyTyped form binder info iv ib =>
    obtain ⟨arg,aa,ar,at_,af⟩ := (iv values)
    have eq := argument.unique ar
    rw [eq] at argument
    have fn := CastTyping.lambda ((annotation.type_typed library.toSignatures).withCasts (SourceCasts env)) bodyTyped
    have t := CastTyping.checkedApplication fn (annotation.argument (aa.result at_))
    refine ⟨.app (.lam annotation.core _) arg,resultAnnotation,?_,?_,.beta annotation resultAnnotation bodyTyped⟩
    · simp only [expand,LexicalScalarSyntax.expand,LeanBindings.substitute,WordBinder.Annotation.substitute_native]
      first
      | exact .letE annotation.represented argument body
      | exact .app (.lam annotation.represented body) argument
    · simpa only [resultAnnotation.closed.instN_eq (Nat.zero_le _)] using t

/-- Typing of a retained variable uses its actual annotation in the context. -/
theorem Evidence.variable (annotation : WordBinder.Annotation)
    (selected : Lean4Lean.Lookup ctx n annotation.core) : Evidence env ctx (.bvar n) :=
  ⟨_,annotation,.bvar,.bvar selected,.bound⟩

private theorem head_lift (value : VExpr) (k : Nat) :
    LeanTypeReduction.constantHead (value.liftN 1 k) = LeanTypeReduction.constantHead value := by
  induction value generalizing k <;> simp_all [VExpr.liftN,LeanTypeReduction.constantHead]

theorem valueShape_lift (shape : LexicalScalarSyntax.ValueShape env ctx value type)
    (closed : ClosedConstantTypes env) (binder : VExpr) :
    LexicalScalarSyntax.ValueShape env (binder::ctx) value.lift type.lift := by
  cases shape with
  | bound => exact .bound
  | constant head allowed => exact .constant ((head_lift _ 0).trans head) allowed
  | @beta body arg domain result typed =>
    have lifted : CastTyping env 0 (SourceCasts env) (domain.core::binder::ctx)
        (body.liftN 1 1) result.core := by
      simpa only [domain.closed.liftN_eq (Nat.zero_le _),result.closed.liftN_eq (Nat.zero_le _)] using
        typed.weakN closed SourceCasts.closed (Ctx.LiftN.succ Ctx.LiftN.one)
    simpa only [VExpr.lift,VExpr.liftN,domain.closed.liftN_eq (Nat.zero_le _),result.closed.liftN_eq (Nat.zero_le _)] using
      (LexicalScalarSyntax.ValueShape.beta (arg := arg.lift) domain result lifted)

theorem Evidence.lift (value : Evidence env ctx raw) (closed : ClosedConstantTypes env) (ty : VExpr) :
    Evidence env (ty::ctx) (LeanBindings.rename Nat.succ raw) := by
  obtain ⟨core,annotation,rep,typed,shape⟩ := value
  refine ⟨core.lift,annotation,rep.lift,?_,?_⟩
  · simpa only [annotation.closed.lift_eq] using typed.lift closed SourceCasts.closed ty
  · simpa only [annotation.closed.lift_eq] using valueShape_lift shape closed ty

private theorem head_instantiate {term : VExpr}
    (head : LeanTypeReduction.constantHead term = some (name,levels)) (value : VExpr) (index : Nat) :
    LeanTypeReduction.constantHead (term.inst value index) = some (name,levels) := by
  induction term generalizing index with
  | bvar | sort | lam | forallE => simp [LeanTypeReduction.constantHead] at head
  | const => exact head
  | app f a ihf iha => exact ihf head index

/-- Typed substitution crosses any number of retained binders. The removed
binder can be a State, scalar, or other closed source type; no limit is put on
State/read/loop nesting. The existing context substitution determines which
binder is removed. -/
private theorem lookup_shape_inst (found : Lookup before n ty)
    (closed : ClosedConstantTypes env)
    (shape : LexicalScalarSyntax.ValueShape env base value domain)
    (substitution : Ctx.InstN base value domain k before after) :
    LexicalScalarSyntax.ValueShape env after ((VExpr.bvar n).inst value k) (ty.inst value k) := by
  induction substitution generalizing n ty with
  | zero =>
    cases found with
    | zero => simpa [VExpr.inst,VExpr.inst_lift] using shape
    | succ found => exact .bound
  | @succ k before after binder sub ih =>
    cases found with
    | zero => exact .bound
    | succ found =>
      simp only [VExpr.inst]
      simp
      rw [Nat.add_comm, ← VExpr.liftN_instN_lo (hj := Nat.zero_le _)]
      exact valueShape_lift (ih found) closed _

theorem _root_.IRComparison.WordFrontend.LexicalScalarSyntax.ValueShape.instantiateAt
    (shape : LexicalScalarSyntax.ValueShape env before core ty)
    (typed : CastTyping env 0 (SourceCasts env) before core ty)
    (closed : ClosedConstantTypes env)
    (argTyped : CastTyping env 0 (SourceCasts env) base arg domain)
    (argShape : LexicalScalarSyntax.ValueShape env base arg domain)
    (substitution : Ctx.InstN base arg domain k before after) :
    LexicalScalarSyntax.ValueShape env after (core.inst arg k) (ty.inst arg k) := by
  cases shape with
  | bound => cases typed with
    | bvar found => exact lookup_shape_inst found closed argShape substitution
  | constant head allowed => exact .constant (head_instantiate head arg k) allowed
  | @beta body actualArg inner result innerTyped =>
    have moved := innerTyped.instN closed SourceCasts.closed argTyped substitution.succ
    simp only [inner.closed.instN_eq (Nat.zero_le _),result.closed.instN_eq (Nat.zero_le _)] at moved
    simpa only [VExpr.inst,inner.closed.instN_eq (Nat.zero_le _),result.closed.instN_eq (Nat.zero_le _)] using
      (LexicalScalarSyntax.ValueShape.beta (arg := actualArg.inst arg k) inner result moved)
/-- Preserve scalar evidence when the removed argument is below arbitrary
State, read-result, and loop binders. -/
theorem Evidence.instantiateAt
    (source : Evidence env before raw)
    (closed : ClosedConstantTypes env)
    (argument : Represents value arg)
    (argTyped : CastTyping env 0 (SourceCasts env) base arg domain)
    (argShape : LexicalScalarSyntax.ValueShape env base arg domain)
    (substitution : Ctx.InstN base arg domain k before after) :
    Evidence env after (LeanBindings.substitute (argumentAt value k) raw) := by
  obtain ⟨core,result,rep,typed,shape⟩ := source
  refine ⟨core.inst arg k,result,rep.instantiate_at argument k,?_,?_⟩
  · simpa only [result.closed.instN_eq (Nat.zero_le _)] using
      typed.instN closed SourceCasts.closed argTyped substitution
  · simpa only [result.closed.instN_eq (Nat.zero_le _)] using
      shape.instantiateAt typed closed argTyped argShape substitution

/-- Exact typed substitution is shared by opening and closing scalar binders.
Alias-convertible arguments must first select their actual annotation; this
lemma does not assert false preservation of an inferred Word spelling. -/
theorem Evidence.instantiateExact (domain : WordBinder.Annotation)
    (source : Evidence env (domain.core::ctx) raw)
    (closed : ClosedConstantTypes env)
    (argument : Represents value arg)
    (argTyped : CastTyping env 0 (SourceCasts env) ctx arg domain.core)
    (argShape : LexicalScalarSyntax.ValueShape env ctx arg domain.core) :
    Evidence env ctx (LeanBindings.instantiate value raw) :=
  source.instantiateAt closed argument argTyped argShape Ctx.InstN.zero

/-- The typed form of substitution retains the known inferred annotation. -/
theorem _root_.IRComparison.WordFrontend.LexicalScalarSyntax.ValueShape.instantiateExact
    (domain : WordBinder.Annotation)
    (shape : LexicalScalarSyntax.ValueShape env (domain.core::ctx) core ty)
    (typed : CastTyping env 0 (SourceCasts env) (domain.core::ctx) core ty)
    (closed : ClosedConstantTypes env)
    (argTyped : CastTyping env 0 (SourceCasts env) ctx arg domain.core)
    (argShape : LexicalScalarSyntax.ValueShape env ctx arg domain.core) :
    LexicalScalarSyntax.ValueShape env ctx (core.inst arg) (ty.inst arg) :=
  shape.instantiateAt typed closed argTyped argShape Ctx.InstN.zero

/-- A value-head condition alone does not determine its inferred annotation.
For a substituted bound variable, use the argument's actual value form. -/
theorem _root_.IRComparison.WordFrontend.LexicalScalarSyntax.ValueShape.instantiateSome
    (domain : WordBinder.Annotation)
    (shape : LexicalScalarSyntax.ValueShape env (domain.core::ctx) core ty)
    (closed : ClosedConstantTypes env)
    (argTyped : CastTyping env 0 (SourceCasts env) ctx arg domain.core)
    (argShape : LexicalScalarSyntax.ValueShape env ctx arg domain.core) :
    ∃ actual : WordBinder.Annotation, LexicalScalarSyntax.ValueShape env ctx (core.inst arg) actual.core := by
  cases shape with
  | @bound n ty =>
    cases n with
    | zero => exact ⟨domain,by simpa [VExpr.inst,VExpr.instVar] using argShape⟩
    | succ n => exact ⟨.word,.bound⟩
  | constant head allowed => exact ⟨.word,.constant (head_instantiate head arg 0) allowed⟩
  | @beta body actualArg inner result innerTyped =>
    have moved := innerTyped.instN closed SourceCasts.closed argTyped (Ctx.InstN.succ Ctx.InstN.zero)
    simp only [inner.closed.instN_eq (Nat.zero_le _),result.closed.instN_eq (Nat.zero_le _)] at moved
    refine ⟨result,?_⟩
    simpa only [VExpr.inst,inner.closed.instN_eq (Nat.zero_le _)] using
      (LexicalScalarSyntax.ValueShape.beta (arg := actualArg.inst arg) inner result moved)

theorem ScopeTyped.lift (scope : ScopeTyped env ctx p) (closed : ClosedConstantTypes env) (ty : VExpr) :
    ScopeTyped env (ty::ctx) p.lift := by
  refine ⟨scope.index.lift closed ty,scope.left.lift closed ty,scope.right.lift closed ty,?_⟩
  intro e h
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
  exact (scope.locals v hv).lift closed ty

theorem ScopeTyped.nextWord (scope : ScopeTyped env ctx p) (closed : ClosedConstantTypes env)
    (annotation : WordBinder.Annotation) :
    ScopeTyped env (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} := by
  have lifted := scope.lift closed annotation.core
  refine ⟨lifted.index,lifted.left,lifted.right,?_⟩
  intro e h
  rcases List.mem_cons.mp h with rfl | h
  · apply Evidence.variable annotation
    simpa only [annotation.closed.lift_eq] using (Lean4Lean.Lookup.zero (Γ := ctx) (ty := annotation.core))
  · exact lifted.locals e h

/-- A new State changes the current state reference, but retains all scalar
values, including values saved before a write. -/
theorem ScopeTyped.nextState (scope : ScopeTyped env ctx p) (closed : ClosedConstantTypes env) :
    ScopeTyped env (stateType::ctx) {p.lift with s := .bvar 0} := by
  have lifted := scope.lift closed stateType
  exact ⟨lifted.index,lifted.left,lifted.right,lifted.locals⟩

theorem ScopeTyped.forStatic (scope : ScopeTyped env ctx p) (closed : ClosedConstantTypes env) :
    ScopeTyped env (stateType::wordType::ctx) (For.parameters p) :=
  (scope.nextWord closed .word).nextState closed

/-- Nat loop counters are retained at their actual BV32 annotation. No bound
on the run-time iteration count is used to type the source expression. -/
theorem Evidence.naturalIndex (library : Arithmetic.Signatures env)
    (registered : env.constants ``BitVec.ofNat = some ⟨0,NaturalScope.ofNatSignature⟩)
    (represented : Represents n core) (typed : DirectTyping env 0 ctx core natType) :
    Evidence env ctx (NaturalScope.nativeIndex n) :=
  ⟨_,.bitvec,NaturalScope.index_represents represented,
    (NaturalScope.index_inferred library registered typed).mono (fun _ _ _ h => .arithmetic h),
    .constant rfl (by simp [LexicalScalarSyntax.valueHeads])⟩

theorem ScopeTyped.withLocal (scope : ScopeTyped env ctx p) (value : Evidence env ctx raw) :
    ScopeTyped env ctx {p with locals := raw::p.locals} := by
  refine ⟨scope.index,scope.left,scope.right,?_⟩
  intro e h
  rcases List.mem_cons.mp h with rfl | h
  · exact value
  · exact scope.locals e h

theorem ScopeTyped.naturalLoop (scope : ScopeTyped env ctx p) (closed : ClosedConstantTypes env)
    (library : Arithmetic.Signatures env) (loops : NaturalLoop.Signatures env) (kind : NaturalLoop.Kind) :
    ScopeTyped env (kind.context ctx) (kind.parameters p) := by
  cases kind with
  | forIn =>
    exact ((scope.lift closed natType).nextState closed).withLocal
      (.naturalIndex library loops.ofNat .bvar (.bvar (.succ .zero)))
  | fold =>
    exact ((scope.nextState closed).lift closed natType).withLocal
      (.naturalIndex library loops.ofNat .bvar (.bvar .zero))

theorem ScopeTyped.initial : ScopeTyped env context parameters := by
  refine ⟨Evidence.variable .word ?_,Evidence.variable .word ?_,Evidence.variable .word ?_,by simp [parameters]⟩
  · exact .succ (.succ (.succ .zero))
  · exact .succ (.succ .zero)
  · exact .succ .zero

/-- Annotation and value-shape premises are obtained from the children. This
is a derived source rule; it does not invoke the compiler or assume success. -/
theorem Source.binaryInferred (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (typing : ScopeTyped env ctx p) (values : ValuesTyped env ctx vs)
    (op : Binary) (aa ab ac ad : WordBinder.Annotation)
    (left : Source env ctx p vs a f lc lq) (right : Source env ctx p vs b g rc rq)
    (separated : Separated p (expand vs (Lean.mkApp2 (AnnotatedBinary.nativeHeader op aa ab ac ad) a b))) :
    Source env ctx p vs (Lean.mkApp2 (AnnotatedBinary.nativeHeader op aa ab ac ad) a b)
      (fun i x y s ls => (f i x y s ls).bind (fun u => (g i x y s ls).bind (fun v => some (binaryValue op u v))))
      (binaryCode op lc rc) (app op.target [lq,rq]) := by
  obtain ⟨u,ua,ur,ut,uf⟩ := left.evidence library decisions inputs typing values
  obtain ⟨v,va,vr,vt,vf⟩ := right.evidence library decisions inputs typing values
  exact .annotatedBinary op aa ab ac ad ua va left right ur vr ut vt uf vf separated

theorem Source.negInferred (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (typing : ScopeTyped env ctx p) (values : ValuesTyped env ctx vs)
    (annotation : WordBinder.Annotation) (value : Source env ctx p vs v f vc vq)
    (separated : Separated p (expand vs (.app (AnnotatedNeg.nativeHeader annotation) v))) :
    Source env ctx p vs (.app (AnnotatedNeg.nativeHeader annotation) v)
      (fun i x y s ls => (f i x y s ls).bind (fun v => some (-v))) (.neg vc) (app ``HybridWord.Expr.neg [vq]) := by
  obtain ⟨v,va,vr,vt,vf⟩ := value.evidence library decisions inputs typing values
  exact .annotatedNeg annotation va value vr vt vf separated

theorem Source.selectInferred (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (typing : ScopeTyped env ctx p) (values : ValuesTyped env ctx vs)
    (resultAnnotation annotation : WordBinder.Annotation)
    (value : Source env ctx p vs v f vc vq) (yes : Source env ctx p vs a g ac aq) (no : Source env ctx p vs b h bc bq)
    (separated : Separated p (expand vs (AnnotatedCondition.scalarSource resultAnnotation annotation v
      (AnnotatedCondition.nativeDecision annotation v) a b))) :
    Source env ctx p vs (AnnotatedCondition.scalarSource resultAnnotation annotation v (AnnotatedCondition.nativeDecision annotation v) a b)
      (fun i x y s ls => (f i x y s ls).bind (fun v => if v != 0 then g i x y s ls else h i x y s ls))
      (.select vc ac bc) (app ``HybridWord.Expr.select [vq,aq,bq]) := by
  obtain ⟨v,va,vr,vt,vf⟩ := value.evidence library decisions inputs typing values
  obtain ⟨a,aa,ar,at_,af⟩ := yes.evidence library decisions inputs typing values
  obtain ⟨b,ba,br,bt,bf⟩ := no.evidence library decisions inputs typing values
  exact .annotatedSelect resultAnnotation annotation va aa ba value yes no vr ar br vt at_ bt vf af bf separated

/-- The source binding environment obeys the same substitution law as the
runtime cache, but contains no parsed artifacts. -/
theorem expand_cons (value : Value) (vs : List Value) (body : Lean.Expr) :
    expand (value::vs) body = LeanBindings.instantiate value.source (under vs body) :=
  LexicalScalarSyntax.expand_cons value.source (sources vs) body

/-- Lift only the source component of a proof-side cached value. The code
is not executed here: this environment is used to derive source typing. -/
def Value.liftSource (value : Value) : Value :=
  {value with source := LeanBindings.rename Nat.succ value.source}

/-- Keep the newest variable as a cached reference as well, so a body proof
can use `Source.reference` both before and after substitution. -/
def openValues (vs : List Value) : List Value :=
  ⟨.bvar 0,fun _ _ _ _ ls => ls[0]?,.local 0,
    app ``HybridWord.Expr.local [(ClosedTerm.bindingIndex 0).val]⟩ :: vs.map Value.liftSource

/-- An unbound reference passes the cache unchanged in length, but opening a
binder adds one variable to its outer context. Cached references keep their
positions. This is not a new source language or a run-time environment. -/
def openBody (vs : List Value) (body : Lean.Expr) : Lean.Expr :=
  LeanBindings.rename (fun n => if n < vs.length + 1 then n else n + 1) body

theorem expand_open (vs : List Value) (body : Lean.Expr) :
    expand (openValues vs) (openBody vs body) = under vs body := by
  unfold expand under LexicalScalarSyntax.expand LexicalScalarSyntax.under openBody
  rw [LeanBindings.substitute_rename]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp_apply,LeanBindings.underSubst]
    by_cases bound : n < vs.length
    · simp [openValues,sources,Value.liftSource,LexicalScalarSyntax.sourceReference,bound]
    · have missingNext : vs[n+1]? = none := List.getElem?_eq_none (by omega)
      simp [openValues,sources,LexicalScalarSyntax.sourceReference,
        missingNext,bound,LeanBindings.rename]
      congr 1
      omega

theorem ValuesTyped.open (values : ValuesTyped env ctx vs)
    (closed : ClosedConstantTypes env) (annotation : WordBinder.Annotation) :
    ValuesTyped env (annotation.core::ctx) (openValues vs) := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · apply Evidence.variable annotation
    simpa only [annotation.closed.lift_eq] using
      (Lean4Lean.Lookup.zero (Γ := ctx) (ty := annotation.core))
  · obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
    exact (values old oldMember).lift closed annotation.core

/-- The binder connection needs source typing of the open body, not a second
code-generation derivation for it. Both interfaces below share this proof. -/
theorem Source.bindingEvidenceOfEvidence (library : ScopedSyntax.Library env)
    (inputs : InputsTyped env ctx p) (typing : ScopeTyped env ctx p) (values : ValuesTyped env ctx vs)
    (annotation : WordBinder.Annotation)
    (value : Source env ctx p vs v f vc vq)
    (next : Source env ctx p (⟨expand vs v,f,vc,vq⟩::vs) rest g bc bq)
    (openTyped : Evidence env (annotation.core::ctx) (under vs rest)) :
    ∃ (arg body : VExpr) (resultAnnotation : WordBinder.Annotation),
      Represents (expand vs v) arg ∧ Represents (under vs rest) body ∧
      CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core ∧
      ∃ actual : WordBinder.Annotation, LexicalScalarSyntax.ValueShape env ctx (body.inst arg) actual.core := by
  obtain ⟨arg,aa,ar,at_,af⟩ := value.evidence library.scalars library.decisions inputs typing values
  have extended : ValuesTyped env ctx (⟨expand vs v,f,vc,vq⟩::vs) := by
    intro bound member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨arg,aa,ar,at_,af⟩
    · exact values bound member
  obtain ⟨body,result,br,bt,bf⟩ := openTyped
  obtain ⟨reduced,actual,rr,rt,rf⟩ := next.evidence library.scalars library.decisions inputs typing extended
  have substituted : Represents (expand (⟨expand vs v,f,vc,vq⟩::vs) rest) (body.inst arg) := by
    rw [expand_cons]
    exact br.instantiate ar
  have same := rr.unique substituted
  exact ⟨arg,body,result,ar,br,bt,actual,same ▸ rf⟩

/-- Derive a lexical binder's typing from its open source body, and its
post-substitution shape from the recursive child. Neither premise mentions a
parser run. The actual result annotation may change from Word to BitVec 32
(or conversely) when a bound value is substituted. -/
theorem Source.bindingEvidence (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : ScopeTyped env ctx p) (values : ValuesTyped env ctx vs)
    (annotation : WordBinder.Annotation)
    (value : Source env ctx p vs v f vc vq)
    (next : Source env ctx p (⟨expand vs v,f,vc,vq⟩::vs) rest g bc bq)
    (openBody : Source env (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
      [] (under vs rest) bodyF bodyCode bodyQuote) :
    ∃ (arg body : VExpr) (resultAnnotation : WordBinder.Annotation),
      Represents (expand vs v) arg ∧ Represents (under vs rest) body ∧
      CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core ∧
      ∃ actual : WordBinder.Annotation, LexicalScalarSyntax.ValueShape env ctx (body.inst arg) actual.core := by
  apply value.bindingEvidenceOfEvidence library inputs typing values annotation next
  simpa only [expand,sources,List.map_nil,LexicalScalarSyntax.expand_nil] using
    openBody.evidence library.scalars library.decisions
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (typing.nextWord closed annotation) (by intro v h; cases h)

/-- The ordinary scalar let rule with no separately supplied typing or
value-shape proof. It composes the existing source-success induction. -/
theorem Source.letInferred (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : ScopeTyped env ctx p) (values : ValuesTyped env ctx vs)
    (annotation : WordBinder.Annotation)
    (value : Source env ctx p vs v f vc vq)
    (next : Source env ctx p (⟨expand vs v,f,vc,vq⟩::vs) rest g bc bq)
    (openBody : Source env (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
      [] (under vs rest) bodyF bodyCode bodyQuote)
    (binder : Lean.Name) (flag : Bool) :
    Source env ctx p vs (.letE binder annotation.native v rest flag) g bc bq := by
  obtain ⟨arg,body,result,ar,br,bt,form⟩ := value.bindingEvidence library closed inputs typing values annotation next openBody
  exact .letValue annotation result value next ar br bt form binder flag

/-- Immediate lambda application uses the same open-body derivation as let. -/
theorem Source.betaInferred (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : ScopeTyped env ctx p) (values : ValuesTyped env ctx vs)
    (annotation : WordBinder.Annotation)
    (value : Source env ctx p vs v f vc vq)
    (next : Source env ctx p (⟨expand vs v,f,vc,vq⟩::vs) rest g bc bq)
    (openBody : Source env (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
      [] (under vs rest) bodyF bodyCode bodyQuote)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    Source env ctx p vs (.app (.lam binder annotation.native rest info) v) g bc bq := by
  obtain ⟨arg,body,result,ar,br,bt,form⟩ := value.bindingEvidence library closed inputs typing values annotation next openBody
  exact .beta annotation result value next ar br bt form binder info

/-- Open and substituted bodies can now use the same reference-based source
construction. Captured scalar values are lifted once by the common lemma. -/
theorem Source.bindingEvidenceOpen (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : ScopeTyped env ctx p) (values : ValuesTyped env ctx vs)
    (annotation : WordBinder.Annotation)
    (value : Source env ctx p vs v f vc vq)
    (next : Source env ctx p (⟨expand vs v,f,vc,vq⟩::vs) rest g bc bq)
    (body : Source env (annotation.core::ctx) p.lift
      (openValues vs) (openBody vs rest) bodyF bodyCode bodyQuote) :
    ∃ (arg body : VExpr) (resultAnnotation : WordBinder.Annotation),
      Represents (expand vs v) arg ∧ Represents (under vs rest) body ∧
      CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core ∧
      ∃ actual : WordBinder.Annotation, LexicalScalarSyntax.ValueShape env ctx (body.inst arg) actual.core := by
  apply value.bindingEvidenceOfEvidence library inputs typing values annotation next
  rw [← expand_open]
  exact body.evidence library.scalars library.decisions
    (inputs.lift closed annotation.core)
    (typing.lift closed annotation.core) (values.open closed annotation)

theorem Source.letOpen (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : ScopeTyped env ctx p) (values : ValuesTyped env ctx vs)
    (annotation : WordBinder.Annotation)
    (value : Source env ctx p vs v f vc vq)
    (next : Source env ctx p (⟨expand vs v,f,vc,vq⟩::vs) rest g bc bq)
    (body : Source env (annotation.core::ctx) p.lift
      (openValues vs) (openBody vs rest) bodyF bodyCode bodyQuote)
    (binder : Lean.Name) (flag : Bool) :
    Source env ctx p vs (.letE binder annotation.native v rest flag) g bc bq := by
  obtain ⟨arg,body,result,ar,br,bt,form⟩ := value.bindingEvidenceOpen library closed inputs typing values annotation next body
  exact .letValue annotation result value next ar br bt form binder flag

theorem Source.betaOpen (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : ScopeTyped env ctx p) (values : ValuesTyped env ctx vs)
    (annotation : WordBinder.Annotation)
    (value : Source env ctx p vs v f vc vq)
    (next : Source env ctx p (⟨expand vs v,f,vc,vq⟩::vs) rest g bc bq)
    (body : Source env (annotation.core::ctx) p.lift
      (openValues vs) (openBody vs rest) bodyF bodyCode bodyQuote)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    Source env ctx p vs (.app (.lam binder annotation.native rest info) v) g bc bq := by
  obtain ⟨arg,body,result,ar,br,bt,form⟩ := value.bindingEvidenceOpen library closed inputs typing values annotation next body
  exact .beta annotation result value next ar br bt form binder info

end IRComparison.WordFrontend.LexicalScalarCode

namespace IRComparison.WordFrontend.LexicalScalarSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarSyntax

/-- Static register names in the existing syntax judgment. This condition
mentions source notation only, not a parser result or generated expression.
Other static numerical expressions (notably signed loop bounds) have their
own existing judgment; this predicate does not redefine the input language. -/
def StaticRegisters : Lean.Expr → Prop
  | .app (.app (.const ``HybridWord.State.regs []) st) r =>
      Nonempty (NatNotation.View r) ∧ StaticRegisters st
  | .app fn arg => StaticRegisters fn ∧ StaticRegisters arg
  | .lam _ _ body _ => StaticRegisters body
  | .letE _ _ value body _ => StaticRegisters value ∧ StaticRegisters body
  | .mdata _ value => StaticRegisters value
  | .proj _ _ value => StaticRegisters value
  | _ => True

private theorem expand_nat_notation (values : List Lean.Expr) (form : NatNotation) (n : Nat) :
    expand values (form.native n) = form.native n := by
  cases form <;> rfl

/-- A local occurrence is either a cached lexical variable or outside the
cache. This is a scope fact over source syntax, not a lookup success premise. -/
private theorem cached_or_unbound (vs : List LexicalScalarCode.Value) (raw : Lean.Expr) :
    (∃ index value, raw = .bvar index ∧ vs[index]? = some value) ∨
      ScalarEnvironment.Unbound raw vs.length := by
  cases raw with
  | bvar index =>
    cases found : vs[index]? with
    | some value => exact Or.inl ⟨index,value,rfl,found⟩
    | none =>
      apply Or.inr
      intro n same
      cases same
      exact List.getElem?_eq_none_iff.mp found
  | _ => exact Or.inr (by intro n same; cases same)

/-- Reconstruct source computation and code from the older, computation-free
syntax judgment. One induction handles all nested lets and beta applications;
no generated code, Source derivation, or parser success is an input condition.
The register condition is independent static notation, not compiler acceptance. -/
theorem Form.constructSource (form : Form env ctx p values raw)
    (static : StaticRegisters raw) (vs : List LexicalScalarCode.Value)
    (aligned : LexicalScalarCode.sources vs = values) :
    ∃ native code quotation, LexicalScalarCode.Source env ctx p vs raw native code quotation := by
  induction form generalizing vs with
  | @reference values index value selected =>
    have found : (vs.map LexicalScalarCode.Value.source)[index]? = some value := by
      change (LexicalScalarCode.sources vs)[index]? = some value
      rw [aligned]; exact selected
    simp only [List.getElem?_map] at found
    cases h : vs[index]? with
    | none => simp [h] at found
    | some bound => exact ⟨_,_,_,.reference h⟩
  | @index raw values shape same =>
    rcases cached_or_unbound vs raw with ⟨index,value,rfl,found⟩ | outside
    · exact ⟨_,_,_,.reference found⟩
    · exact ⟨_,_,_,.index shape (by simpa only [LexicalScalarCode.expand,aligned] using same) outside⟩
  | @parameter raw values side shape same ni nl =>
    rcases cached_or_unbound vs raw with ⟨index,value,rfl,found⟩ | outside
    · exact ⟨_,_,_,.reference found⟩
    · exact ⟨_,_,_,.parameter side shape (by simpa only [LexicalScalarCode.expand,aligned] using same) outside ni nl⟩
  | @localValue raw values shape k selected ni nl nr first =>
    rcases cached_or_unbound vs raw with ⟨index,value,rfl,found⟩ | outside
    · exact ⟨_,_,_,.reference found⟩
    · refine ⟨_,_,_,.localValue shape k outside ?_ ?_ ?_ ?_ ?_⟩
      all_goals simpa only [LexicalScalarCode.expand,aligned] using ‹_›
  | literal n scope => exact ⟨_,_,_,.literal n scope⟩
  | @binary values a b op left right scope il ir =>
    have children : StaticRegisters a ∧ StaticRegisters b := by
      cases op <;> exact ⟨static.1.2,static.2⟩
    obtain ⟨f,ac,aq,a⟩ := il children.1 vs aligned
    obtain ⟨g,bc,bq,b⟩ := ir children.2 vs aligned
    exact ⟨_,_,_,.binary op a b (by simpa only [LexicalScalarCode.expand,aligned] using scope)⟩
  | @neg values v value scope ih =>
    have child : StaticRegisters v := by
      exact static.2
    obtain ⟨f,c,q,value⟩ := ih child vs aligned
    exact ⟨_,_,_,.neg value (by simpa only [LexicalScalarCode.expand,aligned] using scope)⟩
  | @register values st r stateSame register scope =>
    change Nonempty (NatNotation.View r) ∧ StaticRegisters st at static
    obtain ⟨view⟩ := static.1
    refine ⟨_,_,_,.register view.value view.form ?_ ?_ ?_⟩
    · simpa only [LexicalScalarCode.expand,aligned] using stateSame
    · simp only [LexicalScalarCode.expand,aligned,view.shape,expand_nat_notation]
    · simpa only [LexicalScalarCode.expand,aligned] using scope
  | @select values v d a b value decision yes no scope iv ia ib =>
    have children : StaticRegisters v ∧ StaticRegisters a ∧ StaticRegisters b := by
      have condition : StaticRegisters (Branch.nativeCondition v) := static.1.1.1.2
      exact ⟨condition.1.2.1.2,static.1.2,static.2⟩
    obtain ⟨f,vc,vq,v⟩ := iv children.1 vs aligned
    obtain ⟨g,ac,aq,a⟩ := ia children.2.1 vs aligned
    obtain ⟨h,bc,bq,b⟩ := ib children.2.2 vs aligned
    refine ⟨_,_,_,.select v ?_ a b ?_⟩
    · simpa only [LexicalScalarCode.expand,aligned] using decision
    · simpa only [LexicalScalarCode.expand,aligned] using scope
  | annotatedLiteral annotation n scope => exact ⟨_,_,_,.annotatedLiteral annotation n scope⟩
  | @annotatedBinary values a b leftCore rightCore op aa ab ac ad oa ob left right lr rr lt rt lf rf scope il ir =>
    have children : StaticRegisters a ∧ StaticRegisters b := by
      cases op <;> exact ⟨static.1.2,static.2⟩
    obtain ⟨f,lc,lq,left⟩ := il children.1 vs aligned
    obtain ⟨g,rc,rq,right⟩ := ir children.2 vs aligned
    refine ⟨_,_,_,.annotatedBinary op aa ab ac ad oa ob left right ?_ ?_ lt rt lf rf ?_⟩
    all_goals simpa only [LexicalScalarCode.expand,aligned] using ‹_›
  | @annotatedNeg values v valueCore annotation operand value rep typed shape scope ih =>
    have child : StaticRegisters v := by cases annotation <;> exact static.2
    obtain ⟨f,c,q,value⟩ := ih child vs aligned
    refine ⟨_,_,_,.annotatedNeg annotation operand value ?_ typed shape ?_⟩
    all_goals simpa only [LexicalScalarCode.expand,aligned] using ‹_›
  | @annotatedSelect values v a b valueCore leftCore rightCore ra ca oa ob oc value yes no vr ar br vt at_ bt vf af bf scope iv ia ib =>
    have children : StaticRegisters v ∧ StaticRegisters a ∧ StaticRegisters b := by
      cases ra <;> cases ca <;> exact ⟨static.1.1.1.2.1.2.1.2,static.1.2,static.2⟩
    obtain ⟨f,vc,vq,value⟩ := iv children.1 vs aligned
    obtain ⟨g,ac,aq,yes⟩ := ia children.2.1 vs aligned
    obtain ⟨h,bc,bq,no⟩ := ib children.2.2 vs aligned
    refine ⟨_,_,_,.annotatedSelect ra ca oa ob oc value yes no ?_ ?_ ?_ vt at_ bt vf af bf ?_⟩
    all_goals simpa only [LexicalScalarCode.expand,aligned] using ‹_›
  | @letValue values v rest bodyCore argCore annotation resultAnnotation value next arg body typed shape binder flag iv ib
  | @beta values v rest bodyCore argCore annotation resultAnnotation value next arg body typed shape binder flag iv ib =>
    have children : StaticRegisters v ∧ StaticRegisters rest := by
      first | exact static | exact ⟨static.2,static.1⟩
    obtain ⟨f,vc,vq,derivedValue⟩ := iv children.1 vs aligned
    obtain ⟨g,bc,bq,b⟩ := ib children.2 (⟨LexicalScalarCode.expand vs v,f,vc,vq⟩::vs)
      (by simp only [LexicalScalarCode.sources,List.map_cons,LexicalScalarCode.expand,aligned])
    first
    | refine ⟨_,_,_,.letValue annotation resultAnnotation derivedValue b ?_ ?_ typed shape binder flag⟩
    | refine ⟨_,_,_,.beta annotation resultAnnotation derivedValue b ?_ ?_ typed shape binder flag⟩
    all_goals simpa only [LexicalScalarCode.expand,LexicalScalarCode.under,aligned] using ‹_›

/-- Source typing is obtained from the computation-free judgment. The temporary
value records below supply no correctness assumptions and occur only in this
proof: source evidence never inspects their code or computation fields. -/
theorem Form.evidence (form : Form env ctx p values raw) (static : StaticRegisters raw)
    (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (valuesTyped : ∀ value ∈ values, LexicalScalarCode.Evidence env ctx value) :
    LexicalScalarCode.Evidence env ctx (expand values raw) := by
  let vs : List LexicalScalarCode.Value := values.map fun value =>
    ⟨value,fun _ _ _ _ _ => none,.lit 0,.const ``HybridWord.Expr.index []⟩
  have aligned : LexicalScalarCode.sources vs = values := by simp [vs,LexicalScalarCode.sources,Function.comp_def]
  obtain ⟨native,code,quotation,source⟩ := form.constructSource static vs aligned
  have typed : LexicalScalarCode.ValuesTyped env ctx vs := by
    intro value member
    dsimp only [vs] at member
    obtain ⟨raw,rawMember,same⟩ := List.mem_map.mp member
    subst value
    exact valuesTyped raw rawMember
  simpa only [LexicalScalarCode.expand,aligned] using source.evidence library decisions inputs typing typed

/-- The actual annotations of the operands are inferred from their source
judgments. Callers do not provide representations or compiler CastTyping. -/
theorem Form.binaryInferred (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (valuesTyped : ∀ value ∈ values, LexicalScalarCode.Evidence env ctx value)
    (op : Binary) (aa ab ac ad : WordBinder.Annotation)
    (left : Form env ctx p values a) (right : Form env ctx p values b)
    (leftStatic : StaticRegisters a) (rightStatic : StaticRegisters b)
    (separated : Separated p (expand values (Lean.mkApp2 (AnnotatedBinary.nativeHeader op aa ab ac ad) a b))) :
    Form env ctx p values (Lean.mkApp2 (AnnotatedBinary.nativeHeader op aa ab ac ad) a b) := by
  obtain ⟨u,ua,ur,ut,uf⟩ := left.evidence leftStatic library decisions inputs typing valuesTyped
  obtain ⟨v,va,vr,vt,vf⟩ := right.evidence rightStatic library decisions inputs typing valuesTyped
  exact .annotatedBinary op aa ab ac ad ua va left right ur vr ut vt uf vf separated

theorem Form.negInferred (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (valuesTyped : ∀ value ∈ values, LexicalScalarCode.Evidence env ctx value)
    (annotation : WordBinder.Annotation) (value : Form env ctx p values v) (static : StaticRegisters v)
    (separated : Separated p (expand values (.app (AnnotatedNeg.nativeHeader annotation) v))) :
    Form env ctx p values (.app (AnnotatedNeg.nativeHeader annotation) v) := by
  obtain ⟨v,va,vr,vt,vf⟩ := value.evidence static library decisions inputs typing valuesTyped
  exact .annotatedNeg annotation va value vr vt vf separated

theorem Form.selectInferred (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (valuesTyped : ∀ value ∈ values, LexicalScalarCode.Evidence env ctx value)
    (resultAnnotation annotation : WordBinder.Annotation)
    (value : Form env ctx p values v) (yes : Form env ctx p values a) (no : Form env ctx p values b)
    (valueStatic : StaticRegisters v) (yesStatic : StaticRegisters a) (noStatic : StaticRegisters b)
    (separated : Separated p (expand values (AnnotatedCondition.scalarSource resultAnnotation annotation v
      (AnnotatedCondition.nativeDecision annotation v) a b))) :
    Form env ctx p values (AnnotatedCondition.scalarSource resultAnnotation annotation v (AnnotatedCondition.nativeDecision annotation v) a b) := by
  obtain ⟨v,va,vr,vt,vf⟩ := value.evidence valueStatic library decisions inputs typing valuesTyped
  obtain ⟨a,aa,ar,at_,af⟩ := yes.evidence yesStatic library decisions inputs typing valuesTyped
  obtain ⟨b,ba,br,bt,bf⟩ := no.evidence noStatic library decisions inputs typing valuesTyped
  exact .annotatedSelect resultAnnotation annotation va aa ba value yes no vr ar br vt at_ bt vf af bf separated

/-- One binding connection for source-only let and beta rules. Open-body
source typing and substituted-body syntax have different roles; no second
code-indexed Source derivation is requested from the caller. -/
theorem Form.bindingEvidence (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (valuesTyped : ∀ value ∈ values, LexicalScalarCode.Evidence env ctx value)
    (annotation : WordBinder.Annotation)
    (value : Form env ctx p values v) (valueStatic : StaticRegisters v)
    (next : Form env ctx p (expand values v::values) rest) (nextStatic : StaticRegisters rest)
    (openTyped : LexicalScalarCode.Evidence env (annotation.core::ctx) (under values rest)) :
    ∃ (arg body : VExpr) (result : WordBinder.Annotation),
      Represents (expand values v) arg ∧ Represents (under values rest) body ∧
      CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body result.core ∧
      ∃ actual : WordBinder.Annotation, ValueShape env ctx (body.inst arg) actual.core := by
  obtain ⟨arg,aa,ar,at_,af⟩ := value.evidence valueStatic library decisions inputs typing valuesTyped
  have extended : ∀ e ∈ expand values v::values, LexicalScalarCode.Evidence env ctx e := by
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨arg,aa,ar,at_,af⟩
    · exact valuesTyped e member
  obtain ⟨body,result,br,bt,bf⟩ := openTyped
  obtain ⟨reduced,actual,rr,rt,rf⟩ := next.evidence nextStatic library decisions inputs typing extended
  have substituted : Represents (expand (expand values v::values) rest) (body.inst arg) := by
    rw [expand_cons]
    exact br.instantiate ar
  exact ⟨arg,body,result,ar,br,bt,actual,(rr.unique substituted) ▸ rf⟩

theorem Form.letFromTyping (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (valuesTyped : ∀ value ∈ values, LexicalScalarCode.Evidence env ctx value)
    (annotation : WordBinder.Annotation)
    (value : Form env ctx p values v) (valueStatic : StaticRegisters v)
    (next : Form env ctx p (expand values v::values) rest) (nextStatic : StaticRegisters rest)
    (openTyped : LexicalScalarCode.Evidence env (annotation.core::ctx) (under values rest))
    (binder : Lean.Name) (flag : Bool) :
    Form env ctx p values (.letE binder annotation.native v rest flag) := by
  obtain ⟨arg,body,result,ar,br,bt,shape⟩ := value.bindingEvidence library decisions inputs typing valuesTyped
    annotation valueStatic next nextStatic openTyped
  exact .letValue annotation result value next ar br bt shape binder flag

theorem Form.betaFromTyping (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (valuesTyped : ∀ value ∈ values, LexicalScalarCode.Evidence env ctx value)
    (annotation : WordBinder.Annotation)
    (value : Form env ctx p values v) (valueStatic : StaticRegisters v)
    (next : Form env ctx p (expand values v::values) rest) (nextStatic : StaticRegisters rest)
    (openTyped : LexicalScalarCode.Evidence env (annotation.core::ctx) (under values rest))
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    Form env ctx p values (.app (.lam binder annotation.native rest info) v) := by
  obtain ⟨arg,body,result,ar,br,bt,shape⟩ := value.bindingEvidence library decisions inputs typing valuesTyped
    annotation valueStatic next nextStatic openTyped
  exact .beta annotation result value next ar br bt shape binder info

end IRComparison.WordFrontend.LexicalScalarSyntax

namespace IRComparison.WordFrontend.LexicalScalarCode
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarSyntax
set_option maxHeartbeats 1800000

/-- The historical scalar entry parameters lie outside the local source scope.
Local scalar bindings and loop counters are carried separately in `p.locals`. -/
def ExternalAt (bound : Nat) (p : Inputs) : Prop :=
  p.i = .bvar (bound+2) ∧ p.x = .bvar (bound+1) ∧ p.y = .bvar bound

theorem ExternalAt.lift (external : ExternalAt bound p) : ExternalAt (bound+1) p.lift := by
  rcases external with ⟨hi,hx,hy⟩
  simp [ExternalAt,Inputs.lift,hi,hx,hy,LeanBindings.rename,Nat.succ_eq_add_one,Nat.add_assoc]

/-- Source scope of cached scalar values, independent of parsing or code. -/
def ValuesCompared (bound : Nat) (project : List HybridWord.Word → List HybridWord.Word) (vs : List Value) : Prop := ∀ value ∈ vs,
  LeanScalar.wellScoped bound value.source = true ∧
  ∀ i x y s ls, value.native i x y s ls = value.native 0 0 0 s (project ls)

/-- Expanding a lexical cache cannot introduce an external scalar input if
all cached values and uncached references respect the same source scope. -/
theorem expand_scoped_compared (values : ValuesCompared bound project vs)
    (scope_ok : LeanScalar.wellScoped (vs.length+bound) raw = true) :
    LeanScalar.wellScoped bound (expand vs raw) = true := by
  apply LeanBindings.substitute_wellScoped raw (vs.length+bound) bound scope_ok
  intro index bound
  simp only [LexicalScalarSyntax.sourceReference,sources,List.getElem?_map,List.length_map]
  cases found : vs[index]? with
  | some value => exact (values value (List.mem_of_getElem? found)).1
  | none =>
    have outside := List.getElem?_eq_none_iff.mp found
    simp only [Option.map_none,LeanScalar.wellScoped,decide_eq_true_eq]
    omega

/-- Source scope excludes the historical scalar parameters. A local-list
projection may discard only unreferenced locals; cached values use the same
projection. One induction supplies initial-entry and nested-body cases. -/
theorem Source.compareLocals (source : Source env ctx p vs raw native code quotation)
    (external : ExternalAt bound p)
    (localValues : ∀ (k : Nat) e, p.locals[k]? = some e → ∀ (ls : List HybridWord.Word), ls[k]? = (project ls)[k]?)
    (values : ValuesCompared bound project vs)
    (scope_ok : LeanScalar.wellScoped (vs.length+bound) raw = true) :
    ∀ i x y s ls, native i x y s ls = native 0 0 0 s (project ls) := by
  induction source with
  | reference selected => exact (values _ (List.mem_of_getElem? selected)).2
  | index shape same outside =>
    have h := expand_scoped_compared values scope_ok
    rw [same] at h
    simp [external.1,LeanScalar.wellScoped] at h
    omega
  | parameter side shape same outside ni nl =>
    have h := expand_scoped_compared values scope_ok
    rw [same] at h
    cases side <;> simp [ScalarSyntax.Side.source,external.2.1,external.2.2,LeanScalar.wellScoped] at h <;> omega
  | localValue shape k outside selected ni nl nr first =>
    intro i x y s ls
    exact localValues k _ selected ls
  | literal | annotatedLiteral | register => intros; rfl
  | binary op left right scope il ir
  | annotatedBinary op aa ab ac ad oa ob left right lr rr lt rt lf rf scope il ir =>
    have children := Bool.and_eq_true_iff.mp scope_ok
    have a := il values (Bool.and_eq_true_iff.mp children.1).2
    have b := ir values children.2
    intro i x y s ls; dsimp only; rw [a i x y s ls,b i x y s ls]
  | neg value scope ih
  | annotatedNeg annotation operand value rep typed shape scope ih =>
    have child := ih values (Bool.and_eq_true_iff.mp scope_ok).2
    intro i x y s ls; dsimp only; rw [child i x y s ls]
  | select value decision yes no scope iv ia ib
  | booleanSelect value yes no scope iv ia ib
  | annotatedSelect resultAnnotation annotation operand oa ob value yes no vr ar br vt at_ bt vf af bf scope iv ia ib =>
    have bscope := Bool.and_eq_true_iff.mp scope_ok
    have ascope := Bool.and_eq_true_iff.mp bscope.1
    have dscope := Bool.and_eq_true_iff.mp ascope.1
    have cscope := Bool.and_eq_true_iff.mp dscope.1
    have cargs := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp cscope.2).1
    have vscope := (Bool.and_eq_true_iff.mp cargs.2).1
    have av := iv values (Bool.and_eq_true_iff.mp vscope).2
    have aa := ia values ascope.2
    have ab := ib values bscope.2
    intro i x y s ls; dsimp only; rw [av i x y s ls,aa i x y s ls,ab i x y s ls]
  | @letValue vs v f vc vq rest g bc bq body arg annotation resultAnnotation value next ar br typed form binder flag iv ib
  | @beta vs v f vc vq rest g bc bq body arg annotation resultAnnotation value next ar br typed form binder flag iv ib =>
    have children : LeanScalar.wellScoped (vs.length+bound) v = true ∧
        LeanScalar.wellScoped (vs.length+bound+1) rest = true := by
      first
      | exact ⟨(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp scope_ok).1).2,(Bool.and_eq_true_iff.mp scope_ok).2⟩
      | exact ⟨(Bool.and_eq_true_iff.mp scope_ok).2,(Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp scope_ok).1).2⟩
    apply ib
    · intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨expand_scoped_compared values children.1,iv values children.1⟩
      · exact values entry member
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using children.2

/-- Same-local-list specialization used under body/loop binders. -/
abbrev ValuesIndependent (bound : Nat) (vs : List Value) := ValuesCompared bound id vs

theorem expand_scoped (values : ValuesIndependent bound vs)
    (scope_ok : LeanScalar.wellScoped (vs.length+bound) raw = true) :
    LeanScalar.wellScoped bound (expand vs raw) = true := expand_scoped_compared values scope_ok

theorem Source.independent (source : Source env ctx p vs raw native code quotation)
    (external : ExternalAt bound p) (values : ValuesIndependent bound vs)
    (scope_ok : LeanScalar.wellScoped (vs.length+bound) raw = true) :
    ∀ i x y s ls, native i x y s ls = native 0 0 0 s ls :=
  source.compareLocals external (by intros; rfl) values scope_ok

/-- The initial entry has State only and no local inputs. This is a
specialization of the same scope induction, not a second recursive proof. -/
abbrev ValuesStateOnly (vs : List Value) := ValuesCompared 1 (fun _ => []) vs

theorem expand_state_scoped (values : ValuesStateOnly vs)
    (scope_ok : LeanScalar.wellScoped (vs.length+1) raw = true) :
    LeanScalar.wellScoped 1 (expand vs raw) = true := expand_scoped_compared values scope_ok

theorem Source.stateOnly (source : Source env ctx parameters vs raw native code quotation)
    (values : ValuesStateOnly vs)
    (scope_ok : LeanScalar.wellScoped (vs.length+1) raw = true) :
    ∀ i x y s ls, native i x y s ls = native 0 0 0 s [] := by
  exact source.compareLocals ⟨rfl,rfl,rfl⟩ (by intro k e h; simp [parameters] at h) values scope_ok

end IRComparison.WordFrontend.LexicalScalarCode

namespace IRComparison.WordFrontend.ScalarSyntax
open LeanTyped Certificate

/-- Application syntax cannot alias a bound-variable input, even when its
subexpressions contain abstract annotation or numeral parameters. -/
theorem sameTerm_application_variable (f a : Lean.Expr) (n : Nat) :
    sameTerm (.app f a) (.bvar n) = false := by
  unfold sameTerm
  cases h : translate (.app f a) with
  | none => rfl
  | some value =>
    obtain ⟨core,represented⟩ := value
    cases represented with
    | app hf ha => rfl

theorem Separated.initialApplication (f a : Lean.Expr) :
    Separated parameters (.app f a) :=
  ⟨sameTerm_application_variable f a 3,sameTerm_application_variable f a 2,
    sameTerm_application_variable f a 1,by intro n; rfl⟩

end IRComparison.WordFrontend.ScalarSyntax

namespace IRComparison.WordFrontend.ScalarSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic

private theorem represented_head (rep : Represents e core) (head : e.getAppFn = .const name levels) :
    ∃ us, LeanTypeReduction.constantHead core = some (name,us) := by
  induction rep with
  | app fn arg ih _ => exact ih head
  | constant h => cases head; exact ⟨_,rfl⟩
  | metadata rep ih => simp [Lean.Expr.getAppFn] at head
  | _ => simp [Lean.Expr.getAppFn] at head

private theorem sameTerm_head_variable (head : e.getAppFn = .const name levels) (n : Nat) :
    sameTerm e (.bvar n) = false := by
  unfold sameTerm
  cases found : translate e with
  | none => rfl
  | some result =>
    obtain ⟨core,rep⟩ := result
    have different : core ≠ .bvar n := by
      intro same
      obtain ⟨us,h⟩ := represented_head rep head
      rw [same] at h
      cases h
    simp [translate,different]

private theorem sameTerm_head_natural (head : e.getAppFn = .const name levels) (different : name ≠ ``BitVec.ofNat) (n : Nat) :
    sameTerm e (NaturalScope.nativeIndex (.bvar n)) = false := by
  cases found : sameTerm e (NaturalScope.nativeIndex (.bvar n)) with
  | false => rfl
  | true =>
    unfold sameTerm at found
    cases parsed : translate e with
    | none => simp [parsed] at found
    | some result =>
      obtain ⟨core,rep⟩ := result
      have same := sameTerm_sound rep (NaturalScope.index_represents (n := .bvar n) Represents.bvar) (by simpa only [sameTerm,parsed] using found)
      obtain ⟨us,h⟩ := represented_head rep head
      rw [same] at h
      have hn : name = ``BitVec.ofNat := by simpa [NaturalScope.index,applications,LeanTypeReduction.constantHead] using congrArg (Option.map Prod.fst) h.symm
      exact False.elim (different hn)

/-- Shape invariant of references generated by binder/loop scope extension;
not a second program grammar or a restriction on scalar value expressions. -/
def ReferenceShape (e : Lean.Expr) : Prop :=
  ∃ n, e = .bvar n ∨ e = NaturalScope.nativeIndex (.bvar n)

theorem ReferenceShape.lift (shape : ReferenceShape e) :
    ReferenceShape (LeanBindings.rename Nat.succ e) := by
  obtain ⟨n,rfl|rfl⟩ := shape
  · exact ⟨n+1,Or.inl rfl⟩
  · exact ⟨n+1,Or.inr rfl⟩

structure ReferenceScope (p : Inputs) : Prop where
  index : ReferenceShape p.i
  left : ReferenceShape p.x
  right : ReferenceShape p.y
  locals : ∀ e ∈ p.locals, ReferenceShape e

theorem ReferenceScope.initial : ReferenceScope parameters :=
  ⟨⟨3,Or.inl rfl⟩,⟨2,Or.inl rfl⟩,⟨1,Or.inl rfl⟩,by intro e h; cases h⟩

theorem ReferenceScope.lift (scope : ReferenceScope p) : ReferenceScope p.lift := by
  refine ⟨scope.index.lift,scope.left.lift,scope.right.lift,?_⟩
  intro e h
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
  exact (scope.locals v hv).lift

theorem ReferenceScope.scalar (scope : ReferenceScope p) :
    ReferenceScope {p.lift with locals := .bvar 0::p.lift.locals} := by
  refine ⟨scope.lift.index,scope.lift.left,scope.lift.right,?_⟩
  intro e h
  rcases List.mem_cons.mp h with rfl|h
  · exact ⟨0,Or.inl rfl⟩
  · exact scope.lift.locals e h

theorem ReferenceScope.state (scope : ReferenceScope p) :
    ReferenceScope {p.lift with s := .bvar 0} :=
  ⟨scope.lift.index,scope.lift.left,scope.lift.right,scope.lift.locals⟩

theorem ReferenceScope.forStatic (scope : ReferenceScope p) :
    ReferenceScope (For.parameters p) := by
  refine ⟨scope.lift.lift.index,scope.lift.lift.left,scope.lift.lift.right,?_⟩
  intro e h
  rcases List.mem_cons.mp h with rfl|h
  · exact ⟨1,Or.inl rfl⟩
  · exact scope.lift.lift.locals e h

theorem ReferenceScope.forIn (scope : ReferenceScope p) :
    ReferenceScope (NaturalScope.forInParameters p) := by
  refine ⟨scope.lift.lift.index,scope.lift.lift.left,scope.lift.lift.right,?_⟩
  intro e h
  rcases List.mem_cons.mp h with rfl|h
  · exact ⟨1,Or.inr rfl⟩
  · exact scope.lift.lift.locals e h

theorem ReferenceScope.fold (scope : ReferenceScope p) :
    ReferenceScope (NaturalScope.foldParameters p) := by
  refine ⟨scope.lift.lift.index,scope.lift.lift.left,scope.lift.lift.right,?_⟩
  intro e h
  rcases List.mem_cons.mp h with rfl|h
  · exact ⟨0,Or.inr rfl⟩
  · exact scope.lift.lift.locals e h

theorem ReferenceScope.separated (scope : ReferenceScope p)
    (head : e.getAppFn = .const name levels) (different : name ≠ ``BitVec.ofNat) : Separated p e := by
  have apart {value : Lean.Expr} (shape : ReferenceShape value) : sameTerm e value = false := by
    obtain ⟨n,rfl|rfl⟩ := shape
    · exact sameTerm_head_variable head n
    · exact sameTerm_head_natural head different n
  refine ⟨apart scope.index,apart scope.left,apart scope.right,?_⟩
  intro k
  cases found : p.locals[k]? with
  | none => rfl
  | some v => exact apart (scope.locals v (List.mem_of_getElem? found))
end IRComparison.WordFrontend.ScalarSyntax

namespace IRComparison.WordFrontend.LexicalScalarSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarEnvironment ScalarSyntax

def closeValues (value : Lean.Expr) (values : List Lean.Expr) : List Lean.Expr :=
  values.map (LeanBindings.instantiate value) ++ [value]

theorem expand_closeValues (value : Lean.Expr) (values : List Lean.Expr) (raw : Lean.Expr) :
    expand (closeValues value values) raw = LeanBindings.instantiate value (expand values raw) := by
  unfold expand LeanBindings.instantiate
  rw [LeanBindings.substitute_comp]
  congr 1
  funext n
  unfold closeValues sourceReference
  by_cases inside : n < values.length
  · have mapped : n < (values.map (LeanBindings.instantiate value)).length := by simpa using inside
    simp only [List.getElem?_append_left mapped,List.getElem?_map]
    cases h : values[n]? with
    | none => simp_all
    | some found => simp [h,LeanBindings.instantiate]
  · have outside : values[n]? = none := List.getElem?_eq_none (by omega)
    have mapped : (values.map (LeanBindings.instantiate value)).length ≤ n := by simpa using Nat.le_of_not_gt inside
    simp only [List.getElem?_append_right mapped,List.length_map,outside,List.length_append,List.length_cons,List.length_nil]
    by_cases first : n = values.length
    · subst n; simp [LeanBindings.substitute]
    · have next : ∃ k, n - values.length = k+1 := by exact ⟨n-values.length-1,by omega⟩
      obtain ⟨k,hk⟩ := next
      simp [hk,LeanBindings.substitute]
      congr 1
      omega
theorem under_closeValues (value : Lean.Expr) (values : List Lean.Expr) (raw : Lean.Expr) :
    under (closeValues value values) raw =
      LeanBindings.substitute (LeanBindings.underSubst (fun n => match n with
        | 0 => value | n+1 => Lean.Expr.bvar n)) (under values raw) := by
  have law := expand_closeValues value values (.lam .anonymous (.const ``Nat []) raw .default)
  simpa only [expand,under,LeanBindings.instantiate,LeanBindings.substitute,
    Lean.Expr.lam.injEq,true_and,and_true] using law

@[simp] theorem instantiate_lift_source (value source : Lean.Expr) :
    LeanBindings.instantiate value (LeanBindings.rename Nat.succ source) = source := by
  simp only [LeanBindings.instantiate,LeanBindings.substitute_rename,Function.comp_def]
  exact LeanBindings.substitute_id source

theorem sameTerm_lift (ar : Represents a ac) (br : Represents b bc) :
    sameTerm (LeanBindings.rename Nat.succ a) (LeanBindings.rename Nat.succ b) = sameTerm a b := by
  by_cases h : ac = bc
  · subst bc
    rw [sameTerm_complete ar br,sameTerm_complete ar.lift br.lift]
  · have original : sameTerm a b = false := by
      cases hs : sameTerm a b with
      | false => rfl
      | true => exact False.elim (h (sameTerm_sound ar br hs))
    rw [original]
    cases hs : sameTerm (LeanBindings.rename Nat.succ a) (LeanBindings.rename Nat.succ b) with
    | false => rfl
    | true =>
      have lifted := sameTerm_sound ar.lift br.lift hs
      have unlifted := congrArg (fun core : VExpr => core.inst (.bvar 0)) lifted
      exact False.elim (h (by simpa only [VExpr.inst_lift] using unlifted))

@[simp] theorem closeValues_cons (value saved : Lean.Expr) (values : List Lean.Expr) :
    closeValues value (expand values saved :: values) =
      expand (closeValues value values) saved :: closeValues value values := by
  simp only [closeValues,List.map_cons,List.cons_append]
  rw [← expand_closeValues]
  rfl

private theorem expanded_variable (values : List Lean.Expr)
    (same : expand values raw = .bvar 0) : ∃ n, raw = .bvar n ∧ n ≤ values.length := by
  cases raw <;> try (simp [expand,LeanBindings.substitute] at same)
  rename_i n
  refine ⟨n,rfl,?_⟩
  by_cases h : n < values.length
  · omega
  · have absent : values[n]? = none := List.getElem?_eq_none (by omega)
    simp [expand,LeanBindings.substitute,sourceReference,absent] at same
    omega

/-- Close one scalar binder into the lexical cache, keeping the original body
syntax. Separation is an invariant of generated input scopes, not a parser
success premise. Mixed annotations are dealt with before this exact step. -/
theorem Form.closeExact (domain : WordBinder.Annotation)
    (form : Form env (domain.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} values raw)
    (static : StaticRegisters raw)
    (library : Arithmetic.Signatures env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (scope : LexicalScalarCode.ScopeTyped env ctx p)
    (argRep : Represents value arg) (argTyped : CastTyping env 0 (SourceCasts env) ctx arg domain.core)
    (argShape : ValueShape env ctx arg domain.core)
    (heads : ∀ e n levels, e.getAppFn = .const n levels → n ∈ valueHeads → n ≠ ``BitVec.ofNat → Separated p e) :
    Form env ctx p (closeValues value values) raw := by
  have closeLift {values : List Lean.Expr} {raw old : Lean.Expr}
      (h : expand values raw = LeanBindings.rename Nat.succ old) :
      expand (closeValues value values) raw = old := by
    rw [expand_closeValues,h,instantiate_lift_source]
  have closedShape {core ty} (shape : ValueShape env (domain.core::ctx) core ty)
      (typed : CastTyping env 0 (SourceCasts env) (domain.core::ctx) core ty)
      (tc : ty.ClosedN 0) : ValueShape env ctx (core.inst arg) ty := by
    simpa only [tc.instN_eq (Nat.zero_le _)] using shape.instantiateExact domain typed closed argTyped argShape
  induction form with
  | @reference values n old found =>
    have h : n < values.length := List.getElem?_eq_some_iff.mp found |>.1
    apply Form.reference (value := LeanBindings.instantiate value old)
    change (values.map (LeanBindings.instantiate value) ++ [value])[n]? = _
    rw [List.getElem?_append_left (by simpa using h),List.getElem?_map,found]
    rfl
  | @index raw values shape same => exact .index shape (closeLift same)
  | @parameter raw values side shape same ni nl =>
    have lifted : side.source {p.lift with locals := .bvar 0::p.lift.locals} =
        LeanBindings.rename Nat.succ (side.source p) := by cases side <;> rfl
    apply Form.parameter side shape (closeLift (same.trans lifted))
    · rw [lifted] at ni
      simpa only [Inputs.lift,sameTerm_lift (side.representation inputs).property inputs.i.property] using ni
    · intro right
      have h := nl right
      rw [lifted] at h
      simpa only [Inputs.lift,sameTerm_lift (side.representation inputs).property inputs.x.property] using h
  | @localValue raw values shape k selected ni nl nr first =>
    cases k with
    | zero =>
      have same : expand values raw = .bvar 0 := by simpa using selected.symm
      obtain ⟨n,rfl,bound⟩ := expanded_variable values same
      have enough : n < (closeValues value values).length := by simp [closeValues]; omega
      exact .reference (List.getElem?_eq_getElem enough)
    | succ k =>
      change (p.locals.map (LeanBindings.rename Nat.succ))[k]? = some (expand values raw) at selected
      simp only [List.getElem?_map] at selected
      cases old : p.locals[k]? with
      | none => simp [old] at selected
      | some e =>
        have same : expand values raw = LeanBindings.rename Nat.succ e := by simpa [old] using selected.symm
        have newSame := closeLift same
        obtain ⟨core,annotation,rep,typed,sh⟩ := scope.locals e (List.mem_of_getElem? old)
        apply Form.localValue shape k
        · simpa only [newSame] using old
        · simpa only [newSame] using (show sameTerm e p.i = false from by
            simpa only [same,Inputs.lift,sameTerm_lift rep inputs.i.property] using ni)
        · simpa only [newSame] using (show sameTerm e p.x = false from by
            simpa only [same,Inputs.lift,sameTerm_lift rep inputs.x.property] using nl)
        · simpa only [newSame] using (show sameTerm e p.y = false from by
            simpa only [same,Inputs.lift,sameTerm_lift rep inputs.y.property] using nr)
        · intro j hj
          have before := first (j+1) (by omega)
          change (((.bvar 0::p.locals.map (LeanBindings.rename Nat.succ))[j+1]?).map
            (sameTerm (expand values raw))).getD false = false at before
          simp only [List.getElem?_cons_succ,List.getElem?_map] at before
          cases other : p.locals[j]? with
          | none => simp [other]
          | some e' =>
            obtain ⟨core',annotation',rep',typed',sh'⟩ := scope.locals e' (List.mem_of_getElem? other)
            simpa only [newSame,other,Option.map_some,Option.getD_some] using
              (show sameTerm e e' = false from by
                simpa only [other,Option.map_some,Option.getD_some,same,sameTerm_lift rep rep'] using before)
  | literal n ignored =>
    exact .literal n (heads _ _ _ rfl (by simp [valueHeads]) (by decide))
  | annotatedLiteral annotation n ignored =>
    apply Form.annotatedLiteral annotation n
    cases annotation <;> exact heads _ _ _ rfl (by simp [valueHeads]) (by decide)
  | @register values st r stateSame register ignored =>
    obtain ⟨view⟩ := static.1
    apply Form.register (closeLift stateSame)
    · have unchanged (vs : List Lean.Expr) (form : NatNotation) (n : Nat) : expand vs (form.native n) = form.native n := by cases form <;> rfl
      simpa only [view.shape,unchanged] using view.form.argument library view.value
    · exact heads _ _ _ rfl (by simp [valueHeads]) (by decide)
  | @binary values a b op left right ignored il ir =>
    have children : StaticRegisters a ∧ StaticRegisters b := by cases op <;> exact ⟨static.1.2,static.2⟩
    apply Form.binary op (il children.1) (ir children.2)
    cases op <;> exact heads _ _ _ rfl (by simp [valueHeads,Binary.method]) (by decide)
  | neg v ignored ih =>
    exact .neg (ih static.2) (heads _ _ _ rfl (by simp [valueHeads]) (by decide))
  | @select values v d a b fv decision fa fb ignored iv ia ib =>
    have children : StaticRegisters v ∧ StaticRegisters a ∧ StaticRegisters b :=
      ⟨static.1.1.1.2.1.2.1.2,static.1.2,static.2⟩
    refine Form.select (iv children.1) ?_ (ia children.2.1) (ib children.2.2) ?_
    · simpa only [expand_closeValues] using decision.instantiate closed SourceCasts.closed argRep argTyped
    · exact heads _ _ _ rfl (by simp [valueHeads]) (by decide)
  | @annotatedBinary values a b lc rc op aa ab ac ad oa ob fa fb lr rr lt rt lf rf ignored il ir =>
    have children : StaticRegisters a ∧ StaticRegisters b := by cases op <;> exact ⟨static.1.2,static.2⟩
    apply Form.annotatedBinary op aa ab ac ad oa ob (il children.1) (ir children.2)
      (expand_closeValues value values a ▸ lr.instantiate argRep)
      (expand_closeValues value values b ▸ rr.instantiate argRep)
    · simpa only [oa.closed.instN_eq (Nat.zero_le _)] using lt.instantiate closed SourceCasts.closed argTyped
    · simpa only [ob.closed.instN_eq (Nat.zero_le _)] using rt.instantiate closed SourceCasts.closed argTyped
    · exact closedShape lf lt oa.closed
    · exact closedShape rf rt ob.closed
    · cases op <;> exact heads _ _ _ rfl (by simp [valueHeads,Binary.method]) (by decide)
  | @annotatedNeg values v vc annotation operand fv vr vt vf ignored ih =>
    have child : StaticRegisters v := by cases annotation <;> exact static.2
    apply Form.annotatedNeg annotation operand (ih child)
      (expand_closeValues value values v ▸ vr.instantiate argRep)
    · simpa only [operand.closed.instN_eq (Nat.zero_le _)] using vt.instantiate closed SourceCasts.closed argTyped
    · exact closedShape vf vt operand.closed
    · cases annotation <;> exact heads _ _ _ rfl (by simp [valueHeads]) (by decide)
  | @annotatedSelect values v a b vc ac bc ra ca oa ob oc fv fa fb vr ar br vt at_ bt vf af bf ignored iv ia ib =>
    have children : StaticRegisters v ∧ StaticRegisters a ∧ StaticRegisters b := by
      cases ra <;> cases ca <;> exact ⟨static.1.1.1.2.1.2.1.2,static.1.2,static.2⟩
    apply Form.annotatedSelect ra ca oa ob oc (iv children.1) (ia children.2.1) (ib children.2.2)
      (expand_closeValues value values v ▸ vr.instantiate argRep)
      (expand_closeValues value values a ▸ ar.instantiate argRep)
      (expand_closeValues value values b ▸ br.instantiate argRep)
    · simpa only [oa.closed.instN_eq (Nat.zero_le _)] using vt.instantiate closed SourceCasts.closed argTyped
    · simpa only [ob.closed.instN_eq (Nat.zero_le _)] using at_.instantiate closed SourceCasts.closed argTyped
    · simpa only [oc.closed.instN_eq (Nat.zero_le _)] using bt.instantiate closed SourceCasts.closed argTyped
    · exact closedShape vf vt oa.closed
    · exact closedShape af at_ ob.closed
    · exact closedShape bf bt oc.closed
    · cases ra <;> cases ca <;> exact heads _ _ _ rfl (by simp [valueHeads]) (by decide)
  | @letValue values v rest bodyCore argCore annotation resultAnnotation fv next ar br typed shape binder flag iv ib
  | @beta values v rest bodyCore argCore annotation resultAnnotation fv next ar br typed shape binder flag iv ib =>
    have children : StaticRegisters v ∧ StaticRegisters rest := by first | exact static | exact ⟨static.2,static.1⟩
    have next := ib children.2
    rw [closeValues_cons] at next
    have bodyRep : Represents (under (closeValues value values) rest) (bodyCore.inst arg 1) := by
      rw [under_closeValues]
      exact br.instantiate_at argRep 1
    have bodyTyped := typed.instN closed SourceCasts.closed argTyped (Ctx.InstN.succ Ctx.InstN.zero)
    simp only [annotation.closed.instN_eq (Nat.zero_le _),resultAnnotation.closed.instN_eq (Nat.zero_le _)] at bodyTyped
    have resultShape : ∃ actual : WordBinder.Annotation,
        ValueShape env ctx ((bodyCore.inst arg 1).inst (argCore.inst arg)) actual.core := by
      obtain ⟨actual,original⟩ := shape
      simpa only [VExpr.inst0_inst_hi] using original.instantiateSome domain closed argTyped argShape
    first
    | exact .letValue annotation resultAnnotation (iv children.1) next
        (expand_closeValues value values v ▸ ar.instantiate argRep) bodyRep bodyTyped resultShape binder flag
    | exact .beta annotation resultAnnotation (iv children.1) next
        (expand_closeValues value values v ▸ ar.instantiate argRep) bodyRep bodyTyped resultShape binder flag

end IRComparison.WordFrontend.LexicalScalarSyntax

namespace IRComparison.WordFrontend.LexicalScalarSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarEnvironment ScalarSyntax

/-- Remove a redundant final cache slot by redirecting it to the equal head.
Out-of-cache variables shift down; no source occurrence is forbidden. -/
def dropDuplicate (length : Nat) (n : Nat) : Nat :=
  if n < length then n else if n = length then 0 else n-1

private theorem duplicate_lookup (value : Lean.Expr) (values : List Lean.Expr) :
    ∀ n, (value::values)[dropDuplicate (values.length+1) n]? = ((value::values)++[value])[n]? := by
  intro n
  unfold dropDuplicate
  by_cases small : n < values.length+1
  · simp only [if_pos small]
    exact (List.getElem?_append_left (by simpa using small)).symm
  · simp only [if_neg small]
    by_cases last : n=values.length+1
    · subst n
      simp [List.getElem?_append_right]
    · have outside : (value::values)[n-1]?=none := List.getElem?_eq_none (by simp; omega)
      have outside' : ((value::values)++[value])[n]?=none := List.getElem?_eq_none (by simp; omega)
      simp only [if_neg last,outside,outside']

private theorem duplicate_refs (value : Lean.Expr) (values : List Lean.Expr) :
    ∀ n, sourceReference (value::values) (dropDuplicate (values.length+1) n) =
      sourceReference ((value::values)++[value]) n := by
  intro n
  unfold sourceReference
  rw [duplicate_lookup]
  cases found : ((value::values)++[value])[n]? with
  | some x => rfl
  | none =>
    have outside : values.length+2 ≤ n := by simpa using List.getElem?_eq_none_iff.mp found
    simp only [dropDuplicate,if_neg (show ¬ n < values.length+1 by omega),
      if_neg (show n ≠ values.length+1 by omega),List.length_append,List.length_cons,List.length_nil]
    congr 1
    omega

theorem Form.dropDuplicate (form : Form env ctx p ((value::values)++[value]) raw) :
    Form env ctx p (value::values) (LeanBindings.rename (dropDuplicate (values.length+1)) raw) :=
  form.renameCache (duplicate_lookup value values) (duplicate_refs value values)

private theorem close_open_sources (value : Lean.Expr) (vs : List LexicalScalarCode.Value) :
    closeValues value (LexicalScalarCode.sources (LexicalScalarCode.openValues vs)) =
      (value::LexicalScalarCode.sources vs)++[value] := by
  simp only [closeValues,LexicalScalarCode.sources,LexicalScalarCode.openValues,List.map_cons,
    List.map_map,LeanBindings.instantiate,LeanBindings.substitute,List.cons_append]
  congr 2
  apply List.map_congr_left
  intro v member
  exact instantiate_lift_source value v.source

private theorem drop_open_body (value : Lean.Expr) (vs : List LexicalScalarCode.Value) (raw : Lean.Expr) :
    LeanBindings.rename (dropDuplicate (LexicalScalarCode.sources vs |>.length |>.succ))
      (LexicalScalarCode.openBody vs raw) = raw := by
  unfold LexicalScalarCode.openBody
  rw [LeanBindings.rename_comp]
  have same : dropDuplicate (LexicalScalarCode.sources vs |>.length |>.succ) ∘
      (fun n => if n < vs.length+1 then n else n+1) = id := by
    funext n
    simp only [Function.comp_apply,LexicalScalarCode.sources,List.length_map]
    by_cases small : n < vs.length+1
    · simp [small,dropDuplicate]
    · simp [small,dropDuplicate,show ¬n+1 < vs.length+1 by omega,show n ≠ vs.length by omega]
  rw [same,LeanBindings.rename_id]

/-- One open-body derivation supplies the substituted body as well. -/
theorem Form.closeOpenExact (domain : WordBinder.Annotation)
    (form : Form env (domain.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
      (LexicalScalarCode.sources (LexicalScalarCode.openValues vs)) (LexicalScalarCode.openBody vs raw))
    (static : StaticRegisters (LexicalScalarCode.openBody vs raw))
    (library : Arithmetic.Signatures env) (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (scope : LexicalScalarCode.ScopeTyped env ctx p)
    (argRep : Represents value arg) (argTyped : CastTyping env 0 (SourceCasts env) ctx arg domain.core)
    (argShape : ValueShape env ctx arg domain.core)
    (references : ReferenceScope p) :
    Form env ctx p (value::LexicalScalarCode.sources vs) raw := by
  have closedForm := form.closeExact domain static library closed inputs scope argRep argTyped argShape (fun _ _ _ head _ different => references.separated head different)
  rw [close_open_sources] at closedForm
  simpa only [drop_open_body value vs raw] using closedForm.dropDuplicate
end IRComparison.WordFrontend.LexicalScalarSyntax

namespace IRComparison.WordFrontend.LexicalScalarSyntax
open LeanTyped LeanTypeInference Certificate Arithmetic
private theorem nat_form_rename (form : NatNotation) (n : Nat) (ρ : Nat → Nat) :
    LeanBindings.rename ρ (form.native n) = form.native n := by cases form <;> rfl

theorem StaticRegisters.rename (static : StaticRegisters raw) (ρ : Nat → Nat) :
    StaticRegisters (LeanBindings.rename ρ raw) := by
  induction raw generalizing ρ with
  | bvar n => trivial
  | fvar n => trivial
  | mvar n => trivial
  | sort u => trivial
  | const n u => trivial
  | lit l => trivial
  | forallE n t b i it ib => trivial
  | lam n t b i it ib => exact ib static _
  | letE n t v b f it iv ib => exact ⟨iv static.1 _,ib static.2 _⟩
  | mdata d b ih => exact ih static _
  | proj n i b ih => exact ih static _
  | app f a iff ia =>
    cases f with
    | app g st =>
      cases g with
      | const name levels =>
        by_cases hn : name = ``HybridWord.State.regs
        · subst name
          cases levels with
          | nil =>
            obtain ⟨⟨view⟩,child⟩ := static
            refine ⟨⟨⟨view.value,view.form,?_⟩⟩,?_⟩
            · exact (congrArg (LeanBindings.rename ρ) view.shape).trans (nat_form_rename view.form view.value ρ)
            · have stStatic := iff (by simpa [StaticRegisters] using child) ρ
              exact stStatic.2
          | cons level levels => exact ⟨iff static.1 ρ,ia static.2 ρ⟩
        · have parts : StaticRegisters (.app (.const name levels) st) ∧ StaticRegisters a := by simpa [StaticRegisters,hn] using static
          simpa [LeanBindings.rename,StaticRegisters,hn] using And.intro (iff parts.1 ρ) (ia parts.2 ρ)
      | _ => exact ⟨iff static.1 ρ,ia static.2 ρ⟩
    | _ => exact ⟨iff static.1 ρ,ia static.2 ρ⟩
end IRComparison.WordFrontend.LexicalScalarSyntax

namespace IRComparison.WordFrontend.LexicalScalarSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarSyntax

/-- A single annotation-polymorphic body derivation is used both for the
source binder's annotation and for the initializer's actual inferred type.
This supports Word/BitVec aliases without assuming their inferred types equal.
The source cache carries no parser-success assumptions. -/
theorem Form.bindingFromOpen (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p)
    (valuesTyped : ∀ value ∈ LexicalScalarCode.sources vs, LexicalScalarCode.Evidence env ctx value)
    (annotation : WordBinder.Annotation)
    (value : Form env ctx p (LexicalScalarCode.sources vs) v) (valueStatic : StaticRegisters v)
    (body : ∀ a : WordBinder.Annotation,
      Form env (a.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
        (LexicalScalarCode.sources (LexicalScalarCode.openValues vs)) (LexicalScalarCode.openBody vs rest))
    (bodyStatic : StaticRegisters rest) :
    Form env ctx p (expand (LexicalScalarCode.sources vs) v::LexicalScalarCode.sources vs) rest ∧
      LexicalScalarCode.Evidence env (annotation.core::ctx) (under (LexicalScalarCode.sources vs) rest) := by
  obtain ⟨arg,actual,ar,at_,af⟩ := value.evidence valueStatic library decisions inputs typing valuesTyped
  have static : StaticRegisters (LexicalScalarCode.openBody vs rest) := bodyStatic.rename _
  refine ⟨(body actual).closeOpenExact actual static library.toSignatures closed inputs typing ar at_ af references,?_⟩
  have cached : LexicalScalarCode.ValuesTyped env ctx vs := by
    intro bound member
    exact valuesTyped bound.source (List.mem_map.mpr ⟨bound,member,rfl⟩)
  have opened : ∀ value ∈ LexicalScalarCode.sources (LexicalScalarCode.openValues vs),
      LexicalScalarCode.Evidence env (annotation.core::ctx) value := by
    intro e member
    obtain ⟨bound,hbound,rfl⟩ := List.mem_map.mp member
    exact (cached.open closed annotation) bound hbound
  have typed := (body annotation).evidence static library decisions
    (annotation.nextInputs inputs closed library.toSignatures library.localLibrary.cons)
    (typing.nextWord closed annotation) opened
  change LexicalScalarCode.Evidence env (annotation.core::ctx)
    (LexicalScalarCode.expand (LexicalScalarCode.openValues vs) (LexicalScalarCode.openBody vs rest)) at typed
  rw [LexicalScalarCode.expand_open] at typed
  exact typed

theorem Form.letFromOpen (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p)
    (valuesTyped : ∀ value ∈ LexicalScalarCode.sources vs, LexicalScalarCode.Evidence env ctx value)
    (annotation : WordBinder.Annotation)
    (value : Form env ctx p (LexicalScalarCode.sources vs) v) (valueStatic : StaticRegisters v)
    (body : ∀ a : WordBinder.Annotation,
      Form env (a.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
        (LexicalScalarCode.sources (LexicalScalarCode.openValues vs)) (LexicalScalarCode.openBody vs rest))
    (bodyStatic : StaticRegisters rest) (binder : Lean.Name) (flag : Bool) :
    Form env ctx p (LexicalScalarCode.sources vs) (.letE binder annotation.native v rest flag) := by
  obtain ⟨next,openTyped⟩ := value.bindingFromOpen library decisions closed inputs typing references valuesTyped
    annotation valueStatic body bodyStatic
  exact value.letFromTyping library decisions inputs typing valuesTyped annotation valueStatic next bodyStatic openTyped binder flag

theorem Form.betaFromOpen (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p)
    (valuesTyped : ∀ value ∈ LexicalScalarCode.sources vs, LexicalScalarCode.Evidence env ctx value)
    (annotation : WordBinder.Annotation)
    (value : Form env ctx p (LexicalScalarCode.sources vs) v) (valueStatic : StaticRegisters v)
    (body : ∀ a : WordBinder.Annotation,
      Form env (a.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
        (LexicalScalarCode.sources (LexicalScalarCode.openValues vs)) (LexicalScalarCode.openBody vs rest))
    (bodyStatic : StaticRegisters rest) (binder : Lean.Name) (info : Lean.BinderInfo) :
    Form env ctx p (LexicalScalarCode.sources vs) (.app (.lam binder annotation.native rest info) v) := by
  obtain ⟨next,openTyped⟩ := value.bindingFromOpen library decisions closed inputs typing references valuesTyped
    annotation valueStatic body bodyStatic
  exact value.betaFromTyping library decisions inputs typing valuesTyped annotation valueStatic next bodyStatic openTyped binder info
end IRComparison.WordFrontend.LexicalScalarSyntax

namespace IRComparison.WordFrontend.LexicalScalarSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarSyntax
set_option maxHeartbeats 2400000

theorem expand_substituteCache
    (refs : ∀ n, expand target (σ n) = sourceReference values n) (raw : Lean.Expr) :
    expand target (LeanBindings.substitute σ raw) = expand values raw := by
  unfold expand
  rw [LeanBindings.substitute_comp]
  exact congrArg (fun f => LeanBindings.substitute f raw) (funext refs)

theorem under_substituteCache
    (refs : ∀ n, expand target (σ n) = sourceReference values n) (raw : Lean.Expr) :
    under target (LeanBindings.substitute (LeanBindings.underSubst σ) raw) = under values raw := by
  have law := expand_substituteCache refs (.lam .anonymous (.const ``Nat []) raw .default)
  simpa only [expand,under,LeanBindings.substitute,Lean.Expr.lam.injEq,true_and,and_true] using law

theorem sourceReference_cons (saved : Lean.Expr) (values : List Lean.Expr) (n : Nat) :
    sourceReference (saved::values) (n+1) = sourceReference values n := by
  simp [sourceReference]

theorem expand_rename_cons (saved : Lean.Expr) (values : List Lean.Expr) (raw : Lean.Expr) :
    expand (saved::values) (LeanBindings.rename Nat.succ raw) = expand values raw := by
  unfold expand
  rw [LeanBindings.substitute_rename]
  exact congrArg (fun f => LeanBindings.substitute f raw) (funext (sourceReference_cons saved values))

theorem substituteCache_cons
    (refs : ∀ n, expand target (σ n) = sourceReference values n) (saved : Lean.Expr) :
    ∀ n, expand (saved::target) (LeanBindings.underSubst σ n) = sourceReference (saved::values) n := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    simpa only [LeanBindings.underSubst,sourceReference_cons,expand_rename_cons] using refs n

private theorem local_of_reference (shape : ReferenceShape (expand values raw)) : LocalOccurrence raw := by
  obtain ⟨n,equal|equal⟩ := shape
  all_goals constructor
  all_goals intros; intro h; subst raw; cases equal

/-- Substitute expressions for source-cache slots without asking the parser
to accept them. Source/reference invariants are preserved under every scalar
constructor, including nested lets and beta applications. -/
theorem Form.substituteCache (form : Form env ctx p values raw) (scope : ReferenceScope p)
    (lookup : ∀ n value, values[n]? = some value → Form env ctx p target (σ n))
    (refs : ∀ n, expand target (σ n) = sourceReference values n) :
    Form env ctx p target (LeanBindings.substitute σ raw) := by
  induction form generalizing target σ with
  | reference found => exact lookup _ _ found
  | index shape same =>
    exact .index (local_of_reference (by rw [expand_substituteCache refs,same]; exact scope.index))
      ((expand_substituteCache refs _).trans same)
  | parameter side shape same ni nl =>
    refine .parameter side (local_of_reference (values := target) ?_) ((expand_substituteCache refs _).trans same) ni nl
    rw [expand_substituteCache refs,same]
    cases side with | left => exact scope.left | right => exact scope.right
  | localValue shape k selected ni nl nr first =>
    apply Form.localValue (k := k)
    · apply local_of_reference (values := target)
      rw [expand_substituteCache refs]
      exact scope.locals _ (List.mem_of_getElem? selected)
    · rwa [expand_substituteCache refs]
    · rwa [expand_substituteCache refs]
    · rwa [expand_substituteCache refs]
    · rwa [expand_substituteCache refs]
    · simpa only [expand_substituteCache refs] using first
  | literal n separated => exact .literal n separated
  | annotatedLiteral a n separated =>
    simpa only [AnnotatedLiteral.native,Lean.mkApp3,Lean.mkApp2,LeanBindings.substitute,WordBinder.Annotation.substitute_native] using
      Form.annotatedLiteral (values := target) a n separated
  | @register values st r same reg separated =>
    apply Form.register (st := LeanBindings.substitute σ st) (r := LeanBindings.substitute σ r)
    · exact (expand_substituteCache refs _).trans same
    · simpa only [expand_substituteCache refs] using reg
    · simpa only [← expand_substituteCache refs,app,LeanBindings.substitute] using separated
  | @binary values a b op left right separated il ir =>
    have children := Form.binary op (il lookup refs) (ir lookup refs)
    cases op <;> apply children <;> simpa only [← expand_substituteCache refs,Binary.nativeHeader,Lean.mkApp2,LeanBindings.substitute] using separated
  | neg child separated ih =>
    apply Form.neg (ih lookup refs)
    simpa only [← expand_substituteCache refs,LeanBindings.substitute] using separated
  | select child decision yes no separated iv ia ib =>
    refine Form.select (iv lookup refs) (d := LeanBindings.substitute σ _) ?_ (ia lookup refs) (ib lookup refs) ?_
    · simpa only [expand_substituteCache refs] using decision
    · simpa only [← expand_substituteCache refs,Branch.Select.source,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,LeanBindings.substitute] using separated
  | annotatedBinary op aa ab ac ad oa ob left right lr rr lt rt lf rf separated il ir =>
    have nh := fun (a : WordBinder.Annotation) => WordBinder.Annotation.substitute_native a σ
    have head : LeanBindings.substitute σ (AnnotatedBinary.nativeHeader op aa ab ac ad) = AnnotatedBinary.nativeHeader op aa ab ac ad := by
      simp only [AnnotatedBinary.nativeHeader,AnnotatedBinary.nativeDictionary,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,app,LeanBindings.substitute,nh]
      rfl
    simp only [Lean.mkApp2,LeanBindings.substitute,head]
    apply Form.annotatedBinary op aa ab ac ad oa ob (il lookup refs) (ir lookup refs)
      (by simpa only [expand_substituteCache refs] using lr) (by simpa only [expand_substituteCache refs] using rr) lt rt lf rf
    simpa only [← expand_substituteCache refs,Lean.mkApp2,LeanBindings.substitute,head] using separated
  | annotatedNeg a operand child vr vt vf separated ih =>
    have head : LeanBindings.substitute σ (AnnotatedNeg.nativeHeader a) = AnnotatedNeg.nativeHeader a := by cases a <;> rfl
    simp only [LeanBindings.substitute,head]
    apply Form.annotatedNeg a operand (ih lookup refs) (by simpa only [expand_substituteCache refs] using vr) vt vf
    simpa only [← expand_substituteCache refs,LeanBindings.substitute,head] using separated
  | @annotatedSelect values v a b vc ac bc ra ca oa ob oc child yes no vr ar br vt at_ bt vf af bf separated iv ia ib =>
    have renamed : LeanBindings.substitute σ (AnnotatedCondition.scalarSource ra ca v (AnnotatedCondition.nativeDecision ca v) a b) =
        AnnotatedCondition.scalarSource ra ca (LeanBindings.substitute σ v) (AnnotatedCondition.nativeDecision ca (LeanBindings.substitute σ v)) (LeanBindings.substitute σ a) (LeanBindings.substitute σ b) := by cases ra <;> cases ca <;> rfl
    rw [renamed]
    apply Form.annotatedSelect ra ca oa ob oc (iv lookup refs) (ia lookup refs) (ib lookup refs)
      (by simpa only [expand_substituteCache refs] using vr) (by simpa only [expand_substituteCache refs] using ar)
      (by simpa only [expand_substituteCache refs] using br) vt at_ bt vf af bf
    simpa only [← expand_substituteCache refs,renamed] using separated
  | @letValue values v rest bodyCore argCore annotation result fv next ar br typed shape binder flag iv ib
  | @beta values v rest bodyCore argCore annotation result fv next ar br typed shape binder flag iv ib =>
    have nextLookup : ∀ n value, (expand values v::values)[n]? = some value →
        Form env ctx p (expand values v::target) (LeanBindings.underSubst σ n) := by
      intro n value found
      cases n with
      | zero => exact .reference rfl
      | succ n =>
        have child := lookup n value found
        exact child.renameCache (ρ := Nat.succ) (by intro k; rfl) (sourceReference_cons _ _)
    have next := ib nextLookup (substituteCache_cons refs (expand values v))
    have ar' : Represents (expand target (LeanBindings.substitute σ v)) argCore := by simpa only [expand_substituteCache refs] using ar
    have br' : Represents (under target (LeanBindings.substitute (LeanBindings.underSubst σ) rest)) bodyCore := by simpa only [under_substituteCache refs] using br
    rw [← expand_substituteCache refs v] at next
    simp only [LeanBindings.substitute,WordBinder.Annotation.substitute_native]
    first
    | exact .letValue annotation result (iv lookup refs) next ar' br' typed shape binder flag
    | exact .beta annotation result (iv lookup refs) next ar' br' typed shape binder flag



/-- Materialization keeps source syntax, including nested scalar bindings;
its proof is an instance of the general cache-substitution induction. -/
theorem Form.materialize (form : Form env ctx p values raw) (scope : ReferenceScope p)
    (valuesForm : ∀ value ∈ values, Form env ctx p [] value) :
    Form env ctx p [] (expand values raw) := by
  apply form.substituteCache scope (σ := sourceReference values)
  · intro n value found
    simpa only [sourceReference,found] using valuesForm value (List.mem_of_getElem? found)
  · intro n; exact expand_nil _

/-- One annotation-parametric scalar body supplies its instantiated source
form, including arbitrary nested scalar lets and beta expressions. -/
theorem Form.instantiateFromSyntax (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (closed : ClosedConstantTypes env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p)
    (references : ReferenceScope p)
    (value : Form env ctx p [] v) (valueStatic : StaticRegisters v)
    (body : ∀ annotation : WordBinder.Annotation,
      Form env (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} [] raw)
    (bodyStatic : StaticRegisters raw) :
    Form env ctx p [] (LeanBindings.instantiate v raw) := by
  obtain ⟨arg,actual,ar,at_,af⟩ := value.evidence valueStatic library decisions inputs typing (by simp)
  simp only [expand_nil] at ar
  have next := (body actual).closeExact actual bodyStatic library.toSignatures closed inputs typing ar at_ af
    (fun _ _ _ head _ different => references.separated head different)
  have sources : ∀ e ∈ closeValues v [], Form env ctx p [] e := by
    intro e member
    have same : e = v := by simpa [closeValues] using member
    subst e; exact value
  have materialized := next.materialize references sources
  have same : expand (closeValues v []) raw = LeanBindings.instantiate v raw := by
    unfold expand LeanBindings.instantiate
    congr 1
    funext n
    cases n <;> rfl
  rwa [same] at materialized

end IRComparison.WordFrontend.LexicalScalarSyntax

namespace IRComparison.WordFrontend.LexicalScalarSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarSyntax
set_option maxHeartbeats 2400000

private theorem liftCache_refs (values : List Lean.Expr) (n : Nat) :
    sourceReference (values.map (LeanBindings.rename Nat.succ)) (liftVar 1 n values.length) =
      LeanBindings.rename Nat.succ (sourceReference values n) := by
  by_cases inside : n < values.length
  · simp only [liftVar,if_pos inside,sourceReference,List.getElem?_map,List.length_map]
    cases found : values[n]? with
    | some v => rfl
    | none => have := List.getElem?_eq_none_iff.mp found; omega
  · have absent : values[n]? = none := List.getElem?_eq_none (by omega)
    have absent' : (values.map (LeanBindings.rename Nat.succ))[1+n]? = none :=
      List.getElem?_eq_none (by simp only [List.length_map]; omega)
    simp only [liftVar,if_neg inside,sourceReference,absent,absent',List.length_map,LeanBindings.rename]
    congr 1
    omega

/-- Weakening shifts only external references, leaving lexical cache slots
and the actual source binding structure intact. -/
theorem expand_liftCache (values : List Lean.Expr) (raw : Lean.Expr) :
    expand (values.map (LeanBindings.rename Nat.succ))
      (LeanBindings.rename (fun n => liftVar 1 n values.length) raw) =
      LeanBindings.rename Nat.succ (expand values raw) := by
  simp only [expand,LeanBindings.substitute_rename,LeanBindings.rename_substitute]
  exact congrArg (fun f => LeanBindings.substitute f raw) (funext (liftCache_refs values))

private theorem under_liftCache (values : List Lean.Expr) (raw : Lean.Expr) :
    under (values.map (LeanBindings.rename Nat.succ))
      (LeanBindings.rename (LeanBindings.underRename (fun n => liftVar 1 n values.length)) raw) =
      LeanBindings.rename (LeanBindings.underRename Nat.succ) (under values raw) := by
  have h := expand_liftCache values (.lam .anonymous (.const ``Nat []) raw .default)
  simpa only [expand,under,LeanBindings.rename,LeanBindings.substitute,Lean.Expr.lam.injEq,
    true_and,and_true] using h

private theorem cache_under (values : List Lean.Expr) (value : Lean.Expr) :
    LeanBindings.underRename (fun n => liftVar 1 n values.length) =
      fun n => liftVar 1 n (value::values).length := by
  funext n
  cases n with
  | zero => rfl
  | succ n => by_cases h : n < values.length <;> simp [LeanBindings.underRename,liftVar,h,Nat.add_comm]

private theorem occurrence_lift (shape : LocalOccurrence raw) (ρ : Nat → Nat) :
    LocalOccurrence (LeanBindings.rename ρ raw) := by
  cases raw with
  | letE name ty value body flag => exact False.elim (shape.notLet name ty value body flag rfl)
  | app f a => cases f with
    | lam name ty body info => exact False.elim (shape.notBeta name ty body info a rfl)
    | _ => exact ⟨by intros; simp [LeanBindings.rename],by intros; simp [LeanBindings.rename]⟩
  | _ => exact ⟨by intros; simp [LeanBindings.rename],by intros; simp [LeanBindings.rename]⟩

private theorem annotation_rename (a : WordBinder.Annotation) (ρ : Nat → Nat) :
    LeanBindings.rename ρ a.native = a.native := by cases a <;> rfl

/-- Add a retained scalar slot to an existing source expression. This single
induction covers all scalar constructors, including lexical let/beta and
mixed Word/BV32 annotations. It does not assume a successful parse. -/
theorem Form.liftScalar (form : Form env ctx p values raw)
    (closed : ClosedConstantTypes env) (inputs : InputsTyped env ctx p)
    (typing : LexicalScalarCode.ScopeTyped env ctx p) (references : ReferenceScope p)
    (binder : VExpr) :
    Form env (binder::ctx) {p.lift with locals := .bvar 0::p.lift.locals}
      (values.map (LeanBindings.rename Nat.succ))
      (LeanBindings.rename (fun n => liftVar 1 n values.length) raw) := by
  have heads {e : Lean.Expr} {name : Lean.Name} {levels : List Lean.Level}
      (head : e.getAppFn = .const name levels) (different : name ≠ ``BitVec.ofNat) :
      Separated {p.lift with locals := .bvar 0::p.lift.locals} e :=
    references.scalar.separated head different
  have liftedTyped {core} {a : WordBinder.Annotation}
      (h : CastTyping env 0 (SourceCasts env) ctx core a.core) :
      CastTyping env 0 (SourceCasts env) (binder::ctx) core.lift a.core := by
    simpa only [a.closed.lift_eq] using h.lift closed SourceCasts.closed binder
  have liftedShape {core} {a : WordBinder.Annotation} (h : ValueShape env ctx core a.core) :
      ValueShape env (binder::ctx) core.lift a.core := by
    simpa only [a.closed.lift_eq] using LexicalScalarCode.valueShape_lift h closed binder
  induction form with
  | @reference values n value selected =>
    have inside := List.getElem?_eq_some_iff.mp selected |>.1
    simp only [LeanBindings.rename,liftVar,if_pos inside]
    exact .reference (value := LeanBindings.rename Nat.succ value) (by simp only [List.getElem?_map,selected,Option.map_some])
  | @index raw values shape same =>
    exact .index (occurrence_lift shape _) ((expand_liftCache values raw).trans (congrArg _ same))
  | @parameter raw values side shape same ni nl =>
    have sideLift : side.source {p.lift with locals := .bvar 0::p.lift.locals} =
        LeanBindings.rename Nat.succ (side.source p) := by cases side <;> rfl
    refine .parameter side (occurrence_lift shape _) ?_ ?_ ?_
    · exact (expand_liftCache values raw).trans ((congrArg _ same).trans sideLift.symm)
    · change sameTerm (side.source {p.lift with locals := .bvar 0::p.lift.locals}) (LeanBindings.rename Nat.succ p.i) = false
      rw [sideLift,sameTerm_lift (side.representation inputs).property inputs.i.property]
      exact ni
    · intro h
      change sameTerm (side.source {p.lift with locals := .bvar 0::p.lift.locals}) (LeanBindings.rename Nat.succ p.x) = false
      rw [sideLift,sameTerm_lift (side.representation inputs).property inputs.x.property]
      exact nl h
  | @localValue raw values shape k selected ni nl nr first =>
    obtain ⟨core,a,rep,typed,vf⟩ := typing.locals _ (List.mem_of_getElem? selected)
    apply Form.localValue (occurrence_lift shape _) (k+1)
    · simpa only [Inputs.lift,List.getElem?_cons_succ,List.getElem?_map,selected,Option.map_some,expand_liftCache]
    · simpa only [expand_liftCache,Inputs.lift,sameTerm_lift rep inputs.i.property] using ni
    · simpa only [expand_liftCache,Inputs.lift,sameTerm_lift rep inputs.x.property] using nl
    · simpa only [expand_liftCache,Inputs.lift,sameTerm_lift rep inputs.y.property] using nr
    · intro j hj
      cases j with
      | zero =>
        change sameTerm _ (.bvar 0) = false
        rw [expand_liftCache]
        cases h : sameTerm (LeanBindings.rename Nat.succ (expand values raw)) (.bvar 0) with
        | false => rfl
        | true =>
          have bad := sameTerm_sound rep.lift Represents.bvar h
          have impossible (e : VExpr) : e.lift ≠ .bvar 0 := by
            cases e <;> simp [VExpr.lift,VExpr.liftN,liftVar]
          exact False.elim (impossible core bad)
      | succ j =>
        change (((p.locals.map (LeanBindings.rename Nat.succ))[j]?).map (sameTerm _)).getD false = false
        rw [List.getElem?_map]
        cases found : p.locals[j]? with
        | none => rfl
        | some e =>
          obtain ⟨other,oa,er,et,ef⟩ := typing.locals e (List.mem_of_getElem? found)
          simpa only [found,Option.map_some,Option.getD_some,expand_liftCache,sameTerm_lift rep er] using first j (by omega)
  | literal n _ => exact .literal n (heads rfl (by decide))
  | annotatedLiteral a n _ =>
    simpa only [AnnotatedLiteral.native,Lean.mkApp3,Lean.mkApp2,LeanBindings.rename,annotation_rename] using
      Form.annotatedLiteral (values := _) a n (by cases a <;> exact heads rfl (by decide))
  | @register values st r same reg _ =>
    apply Form.register (st := LeanBindings.rename (fun n => liftVar 1 n values.length) st)
      (r := LeanBindings.rename (fun n => liftVar 1 n values.length) r)
    · simpa only [Inputs.lift,expand_liftCache] using congrArg (LeanBindings.rename Nat.succ) same
    · rw [expand_liftCache]
      exact ⟨⟨_,reg.represented.property.lift⟩,reg.typed.lift closed binder,
        LeanBindings.rename_wellScoped _ 0 0 reg.closed Nat.succ (by intros; omega)⟩
    · exact heads rfl (by decide)
  | binary op left right _ il ir =>
    cases op <;> exact .binary _ il ir (heads rfl (by decide))
  | neg value _ ih => exact .neg ih (heads rfl (by decide))
  | @select values v d a b value decision yes no _ iv ia ib =>
    refine .select iv (d := LeanBindings.rename (fun n => liftVar 1 n values.length) d) ?_ ia ib (heads rfl (by decide))
    obtain ⟨vc,dc,vr,dr,pt,dt⟩ := decision.typing
    have hc : Branch.testHeader.ClosedN 0 := Branch.testHeader_represents.closed 0 rfl
    have zc : (literalTerm 0).ClosedN 0 := (Arithmetic.literal_represents 0).closed 0 rfl
    refine ⟨vc.lift,dc.lift,?_,?_,?_,?_⟩
    · rw [expand_liftCache]; exact vr.lift
    · rw [expand_liftCache]; exact dr.lift
    · simpa only [Branch.condition,equalValues,applications,VExpr.lift,VExpr.liftN,hc.liftN_eq (Nat.zero_le _),zc.liftN_eq (Nat.zero_le _)] using pt.lift closed SourceCasts.closed binder
    · simpa only [Branch.condition,equalValues,applications,VExpr.lift,VExpr.liftN,hc.liftN_eq (Nat.zero_le _),zc.liftN_eq (Nat.zero_le _)] using dt.lift closed SourceCasts.closed binder
  | annotatedBinary op aa ab ac ad oa ob left right lr rr lt rt lf rf _ il ir =>
    have header (ρ : Nat → Nat) : LeanBindings.rename ρ
        (AnnotatedBinary.nativeHeader op aa ab ac ad) = AnnotatedBinary.nativeHeader op aa ab ac ad := by
      simp only [AnnotatedBinary.nativeHeader,AnnotatedBinary.nativeDictionary,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,app,LeanBindings.rename,annotation_rename]; rfl
    simp only [Lean.mkApp2,LeanBindings.rename,header]
    apply Form.annotatedBinary op aa ab ac ad oa ob il ir
      (by rw [expand_liftCache]; exact lr.lift) (by rw [expand_liftCache]; exact rr.lift)
      (liftedTyped lt) (liftedTyped rt) (liftedShape lf) (liftedShape rf)
    cases op <;> exact heads rfl (by decide)
  | annotatedNeg a operand child vr vt vf _ ih =>
    have header (ρ : Nat → Nat) : LeanBindings.rename ρ (AnnotatedNeg.nativeHeader a) = AnnotatedNeg.nativeHeader a := by cases a <;> rfl
    simp only [LeanBindings.rename,header]
    exact .annotatedNeg a operand ih (by rw [expand_liftCache]; exact vr.lift)
      (liftedTyped vt) (liftedShape vf) (by cases a <;> exact heads rfl (by decide))
  | @annotatedSelect values v a b vc ac bc ra ca oa ob oc child yes no vr ar br vt at_ bt vf af bf _ iv ia ib =>
    have renamed : LeanBindings.rename (fun n => liftVar 1 n values.length)
        (AnnotatedCondition.scalarSource ra ca v (AnnotatedCondition.nativeDecision ca v) a b) =
        AnnotatedCondition.scalarSource ra ca (LeanBindings.rename (fun n => liftVar 1 n values.length) v)
          (AnnotatedCondition.nativeDecision ca (LeanBindings.rename (fun n => liftVar 1 n values.length) v))
          (LeanBindings.rename (fun n => liftVar 1 n values.length) a) (LeanBindings.rename (fun n => liftVar 1 n values.length) b) := by cases ra <;> cases ca <;> rfl
    rw [renamed]
    exact .annotatedSelect ra ca oa ob oc iv ia ib
      (by rw [expand_liftCache]; exact vr.lift) (by rw [expand_liftCache]; exact ar.lift) (by rw [expand_liftCache]; exact br.lift)
      (liftedTyped vt) (liftedTyped at_) (liftedTyped bt) (liftedShape vf) (liftedShape af) (liftedShape bf)
      (by cases ra <;> cases ca <;> exact heads rfl (by decide))
  | @letValue values v rest bc ac annotation result fv next ar br typed shape name flag iv ib
  | @beta values v rest bc ac annotation result fv next ar br typed shape name flag iv ib =>
    have shifted := ib
    simp only [List.map_cons,← expand_liftCache,← cache_under] at shifted
    have bRep : Represents (under (values.map (LeanBindings.rename Nat.succ))
        (LeanBindings.rename (LeanBindings.underRename (fun n => liftVar 1 n values.length)) rest)) (bc.liftN 1 1) := by
      rw [under_liftCache]
      have renameEq : LeanBindings.underRename Nat.succ = fun n => liftVar 1 n 1 := by funext n; cases n <;> simp [LeanBindings.underRename,liftVar]; omega
      simpa only [renameEq,coreRename_lift] using br.rename (LeanBindings.underRename Nat.succ)
    have bTyped : CastTyping env 0 (SourceCasts env) (annotation.core::binder::ctx) (bc.liftN 1 1) result.core := by
      simpa only [annotation.closed.liftN_eq (Nat.zero_le _),result.closed.liftN_eq (Nat.zero_le _)] using
        typed.weakN closed SourceCasts.closed (Ctx.LiftN.succ Ctx.LiftN.one)
    have bShape : ∃ actual : WordBinder.Annotation, ValueShape env (binder::ctx) ((bc.liftN 1 1).inst ac.lift) actual.core := by
      obtain ⟨actual,shape⟩ := shape
      exact ⟨actual,by simpa only [VExpr.lift,VExpr.liftN_inst_hi] using liftedShape shape⟩
    simp only [LeanBindings.rename,annotation_rename]
    first
    | exact .letValue annotation result iv shifted (by rw [expand_liftCache]; exact ar.lift) bRep bTyped bShape name flag
    | exact .beta annotation result iv shifted (by rw [expand_liftCache]; exact ar.lift) bRep bTyped bShape name flag

end IRComparison.WordFrontend.LexicalScalarSyntax
