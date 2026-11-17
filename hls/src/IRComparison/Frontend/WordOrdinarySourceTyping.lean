import IRComparison.Frontend.WordOrdinarySource

/-! Derive internal source representations/types from original source rules.
These are conclusions of induction; they are not hypotheses of OrdinarySource.
This module does not yet assert current-State use or parser success. -/
namespace IRComparison.WordFrontend.OrdinarySource
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 2400000

/-- The proof calculus view of an original lexical type. -/
def Parameter.core : Parameter → VExpr
  | .scalar a => a.core
  | .state => stateType
  | .natural => natType
  | .unit => UnitStep.unitType

def Result.core : Result → VExpr
  | .body => stateType
  | .step => Step.stepState

def Signature.core (s : Signature) : VExpr :=
  (s.domains.map Parameter.core).foldr VExpr.forallE (optionType s.result.core)

def Slot.core : Slot → VExpr
  | .value p => p.core
  | .function s => s.core

def Context.core (Γ : Context) : List VExpr := Γ.map Slot.core

@[simp] theorem Parameter.closed (p : Parameter) : p.core.ClosedN 0 := by
  cases p with
  | scalar a => exact a.closed
  | state => trivial
  | natural => trivial
  | unit => trivial

@[simp] theorem Result.closed (r : Result) : r.core.ClosedN 0 := by cases r <;> trivial

@[simp] theorem Signature.closed (s : Signature) : s.core.ClosedN 0 := by
  rcases s with ⟨domains,result⟩
  induction domains with
  | nil => exact ⟨by trivial,result.closed⟩
  | cons head tail ih => exact ⟨head.closed,ih.mono (by decide)⟩

@[simp] theorem Slot.closed (s : Slot) : s.core.ClosedN 0 := by
  cases s with | value p => exact p.closed | function f => exact f.closed

theorem Parameter.represented (p : Parameter) : Represents p.native p.core := by
  cases p with
  | scalar a => exact a.represented
  | state => exact .constant rfl
  | natural => exact .constant rfl
  | unit => exact .constant rfl

theorem Result.represented (r : Result) : Represents r.native r.core := by
  cases r with | body => exact .constant rfl | step => exact .app (.constant rfl) (.constant rfl)

theorem Parameter.typed (library : ScopedSyntax.Library env) (p : Parameter) :
    DirectTyping env 0 ctx p.core (.sort (.succ .zero)) := by
  cases p with
  | scalar a => exact a.type_typed library.scalars.toSignatures
  | state => exact .constant library.returns.state (by simp) rfl
  | natural => exact .constant library.scalars.natural (by simp) rfl
  | unit => exact library.units.type_typed

theorem Result.typed (library : ScopedSyntax.Library env) (r : Result) :
    DirectTyping env 0 ctx r.core (.sort (.succ .zero)) := by
  cases r with
  | body => exact .constant library.returns.state (by simp) rfl
  | step => exact library.steps.step_typed

/-- Typed lookup is generated from the original lexical slot, including
arbitrary numbers of intervening State/read/helper binders. -/
theorem Context.lookup {Γ : Context} {slot : Slot} (found : Γ[index]? = some slot) : Lookup Γ.core index slot.core := by
  induction Γ generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      have eq : head = slot := Option.some.inj found
      subst head
      simpa only [Context.core,List.map_cons,slot.closed.lift_eq] using
        (Lookup.zero (Γ := Context.core tail) (ty := slot.core))
    | succ n =>
      simpa only [Context.core,List.map_cons,slot.closed.lift_eq] using Lookup.succ (ih found)

/-- Recover the original lexical slot from an internal lookup. Source slot
types are closed, so lifting them under intervening binders changes nothing. -/
theorem Context.lookup_origin {Γ : Context} (found : Lookup Γ.core index ty) :
    ∃ slot, Γ[index]? = some slot ∧ ty = slot.core := by
  induction Γ generalizing index ty with
  | nil => cases found
  | cons head tail ih =>
    cases found with
    | zero => exact ⟨head,rfl,head.closed.lift_eq⟩
    | succ found =>
      obtain ⟨slot,selected,rfl⟩ := ih found
      exact ⟨slot,selected,slot.closed.lift_eq⟩

theorem Signature.Spelling.represented (spelling : Signature.Spelling signature raw) :
    Represents raw signature.core := by
  induction spelling with
  | result r => exact .app (.constant rfl) r.represented
  | arrow head tail binder info ih => exact .forallE head.represented ih

theorem StateRef.typing (source : StateRef Γ raw) :
    ∃ core, Represents raw core ∧ DirectTyping env 0 Γ.core core stateType := by
  cases source with
  | «variable» found => exact ⟨_,.bvar,.bvar (Context.lookup found)⟩

/-- Scalar typing follows the original tree once, including original let/β
bodies. No substituted copy of a body is requested from the caller. -/
theorem Scalar.typing (source : Scalar Γ raw annotation) (library : ScopedSyntax.Library env) :
    ∃ core, Represents raw core ∧ CastTyping env 0 (SourceCasts env) Γ.core core annotation.core ∧
      LexicalScalarSyntax.ValueShape env Γ.core core annotation.core := by
  induction source with
  | «variable» found => exact ⟨_,.bvar,.bvar (Context.lookup found),.bound⟩
  | literal a n => exact ⟨_,AnnotatedLiteral.represented a n,
      AnnotatedLiteral.annotation_typed library.scalars.toSignatures a n,
      .constant rfl (by simp [LexicalScalarSyntax.valueHeads])⟩
  | @register gamma raw state register rn =>
    obtain ⟨sc,sr,st⟩ := state.typing (env := env)
    let index := rn.argument (ctx := Context.core gamma) library.scalars.toSignatures register
    have fn : CastTyping env 0 (SourceCasts env) gamma.core (.const ``HybridWord.State.regs [])
        (.forallE stateType (.forallE natType wordType)) := .constant library.scalars.registerAccessor (by simp) rfl
    have first := CastTyping.application fn (st.withCasts _)
    simp only [stateType,natType,wordType,VExpr.inst] at first
    have applied := CastTyping.application first (index.typed.withCasts _)
    exact ⟨_,app_represents (.constant rfl) (.cons sr (.cons index.represented.property .nil)),
      applied,.constant rfl (by simp [LexicalScalarSyntax.valueHeads])⟩
  | natural found =>
    exact ⟨_,NaturalScope.index_represents .bvar,
      (NaturalScope.index_inferred library.scalars.toSignatures library.naturalLoops.ofNat (.bvar (Context.lookup found))).mono (fun _ _ _ h => .arithmetic h),
      .constant rfl (by simp [LexicalScalarSyntax.valueHeads])⟩
  | binary op aa ab ac ad left right il ir =>
    obtain ⟨lc,lr,lt,lf⟩ := il
    obtain ⟨rc,rr,rt,rf⟩ := ir
    have first := CastTyping.checkedApplication (AnnotatedBinary.header_typed library.scalars.toSignatures op aa ab ac ad)
      (aa.argument (WordBinder.Annotation.result _ lt))
    simp only [VExpr.inst,ab.closed.instN_eq (Nat.zero_le _),ac.closed.instN_eq (Nat.zero_le _)] at first
    have applied := CastTyping.checkedApplication first (ab.argument (WordBinder.Annotation.result _ rt))
    refine ⟨_,.app (.app (AnnotatedBinary.represented op aa ab ac ad) lr) rr,?_,?_⟩
    · simpa only [VExpr.inst,ac.closed.instN_eq (Nat.zero_le _)] using applied
    · cases op <;> exact .constant rfl (by simp [LexicalScalarSyntax.valueHeads,Binary.method])
  | neg a value ih =>
    obtain ⟨vc,vr,vt,vf⟩ := ih
    have applied := CastTyping.checkedApplication (AnnotatedNeg.header_typed library.scalars.toSignatures a)
      (a.argument (WordBinder.Annotation.result _ vt))
    exact ⟨_,.app (AnnotatedNeg.represented a) vr,
      by simpa only [VExpr.inst,a.closed.instN_eq (Nat.zero_le _)] using applied,
      .constant rfl (by simp [LexicalScalarSyntax.valueHeads])⟩
  | select ra ca guard yes no ig iy ino =>
    obtain ⟨vc,vr,vt,vf⟩ := ig
    obtain ⟨ac,ar,at_,af⟩ := iy
    obtain ⟨bc,br,bt,bf⟩ := ino
    obtain ⟨ct,dt⟩ := AnnotatedCondition.condition_typed library.decisions library.scalars.toSignatures ca
      (WordBinder.Annotation.result _ vt)
    have result := Branch.ite_typed (ra.type_typed library.scalars.toSignatures) ra.closed ct dt
      (ra.argument (WordBinder.Annotation.result _ at_)) (ra.argument (WordBinder.Annotation.result _ bt)) library.scalars.ite
    exact ⟨_,AnnotatedCondition.scalarSource_represents ra ca vr (AnnotatedCondition.decision_represents ca vr) ar br,
      result,.constant rfl (by simp [LexicalScalarSyntax.valueHeads])⟩
  | letValue a value body binder flag iv ib
  | beta a value body binder info iv ib =>
    obtain ⟨vc,vr,vt,vf⟩ := iv
    obtain ⟨bc,br,bt,bf⟩ := ib
    have applied := CastTyping.checkedApplication (.lambda ((a.type_typed library.scalars.toSignatures).withCasts _) bt)
      (a.argument (WordBinder.Annotation.result _ vt))
    refine ⟨.app (.lam a.core bc) vc,?_,?_,.beta a _ bt⟩
    · first | exact .letE a.represented vr br | exact .app (.lam a.represented br) vr
    · simpa only [show ∀ (r : WordBinder.Annotation) (v : VExpr), r.core.inst v = r.core from fun r _ => r.closed.instN_eq (Nat.zero_le _)] using applied

/-- State typing is derived even for updates used directly as helper actuals. -/
theorem StateValue.typing (source : StateValue Γ raw) (library : ScopedSyntax.Library env) :
    ∃ core, Represents raw core ∧ CastTyping env 0 (SourceCasts env) Γ.core core stateType := by
  cases source with
  | reference state =>
    obtain ⟨sc,sr,st⟩ := state.typing (env := env)
    exact ⟨sc,sr,st.withCasts _⟩
  | set state register rn value =>
    obtain ⟨sc,sr,st⟩ := state.typing (env := env)
    obtain ⟨vc,vr,vt,_⟩ := value.typing library
    let index := rn.argument (ctx := Γ.core) library.scalars.toSignatures register
    have fn : CastTyping env 0 (SourceCasts env) Γ.core (.const ``HybridWord.State.set [])
        Return.setterSignature := .constant library.setter (by simp) rfl
    have first := CastTyping.application fn (st.withCasts _)
    simp only [Return.setterSignature,stateType,wordType,VExpr.inst] at first
    have second := CastTyping.application first (index.typed.withCasts _)
    simp only [stateType,wordType,VExpr.inst] at second
    exact ⟨_,app_represents (.constant rfl) (.cons sr (.cons index.represented.property (.cons vr .nil))),
      CastTyping.checkedApplication second (WordBinder.Annotation.result _ vt)⟩

/-- Source arguments are checked at the declared annotation. Their actual
Word/BV32 spelling need not equal that annotation. -/
theorem Argument.typing (source : Argument Γ parameter raw) (library : ScopedSyntax.Library env) :
    ∃ core, Represents raw core ∧ CheckedTyping env 0 (SourceCasts env) Γ.core core parameter.core := by
  cases source with
  | scalar value =>
    obtain ⟨vc,vr,vt,_⟩ := value.typing library
    exact ⟨vc,vr,WordBinder.Annotation.argument _ (WordBinder.Annotation.result _ vt)⟩
  | state value =>
    obtain ⟨vc,vr,vt⟩ := value.typing (env := env)
    exact ⟨vc,vr,.exact (vt.withCasts _)⟩
  | unit => exact ⟨_,.constant rfl,.exact (library.units.value_typed.withCasts _)⟩
  | unitVariable found => exact ⟨_,.bvar,.exact (.bvar (Context.lookup found))⟩

private theorem readTyping {Γ : Context} (library : ScopedSyntax.Library env)
    (annotation : WordBinder.Annotation)
    (sr : Represents st sc) (styped : DirectTyping env 0 Γ.core sc stateType)
    (ar : Represents a ac) (atyped : DirectTyping env 0 Γ.core ac natType)
    (nr : Represents n nc) (ntyped : CastTyping env 0 (SourceCasts env) Γ.core nc natType) :
    ∃ core, Represents (FixedReadSourceCompleteness.naturalSource annotation st a n) core ∧
      CastTyping env 0 (SourceCasts env) Γ.core core (optionType annotation.core) := by
  have fn : DirectTyping env 0 Γ.core (.const ``HybridWord.State.arrays []) WordFrontend.Read.arraysSignature :=
    .constant library.reads.arrays (by simp) rfl
  have first := DirectTyping.application fn styped
  simp only [WordFrontend.Read.arraysSignature,WordFrontend.Read.arrayType,wordType,stateType,VExpr.inst] at first
  have arrayTyped := DirectTyping.application first atyped
  cases annotation with
  | word =>
    have head := CastTyping.application library.reads.header_typed (arrayTyped.withCasts (SourceCasts env))
    simp only [WordFrontend.Read.arrayType,optionType,wordType,VExpr.inst] at head
    exact ⟨_,WordFrontend.Read.source_represents sr ar nr,CastTyping.application head ntyped⟩
  | bitvec =>
    have head := CastTyping.application (library.reads.bits_header_typed library.scalars.toSignatures)
      (arrayTyped.withCasts (SourceCasts env))
    have bvInst (v : VExpr) (k : Nat) : bitvecType.inst v k = bitvecType :=
      (WordBinder.Annotation.closed .bitvec).instN_eq (Nat.zero_le k)
    simp only [natType,optionType,VExpr.inst,bvInst] at head
    exact ⟨_,WordFrontend.Read.bitsSource_represents sr ar nr,
      by simpa only [optionType,VExpr.inst,bvInst] using CastTyping.application head ntyped⟩

/-- Both read spellings derive their Option type from the original array and
index. Declaration checking never supplies a parser-success premise. -/
theorem Read.typing (source : Read ds Γ raw annotation) (library : ScopedSyntax.Library env) :
    ∃ core, Represents raw core ∧ CastTyping env 0 (SourceCasts env) Γ.core core (optionType annotation.core) := by
  cases source with
  | natural annotation state array index an nn declared =>
    obtain ⟨sc,sr,st⟩ := state.typing (env := env)
    let aa := an.argument (ctx := Γ.core) library.scalars.toSignatures array
    let na := nn.argument (ctx := Γ.core) library.scalars.toSignatures index
    exact readTyping library annotation sr st aa.represented.property aa.typed na.represented.property (na.typed.withCasts _)
  | word annotation state array an declared index =>
    obtain ⟨sc,sr,st⟩ := state.typing (env := env)
    obtain ⟨kc,kr,kt,_⟩ := index.typing library
    let aa := an.argument (ctx := Γ.core) library.scalars.toSignatures array
    exact readTyping library annotation sr st aa.represented.property aa.typed
      (.app (.app (.constant rfl) Arithmetic.width_represents) kr)
      (library.reads.word_index_typed library.scalars.toSignatures (WordBinder.Annotation.result _ kt))

private theorem optionArgument
    (declared : env.constants ``Option = some optionSignature)
    (actual expected : WordBinder.Annotation)
    (typed : CastTyping env 0 (SourceCasts env) ctx core (optionType actual.core)) :
    CheckedTyping env 0 (SourceCasts env) ctx core (optionType expected.core) := by
  cases actual <;> cases expected
  · exact .exact typed
  · exact .converted typed (.wordOption declared)
  · exact .converted typed (.bitvecOption declared)
  · exact .exact typed

/-- Original function types are obtained from the declared parameter list;
callers do not supply a separate internal type derivation for each arity. -/
theorem Signature.typed (signature : Signature) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) :
    ∃ level, CastTyping env 0 (SourceCasts env) ctx signature.core (.sort level) := by
  apply FunctionSyntax.functionType_typed _ closed
  · intro d hd
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hd
    exact ⟨_,(p.typed library).withCasts _⟩
  · have optionHead : DirectTyping env 0 [] (.const ``Option [.zero])
        (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
      .constant library.returns.option (by simp [VLevel.WF]) rfl
    exact (DirectTyping.application optionHead (signature.result.typed library)).withCasts _

/-- Application typing consumes the original arguments in order. Bound
helper functions and directly written lambdas use the same proof. -/
theorem Arguments.applyTyping (arguments : Arguments Γ domains raws)
    (library : ScopedSyntax.Library env) (result : Result)
    (represented : Represents fn fc)
    (typed : CastTyping env 0 (SourceCasts env) Γ.core fc (Signature.core ⟨domains,result⟩)) :
    ∃ core, Represents (raws.foldl Lean.Expr.app fn) core ∧
      CastTyping env 0 (SourceCasts env) Γ.core core (optionType result.core) := by
  induction arguments generalizing fn fc with
  | nil => exact ⟨fc,represented,typed⟩
  | @cons head raw tail rest argument args ih =>
    obtain ⟨ac,ar,at_⟩ := argument.typing library
    have applied := CastTyping.checkedApplication typed at_
    have restClosed := Signature.closed ⟨tail,result⟩
    have next : CastTyping env 0 (SourceCasts env) Γ.core (.app fc ac) (Signature.core ⟨tail,result⟩) := by
      change CastTyping env 0 (SourceCasts env) Γ.core (.app fc ac) ((Signature.core ⟨tail,result⟩).inst ac) at applied
      simpa only [restClosed.instN_eq (Nat.zero_le _)] using applied
    exact ih (.app represented ar) next

/-- One simultaneous induction over original functions and command bodies.
Every recursive premise is the original child, not an expanded/retained copy. -/
private theorem sourceTyping (library : ScopedSyntax.Library env) (closed : ClosedConstantTypes env) :
    (∀ {Γ raw signature}, Function ds Γ raw signature →
      ∃ core, Represents raw core ∧ CastTyping env 0 (SourceCasts env) Γ.core core signature.core) ∧
    (∀ {Γ result raw}, Body ds Γ result raw →
      ∃ core, Represents raw core ∧ CastTyping env 0 (SourceCasts env) Γ.core core (optionType result.core)) := by
  refine ⟨@Function.rec ds (fun Γ raw signature _ => ∃ core, Represents raw core ∧ CastTyping env 0 (SourceCasts env) Γ.core core signature.core) (fun Γ result raw _ => ∃ core, Represents raw core ∧ CastTyping env 0 (SourceCasts env) Γ.core core (optionType result.core))
    ?«variable» ?lambda ?returns ?yield ?write ?copy ?letScalar ?letState ?bindState ?bindRead ?branch ?staticRange ?naturalRange ?unitSequence ?call ?letFunction,
    @Body.rec ds (fun Γ raw signature _ => ∃ core, Represents raw core ∧ CastTyping env 0 (SourceCasts env) Γ.core core signature.core) (fun Γ result raw _ => ∃ core, Represents raw core ∧ CastTyping env 0 (SourceCasts env) Γ.core core (optionType result.core))
    ?«variable» ?lambda ?returns ?yield ?write ?copy ?letScalar ?letState ?bindState ?bindRead ?branch ?staticRange ?naturalRange ?unitSequence ?call ?letFunction⟩
  all_goals first
    | (case «variable» =>
      intro Γ index signature found
      exact ⟨_,.bvar,.bvar (Context.lookup found)⟩)
    | (case lambda =>
      intro raw Γ body head tail result shape bodySource ihBody
      obtain ⟨bc,br,bt⟩ := ihBody
      have domainsRep : List.Forall₂ Represents ((head::tail).map Parameter.native) ((head::tail).map Parameter.core) := by
        have all (ps : List Parameter) : List.Forall₂ Represents (ps.map Parameter.native) (ps.map Parameter.core) := by
          induction ps with
          | nil => exact .nil
          | cons p ps ih => exact .cons p.represented ih
        exact all _
      have params : ∀ d ∈ (head::tail).map Parameter.core,
          ∃ u, CastTyping env 0 (SourceCasts env) [] d (.sort u) := by
        intro d hd
        obtain ⟨p,_,rfl⟩ := List.mem_map.mp hd
        exact ⟨_,(p.typed library).withCasts _⟩
      have bodyTyped : CastTyping env 0 (SourceCasts env)
          (((head::tail).map Parameter.core).reverse ++ Γ.core) bc (optionType result.core) := by
        simpa [Context.core,List.map_append,List.map_reverse,List.map_map,Slot.core] using bt
      obtain ⟨rep,typed⟩ := FunctionSyntax.lambdaSource_typed shape domainsRep closed params br bodyTyped
      exact ⟨_,rep,typed⟩)
    | (case returns =>
      intro Γ st tag value
      obtain ⟨sc,sr,st⟩ := value.typing library
      have header := (library.returns.header_typed (ctx := Γ.core) tag).withCasts (SourceCasts env)
      exact ⟨_,.app tag.header_represents sr,CastTyping.application header st⟩)
    | (case yield =>
      intro Γ st value
      obtain ⟨sc,sr,st⟩ := value.typing library
      exact ⟨_,Step.yield_represents sr,Step.yield_typed library.steps st⟩)
    | (case write =>
      intro Γ st k ka v va state array an declared index value
      obtain ⟨sc,sr,st⟩ := state.typing (env := env)
      obtain ⟨ic,ir,it,_⟩ := index.typing library
      obtain ⟨vc,vr,vt,_⟩ := value.typing library
      let aa := an.argument (ctx := Γ.core) library.scalars.toSignatures array
      have fn : CastTyping env 0 (SourceCasts env) Γ.core (.const ``HybridWord.State.write []) writeSignature :=
        .constant library.writer (by simp) rfl
      have a1 := CastTyping.application fn (st.withCasts _)
      simp only [writeSignature,stateType,wordType,optionType,VExpr.inst] at a1
      have a2 := CastTyping.application a1 (aa.typed.withCasts _)
      simp only [stateType,wordType,optionType,VExpr.inst] at a2
      have a3 := CastTyping.checkedApplication a2 (WordBinder.Annotation.result _ it)
      simp only [stateType,wordType,optionType,VExpr.inst] at a3
      exact ⟨_,app_represents (.constant rfl) (.cons sr (.cons aa.represented.property (.cons ir (.cons vr .nil)))),
        CastTyping.checkedApplication a3 (WordBinder.Annotation.result _ vt)⟩)
    | (case copy =>
      intro Γ st state destination origin count dn sn cn target original
      obtain ⟨sc,sr,st⟩ := state.typing (env := env)
      let da := dn.argument (ctx := Γ.core) library.scalars.toSignatures destination
      let sa := sn.argument (ctx := Γ.core) library.scalars.toSignatures origin
      let na := cn.argument (ctx := Γ.core) library.scalars.toSignatures count
      have fn : CastTyping env 0 (SourceCasts env) Γ.core (.const ``HybridWord.State.copy []) copySourceSignature :=
        .constant library.copier (by simp) rfl
      have a1 := CastTyping.application fn (st.withCasts _)
      simp only [copySourceSignature,stateType,optionType,VExpr.inst] at a1
      have a2 := CastTyping.application a1 (da.typed.withCasts _)
      simp only [stateType,optionType,VExpr.inst] at a2
      have a3 := CastTyping.application a2 (sa.typed.withCasts _)
      simp only [stateType,optionType,VExpr.inst] at a3
      exact ⟨_,app_represents (.constant rfl) (.cons sr (.cons da.represented.property (.cons sa.represented.property (.cons na.represented.property .nil)))),
        CastTyping.application a3 (na.typed.withCasts _)⟩)
    | (case letScalar =>
      intro Γ v actual b result annotation value body binder flag ihBody
      obtain ⟨vc,vr,vt,_⟩ := value.typing library
      obtain ⟨core,rep,_,typed⟩ := FunctionSyntax.sourceCheckedLetTyping annotation.represented
        ((annotation.type_typed library.scalars.toSignatures).withCasts _) (Signature.closed ⟨[],result⟩)
        ⟨vc,vr,annotation.argument (WordBinder.Annotation.result _ vt)⟩ (ihBody) binder flag .default
      exact ⟨core,rep,typed⟩)
    | (case letState =>
      intro Γ v b result value body binder flag ihBody
      obtain ⟨vc,vr,vt⟩ := value.typing library
      obtain ⟨core,rep,_,typed⟩ := FunctionSyntax.sourceCheckedLetTyping (Parameter.represented .state)
        ((Parameter.typed library .state).withCasts _) (Signature.closed ⟨[],result⟩)
        ⟨vc,vr,.exact vt⟩ (ihBody) binder flag .default
      exact ⟨core,rep,typed⟩)
    | (case bindState =>
      intro Γ a b result first next binder info ihFirst ihNext
      exact FunctionSyntax.sourceBindTyping library (Parameter.represented .state) result.represented
        (Parameter.typed library .state) (result.typed library) (Parameter.closed .state) result.closed
        (ihFirst) (ihNext) binder info)
    | (case bindRead =>
      intro Γ v actual b result annotation read next binder info ihNext
      obtain ⟨vc,vr,vt⟩ := read.typing library
      have checked : CheckedTyping env 0 (SourceCasts env) Γ.core vc (optionType annotation.core) := by
        exact optionArgument library.returns.option _ annotation vt
      exact FunctionSyntax.sourceCheckedBindTyping library annotation.represented result.represented
        (annotation.type_typed library.scalars.toSignatures) (result.typed library) annotation.closed result.closed
        ⟨vc,vr,checked⟩ (ihNext) binder info)
    | (case branch =>
      intro Γ v actual a b result annotation guard yes no ihYes ihNo
      obtain ⟨vc,vr,vt,_⟩ := guard.typing library
      obtain ⟨ac,ar,at_⟩ := ihYes
      obtain ⟨bc,br,bt⟩ := ihNo
      obtain ⟨ct,dt⟩ := AnnotatedCondition.condition_typed library.decisions library.scalars.toSignatures annotation
        (WordBinder.Annotation.result _ vt)
      have optionHead : DirectTyping env 0 Γ.core (.const ``Option [.zero])
          (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := .constant library.returns.option (by simp [VLevel.WF]) rfl
      have ot := DirectTyping.application optionHead (result.typed library)
      have chosen := Branch.ite_typed ot (Signature.closed ⟨[],result⟩) ct dt (.exact at_) (.exact bt) library.ite
      refine ⟨_,?_,chosen⟩
      cases result
      · exact Step.nativeChoice_represents (.app (.constant rfl) (Result.represented .body))
          (AnnotatedCondition.condition_represents annotation vr) (AnnotatedCondition.decision_represents annotation vr) ar br
      · exact Step.nativeChoice_represents (.app (.constant rfl) (Result.represented .step))
          (AnnotatedCondition.condition_represents annotation vr) (AnnotatedCondition.decision_represents annotation vr) ar br)
    | (case staticRange =>
      intro Γ st a startValue b stopValue c strideValue raw state start stop stride body kn tn ki ti ihBody
      obtain ⟨sc,sr,st⟩ := state.typing (env := env)
      obtain ⟨bc,br,bt⟩ := ihBody
      obtain ⟨sa⟩ := start.typed (ctx := Γ.core) library.bounds library.scalars.toSignatures
      obtain ⟨ea⟩ := stop.typed (ctx := Γ.core) library.bounds library.scalars.toSignatures
      obtain ⟨da⟩ := stride.typed (ctx := Γ.core) library.bounds library.scalars.toSignatures
      exact ⟨_,For.source_represents sa.represented.property ea.represented.property da.represented.property sr
        (.lam (.constant rfl) (.lam (.constant rfl) br)),
        For.source_typed library.forHeader.header_typed library.range
          (sa.typed.mono (fun _ _ _ h => .arithmetic h)) (ea.typed.mono (fun _ _ _ h => .arithmetic h))
          (da.typed.mono (fun _ _ _ h => .arithmetic h)) (st.withCasts _)
          (.lambda ((Parameter.typed library (.scalar .word)).withCasts _)
            (.lambda ((Parameter.typed library .state).withCasts _) bt))⟩)
    | (case naturalRange =>
      intro Γ st n actual raw kind state count body kn tn ki ti ihBody
      obtain ⟨sc,sr,st⟩ := state.typing (env := env)
      obtain ⟨nc,nr,nt,_⟩ := count.typing library
      obtain ⟨bc,br,bt⟩ := ihBody
      have first : CastTyping env 0 (SourceCasts env) Γ.core (.const kind.first []) (.sort (.succ .zero)) := by
        cases kind
        · exact (Parameter.typed library .natural).withCasts _
        · exact (Parameter.typed library .state).withCasts _
      have second : CastTyping env 0 (SourceCasts env) ((.const kind.first [])::Γ.core)
          (.const kind.second []) (.sort (.succ .zero)) := by
        cases kind
        · exact (Parameter.typed library .state).withCasts _
        · exact (Parameter.typed library .natural).withCasts _
      have bodyTyped : CastTyping env 0 (SourceCasts env) (kind.context Γ.core) bc (optionType kind.result) := by
        cases kind <;> exact bt
      exact ⟨_,kind.source_represents nr sr (kind.lambda_represents br),
        NaturalLoop.source_typed_state library.naturalLoops library.scalars.toSignatures library.forHeader library.reads
          (st.withCasts _) kind (WordBinder.Annotation.result _ nt) (.lambda first (.lambda second bodyTyped))⟩)
    | (case call =>
      intro Γ f head tail result first rest fn arguments ihFn
      obtain ⟨fc,fr,ft⟩ := ihFn
      exact arguments.applyTyping library _ fr ft)
    | (case letFunction =>
      intro signature ty Γ v result b spelling value next binder flag ihValue ihNext
      obtain ⟨vc,vr,vt⟩ := ihValue
      obtain ⟨u,domainTyped⟩ := Signature.typed _ library closed (ctx := Γ.core)
      obtain ⟨core,rep,_,typed⟩ := FunctionSyntax.sourceCheckedLetTyping spelling.represented domainTyped
        (Signature.closed ⟨[],_⟩) ⟨vc,vr,.exact vt⟩ (ihNext) binder flag .default
      exact ⟨core,rep,typed⟩)
    | (case unitSequence =>
      intro Γ b result body binder info ihBody
      have pureRep := UnitStep.pure_represents
      have pureTyped := UnitStep.pure_typed (ctx := Context.core Γ) library.steps library.units
      have built := FunctionSyntax.sourceBindTyping library (Parameter.represented .unit) result.represented
        (Parameter.typed library .unit) (result.typed library) (Parameter.closed .unit) result.closed
        ⟨_,pureRep,pureTyped.withCasts _⟩ (ihBody) binder info
      cases result <;> exact built)

/-- Original helper typing, including its captured lexical context. -/
theorem Function.typing (source : Function ds Γ raw signature) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) :
    ∃ core, Represents raw core ∧ CastTyping env 0 (SourceCasts env) Γ.core core signature.core :=
  (sourceTyping library closed).1 source

/-- Original body typing for arbitrary nesting of the source constructors. -/
theorem Body.typing (source : Body ds Γ result raw) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) :
    ∃ core, Represents raw core ∧ CastTyping env 0 (SourceCasts env) Γ.core core (optionType result.core) :=
  (sourceTyping library closed).2 source


/-- The internal representation preserves original binder scope in both
 directions, including let (represented as a lambda application). -/
private theorem scopedOfRepresentation (represented : Represents raw core)
    (within : core.ClosedN depth) : LeanScalar.wellScoped depth raw = true := by
  induction represented generalizing depth <;>
    simp_all [LeanScalar.wellScoped,VExpr.ClosedN]
  all_goals grind

/-- Scope is a conclusion of the original syntax/type induction, rather
than a second per-program internal check supplied by the user. -/
theorem Body.wellScoped (source : Body ds Γ result raw) :
    LeanScalar.wellScoped Γ.length raw = true := by
  obtain ⟨core,represented,typed⟩ := source.typing StandardLibrary.library StandardLibrary.closed
  have within := typed.closed_term
  simp only [Context.core,List.length_map] at within
  exact scopedOfRepresentation represented within

theorem Function.wellScoped (source : Function ds Γ raw signature) :
    LeanScalar.wellScoped Γ.length raw = true := by
  obtain ⟨core,represented,typed⟩ := source.typing StandardLibrary.library StandardLibrary.closed
  have within := typed.closed_term
  simp only [Context.core,List.length_map] at within
  exact scopedOfRepresentation represented within

end IRComparison.WordFrontend.OrdinarySource
