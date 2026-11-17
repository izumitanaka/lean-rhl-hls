import IRComparison.Frontend.WordScalarEnvironmentTransport
import IRComparison.Frontend.WordNaturalLiteral
import IRComparison.Frontend.WordAnnotatedLiteral
import IRComparison.Frontend.WordAnnotatedSelectSyntax
import IRComparison.Hybrid.FixedMemory

/-! Source-only derivations for lexical scalar expressions, including their
computations and emitted code. Values here describe source bindings; they are
not parser results. The parser's environment is constructed by the proof.
The native computation of a pure let is substitution, as in Lean. Array reads
are not scalar values in this judgment and their failure is never erased. -/
namespace IRComparison.WordFrontend.LexicalScalarCode
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarEnvironment ScalarSyntax
set_option maxHeartbeats 1800000

abbrev Meaning := HybridWord.Word → HybridWord.Word → HybridWord.Word →
  HybridWord.State → List HybridWord.Word → Option HybridWord.Word

structure Value where
  source : Lean.Expr
  native : Meaning
  code : HybridWord.Expr
  quotation : Lean.Expr

abbrev sources (vs : List Value) := vs.map Value.source
abbrev expand (vs : List Value) := LexicalScalarSyntax.expand (sources vs)
abbrev under (vs : List Value) := LexicalScalarSyntax.under (sources vs)

def binaryCode : Binary → HybridWord.Expr → HybridWord.Expr → HybridWord.Expr
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div

def binaryValue : Binary → HybridWord.Word → HybridWord.Word → HybridWord.Word
  | .add => (· + ·) | .sub => (· - ·) | .mul => (· * ·) | .div => (· / ·)

/-- Typing premises refer only to the source and its standard library. No
constructor assumes a successful parse or a generated target certificate. -/
inductive Source (env : VEnv) (ctx : List VExpr) (p : Inputs) :
    List Value → Lean.Expr → Meaning → HybridWord.Expr → Lean.Expr → Prop where
  | reference (selected : vs[n]? = some bound) :
      Source env ctx p vs (.bvar n) bound.native bound.code bound.quotation
  | index (shape : LocalOccurrence raw) (same : expand vs raw = p.i)
      (outside : Unbound raw vs.length) :
      Source env ctx p vs raw (fun i _ _ _ _ => some i) .index (.const ``HybridWord.Expr.index [])
  | parameter (side : Side) (shape : LocalOccurrence raw) (same : expand vs raw = side.source p)
      (outside : Unbound raw vs.length)
      (notIndex : sameTerm (side.source p) p.i = false)
      (notLeft : side = .right → sameTerm (side.source p) p.x = false) :
      Source env ctx p vs raw (fun _ x y _ _ => some (match side with | .left => x | .right => y))
        (match side with | .left => .left | .right => .right) (.const side.target [])
  | localValue (shape : LocalOccurrence raw) (k : Nat) (outside : Unbound raw vs.length)
      (selected : p.locals[k]? = some (expand vs raw))
      (notIndex : sameTerm (expand vs raw) p.i = false)
      (notLeft : sameTerm (expand vs raw) p.x = false)
      (notRight : sameTerm (expand vs raw) p.y = false)
      (first : ∀ j < k, (p.locals[j]?.map (sameTerm (expand vs raw))).getD false = false) :
      Source env ctx p vs raw (fun _ _ _ _ ls => ls[k]?) (.local k)
        (app ``HybridWord.Expr.local [(ClosedTerm.bindingIndex k).val])
  | literal (n : Nat) (scope : Separated p (nativeLiteral n)) :
      Source env ctx p vs (nativeLiteral n) (fun _ _ _ _ _ => some (BitVec.ofNat 32 n))
        (.lit (BitVec.ofNat 32 n)) (app ``HybridWord.Expr.lit [nativeLiteral n])
  | annotatedLiteral (annotation : WordBinder.Annotation) (n : Nat)
      (scope : Separated p (AnnotatedLiteral.native annotation n)) :
      Source env ctx p vs (AnnotatedLiteral.native annotation n)
        (fun _ _ _ _ _ => some (BitVec.ofNat 32 n)) (.lit (BitVec.ofNat 32 n))
        (app ``HybridWord.Expr.lit [AnnotatedLiteral.native annotation n])
  | register (r : Nat) (rn : NatNotation) (stateSame : expand vs st = p.s)
      (numberSame : expand vs number = rn.native r)
      (scope : Separated p (expand vs (app ``HybridWord.State.regs [st,number]))) :
      Source env ctx p vs (app ``HybridWord.State.regs [st,number]) (fun _ _ _ s _ => some (s.regs r))
        (.reg r) (app ``HybridWord.Expr.reg [rn.native r])
  | binary (op : Binary) (left : Source env ctx p vs a f ac aq) (right : Source env ctx p vs b g bc bq)
      (scope : Separated p (expand vs (Lean.mkApp2 op.nativeHeader a b))) :
      Source env ctx p vs (Lean.mkApp2 op.nativeHeader a b)
        (fun i x y s ls => (f i x y s ls).bind (fun u => (g i x y s ls).bind (fun v => some (binaryValue op u v))))
        (binaryCode op ac bc) (app op.target [aq,bq])
  | annotatedBinary {leftCore rightCore : VExpr} (op : Binary)
      (aa ab ac ad oa ob : WordBinder.Annotation)
      (left : Source env ctx p vs a f leftCode leftQuote)
      (right : Source env ctx p vs b g rightCode rightQuote)
      (leftRep : Represents (expand vs a) leftCore) (rightRep : Represents (expand vs b) rightCore)
      (leftTyped : CastTyping env 0 (SourceCasts env) ctx leftCore oa.core)
      (rightTyped : CastTyping env 0 (SourceCasts env) ctx rightCore ob.core)
      (leftShape : LexicalScalarSyntax.ValueShape env ctx leftCore oa.core)
      (rightShape : LexicalScalarSyntax.ValueShape env ctx rightCore ob.core)
      (scope : Separated p (expand vs (Lean.mkApp2 (AnnotatedBinary.nativeHeader op aa ab ac ad) a b))) :
      Source env ctx p vs (Lean.mkApp2 (AnnotatedBinary.nativeHeader op aa ab ac ad) a b)
        (fun i x y s ls => (f i x y s ls).bind (fun u => (g i x y s ls).bind (fun v => some (binaryValue op u v))))
        (binaryCode op leftCode rightCode) (app op.target [leftQuote,rightQuote])
  | neg (value : Source env ctx p vs v f vc vq)
      (scope : Separated p (expand vs (.app nativeNegHeader v))) :
      Source env ctx p vs (.app nativeNegHeader v)
        (fun i x y s ls => (f i x y s ls).bind (fun v => some (-v))) (.neg vc) (app ``HybridWord.Expr.neg [vq])
  | annotatedNeg {valueCore : VExpr} (annotation operand : WordBinder.Annotation)
      (value : Source env ctx p vs v f vc vq)
      (represented : Represents (expand vs v) valueCore)
      (typed : CastTyping env 0 (SourceCasts env) ctx valueCore operand.core)
      (form : LexicalScalarSyntax.ValueShape env ctx valueCore operand.core)
      (scope : Separated p (expand vs (.app (AnnotatedNeg.nativeHeader annotation) v))) :
      Source env ctx p vs (.app (AnnotatedNeg.nativeHeader annotation) v)
        (fun i x y s ls => (f i x y s ls).bind (fun v => some (-v))) (.neg vc) (app ``HybridWord.Expr.neg [vq])
  | select (value : Source env ctx p vs v f vc vq)
      (decision : Decision env ctx (expand vs v) (expand vs d) (SourceCasts env))
      (yes : Source env ctx p vs a g ac aq) (no : Source env ctx p vs b h bc bq)
      (scope : Separated p (expand vs (Branch.Select.source v d a b))) :
      Source env ctx p vs (Branch.Select.source v d a b)
        (fun i x y s ls => (f i x y s ls).bind (fun v => if v != 0 then g i x y s ls else h i x y s ls))
        (.select vc ac bc) (app ``HybridWord.Expr.select [vq,aq,bq])
  | booleanSelect (value : Source env ctx p vs v f vc vq)
      (yes : Source env ctx p vs a g ac aq) (no : Source env ctx p vs b h bc bq)
      (scope : Separated p (expand vs (Branch.Select.source v (Branch.nativeBooleanDecision v) a b))) :
      Source env ctx p vs (Branch.Select.source v (Branch.nativeBooleanDecision v) a b)
        (fun i x y s ls => (f i x y s ls).bind (fun v => if v != 0 then g i x y s ls else h i x y s ls))
        (.select vc ac bc) (app ``HybridWord.Expr.select [vq,aq,bq])
  | annotatedSelect {valueCore leftCore rightCore : VExpr}
      (resultAnnotation annotation operand oa ob : WordBinder.Annotation)
      (value : Source env ctx p vs v f vc vq)
      (yes : Source env ctx p vs a g ac aq) (no : Source env ctx p vs b h bc bq)
      (vr : Represents (expand vs v) valueCore) (ar : Represents (expand vs a) leftCore) (br : Represents (expand vs b) rightCore)
      (vt : CastTyping env 0 (SourceCasts env) ctx valueCore operand.core)
      (typedLeft : CastTyping env 0 (SourceCasts env) ctx leftCore oa.core)
      (bt : CastTyping env 0 (SourceCasts env) ctx rightCore ob.core)
      (vf : LexicalScalarSyntax.ValueShape env ctx valueCore operand.core)
      (af : LexicalScalarSyntax.ValueShape env ctx leftCore oa.core)
      (bf : LexicalScalarSyntax.ValueShape env ctx rightCore ob.core)
      (scope : Separated p (expand vs (AnnotatedCondition.scalarSource resultAnnotation annotation v
        (AnnotatedCondition.nativeDecision annotation v) a b))) :
      Source env ctx p vs (AnnotatedCondition.scalarSource resultAnnotation annotation v (AnnotatedCondition.nativeDecision annotation v) a b)
        (fun i x y s ls => (f i x y s ls).bind (fun v => if v != 0 then g i x y s ls else h i x y s ls))
        (.select vc ac bc) (app ``HybridWord.Expr.select [vq,aq,bq])
  | letValue {body arg : VExpr} (annotation resultAnnotation : WordBinder.Annotation)
      (value : Source env ctx p vs v f vc vq)
      (next : Source env ctx p (⟨expand vs v,f,vc,vq⟩::vs) rest g bc bq)
      (argument : Represents (expand vs v) arg) (representedBody : Represents (under vs rest) body)
      (bodyTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core)
      (form : ∃ actual : WordBinder.Annotation, LexicalScalarSyntax.ValueShape env ctx (body.inst arg) actual.core)
      (binder : Lean.Name) (flag : Bool) :
      Source env ctx p vs (.letE binder annotation.native v rest flag) g bc bq
  | beta {body arg : VExpr} (annotation resultAnnotation : WordBinder.Annotation)
      (value : Source env ctx p vs v f vc vq)
      (next : Source env ctx p (⟨expand vs v,f,vc,vq⟩::vs) rest g bc bq)
      (argument : Represents (expand vs v) arg) (representedBody : Represents (under vs rest) body)
      (bodyTyped : CastTyping env 0 (SourceCasts env) (annotation.core::ctx) body resultAnnotation.core)
      (form : ∃ actual : WordBinder.Annotation, LexicalScalarSyntax.ValueShape env ctx (body.inst arg) actual.core)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Source env ctx p vs (.app (.lam binder annotation.native rest info) v) g bc bq

/-- Source-binding invariant, independent of the executable parser. -/
def ValuesCorrect (vs : List Value) : Prop := ∀ v ∈ vs,
  (∀ ds, FixedMemory.exprDeclared ds v.code = true) ∧
  ∀ i x y s ls, v.code.eval i x y s ls = v.native i x y s ls

theorem Source.computation (source : Source env ctx p vs raw native code quotation)
    (values : ValuesCorrect vs) :
    (∀ ds, FixedMemory.exprDeclared ds code = true) ∧
    ∀ i x y s ls, code.eval i x y s ls = native i x y s ls := by
  induction source with
  | reference selected => exact values _ (List.mem_of_getElem? selected)
  | index | localValue | literal | annotatedLiteral | register => exact ⟨fun _ => rfl,by intros; rfl⟩
  | parameter side => cases side <;> exact ⟨fun _ => rfl,by intros; rfl⟩
  | binary op left right scope il ir
  | annotatedBinary op aa ab ac ad oa ob left right lr rr lt rt lf rf scope il ir =>
    obtain ⟨dl,el⟩ := il values; obtain ⟨dr,er⟩ := ir values
    constructor
    · intro ds; cases op <;> simp [binaryCode,FixedMemory.exprDeclared,dl,dr]
    · intros; cases op <;> simp [binaryCode,binaryValue,HybridWord.Expr.eval,el,er,bind,Option.bind]
  | neg value scope ih
  | annotatedNeg annotation operand value represented typed form scope ih =>
    obtain ⟨d,e⟩ := ih values
    exact ⟨by intro ds; simp [HybridWord.Expr.neg,FixedMemory.exprDeclared,d],by intros; simp [HybridWord.Expr.neg,HybridWord.Expr.eval,e,BitVec.zero_sub]⟩
  | select value decision yes no scope iv ia ib
  | booleanSelect value yes no scope iv ia ib
  | annotatedSelect resultAnnotation annotation operand oa ob value yes no vr ar br vt typedLeft bt vf af bf scope iv ia ib =>
    obtain ⟨dv,ev⟩ := iv values; obtain ⟨da,ea⟩ := ia values; obtain ⟨db,eb⟩ := ib values
    exact ⟨by intro ds; simp [FixedMemory.exprDeclared,dv,da,db],by intros; simp only [HybridWord.Expr.eval,ev,ea,eb,bind,Option.bind]⟩
  | letValue annotation resultAnnotation value next argument body typed form binder flag iv ib
  | beta annotation resultAnnotation value next argument body typed form binder flag iv ib =>
    apply ib
    intro v h
    rcases List.mem_cons.mp h with rfl | h
    · exact iv values
    · exact values v h

structure Matches (vs : List Value) (bindings : Bindings env ctx p) : Prop where
  sources : LexicalScalarSyntax.Matches (sources vs) bindings
  codes : bindings.map (fun b => b.piece.code) = vs.map Value.quotation

theorem Matches.length (matched : Matches vs bindings) : bindings.length = vs.length := by
  simpa using congrArg List.length matched.codes

variable {env : VEnv} {ctx : List VExpr} {p : Inputs} {bindings : Bindings env ctx p}

theorem Matches.cons (matched : Matches vs bindings)
    {piece : Piece env ctx p (materialize bindings v) scalarExpected} (same : piece.code = quotation) :
    Matches (⟨expand vs v,native,code,quotation⟩::vs) (⟨materialize bindings v,piece⟩::bindings) := by
  constructor
  · exact matched.sources.cons
  · simp [same,matched.codes]

/-- Simultaneously build a typed certificate and prove its exact code, under
arbitrarily many lexical bindings. The recursion is over source derivations. -/
theorem Source.complete (source : Source env ctx p vs raw native code quotation)
    (setup : AliasSetup env) (library : ScalarSyntax.Library env)
    (scalarLibrary : ScalarConversion.Signatures env)
    (decisions : Branch.BooleanLibrary env)
    (freshHeads : ∀ n ∈ LexicalScalarSyntax.valueHeads, ∀ r ∈ setup.rules, n ≠ r.name)
    (freshConditions : ∀ n ∈ [``bne,``Decidable,``instDecidableEqBool], ∀ r ∈ setup.rules, n ≠ r.name)
    (freshEq : ∀ r ∈ setup.rules, ``Eq ≠ r.name)
    (inputs : InputsTyped env ctx p) (locals : Locals env ctx p)
    (coverage : Conversion.Covers conv 0 (ScalarConversion.Casts setup)) (exposure : Exposure env) :
    ∀ bindings : Bindings env ctx p, Matches vs bindings →
      BindingTypes inputs (SourceCasts env) bindings (ScalarConversion.Casts setup) →
      ∃ piece, visit env conv exposure ctx p raw bindings = some piece ∧
        Nonempty (ScalarCasts inputs piece (SourceCasts env) (ScalarConversion.Casts setup)) ∧ piece.code = quotation := by
  have embeds : ∀ scope a b, SourceCasts env scope a b → ScalarConversion.Casts setup scope a b :=
    fun _ _ _ h => .source h
  induction source with
  | @reference vs n value selected =>
    intro bindings matched types
    have found : (bindings.map Binding.source)[n]? = some value.source := by
      rw [matched.sources]; simp [sources,List.getElem?_map,selected]
    simp only [List.getElem?_map] at found
    cases h : bindings[n]? with
    | none => simp [h] at found
    | some bound =>
      obtain ⟨piece,parsed,typed,q⟩ := reference_complete_code types h conv exposure
      have eq := congrArg (fun xs : List Lean.Expr => xs[n]?) matched.codes
      simp only [List.getElem?_map,h,selected,Option.map_some,Option.some.injEq] at eq
      exact ⟨piece,parsed,typed,q.trans eq⟩
  | index shape same outside =>
    intro bindings matched types
    have mat := (matched.sources.materialize _).trans same
    obtain ⟨piece,parsed,typed,q⟩ := index_visit_complete_code inputs library bindings types conv exposure coverage shape (mat.symm ▸ inputs.i.property)
    exact ⟨piece,parsed,typed,q (matched.length.symm ▸ outside)⟩
  | parameter side shape same outside ni nl =>
    intro bindings matched types
    have mat := (matched.sources.materialize _).trans same
    obtain ⟨piece,parsed,typed,q⟩ := parameter_visit_complete_code inputs library bindings types side conv exposure coverage shape
      (mat.symm ▸ (side.representation inputs).property) (mat.symm ▸ ni) (fun h => mat.symm ▸ nl h)
    exact ⟨piece,parsed,typed,q (matched.length.symm ▸ outside)⟩
  | @localValue raw vs shape k outside selected ni nl nr first =>
    intro bindings matched types
    have mat := matched.sources.materialize raw
    obtain ⟨piece,parsed,typed,q⟩ := local_visit_complete_code inputs library bindings types locals conv exposure coverage shape
      (mat.symm ▸ selected) (mat.symm ▸ ni) (mat.symm ▸ nl) (mat.symm ▸ nr) (fun j h => mat.symm ▸ first j h)
    exact ⟨piece,parsed,typed,q (matched.length.symm ▸ outside)⟩
  | literal n scope =>
    intro bindings matched types
    exact literal_visit_complete_code inputs library types embeds coverage exposure scope
  | annotatedLiteral annotation n scope =>
    intro bindings matched types
    exact AnnotatedLiteral.visit_complete inputs library annotation n embeds coverage exposure scope
  | @register vs st number r rn stateSame numberSame scope =>
    intro bindings matched types
    have mat := matched.sources.materialize (app ``HybridWord.State.regs [st,number])
    have stateRep : Represents (materialize bindings st) inputs.s.val := by
      rw [matched.sources.materialize]
      change Represents (expand vs st) inputs.s.val
      rw [stateSame]; exact inputs.s.property
    have number := (matched.sources.materialize number).trans numberSame
    obtain ⟨piece,parsed,typed,q⟩ := register_visit_complete_code inputs library types stateRep
      (number.symm ▸ rn.argument library.toSignatures r) conv exposure coverage (mat.symm ▸ scope)
    exact ⟨piece,parsed,typed,by rw [q,number]⟩
  | binary op left right scope il ir =>
    intro bindings matched types
    obtain ⟨a,ha,⟨ta⟩,qa⟩ := il bindings matched types
    obtain ⟨b,hb,⟨tb⟩,qb⟩ := ir bindings matched types
    obtain ⟨piece,parsed,typed,q⟩ := binary_visit_complete_code inputs library types embeds ta tb op coverage exposure ha hb
      (by rw [matched.sources.materialize]; exact scope)
    exact ⟨piece,parsed,typed,by rw [q,qa,qb]⟩
  | annotatedBinary op aa ab ac ad oa ob left right lr rr lt rt lf rf scope il ir =>
    intro bindings matched types
    obtain ⟨a,ha,⟨ta⟩,qa⟩ := il bindings matched types
    obtain ⟨b,hb,⟨tb⟩,qb⟩ := ir bindings matched types
    have leftSame := ta.sourceCore.property.unique (by rw [matched.sources.materialize]; exact lr)
    have rightSame := tb.sourceCore.property.unique (by rw [matched.sources.materialize]; exact rr)
    obtain ⟨piece,parsed,typed,q⟩ := AnnotatedBinary.visit_complete_code setup scalarLibrary inputs library types ta tb
      op aa ab ac ad oa ob (leftSame.symm ▸ lt) (rightSame.symm ▸ rt)
      (leftSame.symm ▸ lf.toValueForm setup freshHeads) (rightSame.symm ▸ rf.toValueForm setup freshHeads)
      (freshHeads op.method (by cases op <;> simp [Binary.method,LexicalScalarSyntax.valueHeads]))
      coverage exposure ha hb (by rw [matched.sources.materialize]; exact scope)
    exact ⟨piece,parsed,typed,by rw [q,qa,qb]⟩
  | annotatedNeg annotation operand value represented typed form scope ih =>
    intro bindings matched types
    obtain ⟨a,ha,⟨ta⟩,qa⟩ := ih bindings matched types
    have same := ta.sourceCore.property.unique (by rw [matched.sources.materialize]; exact represented)
    obtain ⟨piece,parsed,result,q⟩ := AnnotatedNeg.visit_complete_code setup scalarLibrary inputs library types ta
      annotation operand (same.symm ▸ typed) (same.symm ▸ form.toValueForm setup freshHeads)
      (freshHeads ``Neg.neg (by simp [LexicalScalarSyntax.valueHeads])) coverage exposure ha
      (by rw [matched.sources.materialize]; exact scope)
    exact ⟨piece,parsed,result,by rw [q,qa]⟩
  | neg value scope ih =>
    intro bindings matched types
    obtain ⟨a,ha,⟨ta⟩,qa⟩ := ih bindings matched types
    obtain ⟨piece,parsed,typed,q⟩ := neg_visit_complete_code inputs library types embeds ta coverage exposure ha
      (by rw [matched.sources.materialize]; exact scope)
    exact ⟨piece,parsed,typed,by rw [q,qa]⟩
  | @booleanSelect vs rawValue f vc vq rawYes g ac aq rawNo h bc bq value yes no scope iv ia ib =>
    intro bindings matched types
    obtain ⟨v,hv,⟨tv⟩,vq⟩ := iv bindings matched types
    obtain ⟨a,ha,⟨ta⟩,aq⟩ := ia bindings matched types
    obtain ⟨b,hb,⟨tb⟩,bq⟩ := ib bindings matched types
    obtain ⟨pt,dt⟩ := decisions.condition_typed library.toSignatures tv.value
    have decisionRep : Represents (materialize bindings (Branch.nativeBooleanDecision rawValue))
        (Branch.booleanDecision tv.sourceCore.val) := by
      have materialized (v : Lean.Expr) : materialize bindings (Branch.nativeBooleanDecision v) =
          Branch.nativeBooleanDecision (materialize bindings v) := by cases bindings <;> rfl
      rw [materialized]
      exact Branch.booleanDecision_represents tv.sourceCore.property
    obtain ⟨piece,parsed,typed,q⟩ := select_visit_complete_code inputs types embeds tv ta tb
      decisionRep pt dt (.constant library.word (by simp) rfl)
      library.ite library.selectFact library.selectConstructor coverage exposure hv ha hb
      (by rw [matched.sources.materialize]; exact scope)
    exact ⟨piece,parsed,typed,by rw [q,vq,aq,bq]⟩
  | @annotatedSelect vs rawValue f vc vq rawYes g ac aq rawNo h bc bq valueCore leftCore rightCore
      resultAnnotation annotation operand oa ob value yes no vr ar br vt typedLeft bt vf af bf scope iv ia ib =>
    intro bindings matched types
    obtain ⟨v,hv,⟨tv⟩,vq⟩ := iv bindings matched types
    obtain ⟨a,ha,⟨ta⟩,aq⟩ := ia bindings matched types
    obtain ⟨b,hb,⟨tb⟩,bq⟩ := ib bindings matched types
    have sv := tv.sourceCore.property.unique (by rw [matched.sources.materialize]; exact vr)
    have sa := ta.sourceCore.property.unique (by rw [matched.sources.materialize]; exact ar)
    have sb := tb.sourceCore.property.unique (by rw [matched.sources.materialize]; exact br)
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
      (by rw [matched.sources.materialize]; exact scope)
    exact ⟨piece,parsed,typed,by rw [q,vq,aq,bq]⟩
  | select value decision yes no scope iv ia ib =>
    intro bindings matched types
    obtain ⟨v,hv,⟨tv⟩,vq⟩ := iv bindings matched types
    obtain ⟨a,ha,⟨ta⟩,aq⟩ := ia bindings matched types
    obtain ⟨b,hb,⟨tb⟩,bq⟩ := ib bindings matched types
    obtain ⟨vc,dc,vr,dr,pt,dt⟩ := decision.typing
    have same := tv.sourceCore.property.unique (by rw [matched.sources.materialize]; exact vr)
    rw [← same] at pt dt
    obtain ⟨piece,parsed,typed,q⟩ := select_visit_complete_code inputs types embeds tv ta tb
      (by rw [matched.sources.materialize]; exact dr)
      pt dt
      (.constant library.word (by simp) rfl) library.ite library.selectFact library.selectConstructor
      coverage exposure hv ha hb (by rw [matched.sources.materialize]; exact scope)
    exact ⟨piece,parsed,typed,by rw [q,vq,aq,bq]⟩
  | letValue annotation resultAnnotation value next argument body bodyTyped form binder flag iv ib
  | beta annotation resultAnnotation value next argument body bodyTyped form binder flag iv ib =>
    intro bindings matched types
    obtain ⟨a,ha,⟨ta⟩,qa⟩ := iv bindings matched types
    obtain ⟨b,hb,⟨tb⟩,qb⟩ := ib _ (matched.cons qa) (types.cons ta)
    have argSame := ta.sourceCore.property.unique (by rw [matched.sources.materialize]; exact argument)
    rw [← argSame] at form
    obtain ⟨actual,form⟩ := form
    first
    | obtain ⟨piece,parsed,typed,q⟩ := ScalarConversion.let_visit_complete_code annotation resultAnnotation setup library.toSignatures scalarLibrary
        inputs bindings ta tb (by rw [matched.sources.under]; exact body) bodyTyped ⟨actual,form.toValueForm setup freshHeads⟩
        coverage exposure ha hb binder flag
      exact ⟨piece,parsed,typed,q.trans qb⟩
    | obtain ⟨piece,parsed,typed,q⟩ := ScalarConversion.beta_visit_complete_code annotation resultAnnotation setup library.toSignatures scalarLibrary
        inputs bindings ta tb (by rw [matched.sources.under]; exact body) bodyTyped ⟨actual,form.toValueForm setup freshHeads⟩
        coverage exposure ha hb binder flag
      exact ⟨piece,parsed,typed,q.trans qb⟩

/-- Installing the finite library preserves both the source judgment and its
code/computation indices. Clients supply no per-library typing obligations. -/
theorem Source.install (source : Source before ctx p vs raw native code quotation)
    (installed : SignatureExtension before after) : Source after ctx p vs raw native code quotation := by
  induction source with
  | reference selected => exact .reference selected
  | index shape same outside => exact .index shape same outside
  | parameter side shape same outside ni nl => exact .parameter side shape same outside ni nl
  | localValue shape k outside selected ni nl nr first => exact .localValue shape k outside selected ni nl nr first
  | literal n scope => exact .literal n scope
  | annotatedLiteral annotation n scope => exact .annotatedLiteral annotation n scope
  | register r rn stateSame numberSame scope => exact .register r rn stateSame numberSame scope
  | binary op _ _ scope a b => exact .binary op a b scope
  | annotatedBinary op aa ab ac ad oa ob _ _ lr rr lt rt lf rf scope left right =>
    exact .annotatedBinary op aa ab ac ad oa ob left right lr rr
      (lt.install installed (fun _ _ _ h => SourceCasts.install h installed))
      (rt.install installed (fun _ _ _ h => SourceCasts.install h installed))
      (lf.install installed) (rf.install installed) scope
  | neg _ scope v => exact .neg v scope
  | annotatedNeg annotation operand _ represented typed form scope value =>
    exact .annotatedNeg annotation operand value represented
      (typed.install installed (fun _ _ _ h => SourceCasts.install h installed)) (form.install installed) scope
  | select _ decision _ _ scope v a b => exact .select v (decision.installSource installed) a b scope
  | booleanSelect _ _ _ scope v a b => exact .booleanSelect v a b scope
  | annotatedSelect resultAnnotation annotation operand oa ob value yes no vr ar br vt typedLeft bt vf af bf scope iv ia ib =>
    exact .annotatedSelect resultAnnotation annotation operand oa ob iv ia ib vr ar br
      (vt.install installed (fun _ _ _ h => SourceCasts.install h installed))
      (typedLeft.install installed (fun _ _ _ h => SourceCasts.install h installed))
      (bt.install installed (fun _ _ _ h => SourceCasts.install h installed))
      (vf.install installed) (af.install installed) (bf.install installed) scope
  | letValue annotation resultAnnotation _ _ arg body typed shape binder flag v b =>
    exact .letValue annotation resultAnnotation v b arg body
      (typed.install installed (fun _ _ _ h => SourceCasts.install h installed))
      (by obtain ⟨actual,shape⟩ := shape; exact ⟨actual,shape.install installed⟩) binder flag
  | beta annotation resultAnnotation _ _ arg body typed shape binder info v b =>
    exact .beta annotation resultAnnotation v b arg body
      (typed.install installed (fun _ _ _ h => SourceCasts.install h installed))
      (by obtain ⟨actual,shape⟩ := shape; exact ⟨actual,shape.install installed⟩) binder info

/-- The root environment is empty; typing, quotation and computation are all
derived from the same independent source tree. -/
theorem Source.parse_complete (source : Source env ctx p [] raw native code quotation)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : Locals env ctx p) :
    ∃ piece, ScalarEnvironment.parse env setup.conversion exposure ctx p raw = some piece ∧
      Nonempty (ScalarCasts inputs piece (SourceCasts env) (For.Casts setup)) ∧ piece.code = quotation := by
  have freshSome := fresh.value ``Option.some (by simp)
  obtain ⟨piece,parsed,⟨typed⟩,q⟩ := source.complete setup library.scalars library.scalarCertificates library.decisions fresh.scalar fresh.condition fresh.eq inputs locals
    (ScalarConversion.Casts.covered setup library.scalars.toSignatures library.scalarCertificates closed fresh.eq freshSome)
    exposure [] ⟨rfl,rfl⟩ (BindingTypes.empty inputs (SourceCasts env))
  exact ⟨piece,parsed,⟨⟨typed.sourceCore,typed.value,typed.target,typed.proof.mono
    (fun _ _ _ h => .scalar library.scalarCertificates freshSome h)⟩⟩,q⟩

end IRComparison.WordFrontend.LexicalScalarCode
