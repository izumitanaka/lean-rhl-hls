import IRComparison.Frontend.WordLexicalScope
import IRComparison.Frontend.WordNegCompleteness
import IRComparison.Frontend.WordLocalCompleteness
import IRComparison.Frontend.WordBranchCompleteness

/-! An independent grammar for the arithmetic fragment, and success of the
actual structural scalar parser. This is one component of the larger input
judgment; it is not the full supported-source grammar or the final theorem. -/
namespace IRComparison.WordFrontend.ScalarSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic ScalarEnvironment
variable {casts proofCasts : TypeCasts} [Arithmetic.Includes casts] [Arithmetic.Includes proofCasts]

/-- Dispatch separation is a static scope property, not parser success.
It will be derived for the ordinary bound-variable input environments. -/
structure Separated (p : Inputs) (e : Lean.Expr) : Prop where
  index : sameTerm e p.i = false
  left : sameTerm e p.x = false
  right : sameTerm e p.y = false
  locals : ∀ k : Nat, (p.locals[k]?.map (sameTerm e)).getD false = false

/-- Types of the lexical scalar environment, derived when entering binders. -/
structure Locals (env : VEnv) (ctx : List VExpr) (p : Inputs) where
  values : List VExpr
  represented : List.Forall₂ Represents p.locals values
  typed : ∀ v ∈ values, CheckedTyping env 0 Casts ctx v wordType

def Locals.empty (h : p.locals = []) : Locals env ctx p :=
  ⟨[],h ▸ List.Forall₂.nil,by simp⟩

/-- Retaining a scalar preserves the typed lexical environment, including
values whose inferred type is BitVec 32 rather than the Word abbreviation. -/
def Locals.withLocal (scope : Locals env ctx p)
    (represented : Represents value core)
    (typed : CheckedTyping env 0 Casts ctx core wordType) :
    Locals env ctx {p with locals := value :: p.locals} where
  values := core :: scope.values
  represented := .cons represented scope.represented
  typed := by
    intro v h
    rcases List.mem_cons.mp h with rfl | h
    · exact typed
    · exact scope.typed v h

def Locals.lift (scope : Locals env ctx p) (closed : ClosedConstantTypes env) (ty : VExpr) :
    Locals env (ty::ctx) p.lift where
  values := scope.values.map VExpr.lift
  represented := by
    have aux {xs vs} (h : List.Forall₂ Represents xs vs) :
        List.Forall₂ Represents (xs.map (LeanBindings.rename Nat.succ)) (vs.map VExpr.lift) := by
      induction h with
      | nil => exact .nil
      | cons a b ih => exact .cons a.lift ih
    exact aux scope.represented
  typed := by
    intro v h
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp h
    exact (scope.typed u hu).lift closed casts_closed ty

def Locals.nextState (scope : Locals env ctx p) (closed : ClosedConstantTypes env) :
    Locals env (stateType::ctx) {p.lift with s := .bvar 0} :=
  ⟨(scope.lift closed stateType).values,(scope.lift closed stateType).represented,(scope.lift closed stateType).typed⟩

def Locals.nextWord (scope : Locals env ctx p) (closed : ClosedConstantTypes env) :
    Locals env (wordType::ctx) {p.lift with locals := .bvar 0 :: p.lift.locals} where
  values := .bvar 0 :: scope.values.map VExpr.lift
  represented := .cons .bvar (scope.lift closed wordType).represented
  typed := by
    intro v h
    rcases List.mem_cons.mp h with rfl | h
    · exact .exact (.bvar .zero)
    · exact (scope.lift closed wordType).typed v h

inductive Side where
  | left | right
  deriving DecidableEq

def Side.source (side : Side) (p : Inputs) : Lean.Expr := match side with
  | .left => p.x | .right => p.y

def Side.target : Side → Lean.Name
  | .left => ``HybridWord.Expr.left | .right => ``HybridWord.Expr.right

def Side.fact : Side → Lean.Name
  | .left => ``WordFrontendFacts.left | .right => ``WordFrontendFacts.right

def Side.result (side : Side) : VExpr := equalValues (optionType wordType)
  (scalarValue (.bvar 4) (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0) (.const side.target []))
  (someValue wordType (.bvar (match side with | .left => 3 | .right => 2)))
def Side.signature (side : Side) : VExpr := inputsType side.result

def Side.representation (side : Side) (inputs : InputsTyped env ctx p) :
    {core // Represents (side.source p) core} := match side with
  | .left => inputs.x | .right => inputs.y

theorem Side.typed (side : Side) (inputs : InputsTyped env ctx p) :
    DirectTyping env 0 ctx (side.representation inputs).val wordType := by
  cases side with
  | left => exact inputs.hx
  | right => exact inputs.hy

/-- Elaboration/type conditions on the conditional's decision argument.
This judgment contains no parser result or certificate-check outcome. -/
structure Decision (env : VEnv) (ctx : List VExpr) (v d : Lean.Expr)
    (casts : TypeCasts := Arithmetic.Casts) : Prop where
  typing : ∃ vc dc, Represents v vc ∧ Represents d dc ∧
    CastTyping env 0 casts ctx (Branch.condition vc) (.sort .zero) ∧
    CastTyping env 0 casts ctx dc (.app (.const ``Decidable []) (Branch.condition vc))


theorem Decision.mono (decision : Decision env ctx v d casts)
    (embeds : ∀ scope a b, casts scope a b → other scope a b) : Decision env ctx v d other := by
  obtain ⟨vc,dc,vr,dr,pt,dt⟩ := decision.typing
  exact ⟨vc,dc,vr,dr,pt.mono embeds,dt.mono embeds⟩

/-- Closing a binder preserves the condition and its decision evidence.
The same proof handles the basic and full source conversion relations. -/
theorem Decision.instantiate (decision : Decision env (domain::ctx) v d casts)
    (closed : ClosedConstantTypes env) (stable : ClosedCasts casts)
    (represented : Represents raw arg) (typed : CastTyping env 0 casts ctx arg domain) :
    Decision env ctx (LeanBindings.instantiate raw v) (LeanBindings.instantiate raw d) casts := by
  obtain ⟨vc,dc,vr,dr,pt,dt⟩ := decision.typing
  refine ⟨vc.inst arg,dc.inst arg,vr.instantiate represented,dr.instantiate represented,?_,?_⟩
  · simpa only [Branch.condition_inst,VExpr.inst] using pt.instantiate closed stable typed
  · simpa only [VExpr.inst,Branch.condition_inst] using dt.instantiate closed stable typed

/-- A local occurrence is not an administrative let or beta-redex. In
particular this includes the BV32 conversion of a natural loop binder. -/
structure LocalOccurrence (source : Lean.Expr) : Prop where
  notLet : ∀ name ty value next flag, source ≠ .letE name ty value next flag
  notBeta : ∀ name ty next info value, source ≠ .app (.lam name ty next info) value

theorem LocalOccurrence.variable (n : Nat) : LocalOccurrence (.bvar n) :=
  ⟨by intros; simp, by intros; simp⟩

/-- These constructors inspect the actual elaborated Lean expressions. The
judgment does not mention a parser, its result, fuel or a certificate check. -/
inductive Form (env : VEnv) (ctx : List VExpr) (p : Inputs) : Lean.Expr → Prop where
  | parameter (side : Side) (n : Nat) (bound : side.source p = .bvar n)
      (notIndex : sameTerm (side.source p) p.i = false)
      (notLeft : side = .right → sameTerm (side.source p) p.x = false) : Form env ctx p (side.source p)
  | index (n : Nat) (bound : p.i = .bvar n) : Form env ctx p p.i
  | localValue (source : Lean.Expr) (shape : LocalOccurrence source) (k : Nat)
      (selected : p.locals[k]? = some source)
      (notIndex : sameTerm source p.i = false)
      (notLeft : sameTerm source p.x = false)
      (notRight : sameTerm source p.y = false)
      (first : ∀ j < k, (p.locals[j]?.map (sameTerm source)).getD false = false) :
      Form env ctx p source
  | literal (n : Nat) (scope : Separated p (nativeLiteral n)) : Form env ctx p (nativeLiteral n)
  | binary (op : Binary) (left : Form env ctx p a) (right : Form env ctx p b)
      (scope : Separated p (Lean.mkApp2 op.nativeHeader a b)) :
      Form env ctx p (Lean.mkApp2 op.nativeHeader a b)
  | neg (value : Form env ctx p v) (scope : Separated p (.app nativeNegHeader v)) :
      Form env ctx p (.app nativeNegHeader v)
  | register (register : NatArgument env ctx r)
      (scope : Separated p (app ``HybridWord.State.regs [p.s,r])) :
      Form env ctx p (app ``HybridWord.State.regs [p.s,r])
  | select (value : Form env ctx p v) (decision : Decision env ctx v d)
      (yes : Form env ctx p a) (no : Form env ctx p b)
      (scope : Separated p (Branch.Select.source v d a b)) :
      Form env ctx p (Branch.Select.source v d a b)

structure Library (env : VEnv) : Prop extends Signatures env where
  negFact : env.constants ``WordFrontendFacts.neg = some ⟨0,negSignature⟩
  negConstructor : env.constants ``HybridWord.Expr.neg = some ⟨0,.forallE exprType exprType⟩
  ite : env.constants ``ite = some Branch.iteSignature
  selectFact : env.constants ``WordFrontendFacts.select = some ⟨0,Branch.Select.signature⟩
  selectConstructor : env.constants ``HybridWord.Expr.select = some ⟨0,Branch.Select.constructorSignature⟩
  registerFact : env.constants ``WordFrontendFacts.register = some ⟨0,registerSignature⟩
  registerAccessor : env.constants ``HybridWord.State.regs =
    some ⟨0,.forallE stateType (.forallE (.const ``Nat []) wordType)⟩
  registerConstructor : env.constants ``HybridWord.Expr.reg = some ⟨0,.forallE (.const ``Nat []) exprType⟩
  localLibrary : LocalSignatures env
  sideFact : ∀ side : Side, env.constants side.fact = some ⟨0,side.signature⟩
  sideConstructor : ∀ side : Side, env.constants side.target = some ⟨0,exprType⟩
  indexFact : env.constants ``WordFrontendFacts.index = some ⟨0,indexSignature⟩
  indexConstructor : env.constants ``HybridWord.Expr.index = some ⟨0,exprType⟩
  literalFact : env.constants ``WordFrontendFacts.literal = some ⟨0,literalSignature⟩
  literalConstructor : env.constants ``HybridWord.Expr.lit = some ⟨0,.forallE wordType exprType⟩
  binaryFact : ∀ op : Binary, env.constants op.fact = some ⟨0,op.signature⟩
  binaryConstructor : ∀ op : Binary,
    env.constants op.target = some ⟨0,.forallE exprType (.forallE exprType exprType)⟩

theorem literal_visit_complete_code (inputs : InputsTyped env ctx p) (library : Library env)
    (types : BindingTypes inputs casts bindings proofCasts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (scope : Separated p (nativeLiteral n)) :
    ∃ piece, visit env conv exposure ctx p (nativeLiteral n) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) ∧
      (piece.code = app ``HybridWord.Expr.lit [nativeLiteral n]) := by
  have mat : materialize bindings (nativeLiteral n) = nativeLiteral n :=
    materialize_closed bindings (literal_closed n)
  have rep : Represents (materialize bindings (nativeLiteral n)) (literalTerm n) := mat.symm ▸ literal_represents n
  rcases lookup_typed types (nativeLiteral n) conv with miss | ⟨cached,hit,typed⟩
  ·
    obtain ⟨artifact,checked,typed,codeEq,proofEq⟩ := literal_finish inputs library.toSignatures
      library.literalFact n (fun scope a b h => coverage scope a b (embeds scope a b (Arithmetic.Includes.embed scope a b h))) exposure
    obtain ⟨core,translated,same⟩ := (literal_represents n).translate_complete
    let lit : ClosedTerm := ⟨nativeLiteral n,literal_closed n,core⟩
    let code := ClosedTerm.app ``HybridWord.Expr.lit [lit]
    let art : Artifact env ctx (scalarExpected p code.val (materialize bindings (nativeLiteral n))) := by
      simpa only [mat,code,ClosedTerm.app,lit] using artifact
    let piece : Piece env ctx p (materialize bindings (nativeLiteral n)) scalarExpected :=
      ⟨code.val,art,code.closed,code.represented⟩
    have closed : closedTerm (nativeLiteral n) = some lit := by
      simp only [closedTerm,literal_closed,translated,lit,bind,Option.bind,dite_true,pure]
    refine ⟨piece,?_,⟨⟨⟨literalTerm n,rep⟩,.exact ((library.toSignatures.literal_typed n).mono Arithmetic.Includes.embed),?_,?_⟩⟩,rfl⟩
    · rw [visit] <;> try (solve | intro name ty value next flag h; cases h)
      simp only [miss,node,finishScalar,mat]
      have head : (nativeLiteral n).getAppFn.constName? = some ``OfNat.ofNat := rfl
      simp only [head]
      simp [List.forIn_cons,scope.index,scope.left,scope.right,scope.locals,
        closed,ClosedTerm.app,app,lit,code,piece,art,mat] at checked ⊢
      simp only [forIn_constant_yield,Option.some.injEq,checked,Option.bind_some]
      cases bindings <;> simp [materialize,LeanBindings.substitute,nativeLiteral,nativeWidth,word,
        Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,app] at checked ⊢
      all_goals simp [checked]
    · have fact : CastTyping env 0 casts ctx (.const ``HybridWord.Expr.lit []) (.forallE wordType exprType) :=
        .constant library.literalConstructor (by simp) rfl
      change CastTyping env 0 casts ctx (.app (.const ``HybridWord.Expr.lit []) core.val) exprType
      rw [same]
      exact .application fact ((library.toSignatures.literal_typed n).mono Arithmetic.Includes.embed)
  
    · cases bindings <;> simpa [piece,art,materialize,LeanBindings.substitute,nativeLiteral,nativeWidth,word,
        Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,app] using typed.mono (fun scope a b h => embeds scope a b (Arithmetic.Includes.embed scope a b h))
  · simp [ScalarEnvironment.lookup,nativeLiteral] at hit

theorem literal_visit_complete (inputs : InputsTyped env ctx p) (library : Library env)
    (types : BindingTypes inputs casts bindings proofCasts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (scope : Separated p (nativeLiteral n)) :
    ∃ piece, visit env conv exposure ctx p (nativeLiteral n) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := literal_visit_complete_code inputs library types embeds coverage exposure scope
  exact ⟨piece,success,typed⟩

theorem literal_complete (inputs : InputsTyped env ctx p) (library : Library env)
    (coverage : Conversion.Covers conv 0 Casts) (exposure : Exposure env)
    (scope : Separated p (nativeLiteral n)) :
    ∃ piece, ScalarEnvironment.parse env conv exposure ctx p (nativeLiteral n) = some piece ∧
      Nonempty (ScalarCasts inputs piece Casts) := by
  exact literal_visit_complete inputs library (BindingTypes.empty inputs Casts)
    (fun _ _ _ h => h) coverage exposure scope

private theorem visit_of_parse {piece : Piece env ctx p source scalarExpected}
    (parsed : ScalarEnvironment.parse env conv exposure ctx p source = some piece) :
    visit env conv exposure ctx p source [] = some piece := parsed

theorem index_visit_complete_code (inputs : InputsTyped env ctx p) (library : Library env)
    (bindings : Bindings env ctx p) (types : BindingTypes inputs casts bindings proofCasts)
    (conv : Conversion env) (exposure : Exposure env) (coverage : conv.Covers 0 proofCasts) (shape : LocalOccurrence raw)
    (represented : Represents (materialize bindings raw) inputs.i.val) :
    ∃ piece, visit env conv exposure ctx p raw bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) ∧
      (Unbound raw bindings.length → piece.code = .const ``HybridWord.Expr.index []) := by
  rcases lookup_typed types raw conv with miss | ⟨cached,hit,typed⟩
  ·
    obtain ⟨artifact,checked,typed,_⟩ := finish_cast_complete
      (expected := scalarExpected p (.const ``HybridWord.Expr.index []) (materialize bindings raw))
      (proof := app ``WordFrontendFacts.index p.args)
      (scalarExpected_represents inputs (.constant rfl) represented)
      (app_represents (.constant rfl) inputs.arguments) (index_cast_typed inputs library.indexFact)
      (known := noKnownTypes env 0) (by intro ctx e hit impossible; cases impossible)
      coverage exposure (.const ``HybridWord.Expr.index [])
    let piece : Piece env ctx p (materialize bindings raw) scalarExpected :=
      ⟨.const ``HybridWord.Expr.index [],artifact,rfl,⟨.const ``HybridWord.Expr.index [],.constant rfl⟩⟩
    refine ⟨piece,?_,⟨⟨⟨_,represented⟩,inputs.hi.withCasts casts,?_,typed⟩⟩,by intro _; rfl⟩
    · have same := sameTerm_complete represented inputs.i.property
      apply eq_of_heq
      rw [visit]
      · simp [-heq_eq_eq,miss,node,same,List.forIn_cons]
        simp only [Option.bind_assoc,Option.bind_some,Option.bind_fun_some]
        apply heq_of_eq
        simp [finishScalar,ClosedTerm.const,checked,piece]
      · exact shape.notLet
      · exact shape.notBeta
    · exact .constant library.indexConstructor (by simp) rfl
  · refine ⟨cached,?_,typed,?_⟩
    · rw [visit]
      · simp only [hit]
      · exact shape.notLet
      · exact shape.notBeta
    · intro outside
      rw [outside.lookup_none] at hit
      contradiction

theorem index_visit_complete (inputs : InputsTyped env ctx p) (library : Library env)
    (bindings : Bindings env ctx p) (types : BindingTypes inputs casts bindings proofCasts)
    (conv : Conversion env) (exposure : Exposure env) (coverage : conv.Covers 0 proofCasts) (shape : LocalOccurrence raw)
    (represented : Represents (materialize bindings raw) inputs.i.val) :
    ∃ piece, visit env conv exposure ctx p raw bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := index_visit_complete_code inputs library bindings types conv exposure coverage shape represented
  exact ⟨piece,success,typed⟩

theorem index_complete (inputs : InputsTyped env ctx p) (library : Library env)
    (conv : Conversion env) (exposure : Exposure env) (coverage : conv.Covers 0 Casts) (bound : p.i = .bvar n) :
    ∃ piece, ScalarEnvironment.parse env conv exposure ctx p p.i = some piece ∧
      Nonempty (ScalarCasts inputs piece Casts) := by
  have shape : LocalOccurrence p.i := by rw [bound]; exact .variable n
  simpa only [ScalarEnvironment.parse,materialize_nil] using
    index_visit_complete inputs library [] (BindingTypes.empty inputs Casts)
      conv exposure coverage shape inputs.i.property

theorem materialize_binary (bindings : Bindings env ctx p) (op : Arithmetic.Binary) (u v : Lean.Expr) :
    materialize bindings (Lean.mkApp2 op.nativeHeader u v) =
      Lean.mkApp2 op.nativeHeader (materialize bindings u) (materialize bindings v) := by
  simp only [Lean.mkApp2,Lean.mkApp,Lean.mkAppB,materialize_app]
  rw [materialize_closed bindings (by cases op <;> rfl)]

/-- Binary syntax composes the two recursive child results in the current
lexical environment. Only explicit variable references reuse a binding. -/
theorem binary_visit_complete_code (inputs : InputsTyped env ctx p) (library : ScalarSyntax.Library env)
    (types : BindingTypes inputs casts bindings proofCasts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    {a : Piece env ctx p (materialize bindings u) scalarExpected}
    {b : Piece env ctx p (materialize bindings v) scalarExpected}
    (left : ScalarCasts inputs a casts proofCasts) (right : ScalarCasts inputs b casts proofCasts)
    (op : Arithmetic.Binary) (coverage : Conversion.Covers conv 0 proofCasts)
    (exposure : Exposure env)
    (leftParsed : visit env conv exposure ctx p u bindings = some a)
    (rightParsed : visit env conv exposure ctx p v bindings = some b)
    (scope : ScalarSyntax.Separated p (materialize bindings (Lean.mkApp2 op.nativeHeader u v))) :
    ∃ piece, visit env conv exposure ctx p (Lean.mkApp2 op.nativeHeader u v) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) ∧
      (piece.code = app op.target [a.code,b.code]) := by
  have rep : Represents (materialize bindings (Lean.mkApp2 op.nativeHeader u v))
      (.app (.app op.header left.sourceCore.val) right.sourceCore.val) := by
    rw [materialize_binary]
    exact .app (.app op.header_represents left.sourceCore.property) right.sourceCore.property
  rcases lookup_typed types (Lean.mkApp2 op.nativeHeader u v) conv with miss | ⟨cached,hit,typed⟩
  · obtain ⟨artifact,checked,typed,_,_⟩ := Arithmetic.binary_finish inputs (left.inProofCasts embeds) (right.inProofCasts embeds) op
      (library.binaryFact op) coverage exposure
    let code := ClosedTerm.app op.target [a.closedTerm,b.closedTerm]
    let art : Artifact env ctx
        (scalarExpected p code.val (materialize bindings (Lean.mkApp2 op.nativeHeader u v))) := by
      simpa only [materialize_binary,code,ClosedTerm.app,Piece.closedTerm] using artifact
    let piece : Piece env ctx p (materialize bindings (Lean.mkApp2 op.nativeHeader u v)) scalarExpected :=
      ⟨code.val,art,code.closed,code.represented⟩
    refine ⟨piece,?_,⟨⟨⟨_,rep⟩,by
      have first := CastTyping.checkedApplication
        ((library.toSignatures.header_typed op).mono Arithmetic.Includes.embed) left.value
      simp only [wordType,VExpr.inst] at first
      exact .exact (.checkedApplication first right.value),?_,?_⟩⟩,rfl⟩
    · have smallerLeft : syntaxSize u < syntaxSize (Lean.mkApp2 op.nativeHeader u v) := by
        change syntaxSize u < syntaxSize op.nativeHeader + syntaxSize u + 1 + syntaxSize v + 1
        omega
      have smallerRight : syntaxSize v < syntaxSize (Lean.mkApp2 op.nativeHeader u v) := by
        change syntaxSize v < syntaxSize op.nativeHeader + syntaxSize u + 1 + syntaxSize v + 1
        omega
      have leftArg : (arguments (Lean.mkApp2 op.nativeHeader u v))[
          (arguments (Lean.mkApp2 op.nativeHeader u v)).length - 2]? = some ⟨u,smallerLeft⟩ := by
        cases op <;> rfl
      have rightArg : (arguments (Lean.mkApp2 op.nativeHeader u v))[
          (arguments (Lean.mkApp2 op.nativeHeader u v)).length - 1]? = some ⟨v,smallerRight⟩ := by
        cases op <;> rfl
      apply eq_of_heq
      rw [visit] <;> try (solve | intro name ty value next flag h; cases h)
      have head : (Lean.mkApp2 op.nativeHeader u v).getAppFn.constName? = some op.method := by cases op <;> rfl
      simp only [miss,node,head]
      simp [-heq_eq_eq,List.forIn_cons,scope.index,scope.left,scope.right,scope.locals]
      cases op <;> simp [-heq_eq_eq,Arithmetic.Binary.method,leftArg,rightArg,forIn_constant_yield]
      all_goals simp only [leftParsed,rightParsed,Option.bind_some]
      all_goals simp only [Option.bind_assoc,Option.bind_some,Option.bind_fun_some]
      all_goals simp only [materialize_binary] at *
      all_goals apply heq_of_eq
      all_goals cases bindings <;> simpa [materialize,LeanBindings.substitute,Arithmetic.Binary.nativeHeader,
        Arithmetic.nativeWidth,app,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,finishScalar,ClosedTerm.app,Piece.closedTerm,code,piece,art,
        Arithmetic.Binary.target,Arithmetic.Binary.fact] using
        congrArg (fun h => h.map (fun artifact =>
          (⟨code.val,artifact,code.closed,code.represented⟩ : Piece env ctx p _ scalarExpected))) checked
    · have fact : CastTyping env 0 casts ctx (.const op.target [])
          (.forallE exprType (.forallE exprType exprType)) :=
        .constant (library.binaryConstructor op) (by simp) rfl
      have first := CastTyping.application fact left.target
      simp only [exprType,VExpr.inst] at first
      exact .application first right.target
    · cases bindings <;> cases op <;> simpa [piece,art,materialize,LeanBindings.substitute,
        Arithmetic.Binary.nativeHeader,Arithmetic.nativeWidth,app,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] using typed
  · simp [ScalarEnvironment.lookup,Lean.mkApp2] at hit

theorem binary_visit_complete (inputs : InputsTyped env ctx p) (library : ScalarSyntax.Library env)
    (types : BindingTypes inputs casts bindings proofCasts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    {a : Piece env ctx p (materialize bindings u) scalarExpected}
    {b : Piece env ctx p (materialize bindings v) scalarExpected}
    (left : ScalarCasts inputs a casts proofCasts) (right : ScalarCasts inputs b casts proofCasts)
    (op : Arithmetic.Binary) (coverage : Conversion.Covers conv 0 proofCasts)
    (exposure : Exposure env)
    (leftParsed : visit env conv exposure ctx p u bindings = some a)
    (rightParsed : visit env conv exposure ctx p v bindings = some b)
    (scope : ScalarSyntax.Separated p (materialize bindings (Lean.mkApp2 op.nativeHeader u v))) :
    ∃ piece, visit env conv exposure ctx p (Lean.mkApp2 op.nativeHeader u v) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := binary_visit_complete_code inputs library types embeds left right op coverage exposure leftParsed rightParsed scope
  exact ⟨piece,success,typed⟩

theorem binary_complete (inputs : InputsTyped env ctx p) (library : Library env)
    {a : Piece env ctx p u scalarExpected} {b : Piece env ctx p v scalarExpected}
    (left : ScalarCasts inputs a Casts) (right : ScalarCasts inputs b Casts) (op : Binary)
    (coverage : Conversion.Covers conv 0 Casts) (exposure : Exposure env)
    (leftParsed : ScalarEnvironment.parse env conv exposure ctx p u = some a)
    (rightParsed : ScalarEnvironment.parse env conv exposure ctx p v = some b)
    (scope : Separated p (Lean.mkApp2 op.nativeHeader u v)) :
    ∃ piece, ScalarEnvironment.parse env conv exposure ctx p (Lean.mkApp2 op.nativeHeader u v) = some piece ∧
      Nonempty (ScalarCasts inputs piece Casts) := by
  simpa only [ScalarEnvironment.parse,materialize_nil] using
    binary_visit_complete inputs library (BindingTypes.empty inputs Casts) (fun _ _ _ h => h) left right op
      coverage exposure leftParsed rightParsed scope

/-- In-scope scalar lookup, using the same local certificate constructor as
before. The lexical position has no fixed bound. -/
theorem local_visit_complete_code (inputs : InputsTyped env ctx p) (library : Library env)
    (bindings : Bindings env ctx p) (types : BindingTypes inputs casts bindings proofCasts)
    (scope : Locals env ctx p) (conv : Conversion env) (exposure : Exposure env) (coverage : conv.Covers 0 proofCasts)
    {n : Nat} (shape : LocalOccurrence raw)
    (selected : p.locals[n]? = some (materialize bindings raw))
    (notIndex : sameTerm (materialize bindings raw) p.i = false)
    (notLeft : sameTerm (materialize bindings raw) p.x = false)
    (notRight : sameTerm (materialize bindings raw) p.y = false)
    (first : ∀ j < n, (p.locals[j]?.map (sameTerm (materialize bindings raw))).getD false = false) :
    ∃ piece, visit env conv exposure ctx p raw bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) ∧
      (Unbound raw bindings.length → piece.code = app ``HybridWord.Expr.local [(ClosedTerm.bindingIndex n).val]) := by
  obtain ⟨proof,proofCore,valueCore,found,proofRep,valueRep,valueTyped,proofTyped⟩ :=
    localFact_typed_complete library.localLibrary inputs scope.represented scope.typed selected
  rcases lookup_typed types raw conv with miss | ⟨cached,hit,typed⟩
  ·
    have listSame : inputs.ls.val = wordList scope.values :=
      inputs.ls.property.unique (wordList_represents scope.represented)
    rw [← listSame] at proofTyped
    let code := ClosedTerm.app ``HybridWord.Expr.local [.bindingIndex n]
    have codeRep : Represents code.val (localValue (ClosedTerm.bindingIndex n).represented.val) :=
      .app (.constant rfl) (ClosedTerm.bindingIndex n).represented.property
    obtain ⟨artifact,checked,proofTyped,_,_⟩ := finish_cast_complete
      (scalarExpected_represents inputs codeRep valueRep) proofRep (proofTyped.mono Arithmetic.Includes.embed)
      (known := noKnownTypes env 0) (by intro _ _ _ h; cases h) coverage exposure code.val
    let piece : Piece env ctx p (materialize bindings raw) scalarExpected := ⟨code.val,artifact,code.closed,code.represented⟩
    refine ⟨piece,?_,⟨⟨⟨valueCore,valueRep⟩,valueTyped.mono Arithmetic.Includes.embed,?_,proofTyped⟩⟩,by intro _; rfl⟩
    · have bound : n < p.locals.length := (List.getElem?_eq_some_iff.mp selected).choose
      have same := sameTerm_complete valueRep valueRep
      rw [visit]
      rotate_left
      · exact shape.notLet
      · exact shape.notBeta
      simp only [miss,node,notIndex,notLeft,notRight]
      simp only [Bool.false_eq_true,↓reduceIte,List.forIn_cons,List.forIn_nil,
        bind,Option.bind,pure,Option.pure_def,notIndex,notLeft,notRight]
      have checkedInline : finish env conv exposure ctx
          (scalarExpected p (ClosedTerm.app ``HybridWord.Expr.local [.bindingIndex n]).val (materialize bindings raw))
          (ClosedTerm.app ``HybridWord.Expr.local [.bindingIndex n]).val proof = some artifact := checked
      have loop := forIn_range_hit p.locals.length n
        (⟨none, PUnit.unit⟩ : MProd (Option (Piece env ctx p (materialize bindings raw) scalarExpected)) PUnit) ⟨some piece, PUnit.unit⟩
        (fun k _ => if (p.locals[k]?.map (sameTerm (materialize bindings raw))).getD false then do
          let pr ← localFact p k p.locals
          let child ← (do
            let h ← finish env conv exposure ctx
              (scalarExpected p (ClosedTerm.app ``HybridWord.Expr.local [.bindingIndex k]).val (materialize bindings raw))
              (ClosedTerm.app ``HybridWord.Expr.local [.bindingIndex k]).val pr
            pure (⟨_,h,(ClosedTerm.app ``HybridWord.Expr.local [.bindingIndex k]).closed,
              (ClosedTerm.app ``HybridWord.Expr.local [.bindingIndex k]).represented⟩ : Piece env ctx p (materialize bindings raw) scalarExpected))
          pure (.done ⟨some child, PUnit.unit⟩)
          else pure (.yield ⟨none, PUnit.unit⟩)) bound
        (by intro k hk; simp only [first k hk,Bool.false_eq_true,↓reduceIte,pure,Option.pure_def])
        (by
          simp only [selected,Option.map_some,same,Option.getD_some,↓reduceIte,
            found,bind,Option.bind,checkedInline,pure,Option.pure_def]
          rfl)
      simp only [bind,Option.bind,pure,Option.pure_def] at loop
      simp only [finishScalar,bind,Option.bind,pure,Option.pure_def]
      rw [loop]
    · have constructor : CastTyping env 0 casts ctx (.const ``HybridWord.Expr.local [])
          (.forallE (.const ``Nat []) exprType) :=
        .constant library.localLibrary.constructor (by simp) rfl
      exact .application constructor ((ClosedTerm.bindingIndex_typed library.localLibrary.naturals n).withCasts casts)
  · refine ⟨cached,?_,typed,?_⟩
    · rw [visit]
      · simp only [hit]
      · exact shape.notLet
      · exact shape.notBeta
    · intro outside
      rw [outside.lookup_none] at hit
      contradiction

theorem local_visit_complete (inputs : InputsTyped env ctx p) (library : Library env)
    (bindings : Bindings env ctx p) (types : BindingTypes inputs casts bindings proofCasts)
    (scope : Locals env ctx p) (conv : Conversion env) (exposure : Exposure env) (coverage : conv.Covers 0 proofCasts)
    {n : Nat} (shape : LocalOccurrence raw)
    (selected : p.locals[n]? = some (materialize bindings raw))
    (notIndex : sameTerm (materialize bindings raw) p.i = false)
    (notLeft : sameTerm (materialize bindings raw) p.x = false)
    (notRight : sameTerm (materialize bindings raw) p.y = false)
    (first : ∀ j < n, (p.locals[j]?.map (sameTerm (materialize bindings raw))).getD false = false) :
    ∃ piece, visit env conv exposure ctx p raw bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := local_visit_complete_code inputs library bindings types scope conv exposure
    coverage shape selected notIndex notLeft notRight first
  exact ⟨piece,success,typed⟩


theorem local_complete (inputs : InputsTyped env ctx p) (library : Library env)
    (scope : Locals env ctx p) (conv : Conversion env) (exposure : Exposure env) (coverage : conv.Covers 0 Casts)
    {n : Nat} {source : Lean.Expr} (shape : LocalOccurrence source)
    (selected : p.locals[n]? = some source)
    (notIndex : sameTerm source p.i = false)
    (notLeft : sameTerm source p.x = false)
    (notRight : sameTerm source p.y = false)
    (first : ∀ j < n, (p.locals[j]?.map (sameTerm source)).getD false = false) :
    ∃ piece, ScalarEnvironment.parse env conv exposure ctx p source = some piece ∧
      Nonempty (ScalarCasts inputs piece Casts) := by
  exact local_visit_complete inputs library [] (BindingTypes.empty inputs Casts)
    scope conv exposure coverage shape selected notIndex notLeft notRight first

theorem parameter_visit_complete_code (inputs : InputsTyped env ctx p) (library : Library env)
    (bindings : Bindings env ctx p) (types : BindingTypes inputs casts bindings proofCasts)
    (side : Side) (conv : Conversion env) (exposure : Exposure env) (coverage : conv.Covers 0 proofCasts)
    (shape : LocalOccurrence raw)
    (represented : Represents (materialize bindings raw) (side.representation inputs).val)
    (notIndex : sameTerm (materialize bindings raw) p.i = false)
    (notLeft : side = .right → sameTerm (materialize bindings raw) p.x = false) :
    ∃ piece, visit env conv exposure ctx p raw bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) ∧
      (Unbound raw bindings.length → piece.code = .const side.target []) := by
  rcases lookup_typed types raw conv with miss | ⟨cached,hit,typed⟩
  ·
    have fact : CastTyping env 0 proofCasts ctx (.const side.fact []) side.signature :=
      .constant (library.sideFact side) (by simp) rfl
    have typed : CastTyping env 0 proofCasts ctx (applications (.const side.fact []) inputs.args)
        (equalValues (optionType wordType)
          (scalarValue inputs.i.val inputs.x.val inputs.y.val inputs.s.val inputs.ls.val (.const side.target []))
          (someValue wordType (side.representation inputs).val)) := by
      have applied := inputs.apply_casts fact
      cases side <;>
        simpa only [Side.signature,Side.result,Side.representation,Side.target,Side.fact,
          InputsTyped.instantiate,applications,wordType,optionType,equalValues,scalarValue,someValue,
          Nat.reduceAdd,← VExpr.lift_instN_lo,VExpr.inst_lift,VExpr.inst,
          VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ] using applied
    obtain ⟨artifact,checked,proofTyped,_⟩ := finish_cast_complete
      (scalarExpected_represents inputs (Represents.constant (name := side.target) (us := []) rfl) represented)
      (app_represents (Represents.constant (name := side.fact) (us := []) rfl) inputs.arguments)
      typed (known := noKnownTypes env 0) (by intro _ _ _ h; cases h)
      coverage exposure (.const side.target [])
    let piece : Piece env ctx p (materialize bindings raw) scalarExpected :=
      ⟨.const side.target [],artifact,rfl,⟨.const side.target [],.constant rfl⟩⟩
    refine ⟨piece,?_,⟨⟨⟨_,represented⟩,(side.typed inputs).withCasts casts,
      .constant (library.sideConstructor side) (by simp) rfl,proofTyped⟩⟩,by intro _; rfl⟩
    have same := sameTerm_complete represented (side.representation inputs).property
    apply eq_of_heq
    rw [visit]
    · cases side <;> simp only [Side.source] at notIndex notLeft same ⊢
      all_goals simp [-heq_eq_eq,miss,node,List.forIn_cons,
        notIndex,notLeft,same]
      all_goals simp only [Option.bind_assoc,Option.bind_some,Option.bind_fun_some]
      all_goals apply heq_of_eq
      all_goals
        simp [finishScalar,ClosedTerm.const,Side.fact,Side.target,Side.source,app] at checked ⊢
        exact ⟨artifact,checked,rfl⟩
    · exact shape.notLet
    · exact shape.notBeta
  · refine ⟨cached,?_,typed,?_⟩
    · rw [visit]
      · simp only [hit]
      · exact shape.notLet
      · exact shape.notBeta
    · intro outside
      rw [outside.lookup_none] at hit
      contradiction

theorem parameter_visit_complete (inputs : InputsTyped env ctx p) (library : Library env)
    (bindings : Bindings env ctx p) (types : BindingTypes inputs casts bindings proofCasts)
    (side : Side) (conv : Conversion env) (exposure : Exposure env) (coverage : conv.Covers 0 proofCasts)
    (shape : LocalOccurrence raw)
    (represented : Represents (materialize bindings raw) (side.representation inputs).val)
    (notIndex : sameTerm (materialize bindings raw) p.i = false)
    (notLeft : side = .right → sameTerm (materialize bindings raw) p.x = false) :
    ∃ piece, visit env conv exposure ctx p raw bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := parameter_visit_complete_code inputs library bindings types side conv exposure coverage shape represented notIndex notLeft
  exact ⟨piece,success,typed⟩

theorem parameter_complete (inputs : InputsTyped env ctx p) (library : Library env)
    (side : Side) (conv : Conversion env) (exposure : Exposure env) (coverage : conv.Covers 0 Casts) (bound : side.source p = .bvar n)
    (notIndex : sameTerm (side.source p) p.i = false)
    (notLeft : side = .right → sameTerm (side.source p) p.x = false) :
    ∃ piece, ScalarEnvironment.parse env conv exposure ctx p (side.source p) = some piece ∧
      Nonempty (ScalarCasts inputs piece Casts) := by
  have shape : LocalOccurrence (side.source p) := by
    rw [bound]
    exact .variable n
  simpa only [ScalarEnvironment.parse,materialize_nil] using
    parameter_visit_complete inputs library [] (BindingTypes.empty inputs Casts)
      side conv exposure coverage shape (side.representation inputs).property notIndex notLeft

theorem materialize_register (bindings : Bindings env ctx p) (s r : Lean.Expr) :
    materialize bindings (app ``HybridWord.State.regs [s,r]) =
      app ``HybridWord.State.regs [materialize bindings s,materialize bindings r] := by
  cases bindings <;> rfl

theorem register_visit_complete_code (inputs : InputsTyped env ctx p) (library : Library env)
    (types : BindingTypes inputs casts bindings proofCasts)
    (stateRep : Represents (materialize bindings s) inputs.s.val)
    (register : NatArgument env ctx (materialize bindings r))
    (conv : Conversion env) (exposure : Exposure env) (coverage : conv.Covers 0 proofCasts)
    (scope : Separated p (materialize bindings (app ``HybridWord.State.regs [s,r]))) :
    ∃ piece, visit env conv exposure ctx p (app ``HybridWord.State.regs [s,r]) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) ∧
      (piece.code = app ``HybridWord.Expr.reg [materialize bindings r]) := by
  have sourceRep : Represents (materialize bindings (app ``HybridWord.State.regs [s,r]))
      (applications (.const ``HybridWord.State.regs []) [inputs.s.val,register.represented.val]) := by
    rw [materialize_register]
    exact .app (.app (.constant rfl) stateRep) register.represented.property
  rcases lookup_typed types (app ``HybridWord.State.regs [s,r]) conv with miss | ⟨cached,hit,typed⟩
  ·
    have targetRep : Represents (app ``HybridWord.Expr.reg [materialize bindings r])
        (.app (.const ``HybridWord.Expr.reg []) register.represented.val) :=
      .app (.constant rfl) register.represented.property
    obtain ⟨artifact,checked,typed,codeEq,proofEq⟩ := finish_cast_complete
      (scalarExpected_represents inputs targetRep sourceRep)
      (app_represents (f := Lean.Expr.const ``WordFrontendFacts.register []) (.constant rfl)
        (.cons register.represented.property inputs.arguments))
      (register_cast_typed inputs register library.registerFact) (known := noKnownTypes env 0)
      (by intro _ _ _ h; cases h) coverage exposure (app ``HybridWord.Expr.reg [materialize bindings r])
    obtain ⟨core,translated,same⟩ := register.represented.property.translate_complete
    let number : ClosedTerm := ⟨materialize bindings r,register.closed,core⟩
    let code := ClosedTerm.app ``HybridWord.Expr.reg [number]
    let piece : Piece env ctx p (materialize bindings (app ``HybridWord.State.regs [s,r])) scalarExpected :=
      ⟨code.val,artifact,code.closed,code.represented⟩
    have closed : closedTerm (materialize bindings r) = some number := by
      simp only [closedTerm,register.closed,translated,number,bind,Option.bind,dite_true,pure]
    refine ⟨piece,?_,⟨⟨⟨_,sourceRep⟩,?_,?_,typed⟩⟩,rfl⟩
    · have stateSame := sameTerm_complete stateRep inputs.s.property
      have head : (app ``HybridWord.State.regs [s,r]).getAppFn.constName? = some ``HybridWord.State.regs := rfl
      rw [visit] <;> try (solve | intro name ty value next flag h; cases h)
      simp only [miss,node,head]
      simp [List.forIn_cons,scope.index,scope.left,scope.right,scope.locals]
      simp only [forIn_constant_yield]
      simp [arguments,stateSame,closed,finishScalar,checked,number,code,piece,ClosedTerm.app,app,
        Lean.mkApp,Lean.mkAppB]
      simpa [app] using checked
    · have fact : CastTyping env 0 casts ctx (.const ``HybridWord.State.regs [])
          (.forallE stateType (.forallE (.const ``Nat []) wordType)) :=
        .constant library.registerAccessor (by simp) rfl
      have first := CastTyping.application fact (inputs.hs.withCasts casts)
      simp only [VExpr.inst,wordType] at first
      exact .exact (.application first (register.typed.withCasts casts))
    · have fact : CastTyping env 0 casts ctx (.const ``HybridWord.Expr.reg []) (.forallE (.const ``Nat []) exprType) :=
        .constant library.registerConstructor (by simp) rfl
      change CastTyping env 0 casts ctx (.app (.const ``HybridWord.Expr.reg []) core.val) exprType
      rw [same]
      exact .application fact (register.typed.withCasts casts)
  · simp [ScalarEnvironment.lookup,app] at hit

theorem register_visit_complete (inputs : InputsTyped env ctx p) (library : Library env)
    (types : BindingTypes inputs casts bindings proofCasts)
    (stateRep : Represents (materialize bindings s) inputs.s.val)
    (register : NatArgument env ctx (materialize bindings r))
    (conv : Conversion env) (exposure : Exposure env) (coverage : conv.Covers 0 proofCasts)
    (scope : Separated p (materialize bindings (app ``HybridWord.State.regs [s,r]))) :
    ∃ piece, visit env conv exposure ctx p (app ``HybridWord.State.regs [s,r]) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := register_visit_complete_code inputs library types stateRep register conv exposure coverage scope
  exact ⟨piece,success,typed⟩

theorem register_complete (inputs : InputsTyped env ctx p) (library : Library env)
    (register : NatArgument env ctx r) (conv : Conversion env) (exposure : Exposure env) (coverage : conv.Covers 0 Casts)
    (scope : Separated p (app ``HybridWord.State.regs [p.s,r])) :
    ∃ piece, ScalarEnvironment.parse env conv exposure ctx p (app ``HybridWord.State.regs [p.s,r]) = some piece ∧
      Nonempty (ScalarCasts inputs piece Casts) := by
  exact register_visit_complete inputs library (BindingTypes.empty inputs Casts)
    inputs.s.property register conv exposure coverage scope

theorem materialize_select (bindings : Bindings env ctx p) (v d yes no : Lean.Expr) :
    materialize bindings (Branch.Select.source v d yes no) =
      Branch.Select.source (materialize bindings v) (materialize bindings d)
        (materialize bindings yes) (materialize bindings no) := by
  cases bindings <;> rfl

open Branch (condition nativeCondition nativeTestHeader iteSignature ite_typed) in
theorem select_visit_complete_code (inputs : InputsTyped env ctx p)
    (types : BindingTypes inputs casts bindings proofCasts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    {e : Piece env ctx p (materialize bindings v) scalarExpected} (value : ScalarCasts inputs e casts proofCasts)
    {a : Piece env ctx p (materialize bindings yes) scalarExpected} (left : ScalarCasts inputs a casts proofCasts)
    {b : Piece env ctx p (materialize bindings no) scalarExpected} (right : ScalarCasts inputs b casts proofCasts)
    (decisionRep : Represents (materialize bindings d) dc)
    (predicateTyped : CastTyping env 0 casts ctx (condition value.sourceCore.val) (.sort .zero))
    (decisionTyped : CastTyping env 0 casts ctx dc (.app (.const ``Decidable []) (condition value.sourceCore.val)))
    (wordTyped : DirectTyping env 0 ctx wordType (.sort (.succ .zero)))
    (iteDecl : env.constants ``ite = some iteSignature)
    (registered : env.constants ``WordFrontendFacts.select = some ⟨0,Branch.Select.signature⟩)
    (constructor : env.constants ``HybridWord.Expr.select = some ⟨0,Branch.Select.constructorSignature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (valueParsed : visit env conv exposure ctx p v bindings = some e)
    (leftParsed : visit env conv exposure ctx p yes bindings = some a)
    (rightParsed : visit env conv exposure ctx p no bindings = some b)
    (scope : Separated p (materialize bindings (Branch.Select.source v d yes no))) :
    ∃ result, visit env conv exposure ctx p (Branch.Select.source v d yes no) bindings = some result ∧
      Nonempty (ScalarCasts inputs result casts proofCasts) ∧
      (result.code = app ``HybridWord.Expr.select [e.code,a.code,b.code]) := by
  have rep : Represents (materialize bindings (Branch.Select.source v d yes no))
      (Branch.Select.choice value.sourceCore.val dc left.sourceCore.val right.sourceCore.val) := by
    rw [materialize_select]
    exact Branch.Select.source_represents value.sourceCore.property decisionRep left.sourceCore.property right.sourceCore.property
  rcases lookup_typed types (Branch.Select.source v d yes no) conv with miss | ⟨cached,hit,typed⟩
  ·
    obtain ⟨artifact,checked,proofTyped,_,_⟩ := Branch.Select.finish_complete inputs (value.inProofCasts embeds) (left.inProofCasts embeds) (right.inProofCasts embeds) decisionRep (decisionTyped.mono embeds)
      registered coverage exposure
    let code := ClosedTerm.app ``HybridWord.Expr.select [e.closedTerm,a.closedTerm,b.closedTerm]
    let art : Artifact env ctx (scalarExpected p code.val (materialize bindings (Branch.Select.source v d yes no))) := by
      simpa only [materialize_select,code,ClosedTerm.app,Piece.closedTerm] using artifact
    let result : Piece env ctx p (materialize bindings (Branch.Select.source v d yes no)) scalarExpected := ⟨code.val,art,code.closed,code.represented⟩
    refine ⟨result,?_,⟨⟨⟨_,rep⟩,?_,?_,?_⟩⟩,rfl⟩
    · have head : (Branch.Select.source v d yes no).getAppFn.constName? = some ``ite := rfl
      apply eq_of_heq
      rw [visit] <;> try (solve | intro name ty value next flag h; cases h)
      simp only [miss,node,head]
      simp [-heq_eq_eq,List.forIn_cons,scope.index,scope.left,scope.right,scope.locals]
      simp only [forIn_constant_yield]
      simp [arguments,conditionValue,below,Branch.Select.source,nativeCondition,nativeTestHeader,
        Arithmetic.nativeLiteral,Arithmetic.nativeWidth,
        Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,
        List.map_cons,List.map_nil,Lean.Expr.getAppFn,Lean.Expr.constName?]
      try apply heq_of_eq
      cases bindings <;> simp [finishScalar,ClosedTerm.app,Piece.closedTerm,code,result,art,
        materialize,LeanBindings.substitute,Branch.Select.source,nativeCondition,nativeTestHeader,
        Arithmetic.nativeLiteral,Arithmetic.nativeWidth,word,app,
        Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked ⊢
      all_goals exact ⟨e,valueParsed,a,leftParsed,b,rightParsed,artifact,checked,⟨⟨rfl,rfl⟩,rfl⟩,HEq.rfl,HEq.rfl⟩
    · exact .exact (ite_typed wordTyped (by trivial) predicateTyped decisionTyped left.value right.value iteDecl)
    · have h : CastTyping env 0 casts ctx (.const ``HybridWord.Expr.select []) Branch.Select.constructorSignature :=
        .constant constructor (by simp) rfl
      have a1 := CastTyping.application h value.target
      simp only [Branch.Select.constructorSignature,exprType,VExpr.inst] at a1
      have a2 := CastTyping.application a1 left.target
      simp only [VExpr.inst] at a2
      exact .application a2 right.target
  
    · cases bindings <;> simpa [result,art,materialize,LeanBindings.substitute,Branch.Select.source,
        nativeCondition,nativeTestHeader,Arithmetic.nativeLiteral,Arithmetic.nativeWidth,word,app,
        Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] using proofTyped
  · simp [ScalarEnvironment.lookup,Branch.Select.source,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2] at hit

open Branch (condition nativeCondition nativeTestHeader iteSignature ite_typed) in
theorem select_visit_complete (inputs : InputsTyped env ctx p)
    (types : BindingTypes inputs casts bindings proofCasts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    {e : Piece env ctx p (materialize bindings v) scalarExpected} (value : ScalarCasts inputs e casts proofCasts)
    {a : Piece env ctx p (materialize bindings yes) scalarExpected} (left : ScalarCasts inputs a casts proofCasts)
    {b : Piece env ctx p (materialize bindings no) scalarExpected} (right : ScalarCasts inputs b casts proofCasts)
    (decisionRep : Represents (materialize bindings d) dc)
    (predicateTyped : CastTyping env 0 casts ctx (condition value.sourceCore.val) (.sort .zero))
    (decisionTyped : CastTyping env 0 casts ctx dc (.app (.const ``Decidable []) (condition value.sourceCore.val)))
    (wordTyped : DirectTyping env 0 ctx wordType (.sort (.succ .zero)))
    (iteDecl : env.constants ``ite = some iteSignature)
    (registered : env.constants ``WordFrontendFacts.select = some ⟨0,Branch.Select.signature⟩)
    (constructor : env.constants ``HybridWord.Expr.select = some ⟨0,Branch.Select.constructorSignature⟩)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (valueParsed : visit env conv exposure ctx p v bindings = some e)
    (leftParsed : visit env conv exposure ctx p yes bindings = some a)
    (rightParsed : visit env conv exposure ctx p no bindings = some b)
    (scope : Separated p (materialize bindings (Branch.Select.source v d yes no))) :
    ∃ result, visit env conv exposure ctx p (Branch.Select.source v d yes no) bindings = some result ∧
      Nonempty (ScalarCasts inputs result casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := select_visit_complete_code inputs types embeds value left right
    decisionRep predicateTyped decisionTyped wordTyped iteDecl registered constructor coverage exposure
    valueParsed leftParsed rightParsed scope
  exact ⟨piece,success,typed⟩

open Branch (condition nativeCondition nativeTestHeader iteSignature ite_typed) in
theorem select_complete (inputs : InputsTyped env ctx p) [Arithmetic.Includes casts]
    {e : Piece env ctx p v scalarExpected} (value : ScalarCasts inputs e casts)
    {a : Piece env ctx p yes scalarExpected} (left : ScalarCasts inputs a casts)
    {b : Piece env ctx p no scalarExpected} (right : ScalarCasts inputs b casts)
    (decisionRep : Represents d dc)
    (predicateTyped : CastTyping env 0 casts ctx (condition value.sourceCore.val) (.sort .zero))
    (decisionTyped : CastTyping env 0 casts ctx dc (.app (.const ``Decidable []) (condition value.sourceCore.val)))
    (wordTyped : DirectTyping env 0 ctx wordType (.sort (.succ .zero)))
    (iteDecl : env.constants ``ite = some iteSignature)
    (registered : env.constants ``WordFrontendFacts.select = some ⟨0,Branch.Select.signature⟩)
    (constructor : env.constants ``HybridWord.Expr.select = some ⟨0,Branch.Select.constructorSignature⟩)
    (coverage : Conversion.Covers conv 0 casts) (exposure : Exposure env)
    (valueParsed : ScalarEnvironment.parse env conv exposure ctx p v = some e)
    (leftParsed : ScalarEnvironment.parse env conv exposure ctx p yes = some a)
    (rightParsed : ScalarEnvironment.parse env conv exposure ctx p no = some b)
    (missI : sameTerm (Branch.Select.source v d yes no) p.i = false)
    (missX : sameTerm (Branch.Select.source v d yes no) p.x = false)
    (missY : sameTerm (Branch.Select.source v d yes no) p.y = false)
    (missLocals : ∀ k : Nat, (p.locals[k]?.map (sameTerm (Branch.Select.source v d yes no))).getD false = false) :
    ∃ result, ScalarEnvironment.parse env conv exposure ctx p (Branch.Select.source v d yes no) = some result ∧
      Nonempty (ScalarCasts inputs result casts) := by
  exact select_visit_complete inputs (BindingTypes.empty inputs casts) (fun _ _ _ h => h)
    value left right decisionRep predicateTyped decisionTyped wordTyped iteDecl registered constructor
    coverage exposure valueParsed leftParsed rightParsed ⟨missI,missX,missY,missLocals⟩


theorem materialize_neg (bindings : Bindings env ctx p) (v : Lean.Expr) :
    materialize bindings (.app nativeNegHeader v) = .app nativeNegHeader (materialize bindings v) := by
  rw [materialize_app,materialize_closed bindings (by rfl)]

theorem neg_visit_complete_code (inputs : InputsTyped env ctx p) (library : Library env)
    (types : BindingTypes inputs casts bindings proofCasts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    {a : Piece env ctx p (materialize bindings v) scalarExpected}
    (value : ScalarCasts inputs a casts proofCasts)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (parsed : visit env conv exposure ctx p v bindings = some a)
    (scope : Separated p (materialize bindings (.app nativeNegHeader v))) :
    ∃ piece, visit env conv exposure ctx p (.app nativeNegHeader v) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) ∧
      (piece.code = app ``HybridWord.Expr.neg [a.code]) := by
  have rep : Represents (materialize bindings (.app nativeNegHeader v)) (.app negHeader value.sourceCore.val) := by
    rw [materialize_neg]
    exact .app negHeader_represents value.sourceCore.property
  rcases lookup_typed types (.app nativeNegHeader v) conv with miss | ⟨cached,hit,typed⟩
  · obtain ⟨artifact,checked,typed,_,_⟩ := neg_finish inputs (value.inProofCasts embeds) library.negFact coverage exposure
    let code := ClosedTerm.app ``HybridWord.Expr.neg [a.closedTerm]
    let art : Artifact env ctx (scalarExpected p code.val (materialize bindings (.app nativeNegHeader v))) := by
      simpa only [materialize_neg,code,ClosedTerm.app,Piece.closedTerm] using artifact
    let piece : Piece env ctx p (materialize bindings (.app nativeNegHeader v)) scalarExpected :=
      ⟨code.val,art,code.closed,code.represented⟩
    have sourceTyped := CastTyping.checkedApplication (library.toSignatures.negHeader_typed.mono Arithmetic.Includes.embed) value.value
    refine ⟨piece,?_,⟨⟨⟨_,rep⟩,.exact sourceTyped,?_,?_⟩⟩,rfl⟩
    · have head : (Lean.Expr.app nativeNegHeader v).getAppFn.constName? = some ``Neg.neg := rfl
      apply eq_of_heq
      rw [visit] <;> try (solve | intro name ty value next flag h; cases h)
      simp only [miss,node,head]
      simp [-heq_eq_eq,List.forIn_cons,scope.index,scope.left,scope.right,scope.locals]
      simp only [forIn_constant_yield]
      have smaller : syntaxSize v < syntaxSize (.app nativeNegHeader v) := by simp only [syntaxSize]; omega
      have last : (arguments (.app nativeNegHeader v)).getLast? = some ⟨v,smaller⟩ := by rfl
      simp only [last,parsed,Option.bind_some,Option.bind_assoc,Option.bind_fun_some]
      apply heq_of_eq
      cases bindings <;> simp [materialize,LeanBindings.substitute,nativeNegHeader,nativeWidth,word,
        finishScalar,ClosedTerm.app,Piece.closedTerm,code,piece,art,app,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at checked ⊢
      all_goals exact ⟨a,parsed,artifact,checked,rfl,HEq.rfl,HEq.rfl⟩
    · have fact : CastTyping env 0 casts ctx (.const ``HybridWord.Expr.neg []) (.forallE exprType exprType) :=
        .constant library.negConstructor (by simp) rfl
      exact .application fact value.target
    · cases bindings <;> simpa [piece,art,materialize,LeanBindings.substitute,nativeNegHeader,nativeWidth,
        app,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] using typed
  · simp [ScalarEnvironment.lookup] at hit

theorem neg_visit_complete (inputs : InputsTyped env ctx p) (library : Library env)
    (types : BindingTypes inputs casts bindings proofCasts)
    (embeds : ∀ scope a b, casts scope a b → proofCasts scope a b)
    {a : Piece env ctx p (materialize bindings v) scalarExpected}
    (value : ScalarCasts inputs a casts proofCasts)
    (coverage : Conversion.Covers conv 0 proofCasts) (exposure : Exposure env)
    (parsed : visit env conv exposure ctx p v bindings = some a)
    (scope : Separated p (materialize bindings (.app nativeNegHeader v))) :
    ∃ piece, visit env conv exposure ctx p (.app nativeNegHeader v) bindings = some piece ∧
      Nonempty (ScalarCasts inputs piece casts proofCasts) := by
  obtain ⟨piece,success,typed,_⟩ := neg_visit_complete_code inputs library types embeds value coverage exposure parsed scope
  exact ⟨piece,success,typed⟩

theorem neg_complete (inputs : InputsTyped env ctx p) (library : Library env)
    {a : Piece env ctx p v scalarExpected} (value : ScalarCasts inputs a Casts)
    (coverage : Conversion.Covers conv 0 Casts) (exposure : Exposure env)
    (parsed : ScalarEnvironment.parse env conv exposure ctx p v = some a)
    (scope : Separated p (.app nativeNegHeader v)) :
    ∃ piece, ScalarEnvironment.parse env conv exposure ctx p (.app nativeNegHeader v) = some piece ∧
      Nonempty (ScalarCasts inputs piece Casts) := by
  simpa only [ScalarEnvironment.parse,materialize_nil] using
    neg_visit_complete inputs library (BindingTypes.empty inputs Casts) (fun _ _ _ h => h)
      value coverage exposure parsed scope

theorem complete (inputs : InputsTyped env ctx p) (library : Library env)
    (locals : Locals env ctx p)
    (coverage : Conversion.Covers conv 0 Casts) (exposure : Exposure env)
    (form : Form env ctx p source) :
    ∃ piece, ScalarEnvironment.parse env conv exposure ctx p source = some piece ∧
      Nonempty (ScalarCasts inputs piece Casts) := by
  induction form with
  | parameter side n bound notIndex notLeft =>
    exact parameter_complete inputs library side conv exposure coverage bound notIndex notLeft
  | localValue source shape k selected notIndex notLeft notRight first =>
    obtain ⟨piece,parsed,⟨typed⟩⟩ := local_complete inputs library locals conv exposure coverage shape selected notIndex notLeft notRight first
    exact ⟨piece,parsed,⟨typed⟩⟩
  | index n bound => exact index_complete inputs library conv exposure coverage bound
  | literal n scope => exact literal_complete inputs library coverage exposure scope
  | neg value scope ih =>
    obtain ⟨a,ha,⟨ta⟩⟩ := ih
    exact neg_complete inputs library ta coverage exposure ha scope
  | select value decision yes no scope ihValue ihYes ihNo =>
    obtain ⟨v,hv,⟨tv⟩⟩ := ihValue
    obtain ⟨a,ha,⟨ta⟩⟩ := ihYes
    obtain ⟨b,hb,⟨tb⟩⟩ := ihNo
    obtain ⟨vc,dc,vr,dr,pt,dt⟩ := decision.typing
    rw [← tv.sourceCore.property.unique vr] at pt dt
    exact select_complete inputs tv ta tb dr pt dt (.constant library.word (by simp) rfl)
      library.ite library.selectFact library.selectConstructor coverage exposure hv ha hb
      scope.index scope.left scope.right scope.locals
  | register register scope =>
    exact register_complete inputs library register conv exposure coverage scope
  | binary op _ _ scope ihLeft ihRight =>
    obtain ⟨a,ha,⟨ca⟩⟩ := ihLeft
    obtain ⟨b,hb,⟨cb⟩⟩ := ihRight
    exact binary_complete inputs library ca cb op coverage exposure ha hb scope

/-- For the actual loaded converter, arithmetic cast coverage follows from the
fixed library definitions. No success of scalar parsing or of a conversion
query is assumed. Loading itself is a separate frontend obligation. -/
theorem complete_loaded
    (loaded : WordFrontend.load native name = some loadedLibrary)
    (wordShape : WordDeclaration native) (decEqShape : DecEqDeclaration native)
    (freshWord : ``HybridWord.Word ≠ name)
    (freshBitVec : ``BitVec ≠ name)
    (freshOfNat : ``OfNat ≠ name)
    (freshNumerals : ∀ n ∈ [``Nat.zero,``Nat.succ,``Nat.mul], n ≠ name)
    (freshClasses : ∀ op : Binary, op.className ≠ name)
    (freshHeterogeneous : ∀ op : Binary, op.heterogeneous ≠ name)
    (freshNeg : ``Neg ≠ name) (freshOption : ``Option ≠ name) (freshReadClass : ``GetElem? ≠ name)
    (inputs : InputsTyped loadedLibrary.model ctx p)
    (library : Library loadedLibrary.model)
    (locals : Locals loadedLibrary.model ctx p)
    (form : Form loadedLibrary.model ctx p source) :
    ∃ piece, ScalarEnvironment.parse loadedLibrary.model loadedLibrary.conversion
      loadedLibrary.exposure ctx p source = some piece ∧
      Nonempty (ScalarCasts inputs piece Casts) := by
  exact complete inputs library locals
    (loaded_conversion_covers loaded wordShape decEqShape freshWord freshBitVec freshOfNat
      freshNumerals freshClasses freshHeterogeneous freshNeg freshOption freshReadClass library.toSignatures) loadedLibrary.exposure form

end IRComparison.WordFrontend.ScalarSyntax
