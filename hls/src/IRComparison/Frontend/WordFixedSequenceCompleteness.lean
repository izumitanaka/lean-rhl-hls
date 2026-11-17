import IRComparison.Frontend.WordFixedReadSourceCompleteness

/-! Source/static conditions for composition of the connected memory rules.
This is a proof-only judgment over ordinary Lean.Expr, not another executable
IR or a new input DSL. Its constructors contain no parser outcome or Entry.
Coverage is incremental: the full ScopedSyntax grammar remains accepted; its
remaining static-code cases are not claimed complete by this module. -/
namespace IRComparison.WordFrontend.FixedSequenceCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic CertifiedHLS
set_option maxHeartbeats 1800000

/-- Contextual native computation. Scalar locals and loop indices remain
parameters inside the induction; only a closed program fixes them at the root. -/
abbrev Meaning := HybridWord.Word → HybridWord.Word → HybridWord.Word →
  List HybridWord.Word → Program

/-- Native iterator computation, retaining forIn/foldlM as written. -/
def naturalRange (kind : NaturalLoop.Kind) (count : HybridWord.Word)
    (body : Nat → Program) (s : HybridWord.State) : Option HybridWord.State :=
  match kind with
  | .forIn => ForIn.forIn (List.range count.toNat) s (fun k t => WordLoopFacts.lift (body k t))
  | .fold => (List.range count.toNat).foldlM (fun t k => body k t) s

/-- Signed integer notation at a static loop bound. This covers numerals,
negation and four arithmetic operations without normalizing arbitrary Lean expressions. -/
inductive StaticBound : Lean.Expr → Int → Prop where
  | natural (n : Nat) : StaticBound (For.nativeNatural n) n
  | negative (value : StaticBound raw n) : StaticBound (For.nativeNegative raw) (-n)
  | binary (op : Binary) (left : StaticBound a n) (right : StaticBound b m) :
      StaticBound (For.nativeBinary op a b) (For.binaryValue op n m)

theorem StaticBound.typed (bound : StaticBound raw n) (library : For.BoundSignatures env)
    (arithmetic : Arithmetic.Signatures env) :
    Nonempty (For.Bound env ctx raw) := by
  induction bound with
  | natural n => exact ⟨.natural library n⟩
  | negative _ ih => obtain ⟨bound⟩ := ih; exact ⟨.negative library bound⟩
  | binary op _ _ il ir =>
    obtain ⟨a⟩ := il; obtain ⟨b⟩ := ir
    exact ⟨.binary library arithmetic op a b⟩

/-- The generated command/quotation indices are fixed by each source rule.
They are not arbitrary backend entries or successful parser results. -/
inductive Source (ds : FixedMemory.Declarations) {env : VEnv} :
    StructuralBody.Mode → List VExpr → Inputs → Lean.Expr → Meaning → HybridWord.Cmd → Lean.Expr → Prop where
  | returns (tag : Return.Form) :
      Source ds (env := env) .body ctx p (tag.source p.s) (fun _ _ _ _ s => some s) .skip (.const ``HybridWord.Cmd.skip [])
  | valueCurrent : Source ds (env := env) .value ctx p p.s (fun _ _ _ _ s => some s) .skip (.const ``HybridWord.Cmd.skip [])
  | valueAssign (register : Nat) (rn : NatNotation)
      (value : FixedScalarCompleteness.Scoped env ctx p v f vc vq) :
      Source ds (env := env) .value ctx p (app ``HybridWord.State.set [p.s,rn.native register,v])
        (fun i x y ls s => (f i x y s ls).bind (fun v => some (s.set register v)))
        (.assign register vc) (app ``HybridWord.Cmd.assign [rn.native register,vq])
  | yield (value : Source ds (env := env) .value ctx p v f vc vq) :
      Source ds (env := env) .step ctx p (Step.yieldSource v) f vc vq

  | copy (destination origin count : Nat) (dn on cn : NatNotation)
      (destinationDeclared : FixedMemory.lookup ds destination = some count)
      (originDeclared : FixedMemory.lookup ds origin = some count) :
      Source ds (env := env) .body ctx p (app ``HybridWord.State.copy [p.s,dn.native destination,on.native origin,cn.native count])
        (fun _ _ _ _ => FixedCopyCompleteness.program destination origin count) (.copy destination origin count)
        (FixedCopyCompleteness.quotedCode destination origin count dn on cn)
  | read (array index register : Nat) (an nn rn : NatNotation)
      (declared : (FixedMemory.lookup ds array).isSome = true)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Source ds (env := env) .body ctx p (FixedReadCompleteness.original array index register an nn rn binder info p)
        (fun _ _ _ _ => FixedReadCompleteness.program array index register)
        (.letValue (.readNat array index) (.assign register (.local 0)))
        (FixedReadCompleteness.quotedCode array index register an nn rn)
  | assign (tag : Return.Form) (register : Nat) (rn : NatNotation)
      (value : FixedScalarCompleteness.Scoped env ctx p v f vc vq) :
      Source ds (env := env) .body ctx p (tag.source (app ``HybridWord.State.set [p.s,rn.native register,v]))
        (fun i x y ls s => (f i x y s ls).bind (fun v => some (s.set register v)))
        (.assign register vc) (app ``HybridWord.Cmd.assign [rn.native register,vq])
  | store (array : Nat) (an : NatNotation)
      (declared : (FixedMemory.lookup ds array).isSome = true)
      (index : FixedScalarCompleteness.Scoped env ctx p j f jc jq)
      (value : FixedScalarCompleteness.Scoped env ctx p v g vc vq) :
      Source ds (env := env) .body ctx p (app ``HybridWord.State.write [p.s,an.native array,j,v])
        (fun i x y ls s => (f i x y s ls).bind (fun j => (g i x y s ls).bind (s.write array j)))
        (.store array jc vc) (app ``HybridWord.Cmd.store [an.native array,jq,vq])
  | branch (value : FixedScalarCompleteness.Scoped env ctx p v f vc vq)
      (yes : Source ds (env := env) .body ctx p a g ac aq) (no : Source ds (env := env) .body ctx p b h bc bq) :
      Source ds (env := env) .body ctx p (Branch.source v (Branch.nativeBooleanDecision v) a b)
        (fun i x y ls s => (f i x y s ls).bind (fun v => if v != 0 then g i x y ls s else h i x y ls s))
        (.branch vc ac bc) (app ``HybridWord.Cmd.branch [vq,aq,bq])
  | stepBranch (value : FixedScalarCompleteness.Scoped env ctx p v f vc vq)
      (yes : Source ds (env := env) .step ctx p a g ac aq) (no : Source ds (env := env) .step ctx p b h bc bq) :
      Source ds (env := env) .step ctx p (StructuralStep.Conditional.source v (Branch.nativeBooleanDecision v) a b)
        (fun i x y ls s => (f i x y s ls).bind (fun v => if v != 0 then g i x y ls s else h i x y ls s))
        (.branch vc ac bc) (app ``HybridWord.Cmd.branch [vq,aq,bq])
  | branchDecision (value : FixedScalarCompleteness.Scoped env ctx p v f vc vq)
      (decision : ScalarSyntax.Decision env ctx v d)
      (yes : Source ds (env := env) .body ctx p a g ac aq) (no : Source ds (env := env) .body ctx p b h bc bq) :
      Source ds (env := env) .body ctx p (Branch.source v d a b)
        (fun i x y ls s => (f i x y s ls).bind (fun v => if v != 0 then g i x y ls s else h i x y ls s))
        (.branch vc ac bc) (app ``HybridWord.Cmd.branch [vq,aq,bq])
  | stepBranchDecision (value : FixedScalarCompleteness.Scoped env ctx p v f vc vq)
      (decision : ScalarSyntax.Decision env ctx v d)
      (yes : Source ds (env := env) .step ctx p a g ac aq) (no : Source ds (env := env) .step ctx p b h bc bq) :
      Source ds (env := env) .step ctx p (StructuralStep.Conditional.source v d a b)
        (fun i x y ls s => (f i x y s ls).bind (fun v => if v != 0 then g i x y ls s else h i x y ls s))
        (.branch vc ac bc) (app ``HybridWord.Cmd.branch [vq,aq,bq])
  | letValue (annotation : WordBinder.Annotation)
      (value : FixedScalarCompleteness.Scoped env ctx p v f vc vq)
      (next : Source ds (env := env) .body (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} b g bc bq)
      (binder : Lean.Name) (flag : Bool) :
      Source ds (env := env) .body ctx p (WordBinder.letSource annotation binder v b flag)
        (fun i x y ls s => (f i x y s ls).bind (fun v => g i x y (v::ls) s))
        (.letValue vc bc) (app ``HybridWord.Cmd.letValue [vq,bq])

  | bindValue (annotation : WordBinder.Annotation)
      (value : FixedReadSourceCompleteness.Source ds (env := env) (ctx := ctx) p v f vc vq)
      (next : Source ds (env := env) .body (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} b g bc bq)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Source ds (env := env) .body ctx p (WordBinder.readSource annotation v (.lam binder annotation.native b info))
        (fun i x y ls s => (f i x y s ls).bind (fun v => g i x y (v::ls) s))
        (.letValue vc bc) (app ``HybridWord.Cmd.letValue [vq,bq])
  | stateAlias (next : Source ds (env := env) .body (stateType::ctx) {p.lift with s := .bvar 0} b g bc bq)
      (binder : Lean.Name) (flag : Bool) :
      Source ds (env := env) .body ctx p (.letE binder state p.s b flag) g bc bq
  | sequence (first : Source ds (env := env) .body ctx p a f ac aq)
      (next : Source ds (env := env) .body (stateType::ctx) {p.lift with s := .bvar 0} b g bc bq)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Source ds (env := env) .body ctx p (sequenceSource a (.lam binder state b info))
        (fun i x y ls s => (f i x y ls s).bind (g i x y ls)) (.seq ac bc) (app ``HybridWord.Cmd.seq [aq,bq])

  | stateLet (value : Source ds (env := env) .value ctx p v f vc vq)
      (next : Source ds (env := env) .body (stateType::ctx) {p.lift with s := .bvar 0} b g bc bq)
      (notAlias : sameTerm v p.s = false) (binder : Lean.Name) (flag : Bool) :
      Source ds (env := env) .body ctx p (StateLet.source binder v b flag)
        (fun i x y ls s => (f i x y ls s).bind (g i x y ls))
        (.seq vc bc) (app ``HybridWord.Cmd.seq [vq,bq])
  | stepStateLet (value : Source ds (env := env) .value ctx p v f vc vq)
      (next : Source ds (env := env) .step (stateType::ctx) {p.lift with s := .bvar 0} b g bc bq)
      (notAlias : sameTerm v p.s = false) (binder : Lean.Name) (flag : Bool) :
      Source ds (env := env) .step ctx p (StructuralStateLet.Loop.source binder v b flag)
        (fun i x y ls s => (f i x y ls s).bind (g i x y ls))
        (.seq vc bc) (app ``HybridWord.Cmd.seq [vq,bq])
  | stepAlias (next : Source ds (env := env) .step (stateType::ctx) {p.lift with s := .bvar 0} b g bc bq)
      (binder : Lean.Name) (flag : Bool) :
      Source ds (env := env) .step ctx p (.letE binder state p.s b flag) g bc bq
  | stepSequence (first : Source ds (env := env) .body ctx p a f ac aq)
      (next : Source ds (env := env) .step (stateType::ctx) {p.lift with s := .bvar 0} b g bc bq)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Source ds (env := env) .step ctx p (StructuralStep.sequenceSource a (.lam binder state b info))
        (fun i x y ls s => (f i x y ls s).bind (g i x y ls))
        (.seq ac bc) (app ``HybridWord.Cmd.seq [aq,bq])
  | forStatic (start : StaticBound a startValue) (stop : StaticBound b stopValue)
      (stride : StaticBound c strideValue)
      (body : Source ds (env := env) .step (stateType::wordType::ctx) (For.parameters p) original f bc bq)
      (kn tn : Lean.Name) (ki ti : Lean.BinderInfo) :
      Source ds (env := env) .body ctx p (For.source a b c p.s (.lam kn word (.lam tn state original ti) ki))
        (fun i x y ls s => ForIn.forIn (HybridWord.range startValue stopValue strideValue) s
          (fun k t => WordLoopFacts.lift (f i x y (k::ls) t)))
        (.forStatic startValue stopValue strideValue bc)
        (app ``HybridWord.Cmd.forStatic [a,b,c,bq])

  | stepLetValue (annotation : WordBinder.Annotation)
      (value : FixedScalarCompleteness.Scoped env ctx p v f vc vq)
      (next : Source ds (env := env) .step (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} b g bc bq)
      (binder : Lean.Name) (flag : Bool) :
      Source ds (env := env) .step ctx p (WordBinder.letSource annotation binder v b flag)
        (fun i x y ls s => (f i x y s ls).bind (fun v => g i x y (v::ls) s))
        (.letValue vc bc) (app ``HybridWord.Cmd.letValue [vq,bq])
  | stepBindValue (annotation : WordBinder.Annotation)
      (value : FixedReadSourceCompleteness.Source ds (env := env) (ctx := ctx) p v f vc vq)
      (next : Source ds (env := env) .step (annotation.core::ctx) {p.lift with locals := .bvar 0::p.lift.locals} b g bc bq)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Source ds (env := env) .step ctx p (WordBinder.stepReadSource annotation v (.lam binder annotation.native b info))
        (fun i x y ls s => (f i x y s ls).bind (fun v => g i x y (v::ls) s))
        (.letValue vc bc) (app ``HybridWord.Cmd.letValue [vq,bq])

  | unitBody (next : Source ds (env := env) .body (UnitStep.unitType::ctx) p.lift b g bc bq) (binder : Lean.Name) (info : Lean.BinderInfo) :
      Source ds (env := env) .body ctx p (StructuralUnit.source false binder b info) g bc bq
  | unitLoop (next : Source ds (env := env) .step (UnitStep.unitType::ctx) p.lift b g bc bq) (binder : Lean.Name) (info : Lean.BinderInfo) :
      Source ds (env := env) .step ctx p (StructuralUnit.source true binder b info) g bc bq

  | forRange (kind : NaturalLoop.Kind)
      (count : FixedScalarCompleteness.Scoped env ctx p n f nc nq)
      (body : Source ds (env := env) kind.mode (kind.context ctx) (kind.parameters p) original g bc bq)
      (kn tn : Lean.Name) (ki ti : Lean.BinderInfo) :
      Source ds (env := env) .body ctx p (kind.source n p.s (kind.nativeLambda kn tn ki ti original))
        (fun i x y ls s => (f i x y s ls).bind (fun n =>
          naturalRange kind n (fun k t => g i x y (BitVec.ofNat 32 k::ls) t) s))
        (.forRange nc bc) (app ``HybridWord.Cmd.forRange [nq,bq])

/-- Representation preserves source scope in both directions, including
ordinary lets represented as beta applications. -/
theorem represented_scoped (represented : Represents raw core)
    (closed : core.ClosedN bound) : LeanScalar.wellScoped bound raw = true := by
  induction represented generalizing bound <;>
    simp_all [LeanScalar.wellScoped,VExpr.ClosedN]
  all_goals grind

private theorem applications_scope (fn : VExpr) (args : List VExpr)
    (closed : (applications fn args).ClosedN bound) :
    fn.ClosedN bound ∧ ∀ arg ∈ args, arg.ClosedN bound := by
  induction args generalizing fn with
  | nil => exact ⟨closed,by simp⟩
  | cons arg rest ih =>
    obtain ⟨pair,tail⟩ := ih (.app fn arg) closed
    exact ⟨pair.1,by intro a ha; rcases List.mem_cons.mp ha with rfl | ha; exact pair.2; exact tail a ha⟩

private theorem reduced_applications_scope (fn : VExpr) (args : List VExpr)
    (head : fn.ClosedN bound) (arguments : ∀ arg ∈ args, arg.ClosedN bound) :
    (args.foldl LeanTypeReduction.applyReduced fn).ClosedN bound := by
  induction args generalizing fn with
  | nil => exact head
  | cons arg rest ih =>
    apply ih
    · cases fn <;> first
      | exact ⟨head,arguments arg (by simp)⟩
      | exact head.2.inst (arguments arg (by simp))
    · intro a ha; exact arguments a (by simp [ha])

/-- A helper application/let cannot introduce an out-of-scope reference.
The same source-representation equation used by typing discharges this
condition; no separate per-call scope certificate is needed. -/
theorem reduced_scoped
    (represented : Represents raw (applications (.app (.lam domain original) first) rest))
    (reduced : Represents next (rest.foldl LeanTypeReduction.applyReduced (original.inst first)))
    (scope_ok : LeanScalar.wellScoped bound raw = true) :
    LeanScalar.wellScoped bound next = true := by
  obtain ⟨head,args⟩ := applications_scope _ _ (represented.closed bound scope_ok)
  exact represented_scoped reduced (reduced_applications_scope _ _ (head.1.2.inst head.2) args)

/-- Free historical scalar parameters are irrelevant whenever source scope
excludes them. Locals remain contextual, so the same induction covers nested
loops and bindings without specializing generated code. -/
theorem Source.independent (source : Source ds (env := env) mode ctx p raw native code quotation)
    (external : LexicalScalarCode.ExternalAt bound p)
    (scope_ok : LeanScalar.wellScoped bound raw = true) :
    ∀ i x y ls s, native i x y ls s = native 0 0 0 ls s := by
  induction source generalizing bound with
  | returns | valueCurrent | copy | read => intros; rfl
  | valueAssign register rn value | assign tag register rn value =>
    have hs := value.independent external (by
      first
      | exact (Bool.and_eq_true_iff.mp scope_ok).2
      | cases tag <;> exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp scope_ok).2).2)
    intros; simp only [hs]
  | yield value ih => exact ih external (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp scope_ok).2).2
  | store array an declared index value =>
    have hj := index.independent external (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp scope_ok).1).2
    have hv := value.independent external (Bool.and_eq_true_iff.mp scope_ok).2
    intros; simp only [hj,hv]
  | branch value yes no ia ib | branchDecision value decision yes no ia ib
  | stepBranch value yes no ia ib | stepBranchDecision value decision yes no ia ib =>
    have bs := (Bool.and_eq_true_iff.mp scope_ok)
    have as_ := (Bool.and_eq_true_iff.mp bs.1)
    have cs := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp as_.1).1).2
    have vs_ := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp cs).1).2).1
    have hv := value.independent external (Bool.and_eq_true_iff.mp vs_).2
    have ha := ia external as_.2
    have hb := ib external bs.2
    intros; simp only [hv,ha,hb]
  | letValue annotation value next binder flag ih
  | stepLetValue annotation value next binder flag ih =>
    have parts := Bool.and_eq_true_iff.mp scope_ok
    have hv := value.independent external (Bool.and_eq_true_iff.mp parts.1).2
    have hn := ih (show LexicalScalarCode.ExternalAt (bound+1) _ from external.lift) parts.2
    intros; simp only [hv,hn]
  | bindValue annotation value next binder info ih
  | stepBindValue annotation value next binder info ih =>
    have parts := Bool.and_eq_true_iff.mp scope_ok
    have hv := value.independent external (Bool.and_eq_true_iff.mp parts.1).2
    have hn := ih (show LexicalScalarCode.ExternalAt (bound+1) _ from external.lift)
      (Bool.and_eq_true_iff.mp parts.2).2
    intros; simp only [hv,hn]
  | stateAlias next binder flag ih | stepAlias next binder flag ih =>
    exact ih (show LexicalScalarCode.ExternalAt (bound+1) _ from external.lift) (Bool.and_eq_true_iff.mp scope_ok).2
  | stateLet value next notAlias binder flag iv ih
  | stepStateLet value next notAlias binder flag iv ih =>
    have parts := Bool.and_eq_true_iff.mp scope_ok
    have hv := iv external (Bool.and_eq_true_iff.mp parts.1).2
    have hn := ih (show LexicalScalarCode.ExternalAt (bound+1) _ from external.lift) parts.2
    intro i x y ls s
    simp only [hv]
    congr 1
    exact funext (hn i x y ls)
  | sequence first next binder info iv ih | stepSequence first next binder info iv ih =>
    have parts := Bool.and_eq_true_iff.mp scope_ok
    have hv := iv external (Bool.and_eq_true_iff.mp parts.1).2
    have hn := ih (show LexicalScalarCode.ExternalAt (bound+1) _ from external.lift)
      (Bool.and_eq_true_iff.mp parts.2).2
    intro i x y ls s
    simp only [hv]
    congr 1
    exact funext (hn i x y ls)
  | unitBody next binder info ih | unitLoop next binder info ih =>
    exact ih external.lift (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp scope_ok).2).2
  | forStatic start stop stride body kn tn ki ti ih =>
    have hn := ih (show LexicalScalarCode.ExternalAt (bound+1+1) _ from external.lift.lift)
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp scope_ok).2).2).2
    intros; simp only [hn]
  | forRange kind count body kn tn ki ti ih =>
    have hn := ih (bound := bound+1+1) (by cases kind <;> exact external.lift.lift) (by
      cases kind
      · exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp scope_ok).2).2).2
      · exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp scope_ok).1).1).2).2).2)
    have hv := count.independent external (by
      cases kind
      · exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp scope_ok).1).1).2).2).2
      · exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp scope_ok).2).2).2)
    intros; simp only [hv,hn]

/-- Declaration consistency and the native computation are established in
one source induction. Neither component assumes successful parsing. -/
theorem Source.facts (source : Source ds (env := env) mode ctx p raw native code quotation) :
    FixedMemory.declared ds code = true ∧
      ∀ i x y s ls, code.eval i x y s ls = native i x y ls s := by
  induction source with
  | returns | valueCurrent => exact ⟨rfl,by intros; rfl⟩
  | valueAssign register rn value | assign tag register rn value =>
    exact ⟨value.declared,by intros; simp [HybridWord.Cmd.eval,value.computation]⟩
  | yield value ih => exact ih
  | copy destination origin count dn on cn hd hs =>
    exact ⟨by simp [FixedMemory.declared,hd,hs],by intros; rfl⟩
  | read array index register an nn rn ha binder info =>
    exact ⟨by simp [FixedMemory.declared,FixedMemory.exprDeclared,ha],
      by intros; simp [HybridWord.Cmd.eval,HybridWord.Expr.eval,FixedReadCompleteness.program]⟩
  | store array an declared index value =>
    exact ⟨by simp [FixedMemory.declared,declared,index.declared,value.declared],
      by intros; simp [HybridWord.Cmd.eval,index.computation,value.computation]⟩
  | branch value yes no ia ib | stepBranch value yes no ia ib
  | branchDecision value decision yes no ia ib | stepBranchDecision value decision yes no ia ib =>
    exact ⟨by simp [FixedMemory.declared,value.declared,ia.1,ib.1],
      by intros; simp only [HybridWord.Cmd.eval,value.computation,ia.2,ib.2,bind,Option.bind]⟩
  | letValue annotation value next binder flag ih
  | stepLetValue annotation value next binder flag ih
  | bindValue annotation value next binder info ih
  | stepBindValue annotation value next binder info ih =>
    exact ⟨by simp [FixedMemory.declared,value.declared,ih.1],
      by intros; simp only [HybridWord.Cmd.eval,value.computation,ih.2,bind,Option.bind]⟩
  | stateAlias next binder flag ih | stepAlias next binder flag ih
  | unitBody next binder info ih | unitLoop next binder info ih => exact ih
  | sequence first next binder info ia ib | stepSequence first next binder info ia ib
  | stateLet value next notAlias binder flag ia ib | stepStateLet value next notAlias binder flag ia ib =>
    exact ⟨by simp [FixedMemory.declared,ia.1,ib.1],
      by intros; simp only [HybridWord.Cmd.eval,ia.2,ib.2,bind,Option.bind]⟩
  | forStatic start stop stride body kn tn ki ti ih =>
    refine ⟨ih.1,?_⟩
    intro i x y s ls
    exact WordLoopFacts.forStatic _ _ _ _ i x y s ls _ (fun k t => congrArg WordLoopFacts.lift (ih.2 i x y t (k::ls)))
  | forRange kind count body kn tn ki ti ih =>
    refine ⟨by simp [FixedMemory.declared,count.declared,ih.1],?_⟩
    intro i x y s ls
    cases kind with
    | fold => simp only [HybridWord.Cmd.eval,count.computation,naturalRange,ih.2,bind,Option.bind]
    | forIn =>
      simp only [HybridWord.Cmd.eval,count.computation,naturalRange]
      congr 1
      funext n
      rw [WordLoopFacts.forIn_lift _ _ _ _ (fun _ _ => rfl)]
      simp only [ih.2]

theorem Source.declared (source : Source ds (env := env) mode ctx p raw native code quotation) :
    FixedMemory.declared ds code = true := source.facts.1

theorem Source.computation (source : Source ds (env := env) mode ctx p raw native code quotation) :
    ∀ i x y s ls, code.eval i x y s ls = native i x y ls s := source.facts.2

/-- The same source induction constructs certificates for ordinary bodies,
pure State expressions, and ForInStep-valued loop bodies. -/
def Outcome (setup : AliasSetup env) (exposure : Exposure env) (inputs : InputsTyped env ctx p)
    (mode : StructuralBody.Mode) (raw quotation : Lean.Expr) : Prop :=
  match mode with
  | .body => ∃ piece, StructuralBody.bodyRetained env setup.conversion exposure ctx p raw = some piece ∧
      ∃ typed : BodyCasts inputs piece (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType stateType) ∧ piece.code = quotation
  | .value => ∃ piece, StructuralBody.visit env setup.conversion exposure raw ctx p .value .identity (fun _ => none) = some piece ∧
      Nonempty (StructuralLoop.ValueCasts inputs piece (SourceCasts env) (For.Casts setup)) ∧ piece.code = quotation
  | .step => ∃ piece, StructuralBody.visit env setup.conversion exposure raw ctx p .step .identity (fun _ => none) = some piece ∧
      ∃ typed : StructuralLoop.StepCasts inputs piece (SourceCasts env) (For.Casts setup),
        ValueForm setup ctx typed.sourceCore.val (optionType Step.stepState) ∧ piece.code = quotation

/-- Source typing moves from the finite standard signature table to the
ordinary loaded environment. Commands and computations are unchanged. -/
theorem Source.install (source : Source ds (env := before) mode ctx p raw native code quotation)
    (installed : SignatureExtension before after) : Source ds (env := after) mode ctx p raw native code quotation := by
  induction source with
  | returns tag => exact .returns tag
  | valueCurrent => exact .valueCurrent
  | valueAssign register rn value => exact .valueAssign register rn (value.install installed)
  | yield value ih => exact .yield ih
  | copy dst src count dn sn cn hd hs => exact .copy dst src count dn sn cn hd hs
  | read array index register an nn rn declared binder info => exact .read array index register an nn rn declared binder info
  | assign tag register rn value => exact .assign tag register rn (value.install installed)
  | store array an declared index value => exact .store array an declared (index.install installed) (value.install installed)
  | branch value yes no ia ib => exact .branch (value.install installed) ia ib
  | stepBranch value yes no ia ib => exact .stepBranch (value.install installed) ia ib
  | branchDecision value decision yes no ia ib => exact .branchDecision (value.install installed) (decision.install installed) ia ib
  | stepBranchDecision value decision yes no ia ib => exact .stepBranchDecision (value.install installed) (decision.install installed) ia ib
  | letValue annotation value next binder flag ih => exact .letValue annotation (value.install installed) ih binder flag
  | stepLetValue annotation value next binder flag ih => exact .stepLetValue annotation (value.install installed) ih binder flag
  | bindValue annotation value next binder info ih => exact .bindValue annotation (value.install installed) ih binder info
  | stepBindValue annotation value next binder info ih => exact .stepBindValue annotation (value.install installed) ih binder info
  | stateAlias next binder flag ih => exact .stateAlias ih binder flag
  | stepAlias next binder flag ih => exact .stepAlias ih binder flag
  | sequence a b binder info ia ib => exact .sequence ia ib binder info
  | stepSequence a b binder info ia ib => exact .stepSequence ia ib binder info
  | stateLet a b na binder flag ia ib => exact .stateLet ia ib na binder flag
  | stepStateLet a b na binder flag ia ib => exact .stepStateLet ia ib na binder flag
  | unitBody next binder info ih => exact .unitBody ih binder info
  | unitLoop next binder info ih => exact .unitLoop ih binder info
  | forStatic start stop stride body kn tn ki ti ih => exact .forStatic start stop stride ih kn tn ki ti
  | forRange kind count body kn tn ki ti ih => exact .forRange kind (count.install installed) ih kn tn ki ti

/-- One induction carries successful parsing, exact emitted code, and the
source/certificate typing needed by an enclosing ordinary Lean continuation. -/
theorem Source.complete (source : Source ds (env := env) mode ctx p raw native command quotation)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env) :
    ∀ (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p),
      Outcome setup exposure inputs mode raw quotation := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have embed : ∀ scope a b, SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  induction source with
  | valueCurrent =>
    intro inputs locals
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralLoop.value_skip_complete_code inputs
      (library.returnFact .some) library.skipConstructor setup.conversion exposure (SourceCasts env)
      (setup.covers_source library.scalars.toSignatures closed)
    exact ⟨piece,parsed,⟨⟨typed.sourceCore,typed.value,typed.target,typed.proof.mono embed⟩⟩,code⟩
  | valueAssign register rn value =>
    intro inputs locals
    obtain ⟨v,hv,⟨tv⟩,vq⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨piece,parsed,typed,code⟩ := StructuralLoop.value_assign_split_complete_code inputs
      (rn.argument library.scalars.toSignatures register) tv (library.assignFact .some)
      library.assignConstructor library.setter embed coverage exposure hv
    exact ⟨piece,parsed,typed,by rw [code,vq]⟩
  | yield value ih =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩,aCode⟩ := ih inputs locals
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralLoop.yield_complete_code inputs library.steps
      library.eval library.compose embed ta coverage exposure ha
    exact ⟨piece,parsed,typed,ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp),code.trans aCode⟩
  | returns tag =>
    intro inputs locals
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := Return.body_skip_invariant_complete_code library.returns inputs tag
      (library.returnFact tag) library.skipConstructor setup.conversion exposure Arithmetic.Casts
      (setup.covers library.scalars.toSignatures)
    let lifted : BodyCasts inputs piece (SourceCasts env) (For.Casts setup) := (typed.mapSource (fun _ _ _ h => SourceCasts.arithmetic h)).mapProofs
      (fun _ _ _ h => embed _ _ _ (.arithmetic h))
    refine ⟨piece,(StructuralSyntax.return_leaf inputs tag).trans parsed,lifted,?_,code⟩
    cases tag <;> exact ScopedSyntax.head_form fresh lifted.sourceCore.property rfl (by simp)
  | @copy ctx p destination origin count dn on cn hd hs =>
    intro inputs locals
    let d := dn.argument (ctx := ctx) library.scalars.toSignatures destination
    let s := on.argument (ctx := ctx) library.scalars.toSignatures origin
    let n := cn.argument (ctx := ctx) library.scalars.toSignatures count
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := body_copy_invariant_complete_code inputs d s n library.copyFact
      library.copyConstructor library.copier setup.conversion exposure Arithmetic.Casts
      (setup.covers library.scalars.toSignatures)
    let lifted : BodyCasts inputs piece (SourceCasts env) (For.Casts setup) :=
      (typed.mapSource (fun _ _ _ h => SourceCasts.arithmetic h)).mapProofs
        (fun _ _ _ h => embed _ _ _ (.arithmetic h))
    exact ⟨piece,(StructuralSyntax.copy_leaf inputs).trans parsed,lifted,
      ScopedSyntax.head_form fresh lifted.sourceCore.property rfl (by simp),code⟩
  | read array index register an nn rn ha binder info =>
    intro inputs locals
    obtain ⟨piece,parsed,typed,code⟩ := FixedReadCompleteness.body_complete_at setup library closed fresh exposure
      inputs locals array index register an nn rn binder info
    exact ⟨piece,parsed,typed,ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp),code⟩
  | assign tag register rn value =>
    intro inputs locals
    obtain ⟨v,hv,⟨tv⟩,vq⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := Return.assign_step_split_complete_code library.returns inputs tag
      (rn.argument library.scalars.toSignatures register) tv (library.assignFact tag)
      library.assignConstructor library.setter embed coverage exposure _ _ _ _ hv
    refine ⟨piece,(StructuralSyntax.assign_node tag).trans parsed,typed,?_,?_⟩
    · cases tag <;> exact ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp)
    · rw [code,vq]
  | store array an declared index value =>
    intro inputs locals
    obtain ⟨j,hj,⟨tj⟩,jq⟩ := index.complete setup library closed fresh exposure inputs locals
    obtain ⟨v,hv,⟨tv⟩,vq⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := store_step_invariant_complete_code inputs
      (an.argument library.scalars.toSignatures array) tj tv library.storeFact library.storeConstructor
      library.writer embed coverage exposure _ _ _ _ hj hv
    refine ⟨piece,(StructuralSyntax.store_leaf inputs).trans parsed,typed,
      ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp),?_⟩
    rw [code,jq,vq]
  | branch value yes no ihYes ihNo =>
    intro inputs locals
    obtain ⟨v,hv,⟨tv⟩,vCode⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨a,ha,ta,fa,aCode⟩ := ihYes inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ihNo inputs locals
    obtain ⟨pt,dt⟩ := library.decisions.condition_typed library.scalars.toSignatures tv.value
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := Branch.branch_step_split_complete_code inputs tv ta tb
      (Branch.booleanDecision_represents tv.sourceCore.property) pt dt
      library.toLibrary.option_typed library.ite library.branchFact library.branchConstructor
      embed coverage exposure _ _ _ _ hv ha hb
    exact ⟨piece,(StructuralSyntax.branch_node).trans parsed,typed,
      ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp),by rw [code,vCode,aCode,bCode]⟩
  | stepBranch value yes no ihYes ihNo =>
    intro inputs locals
    obtain ⟨v,hv,⟨tv⟩,vCode⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨a,ha,ta,fa,aCode⟩ := ihYes inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ihNo inputs locals
    obtain ⟨pt,dt⟩ := library.decisions.condition_typed library.scalars.toSignatures tv.value
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralStep.Conditional.split_complete_code inputs tv ta tb
      (Branch.booleanDecision_represents tv.sourceCore.property) pt dt
      library.stepOption_typed library.ite library.stepBranch library.branchConstructor
      embed coverage exposure hv ha hb
    exact ⟨piece,parsed,typed,ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp),
      by rw [code,vCode,aCode,bCode]⟩
  | branchDecision value decision yes no ihYes ihNo =>
    intro inputs locals
    obtain ⟨v,hv,⟨tv⟩,vCode⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨a,ha,ta,fa,aCode⟩ := ihYes inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ihNo inputs locals
    obtain ⟨vc,dc,vr,dr,pt,dt⟩ := decision.typing
    rw [← tv.sourceCore.property.unique vr] at pt dt
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := Branch.branch_step_split_complete_code inputs tv ta tb
      dr (pt.mono (fun _ _ _ h => SourceCasts.arithmetic h))
      (dt.mono (fun _ _ _ h => SourceCasts.arithmetic h))
      library.toLibrary.option_typed library.ite library.branchFact library.branchConstructor
      embed coverage exposure _ _ _ _ hv ha hb
    exact ⟨piece,(StructuralSyntax.branch_node).trans parsed,typed,
      ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp),by rw [code,vCode,aCode,bCode]⟩
  | stepBranchDecision value decision yes no ihYes ihNo =>
    intro inputs locals
    obtain ⟨v,hv,⟨tv⟩,vCode⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨a,ha,ta,fa,aCode⟩ := ihYes inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ihNo inputs locals
    obtain ⟨vc,dc,vr,dr,pt,dt⟩ := decision.typing
    rw [← tv.sourceCore.property.unique vr] at pt dt
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralStep.Conditional.split_complete_code inputs tv ta tb
      dr (pt.mono (fun _ _ _ h => SourceCasts.arithmetic h))
      (dt.mono (fun _ _ _ h => SourceCasts.arithmetic h))
      library.stepOption_typed library.ite library.stepBranch library.branchConstructor
      embed coverage exposure hv ha hb
    exact ⟨piece,parsed,typed,ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp),
      by rw [code,vCode,aCode,bCode]⟩
  | letValue annotation value next binder flag ih =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩,aCode⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ih
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (annotation.nextLocals locals closed)
    obtain ⟨piece,parsed,typed,form,code⟩ := WordBinder.let_complete_code annotation setup
      library.scalars.toSignatures inputs closed library.cons library.returns.state library.returns.option
      library.eq library.eval library.letValue library.letValueConstructor fresh.option coverage exposure
      ta tb fb ha hb binder flag
    exact ⟨piece,parsed,typed,form,by rw [code,aCode,bCode]⟩
  | bindValue annotation value next binder info ih =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩,aCode⟩ := value.complete setup library closed fresh exposure inputs locals
    cases annotation with
    | word =>
      obtain ⟨b,hb,tb,fb,bCode⟩ := ih
        (inputs.nextWord closed library.scalars.word library.cons) (locals.nextWord closed)
      obtain ⟨target,_,_⟩ := bindValue_next_typed inputs closed SourceCasts.closed
        library.scalars.word library.cons tb
      obtain ⟨piece,parsed,⟨typed⟩,code⟩ := bindValue_step_complete_code inputs closed SourceCasts.closed
        embed library.scalars.word library.cons ta tb
        (.base (.base (.valueContinuation inputs target tb.value fb))) library.bindValueFact library.letValueConstructor
        coverage exposure library.bind library.returns.state binder info
        (ScalarEnvironment.parse env setup.conversion exposure)
        (fun ctx p => readStep env setup.conversion exposure ctx p (ScalarEnvironment.parse env setup.conversion exposure ctx p))
        (fun _ _ => none) (StructuralBody.bodyRetained env setup.conversion exposure) ha hb
      exact ⟨piece,(StructuralSyntax.bindValue_node).trans parsed,typed,
        ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp),by rw [code,aCode,bCode]⟩
    | bitvec =>
      obtain ⟨b,hb,tb,fb,bCode⟩ := ih
        (WordBinder.Annotation.bitvec.nextInputs inputs closed library.scalars.toSignatures library.cons)
        (WordBinder.Annotation.bitvec.nextLocals locals closed)
      obtain ⟨piece,parsed,typed,form,code⟩ := WordBinder.bind_bits_complete_code setup library.scalars.toSignatures
        library.bind inputs closed library.cons library.returns.state library.eq library.eval
        library.bindValueFact library.letValueConstructor fresh.state (fresh.value _ (by simp))
        coverage exposure ta (value.valueForm fresh ta.sourceCore.property) tb fb ha hb binder info
      exact ⟨piece,parsed,typed,form,by rw [code,aCode,bCode]⟩
  | stateAlias next binder flag ih =>
    intro inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ih (inputs.nextState closed) (locals.nextState closed)
    obtain ⟨target,_,_⟩ := sequence_next_typed inputs closed SourceCasts.closed library.returns.state tb
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StateAlias.alias_step_complete inputs closed SourceCasts.closed
      embed library.returns.state tb (.base (.base (.stateContinuation inputs target tb.value fb)))
      library.stateAlias coverage exposure binder flag
      (ScalarEnvironment.parse env setup.conversion exposure) (fun _ _ _ => none)
      (fun _ _ => none) (StructuralBody.bodyRetained env setup.conversion exposure) hb
    have same := typed.sourceCore.property.unique
      (Represents.letE (Represents.constant rfl) inputs.s.property tb.sourceCore.property)
    refine ⟨piece,(StructuralSyntax.alias_node inputs).trans parsed,typed,?_,?_⟩
    · rw [same]
      exact .beta tb.value
    · exact code.trans bCode
  | sequence first next binder info ihFirst ihNext =>
    intro inputs locals
    obtain ⟨a,ha,ta,fa,aCode⟩ := ihFirst inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ihNext (inputs.nextState closed) (locals.nextState closed)
    obtain ⟨target,_,_⟩ := sequence_next_typed inputs closed SourceCasts.closed library.returns.state tb
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := sequence_step_complete_code inputs closed SourceCasts.closed
      embed library.returns.state ta tb (.base (.base (.stateContinuation inputs target tb.value fb)))
      library.sequence library.sequenceConstructor coverage exposure library.bind binder info
      (ScalarEnvironment.parse env setup.conversion exposure) (fun _ _ _ => none)
      (fun _ _ => none) (StructuralBody.bodyRetained env setup.conversion exposure) ha hb
    refine ⟨piece,(StructuralSyntax.sequence_node).trans parsed,typed,
      ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp),?_⟩
    rw [code,aCode,bCode]
  | stateLet value next notAlias binder flag ihValue ihNext =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩,aCode⟩ := ihValue inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ihNext (inputs.nextState closed) (locals.nextState closed)
    obtain ⟨target,_,_⟩ := sequence_next_typed inputs closed Arithmetic.SourceCasts.closed library.returns.state tb
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralStateLet.complete_code inputs closed Arithmetic.SourceCasts.closed
      embed library.returns.state ta library.returns tb
      (.base (.base (.stateContinuation inputs target tb.value fb))) library.stateLet library.sequenceConstructor
      coverage exposure binder flag notAlias ha hb
    have same := typed.sourceCore.property.unique
      (Represents.letE (Represents.constant rfl) ta.sourceCore.property tb.sourceCore.property)
    refine ⟨piece,parsed,typed,?_,?_⟩
    · rw [same]; exact .beta tb.value
    · rw [code,aCode,bCode]
  | @stepStateLet ctx p v f vc vq b g bc bq value next notAlias binder flag ihValue ihNext =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩,aCode⟩ := ihValue inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ihNext (inputs.nextState closed) (locals.nextState closed)
    have eval := eval_cast_typed (inputs.nextState closed) library.eval tb.target
    have beta := For.Casts.directContinuation (setup := setup) .state eval tb.value fb
    have codeClosed := b.represented.property.closed 0 b.closed
    have cast : For.Casts setup ctx
        (StructuralStep.sequenceNextActual inputs b.represented.val tb.sourceCore.val)
        (StructuralStep.sequenceContinuationType inputs b.represented.val (.lam stateType tb.sourceCore.val)) := by
      simpa only [StructuralStep.sequenceNextActual,StructuralStep.sequenceContinuationType,
        InputsTyped.nextState,InputsTyped.lift,Step.Binder.core,Arithmetic.continuationValue,
        VExpr.lift,VExpr.liftN,stateType,codeClosed.liftN_eq (Nat.zero_le _)] using beta
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralStateLet.Loop.complete_code inputs closed Arithmetic.SourceCasts.closed
      embed library.returns.state ta library.returns tb cast library.stepStateLet library.sequenceConstructor
      coverage exposure binder flag notAlias ha hb
    have same := typed.sourceCore.property.unique
      (Represents.letE (Represents.constant rfl) ta.sourceCore.property tb.sourceCore.property)
    refine ⟨piece,parsed,typed,?_,?_⟩
    · rw [same]; exact .beta tb.value
    · rw [code,aCode,bCode]
  | @stepAlias ctx b g bc bq p next binder flag ihNext =>
    intro inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ihNext (inputs.nextState closed) (locals.nextState closed)
    have eval := eval_cast_typed (inputs.nextState closed) library.eval tb.target
    have beta := For.Casts.directContinuation (setup := setup) .state eval tb.value fb
    have codeClosed := b.represented.property.closed 0 b.closed
    have cast : For.Casts setup ctx
        (StructuralStep.sequenceNextActual inputs b.represented.val tb.sourceCore.val)
        (StructuralStep.sequenceContinuationType inputs b.represented.val (.lam stateType tb.sourceCore.val)) := by
      simpa only [StructuralStep.sequenceNextActual,StructuralStep.sequenceContinuationType,
        InputsTyped.nextState,InputsTyped.lift,Step.Binder.core,Arithmetic.continuationValue,
        VExpr.lift,VExpr.liftN,stateType,codeClosed.liftN_eq (Nat.zero_le _)] using beta
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralStep.Alias.alias_step_complete inputs closed Arithmetic.SourceCasts.closed
      embed library.returns.state tb cast library.stepAlias coverage exposure binder flag hb
    have same := typed.sourceCore.property.unique
      (Represents.letE (Represents.constant rfl) inputs.s.property tb.sourceCore.property)
    refine ⟨piece,parsed,typed,?_,?_⟩
    · rw [same]; exact .beta tb.value
    · exact code.trans bCode
  | @stepSequence ctx p a f ac aq b g bc bq first next binder info ihFirst ihNext =>
    intro inputs locals
    obtain ⟨a,ha,ta,fa,aCode⟩ := ihFirst inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ihNext (inputs.nextState closed) (locals.nextState closed)
    have eval := eval_cast_typed (inputs.nextState closed) library.eval tb.target
    have beta := For.Casts.directContinuation (setup := setup) .state eval tb.value fb
    have codeClosed := b.represented.property.closed 0 b.closed
    have cast : For.Casts setup ctx
        (StructuralStep.sequenceNextActual inputs b.represented.val tb.sourceCore.val)
        (StructuralStep.sequenceContinuationType inputs b.represented.val (.lam stateType tb.sourceCore.val)) := by
      simpa only [StructuralStep.sequenceNextActual,StructuralStep.sequenceContinuationType,
        InputsTyped.nextState,InputsTyped.lift,Step.Binder.core,Arithmetic.continuationValue,
        VExpr.lift,VExpr.liftN,stateType,codeClosed.liftN_eq (Nat.zero_le _)] using beta
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralStep.sequence_complete_code inputs closed Arithmetic.SourceCasts.closed
      embed library.returns.state ta tb cast library.stepSequence library.sequenceConstructor coverage exposure
      library.bind library.steps binder info ha hb
    exact ⟨piece,parsed,typed,ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp),by rw [code,aCode,bCode]⟩
  | @forStatic a startValue b stopValue c strideValue ctx p original f bc bq start stop stride body kn tn ki ti ih =>
    intro inputs locals
    obtain ⟨startBound⟩ := start.typed (ctx := ctx) library.bounds library.scalars.toSignatures
    obtain ⟨stopBound⟩ := stop.typed (ctx := ctx) library.bounds library.scalars.toSignatures
    obtain ⟨strideBound⟩ := stride.typed (ctx := ctx) library.bounds library.scalars.toSignatures
    obtain ⟨b,hb,tb,fb,bCode⟩ := ih (For.nextInputs inputs closed library.scalars.word library.cons)
      ((locals.nextWord closed).nextState closed)
    obtain ⟨target,_,_⟩ := StructuralLoop.next_typed inputs closed Arithmetic.SourceCasts.closed
      library.scalars.word library.returns.state library.cons tb
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralLoop.body_forStatic_complete_code inputs closed Arithmetic.SourceCasts.closed
      embed startBound stopBound strideBound library.scalars.word library.returns.state library.cons tb
      (.continuation inputs target (b.represented.property.closed 0 b.closed) tb.value fb)
      library.forFact library.forConstructor library.range library.forHeader.header_typed
      coverage exposure kn tn ki ti hb
    exact ⟨piece,parsed,typed,ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp),by rw [code,bCode]⟩
  | stepLetValue annotation value next binder flag ih =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩,aCode⟩ := value.complete setup library closed fresh exposure inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ih
      (annotation.nextInputs inputs closed library.scalars.toSignatures library.cons)
      (annotation.nextLocals locals closed)
    obtain ⟨piece,parsed,typed,form,code⟩ := WordBinder.step_let_complete_code annotation setup library.scalars.toSignatures inputs closed library.cons
      library.steps library.eq library.eval library.stepLetValue library.letValueConstructor
      fresh.option coverage exposure ta tb fb ha hb binder flag
    exact ⟨piece,parsed,typed,form,by rw [code,aCode,bCode]⟩
  | @stepBindValue ctx p v f vc vq b g bc bq annotation value next binder info ih =>
    intro inputs locals
    obtain ⟨a,ha,⟨ta⟩,aCode⟩ := value.complete setup library closed fresh exposure inputs locals
    cases annotation with
    | word =>
      obtain ⟨b,hb,tb,fb,bCode⟩ := ih (inputs.nextWord closed library.scalars.word library.cons) (locals.nextWord closed)
      have eval := eval_cast_typed (inputs.nextWord closed library.scalars.word library.cons) library.eval tb.target
      have beta := For.Casts.directContinuation (setup := setup) .word eval tb.value fb
      have codeClosed := b.represented.property.closed 0 b.closed
      have cast : For.Casts setup ctx
          (StructuralReadBind.bindValueNextActual inputs b.represented.val tb.sourceCore.val)
          (StructuralReadBind.bindValueContinuationType inputs b.represented.val (.lam wordType tb.sourceCore.val)) := by
        simpa only [StructuralReadBind.bindValueNextActual,StructuralReadBind.bindValueContinuationType,
          InputsTyped.nextWord,InputsTyped.lift,Step.Binder.core,Arithmetic.continuationValue,
          VExpr.lift,VExpr.liftN,wordType,codeClosed.liftN_eq (Nat.zero_le _)] using beta
      obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralReadBind.complete_code inputs closed Arithmetic.SourceCasts.closed
        embed library.scalars.word library.cons ta tb cast library.stepBindValue library.letValueConstructor
        coverage exposure library.bind library.steps binder info ha hb
      exact ⟨piece,parsed,typed,ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp),by rw [code,aCode,bCode]⟩
    | bitvec =>
      obtain ⟨b,hb,tb,fb,bCode⟩ := ih
        (WordBinder.Annotation.bitvec.nextInputs inputs closed library.scalars.toSignatures library.cons)
        (WordBinder.Annotation.bitvec.nextLocals locals closed)
      obtain ⟨piece,parsed,typed,form,code⟩ := WordBinder.step_bind_bits_complete_code setup library.scalars.toSignatures library.bind inputs closed
        library.cons library.steps library.eq library.eval library.stepBindValue library.letValueConstructor
        (fresh.readAux _ (by simp)) (fresh.value _ (by simp)) coverage exposure ta
        (value.valueForm fresh ta.sourceCore.property) tb fb ha hb binder info
      exact ⟨piece,parsed,typed,form,by rw [code,aCode,bCode]⟩
  | unitBody next binder info ih =>
    intro inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ih (inputs.lift closed UnitStep.unitType) (locals.lift closed UnitStep.unitType)
    have eval := eval_cast_typed (inputs.lift closed UnitStep.unitType) library.eval tb.target
    have beta := For.Casts.unitContinuation (setup := setup) library.units false eval tb.value fb fresh.unit
    have codeClosed := b.represented.property.closed 0 b.closed
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralUnit.complete_code false inputs closed Arithmetic.SourceCasts.closed
      embed library.units library.steps library.bind
      ⟨tb.sourceCore,tb.value,tb.target,tb.proof⟩
      (by simpa only [StructuralUnit.continuationType,StructuralUnit.lhs,For.unitRequired,
        InputsTyped.lift,Arithmetic.continuationValue,VExpr.lift,VExpr.liftN,UnitStep.unitType,
        codeClosed.liftN_eq (Nat.zero_le _)] using beta)
      (library.unitFact false) coverage exposure binder info hb
    exact ⟨piece,parsed,⟨typed.sourceCore,typed.value,typed.target,typed.proof⟩,
      ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp),code.trans bCode⟩
  | unitLoop next binder info ih =>
    intro inputs locals
    obtain ⟨b,hb,tb,fb,bCode⟩ := ih (inputs.lift closed UnitStep.unitType) (locals.lift closed UnitStep.unitType)
    have eval := eval_cast_typed (inputs.lift closed UnitStep.unitType) library.eval tb.target
    have beta := For.Casts.unitContinuation (setup := setup) library.units true eval tb.value fb fresh.unit
    have codeClosed := b.represented.property.closed 0 b.closed
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := StructuralUnit.complete_code true inputs closed Arithmetic.SourceCasts.closed
      embed library.units library.steps library.bind
      ⟨tb.sourceCore,tb.value,tb.target,tb.proof⟩
      (by simpa only [StructuralUnit.continuationType,StructuralUnit.lhs,For.unitRequired,
        InputsTyped.lift,Arithmetic.continuationValue,VExpr.lift,VExpr.liftN,UnitStep.unitType,
        codeClosed.liftN_eq (Nat.zero_le _)] using beta)
      (library.unitFact true) coverage exposure binder info hb
    exact ⟨piece,parsed,⟨typed.sourceCore,typed.value,typed.target,typed.proof⟩,
      ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp),code.trans bCode⟩
  | @forRange ctx p n f nc nq original g bc bq kind count body kn tn ki ti ih =>
    intro inputs locals
    obtain ⟨c,hc,⟨tc⟩,cCode⟩ := count.complete setup library closed fresh exposure inputs locals
    let nextInputs := kind.nextInputs inputs closed library.scalars.toSignatures library.naturalLoops library.cons
    let nextLocals := kind.nextLocals locals closed library.scalars.toSignatures library.naturalLoops
    have child : ∃ b, StructuralBody.visit env setup.conversion exposure original (kind.context ctx) (kind.parameters p)
        kind.mode .identity (fun _ => none) = some b ∧
        ∃ typed : NaturalLoop.ChildCasts kind nextInputs b (Arithmetic.SourceCasts env) (For.Casts setup),
          Arithmetic.ValueForm setup (kind.context ctx) typed.sourceCore.val (optionType kind.result) ∧ b.code = bq := by
      cases kind with
      | forIn => exact ih nextInputs nextLocals
      | fold => exact ih nextInputs nextLocals
    obtain ⟨b,hb,tb,fb,bCode⟩ := child
    have beta := NaturalLoop.continuation_cast setup inputs kind closed library.scalars.toSignatures
      library.naturalLoops library.steps library.cons library.eval fresh.nat fresh.state tb fb
    obtain ⟨piece,parsed,⟨typed⟩,code⟩ := NaturalLoop.body_forRange_complete_code inputs kind closed embed
      library.scalars.toSignatures library.naturalLoops library.forHeader library.reads library.steps.state
      library.cons tc tb beta coverage exposure kn tn ki ti hc hb
    refine ⟨piece,parsed,typed,?_,?_⟩
    · cases kind <;> exact ScopedSyntax.head_form fresh typed.sourceCore.property rfl (by simp)
    · rw [code,cCode,bCode]
/-- Static source requirements carried through the existing scoped grammar.
They mention source syntax, array declarations and static integer values only.
The default grammar has no added requirements; this specialization records
exactly the information needed to construct a fixed-memory command. -/
structure InputConditions (ds : FixedMemory.Declarations) (raw : Lean.Expr) : Prop where
  registers : LexicalScalarSyntax.StaticRegisters raw
  assignment : ∀ tag st r v, raw = Return.Form.source tag (app ``HybridWord.State.set [st,r,v]) →
    Nonempty (NatNotation.View r)
  valueAssignment : ∀ st r v, raw = app ``HybridWord.State.set [st,r,v] → Nonempty (NatNotation.View r)
  store : ∀ st a k v, raw = app ``HybridWord.State.write [st,a,k,v] →
    ∃ id an, a = NatNotation.native an id ∧ (FixedMemory.lookup ds id).isSome = true
  copy : ∀ st d o n, raw = app ``HybridWord.State.copy [st,d,o,n] →
    ∃ dst src count dn sn cn, d = NatNotation.native dn dst ∧ o = NatNotation.native sn src ∧
      n = NatNotation.native cn count ∧ FixedMemory.lookup ds dst = some count ∧ FixedMemory.lookup ds src = some count
  readBody : ∀ annotation v fn, raw = WordBinder.readSource annotation v fn → FixedReadSourceCompleteness.Conditions ds v
  readStep : ∀ annotation v fn, raw = WordBinder.stepReadSource annotation v fn → FixedReadSourceCompleteness.Conditions ds v
  staticRange : ∀ a b c st fn, raw = For.source a b c st fn →
    ∃ start stop stride, StaticBound a start ∧ StaticBound b stop ∧ StaticBound c stride

/-- Read-binding requirements are assembled once from the read's source
conditions. The arbitrary continuation supplies its own syntax derivation. -/
theorem InputConditions.readBind (annotation : WordBinder.Annotation)
    (read : FixedReadSourceCompleteness.Conditions ds v)
    (registers : LexicalScalarSyntax.StaticRegisters (WordBinder.readSource annotation v fn)) :
    InputConditions ds (WordBinder.readSource annotation v fn) := by
  constructor
  · exact registers
  · intro tag st r value h; cases annotation <;> cases tag <;> cases h
  · intro st r value h; cases annotation <;> cases h
  · intro st a k value h; cases annotation <;> cases h
  · intro st d o n h; cases annotation <;> cases h
  · intro other value next h
    cases annotation <;> cases other <;>
      simp only [WordBinder.readSource,bindValueSource,bindHead,Lean.mkApp5,Lean.mkApp4,
        Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,Lean.Expr.app.injEq] at h
    all_goals first | contradiction | exact h.1.2 ▸ read
  · intro other value next h; cases annotation <;> cases other <;> cases h
  · intro a b c st next h; cases annotation <;> cases h

/-- The choice node itself introduces no array declarations or static loop
bounds. Its children retain their own conditions in the syntax judgment. -/
theorem InputConditions.choice
    (registers : LexicalScalarSyntax.StaticRegisters (Step.nativeChoice ty predicate decision yes no)) :
    InputConditions ds (Step.nativeChoice ty predicate decision yes no) := by
  constructor
  · exact registers
  · intro tag st r v h
    cases tag <;> cases h
  · intro st r v h; cases h
  · intro st a k v h; cases h
  · intro st d o n h; cases h
  · intro annotation v fn h
    cases annotation <;> cases h
  · intro annotation v fn h
    cases annotation <;> cases h
  · intro a b c st fn h; cases h

/-- Returning the current state variable imposes no array or loop conditions. -/
theorem InputConditions.returnVariable (tag : Return.Form) (index : Nat) :
    InputConditions ds (tag.source (.bvar index)) := by
  constructor
  · cases tag <;> trivial
  · intro other st r v h; cases tag <;> cases other <;> cases h
  · intro st r v h; cases tag <;> cases h
  · intro st a k v h; cases tag <;> cases h
  · intro st d o n h; cases tag <;> cases h
  · intro annotation v fn h; cases tag <;> cases annotation <;> cases h
  · intro annotation v fn h; cases tag <;> cases annotation <;> cases h
  · intro a b c st fn h; cases tag <;> cases h

/-- Source-static conditions for a register update. Irrelevant source heads
are excluded by syntax, not by running the frontend. -/
theorem InputConditions.valueAssign (rn : NatNotation) (r : Nat)
    (registers : LexicalScalarSyntax.StaticRegisters (app ``HybridWord.State.set [st,rn.native r,v])) :
    InputConditions ds (app ``HybridWord.State.set [st,rn.native r,v]) := by
  constructor
  · exact registers
  · intro tag t k w h; cases tag <;> simp [Return.Form.source,Return.Form.nativeHeader,app,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro t k w h
    simp only [app,List.foldl_cons,List.foldl_nil,Lean.Expr.app.injEq] at h
    exact ⟨⟨r,rn,h.1.2.symm⟩⟩
  · intro t a k w h; simp [app] at h
  · intro t d o n h; simp [app] at h
  · intro annotation value fn h; cases annotation <;> simp [app,WordBinder.readSource,bindHead,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro annotation value fn h; cases annotation <;> simp [app,WordBinder.stepReadSource,bindHead,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro a b c t fn h; simp [app,For.source,For.nativeHeader,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h

/-- The return wrapper contributes no array obligations. Static register
notation is supplied once for both ordinary return forms. -/
theorem InputConditions.assign (tag : Return.Form) (rn : NatNotation) (r : Nat)
    (registers : LexicalScalarSyntax.StaticRegisters (tag.source (app ``HybridWord.State.set [st,rn.native r,v]))) :
    InputConditions ds (tag.source (app ``HybridWord.State.set [st,rn.native r,v])) := by
  constructor
  · exact registers
  · intro other t k w h
    cases tag <;> cases other <;>
      simp [Return.Form.source,Return.Form.nativeHeader,app,Lean.mkApp5,Lean.mkApp4,
        Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
    all_goals exact ⟨⟨r,rn,h.1.2.symm⟩⟩
  · intro t k w h; cases tag <;> simp [Return.Form.source,Return.Form.nativeHeader,app,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro t a k w h; cases tag <;> simp [Return.Form.source,Return.Form.nativeHeader,app,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro t d o n h; cases tag <;> simp [Return.Form.source,Return.Form.nativeHeader,app,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro annotation value fn h; cases tag <;> cases annotation <;>
      simp [Return.Form.source,Return.Form.nativeHeader,app,WordBinder.readSource,bindHead,
        Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro annotation value fn h; cases tag <;> cases annotation <;>
      simp [Return.Form.source,Return.Form.nativeHeader,app,WordBinder.stepReadSource,bindHead,
        Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro a b c t fn h; cases tag <;>
      simp [Return.Form.source,Return.Form.nativeHeader,app,For.source,For.nativeHeader,
        Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h

theorem InputConditions.yield
    (registers : LexicalScalarSyntax.StaticRegisters (Step.yieldSource v)) : InputConditions ds (Step.yieldSource v) := by
  constructor
  · exact registers
  · intro tag t k w h; cases tag <;> simp [Step.yieldSource,Return.Form.source,Return.Form.nativeHeader,stepType,state,app,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro t k w h; simp [Step.yieldSource,app,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro t a k w h; simp [Step.yieldSource,app,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro t d o n h; simp [Step.yieldSource,app,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro annotation value fn h; cases annotation <;> simp [Step.yieldSource,app,WordBinder.readSource,bindHead,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro annotation value fn h; cases annotation <;> simp [Step.yieldSource,app,WordBinder.stepReadSource,bindHead,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro a b c t fn h; simp [Step.yieldSource,app,For.source,For.nativeHeader,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h

theorem InputConditions.forStatic (start : StaticBound a startValue) (stop : StaticBound b stopValue)
    (stride : StaticBound c strideValue)
    (registers : LexicalScalarSyntax.StaticRegisters (For.source a b c st fn)) :
    InputConditions ds (For.source a b c st fn) := by
  constructor
  · exact registers
  · intro tag t r v h; cases tag <;> simp [For.source,For.nativeHeader,Return.Form.source,Return.Form.nativeHeader,app,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro t r v h; simp [For.source,For.nativeHeader,app,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro t k j v h; simp [For.source,For.nativeHeader,app,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro t d o n h; simp [For.source,For.nativeHeader,app,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro annotation v next h; cases annotation <;> simp [For.source,For.nativeHeader,WordBinder.readSource,bindHead,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro annotation v next h; cases annotation <;> simp [For.source,For.nativeHeader,WordBinder.stepReadSource,bindHead,
      Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro x y z t next h
    simp only [For.source,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,Lean.Expr.app.injEq] at h
    obtain ⟨⟨⟨_,⟨⟨⟨_,hx⟩,hy⟩,hz⟩⟩,_⟩,_⟩ := h
    exact ⟨startValue,stopValue,strideValue,hx ▸ start,hy ▸ stop,hz ▸ stride⟩

/-- Natural-range loop requirements depend on source register conditions only.
The child syntax supplies its own declaration/read/copy obligations. This
covers both native iterator heads and does not inspect a generated command. -/
theorem InputConditions.forRange (kind : NaturalLoop.Kind)
    (registers : LexicalScalarSyntax.StaticRegisters (kind.source n st fn)) :
    InputConditions ds (kind.source n st fn) := by
  constructor
  · exact registers
  · intro tag t r v h
    cases kind <;> cases tag <;>
      simp [NaturalLoop.Kind.source,NaturalLoop.Kind.nativeHeader,NaturalLoop.nativeFoldHeader,
        For.Header.At.nativeHeader,Return.Form.source,Return.Form.nativeHeader,app,word,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro t r v h
    cases kind <;> simp [NaturalLoop.Kind.source,NaturalLoop.Kind.nativeHeader,NaturalLoop.nativeFoldHeader,
      For.Header.At.nativeHeader,app,word,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro t a k v h
    cases kind <;> simp [NaturalLoop.Kind.source,NaturalLoop.Kind.nativeHeader,NaturalLoop.nativeFoldHeader,
      For.Header.At.nativeHeader,app,word,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro t d o c h
    cases kind <;> simp [NaturalLoop.Kind.source,NaturalLoop.Kind.nativeHeader,NaturalLoop.nativeFoldHeader,
      For.Header.At.nativeHeader,app,word,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro annotation v next h
    cases kind <;> cases annotation <;>
      simp [NaturalLoop.Kind.source,NaturalLoop.Kind.nativeHeader,NaturalLoop.nativeFoldHeader,
        For.Header.At.nativeHeader,WordBinder.readSource,bindHead,app,word,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro annotation v next h
    cases kind <;> cases annotation <;>
      simp [NaturalLoop.Kind.source,NaturalLoop.Kind.nativeHeader,NaturalLoop.nativeFoldHeader,
        For.Header.At.nativeHeader,WordBinder.stepReadSource,bindHead,app,word,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro a b c t next h
    cases kind <;> simp [NaturalLoop.Kind.source,NaturalLoop.Kind.nativeHeader,NaturalLoop.nativeFoldHeader,
      NaturalLoop.nativeRange,For.Header.At.nativeHeader,For.source,For.nativeHeader,app,word,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h

/-- The existing basic-body grammar, refined only by independent source
requirements, determines a computation and command. -/
theorem constructAtomSource
    (form : StructuralSyntax.Form env ctx p raw requirements) :
    (∀ e, requirements e → InputConditions ds e) →
    ∃ native code quotation, Source ds (env := env) .body ctx p raw native code quotation := by
  induction form with
  | returns tag checked =>
    intro conditions
    have checked := conditions _ checked
    exact ⟨_,_,_,.returns tag⟩
  | write array index value checked =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨id,an,rfl,declared⟩ := checked.store _ _ _ _ rfl
    obtain ⟨f,kc,kq,index⟩ := FixedScalarCompleteness.Scoped.fromSyntax index.lexical checked.registers.1.2
    obtain ⟨g,vc,vq,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value.lexical checked.registers.2
    exact ⟨_,_,_,.store id an declared index value⟩
  | assign tag register value checked =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨view⟩ := checked.assignment tag _ _ _ rfl
    obtain ⟨f,vc,vq,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value.lexical
      (by cases tag <;> exact checked.registers.2.2)
    rw [view.shape]
    exact ⟨_,_,_,.assign tag view.value view.form value⟩
  | copy destination origin count checked =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨dst,src,size,dn,sn,cn,rfl,rfl,rfl,dd,sd⟩ := checked.copy _ _ _ _ rfl
    exact ⟨_,_,_,.copy dst src size dn sn cn dd sd⟩
  | branch value decision yes no checked iy ino =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨f,vc,vq,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value.lexical checked.registers.1.1.1.2.1.2.1.2
    obtain ⟨g,ac,aq,yes⟩ := iy conditions
    obtain ⟨h,bc,bq,no⟩ := ino conditions
    exact ⟨_,_,_,.branchDecision value decision yes no⟩

/-- A single induction for all modes of the existing scoped grammar, including
nested control, reads, bindings and helper applications. The generated
computation, command and quotation are conclusions, not source premises. -/
theorem constructSource
    (form : ScopedSyntax.Syntax env mode ctx p raw requirements) :
    (∀ e, requirements e → InputConditions ds e) →
    ∃ native code quotation, Source ds (env := env) mode ctx p raw native code quotation := by
  induction form with
  | atom form checked =>
    intro conditions
    have checked := conditions _ checked
    exact constructAtomSource form conditions
  | write array index value checked =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨id,an,rfl,declared⟩ := checked.store _ _ _ _ rfl
    obtain ⟨f,kc,kq,index⟩ := FixedScalarCompleteness.Scoped.fromSyntax index checked.registers.1.2
    obtain ⟨g,vc,vq,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value checked.registers.2
    exact ⟨_,_,_,.store id an declared index value⟩
  | assign tag register value checked =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨view⟩ := checked.assignment tag _ _ _ rfl
    obtain ⟨f,vc,vq,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value
      (by cases tag <;> exact checked.registers.2.2)
    rw [view.shape]
    exact ⟨_,_,_,.assign tag view.value view.form value⟩
  | branch value decision yes no checked iy ino =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨f,vc,vq,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value checked.registers.1.1.1.2.1.2.1.2
    obtain ⟨g,ac,aq,yes⟩ := iy conditions
    obtain ⟨h,bc,bq,no⟩ := ino conditions
    exact ⟨_,_,_,.branchDecision value decision yes no⟩
  | letValue annotation value next binder flag checked ih =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨f,vc,vq,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value checked.registers.1
    obtain ⟨g,bc,bq,next⟩ := ih conditions
    exact ⟨_,_,_,.letValue annotation value next binder flag⟩
  | sequence first next binder info checked ia ib =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨f,ac,aq,first⟩ := ia conditions; obtain ⟨g,bc,bq,next⟩ := ib conditions
    exact ⟨_,_,_,.sequence first next binder info⟩
  | bindValue value next binder info checked ih =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨f,vc,vq,value⟩ := FixedReadSourceCompleteness.constructSource value (checked.readBody .word _ _ rfl)
    obtain ⟨g,bc,bq,next⟩ := ih conditions
    exact ⟨_,_,_,.bindValue .word value next binder info⟩
  | bindBits value next binder info checked ih =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨f,vc,vq,value⟩ := FixedReadSourceCompleteness.constructSource value (checked.readBody .bitvec _ _ rfl)
    obtain ⟨g,bc,bq,next⟩ := ih conditions
    exact ⟨_,_,_,.bindValue .bitvec value next binder info⟩
  | stateAlias next binder flag checked ih =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨g,bc,bq,next⟩ := ih conditions; exact ⟨_,_,_,.stateAlias next binder flag⟩
  | stepBranch value decision yes no checked iy ino =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨f,vc,vq,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value checked.registers.1.1.1.2.1.2.1.2
    obtain ⟨g,ac,aq,yes⟩ := iy conditions
    obtain ⟨h,bc,bq,no⟩ := ino conditions
    exact ⟨_,_,_,.stepBranchDecision value decision yes no⟩
  | unitBody next binder info checked ih =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨g,bc,bq,next⟩ := ih conditions; exact ⟨_,_,_,.unitBody next binder info⟩
  | unitLoop next binder info checked ih =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨g,bc,bq,next⟩ := ih conditions; exact ⟨_,_,_,.unitLoop next binder info⟩
  | stateLet value next notAlias binder flag checked ia ib =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨f,ac,aq,value⟩ := ia conditions; obtain ⟨g,bc,bq,next⟩ := ib conditions
    exact ⟨_,_,_,.stateLet value next notAlias binder flag⟩
  | stepStateLet value next notAlias binder flag checked ia ib =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨f,ac,aq,value⟩ := ia conditions; obtain ⟨g,bc,bq,next⟩ := ib conditions
    exact ⟨_,_,_,.stepStateLet value next notAlias binder flag⟩
  | stepAlias next binder flag checked ih =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨g,bc,bq,next⟩ := ih conditions; exact ⟨_,_,_,.stepAlias next binder flag⟩
  | stepLetValue annotation value next binder flag checked ih =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨f,vc,vq,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value checked.registers.1
    obtain ⟨g,bc,bq,next⟩ := ih conditions
    exact ⟨_,_,_,.stepLetValue annotation value next binder flag⟩
  | stepBindValue value next binder info checked ih =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨f,vc,vq,value⟩ := FixedReadSourceCompleteness.constructSource value (checked.readStep .word _ _ rfl)
    obtain ⟨g,bc,bq,next⟩ := ih conditions
    exact ⟨_,_,_,.stepBindValue .word value next binder info⟩
  | stepBindBits value next binder info checked ih =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨f,vc,vq,value⟩ := FixedReadSourceCompleteness.constructSource value (checked.readStep .bitvec _ _ rfl)
    obtain ⟨g,bc,bq,next⟩ := ih conditions
    exact ⟨_,_,_,.stepBindValue .bitvec value next binder info⟩
  | stepSequence first next binder info checked ia ib =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨f,ac,aq,first⟩ := ia conditions; obtain ⟨g,bc,bq,next⟩ := ib conditions
    exact ⟨_,_,_,.stepSequence first next binder info⟩
  | valueCurrent checked =>
    intro conditions
    have checked := conditions _ checked
    exact ⟨_,_,_,.valueCurrent⟩
  | valueAssign register value checked =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨view⟩ := checked.valueAssignment _ _ _ rfl
    obtain ⟨f,vc,vq,value⟩ := FixedScalarCompleteness.Scoped.fromSyntax value checked.registers.2
    rw [view.shape]
    exact ⟨_,_,_,.valueAssign view.value view.form value⟩
  | yield value checked ih =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨f,vc,vq,value⟩ := ih conditions; exact ⟨_,_,_,.yield value⟩
  | forStatic start stop stride body kn tn ki ti checked ih =>
    intro conditions
    have checked := conditions _ checked
    obtain ⟨a,b,c,start,stop,stride⟩ := checked.staticRange _ _ _ _ _ rfl
    obtain ⟨f,bc,bq,body⟩ := ih conditions
    exact ⟨_,_,_,.forStatic start stop stride body kn tn ki ti⟩
  | @forRange ctx p n original requirements kind count body kn tn ki ti checked ih =>
    intro conditions
    have checked := conditions _ checked
    have static : LexicalScalarSyntax.StaticRegisters n := by
      cases kind with
      | forIn => exact checked.registers.1.1.2.2.2
      | fold => exact checked.registers.2.2.2
    obtain ⟨f,nc,nq,count⟩ := FixedScalarCompleteness.Scoped.fromSyntax count static
    obtain ⟨g,bc,bq,body⟩ := ih conditions
    exact ⟨_,_,_,.forRange kind count body kn tn ki ti⟩

end IRComparison.WordFrontend.FixedSequenceCompleteness
