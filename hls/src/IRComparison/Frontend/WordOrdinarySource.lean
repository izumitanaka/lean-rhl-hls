import IRComparison.Frontend.WordFixedFunctionCompleteness

/-! Original ordinary-Lean source judgments. These describe native expressions,
their lexical types and source array declarations. There are no compiler
results, expanded/retained bodies, substitutions or internal typing premises
in any constructor below. Fresh-State use is a separate source static
obligation: typing alone intentionally does not assert generation success. -/
namespace IRComparison.WordFrontend.OrdinarySource
open Certificate Arithmetic

inductive Result where
  | body | step
  deriving DecidableEq

inductive Parameter where
  | scalar (annotation : WordBinder.Annotation)
  | state | natural | unit
  deriving DecidableEq

structure Signature where
  domains : List Parameter
  result : Result
  deriving DecidableEq

inductive Slot where
  | value (type : Parameter)
  | function (signature : Signature)
  deriving DecidableEq

abbrev Context := List Slot

def Parameter.native : Parameter → Lean.Expr
  | .scalar a => a.native
  | .state => WordFrontend.state
  | .natural => .const ``Nat []
  | .unit => UnitStep.nativeUnitType

def Result.native : Result → Lean.Expr
  | .body => state
  | .step => stepType

def Result.mode : Result → StructuralBody.Mode
  | .body => .body
  | .step => .step

/-- Original function-type spelling, including names and binder annotations.
No canonical binder name is imposed on ordinary Lean definitions. -/
inductive Signature.Spelling : Signature → Lean.Expr → Prop where
  | result (result : Result) : Spelling ⟨[],result⟩ (.app (.const ``Option [.zero]) result.native)
  | arrow {resultKind : Result} (head : Parameter) (tail : Spelling ⟨rest,resultKind⟩ raw)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Spelling ⟨head::rest,resultKind⟩ (.forallE binder head.native raw info)

/-- A reference to an original State variable. Whether this is the current
State is checked by the source state-flow obligation, not by typing. -/
inductive StateRef (Γ : Context) : Lean.Expr → Prop where
  | variable (found : Γ[index]? = some (.value .state)) : StateRef Γ (.bvar index)

/-- All children refer to original syntax under its original binders. Word and
BitVec are interchangeable scalar types; original annotation spelling is kept. -/
inductive Scalar : Context → Lean.Expr → WordBinder.Annotation → Prop where
  | variable (found : Γ[index]? = some (.value (.scalar annotation))) :
      Scalar Γ (.bvar index) annotation
  | literal (annotation : WordBinder.Annotation) (n : Nat) :
      Scalar Γ (AnnotatedLiteral.native annotation n) annotation
  | register (state : StateRef Γ st) (register : Nat) (rn : NatNotation) :
      Scalar Γ (app ``HybridWord.State.regs [st,rn.native register]) .word
  | natural (found : Γ[index]? = some (.value .natural)) :
      Scalar Γ (NaturalScope.nativeIndex (.bvar index)) .bitvec
  | binary (op : Binary) (aa ab ac ad : WordBinder.Annotation)
      (left : Scalar Γ a leftType) (right : Scalar Γ b rightType) :
      Scalar Γ (Lean.mkApp2 (AnnotatedBinary.nativeHeader op aa ab ac ad) a b) ac
  | neg (annotation : WordBinder.Annotation) (value : Scalar Γ v actual) :
      Scalar Γ (.app (AnnotatedNeg.nativeHeader annotation) v) annotation
  | select (resultAnnotation conditionAnnotation : WordBinder.Annotation)
      (guard : Scalar Γ v va) (yes : Scalar Γ a aa) (no : Scalar Γ b ba) :
      Scalar Γ (AnnotatedCondition.scalarSource resultAnnotation conditionAnnotation v
        (AnnotatedCondition.nativeDecision conditionAnnotation v) a b) resultAnnotation
  | letValue (annotation : WordBinder.Annotation) (value : Scalar Γ v actual)
      (body : Scalar (.value (.scalar annotation)::Γ) b result)
      (binder : Lean.Name) (flag : Bool) :
      Scalar Γ (WordBinder.letSource annotation binder v b flag) result
  | beta (annotation : WordBinder.Annotation) (value : Scalar Γ v actual)
      (body : Scalar (.value (.scalar annotation)::Γ) b result)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Scalar Γ (.app (.lam binder annotation.native b info) v) result

inductive StateValue (Γ : Context) : Lean.Expr → Prop where
  | reference (state : StateRef Γ st) : StateValue Γ st
  | set (state : StateRef Γ st) (register : Nat) (rn : NatNotation)
      (value : Scalar Γ v annotation) :
      StateValue Γ (app ``HybridWord.State.set [st,rn.native register,v])

/-- Array declarations and literal/index spelling are source static facts.
Bounds of individual accesses remain run-time Option behavior. -/
inductive Read (ds : FixedMemory.Declarations) (Γ : Context) : Lean.Expr → WordBinder.Annotation → Prop where
  | natural (annotation : WordBinder.Annotation) (state : StateRef Γ st)
      (array index : Nat) (an nn : NatNotation)
      (declared : (FixedMemory.lookup ds array).isSome = true) :
      Read ds Γ (FixedReadSourceCompleteness.naturalSource annotation st (an.native array) (nn.native index)) annotation
  | word (annotation : WordBinder.Annotation) (state : StateRef Γ st)
      (array : Nat) (an : NatNotation) (declared : (FixedMemory.lookup ds array).isSome = true)
      (index : Scalar Γ k indexAnnotation) :
      Read ds Γ (FixedReadSourceCompleteness.wordSource annotation st (an.native array) k) annotation

/-- Source actual arguments follow the existing State/Unit/Word/BV32 calling
convention. Nat iterator variables remain available through Scalar.natural;
arbitrary Nat-valued helper actuals are not part of that convention.
No retained value or generated local index occurs in this source rule. -/
inductive Argument (Γ : Context) : Parameter → Lean.Expr → Prop where
  | scalar (value : Scalar Γ raw actual) : Argument Γ (.scalar declared) raw
  | state (value : StateRef Γ raw) : Argument Γ .state raw
  | unit : Argument Γ .unit UnitStep.nativeUnitValue
  | unitVariable (found : Γ[index]? = some (.value .unit)) : Argument Γ .unit (.bvar index)

abbrev Arguments (Γ : Context) (domains : List Parameter) (raws : List Lean.Expr) :=
  List.Forall₂ (Argument Γ) domains raws

def rangeResult : NaturalLoop.Kind → Result
  | .forIn => .step | .fold => .body

def rangeContext (kind : NaturalLoop.Kind) (Γ : Context) : Context := match kind with
  | .forIn => .value .state :: .value .natural :: Γ
  | .fold => .value .natural :: .value .state :: Γ

def sequence (result : Result) (first next : Lean.Expr) : Lean.Expr :=
  Lean.mkApp2 (bindHead state result.native) first next

def readBind (result : Result) (annotation : WordBinder.Annotation) (first next : Lean.Expr) : Lean.Expr :=
  Lean.mkApp2 (bindHead annotation.native result.native) first next

def branch (result : Result) (annotation : WordBinder.Annotation) (v a b : Lean.Expr) : Lean.Expr :=
  match result with
  | .body => AnnotatedBranch.source annotation v (AnnotatedCondition.nativeDecision annotation v) a b
  | .step => AnnotatedBranch.Loop.source annotation v (AnnotatedCondition.nativeDecision annotation v) a b

mutual
/-- A function body occurs only at its original lambda declaration. Calls
refer to its lexical signature and original argument list, not a body family. -/
inductive Function (ds : FixedMemory.Declarations) : Context → Lean.Expr → Signature → Prop where
  | variable (found : Γ[index]? = some (.function signature)) : Function ds Γ (.bvar index) signature
  | lambda {body : Lean.Expr} (head : Parameter) (tail : List Parameter) (result : Result)
      (shape : StructuralBody.LambdaSource raw ((head::tail).map Parameter.native) body)
      (bodySource : Body ds ((head::tail).reverse.map Slot.value ++ Γ) result body) :
      Function ds Γ raw ⟨head::tail,result⟩
inductive Body (ds : FixedMemory.Declarations) : Context → Result → Lean.Expr → Prop where
  | returns (tag : Return.Form) (value : StateValue Γ st) :
      Body ds Γ .body (tag.source st)
  | yield (value : StateValue Γ st) : Body ds Γ .step (Step.yieldSource st)
  | write (state : StateRef Γ st) (array : Nat) (an : NatNotation)
      (declared : (FixedMemory.lookup ds array).isSome = true)
      (index : Scalar Γ k ka) (value : Scalar Γ v va) :
      Body ds Γ .body (app ``HybridWord.State.write [st,an.native array,k,v])
  | copy (state : StateRef Γ st) (destination origin count : Nat) (dn sn cn : NatNotation)
      (target : FixedMemory.lookup ds destination = some count)
      (source : FixedMemory.lookup ds origin = some count) :
      Body ds Γ .body (app ``HybridWord.State.copy [st,dn.native destination,sn.native origin,cn.native count])
  | letScalar (result : Result) (annotation : WordBinder.Annotation) (value : Scalar Γ v actual)
      (body : Body ds (.value (.scalar annotation)::Γ) result b) (binder : Lean.Name) (flag : Bool) :
      Body ds Γ result (WordBinder.letSource annotation binder v b flag)
  | letState (result : Result) (value : StateValue Γ v)
      (body : Body ds (.value .state::Γ) result b) (binder : Lean.Name) (flag : Bool) :
      Body ds Γ result (StateLet.source binder v b flag)
  | bindState (result : Result) (first : Body ds Γ .body a)
      (next : Body ds (.value .state::Γ) result b) (binder : Lean.Name) (info : Lean.BinderInfo) :
      Body ds Γ result (sequence result a (.lam binder state b info))
  | bindRead (result : Result) (annotation : WordBinder.Annotation) (read : Read ds Γ v actual)
      (next : Body ds (.value (.scalar annotation)::Γ) result b) (binder : Lean.Name) (info : Lean.BinderInfo) :
      Body ds Γ result (readBind result annotation v (.lam binder annotation.native b info))
  | branch (result : Result) (annotation : WordBinder.Annotation) (guard : Scalar Γ v actual)
      (yes : Body ds Γ result a) (no : Body ds Γ result b) :
      Body ds Γ result (OrdinarySource.branch result annotation v a b)
  | staticRange (state : StateRef Γ st)
      (start : FixedSequenceCompleteness.StaticBound a startValue)
      (stop : FixedSequenceCompleteness.StaticBound b stopValue)
      (stride : FixedSequenceCompleteness.StaticBound c strideValue)
      (body : Body ds (.value .state::.value (.scalar .word)::Γ) .step raw)
      (kn tn : Lean.Name) (ki ti : Lean.BinderInfo) :
      Body ds Γ .body (For.source a b c st (.lam kn word (.lam tn WordFrontend.state raw ti) ki))
  | naturalRange (kind : NaturalLoop.Kind) (state : StateRef Γ st) (count : Scalar Γ n actual)
      (body : Body ds (rangeContext kind Γ) (rangeResult kind) raw)
      (kn tn : Lean.Name) (ki ti : Lean.BinderInfo) :
      Body ds Γ .body (kind.source n st (kind.nativeLambda kn tn ki ti raw))
  | unitSequence (result : Result) (body : Body ds (.value .unit::Γ) result b)
      (binder : Lean.Name) (info : Lean.BinderInfo) :
      Body ds Γ result (StructuralUnit.source (result == .step) binder b info)
  | call (fn : Function ds Γ f ⟨head::tail,result⟩)
      (arguments : Arguments Γ (head::tail) (first::rest)) :
      Body ds Γ result (rest.foldl Lean.Expr.app (.app f first))
  | letFunction (spelling : Signature.Spelling signature ty) (value : Function ds Γ v signature)
      (next : Body ds (.function signature::Γ) result b)
      (binder : Lean.Name) (flag : Bool) :
      Body ds Γ result (.letE binder ty v b flag)
end

end IRComparison.WordFrontend.OrdinarySource
