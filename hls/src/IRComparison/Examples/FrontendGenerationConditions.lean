import IRComparison.Frontend.WordFixedSequenceCompleteness
import IRComparison.Frontend.WordFixedFunctionCompleteness
import IRComparison.Frontend.LeanHLSCommand
import IRComparison.Examples.FrontendSourceMatching

/-! An ordinary definition uses the syntax/static-conditions theorem, without
assuming its parser succeeds or supplying a generated Entry. This is the first
source family through the connection, not a completeness claim for all forms. -/
namespace IRComparison.FrontendGenerationConditions
open Lean Elab Command WordFrontend FrontendSourceMatching
set_option linter.unusedVariables false

/-- Deliberately use different binder names from the compiler's proof binder
names. The source-language condition must not depend on those names. -/
def transfer (row left right : HybridWord.Word) (memory : HybridWord.State) : Option HybridWord.State :=
  memory.copy 1 0 4

def regions : FixedMemory.Declarations := #[(0,4),(1,4)]

-- Exercise the ordinary executable export as well, independently of the
-- proof-producing condition collector above. No custom source notation.
hls_word transfer as transferHLS
example : transferHLS.wordBody = HybridWord.Cmd.copy 1 0 4 := rfl

def scalarWord (i x y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 (let v : HybridWord.Word := x; v))

def scalarBits (i x y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 (let v : BitVec 32 := x; v))

def betaBits (i x y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 ((fun v : BitVec 32 => v) x))

open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic in
private theorem identity_scalar_syntax (annotation : WordBinder.Annotation)
    (binder : Lean.Name) (flag : Bool) :
    LexicalScalarSyntax.Form StandardLibrary.model context parameters []
      (.letE binder annotation.native (.bvar 2) (.bvar 0) flag) := by
  apply LexicalScalarSyntax.Form.letFromOpen (vs := []) StandardLibrary.library.scalars StandardLibrary.library.decisions StandardLibrary.closed
    (initialInputs StandardLibrary.library.connection.word StandardLibrary.library.connection.nilWords)
    LexicalScalarCode.ScopeTyped.initial ScalarSyntax.ReferenceScope.initial (by intro e h; cases h) annotation
  · exact .parameter .left (.variable 2) rfl rfl (by intro h; cases h)
  · trivial
  · intro a
    exact .reference rfl
  · trivial

open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic in
private theorem identity_beta_syntax (annotation : WordBinder.Annotation)
    (binder : Lean.Name) (info : Lean.BinderInfo) :
    LexicalScalarSyntax.Form StandardLibrary.model context parameters []
      (.app (.lam binder annotation.native (.bvar 0) info) (.bvar 2)) := by
  apply LexicalScalarSyntax.Form.betaFromOpen (vs := []) StandardLibrary.library.scalars StandardLibrary.library.decisions StandardLibrary.closed
    (initialInputs StandardLibrary.library.connection.word StandardLibrary.library.connection.nilWords)
    LexicalScalarCode.ScopeTyped.initial ScalarSyntax.ReferenceScope.initial (by intro e h; cases h) annotation
  · exact .parameter .left (.variable 2) rfl rfl (by intro h; cases h)
  · trivial
  · intro a
    exact .reference rfl
  · trivial

/-- Test-side recognition of the ordinary examples builds source judgments;
it neither calls the compiler nor supplies generated command certificates. -/
private def identityAssignment (source : Lean.Expr) :
    Option (PLift (ScopedSyntax.Form StandardLibrary.model context parameters source)) :=
  match source with
  | .app (.app (.const ``Option.some [.zero]) (.const ``HybridWord.State []))
      (.app (.app (.app (.const ``HybridWord.State.set []) (.bvar 0)) register)
        (.letE binder ty (.bvar 2) (.bvar 0) flag)) => do
    let n ← NatNotation.view register
    let a ← WordBinder.Annotation.view ty
    return ⟨by
      rw [n.shape,a.shape]
      exact .assign .some (n.form.argument StandardLibrary.library.scalars.toSignatures n.value)
        (identity_scalar_syntax a.annotation binder flag)⟩
  | .app (.app (.const ``Option.some [.zero]) (.const ``HybridWord.State []))
      (.app (.app (.app (.const ``HybridWord.State.set []) (.bvar 0)) register)
        (.app (.lam binder ty (.bvar 0) info) (.bvar 2))) => do
    let n ← NatNotation.view register
    let a ← WordBinder.Annotation.view ty
    return ⟨by
      rw [n.shape,a.shape]
      exact .assign .some (n.form.argument StandardLibrary.library.scalars.toSignatures n.value)
        (identity_beta_syntax a.annotation binder info)⟩
  | _ => none

hls_word scalarWord as scalarWordHLS
hls_word scalarBits as scalarBitsHLS
hls_word betaBits as betaBitsHLS
example : scalarWordHLS.wordBody = HybridWord.Cmd.assign 0 .left := rfl
example : scalarBitsHLS.wordBody = HybridWord.Cmd.assign 0 .left := rfl
example : betaBitsHLS.wordBody = HybridWord.Cmd.assign 0 .left := rfl

/-- Ordinary lambda application, including its source certificate transport. -/
def helperCall (i x y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  (fun t : HybridWord.State => some t) s

hls_word helperCall as helperCallHLS
example : helperCallHLS.wordBody = HybridWord.Cmd.skip := rfl

def helperLet (i x y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  let k : HybridWord.State → Option HybridWord.State := fun t => some t
  k s

hls_word helperLet as helperLetHLS
example : helperLetHLS.wordBody = HybridWord.Cmd.skip := rfl


/-- The local helper is traversed inside a loop body, with the loop's lexical
bindings still present. No run-time iteration is expanded by the source proof. -/
def loopLocalHelper (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  ForIn.forIn (HybridWord.range 0 4 1) s (fun _k t => do
    let next ← (let helper : HybridWord.State → Option HybridWord.State := fun u => some u; helper t)
    pure (.yield next))

private def functionRaw (_ : FixedFunctionCompleteness.Source ds (env := env) ctx p σ scope raw native code quotation mode) := raw
private def functionMeaning (_ : FixedFunctionCompleteness.Source ds (env := env) ctx p σ scope raw native code quotation mode) := native
private def functionCode (_ : FixedFunctionCompleteness.Source ds (env := env) ctx p σ scope raw native code quotation mode) := code
private def functionQuotation (_ : FixedFunctionCompleteness.Source ds (env := env) ctx p σ scope raw native code quotation mode) := quotation

hls_word loopLocalHelper as loopLocalHelperHLS
example : loopLocalHelperHLS.wordBody = .forStatic 0 4 1 (.seq .skip .skip) := rfl

/-- A scalar binder between a captured function and its call must preserve
that function's binding position. This exercises the combined source rule. -/
def helperAfterScalar (i x y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  let k : HybridWord.State → Option HybridWord.State := fun t => some t
  let saved : HybridWord.Word := x
  k s

hls_word helperAfterScalar as helperAfterScalarHLS
example : helperAfterScalarHLS.wordBody = HybridWord.Cmd.letValue .left .skip := rfl

def readBits (i x y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let v : BitVec 32 ← (s.arrays 0)[0]?
  pure (s.set 0 v)

private def readBinding (source : Lean.Expr) :
    Option (FixedReadCompleteness.Source source) := do
  match source with
  | .app (.app head first) (.lam binder ty next info) =>
    let bv := WordBinder.Annotation.bitvec
    let sameHead ← sameClosedHeader (bindHead bv.native state) head
    let sameType ← sameClosedHeader bv.native ty
    match first, next with
    | .app (.app readHead (.app (.app (.const ``HybridWord.State.arrays []) (.bvar 0)) array)) index,
      .app returnHead (.app (.app (.app (.const ``HybridWord.State.set []) (.bvar 1)) register) (.bvar 0)) =>
      let sameRead ← sameClosedHeader Read.nativeBitsHeader readHead
      let sameReturn ← sameClosedHeader Certificate.Return.Form.pure.nativeHeader returnHead
      let a ← NatNotation.view array
      let n ← NatNotation.view index
      let r ← NatNotation.view register
      return ⟨a.value,n.value,r.value,a.form,n.form,r.form,binder,info,by
        rw [sameHead.down,sameType.down,sameRead.down,sameReturn.down]
        exact (congrArg (fun array => (bindHead bv.native state).app
          ((Read.nativeBitsHeader.app ((Lean.Expr.const ``HybridWord.State.arrays []).app (.bvar 0) |>.app array)).app index)
          |>.app (.lam binder bv.native
            (Certificate.Return.Form.pure.nativeHeader.app
              ((((Lean.Expr.const ``HybridWord.State.set []).app (.bvar 1)).app register).app (.bvar 0))) info)) a.shape).trans (by
                simp only [n.shape,r.shape]
                rfl)⟩
    | _, _ => none
  | _ => none

hls_word readBits as readBitsHLS
example : readBitsHLS.wordBody = HybridWord.Cmd.letValue (.readNat 0 0) (.assign 0 (.local 0)) := rfl

/-- Loop-body do elaboration keeps the explicit BV32 binder, too. -/
def loopReadBits (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let mut s := s
  for k in HybridWord.range 0 4 1 do
    let v : BitVec 32 ← (s.arrays 0)[k.toNat]?
    s := s.set 0 v
  pure s

run_cmd do
  unless (StructuralBody.compileRetained (← getEnv) ``loopReadBits).isSome do
    throwError "annotated loop must use the structural entry without legacy fallback"
hls_word loopReadBits as loopReadBitsHLS
example : loopReadBitsHLS.wordBody =
    HybridWord.Cmd.seq (.forStatic 0 4 1 (.letValue (.read 0 (.local 0)) (.seq (.assign 0 (.local 0)) .skip))) .skip := rfl

/-- Retained scalars and a do-read inside a local function exercise captured
scopes rather than a normalized/reparsed function body. -/
def helperRead (i x y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let helper := fun (t : HybridWord.State) => do
    let v : HybridWord.Word ← (t.arrays 0)[0]?
    let retained : HybridWord.Word := v + x
    pure (t.set 0 retained)
  helper s

run_cmd do
  unless (StructuralBody.compileRetained (← getEnv) ``helperRead).isSome do
    throwError "captured read and scalar let must compile without the legacy fallback"
hls_word helperRead as helperReadHLS

/-- The new dispatch clauses are source conditions, not parser outcomes. The
existing helper-completeness induction consumes this derivation at any scope. -/
example (σ : StructuralBody.Substitution) (p : Inputs)
    (current : σ.apply (.bvar 0) = p.s) (a j r v : Lean.Expr) :
    StructuralSyntax.HeadForm σ p
      (Certificate.bindValueSource (Read.source (.bvar 0) a j)
        (.lam `v word (Certificate.letValueSource `retained v
          (Certificate.Return.Form.pure.source (app ``HybridWord.State.set [.bvar 2,r,.bvar 0])) false) .default)) := by
  apply StructuralSyntax.HeadForm.bindValue
  apply StructuralSyntax.HeadForm.letValue
  apply StructuralSyntax.HeadForm.assign .pure
  cases σ <;> simpa [StructuralBody.Substitution.apply,StructuralBody.under,LeanBindings.substitute,
    LeanBindings.underSubst,Inputs.lift] using congrArg (LeanBindings.rename Nat.succ ∘ LeanBindings.rename Nat.succ) current

private structure FixedSourceView (ds : FixedMemory.Declarations) (ctx : List Lean4Lean.VExpr) (p : Inputs) (source : Lean.Expr) where
  native : CertifiedHLS.Program
  code : HybridWord.Cmd
  quotation : Lean.Expr
  derivation : FixedSequenceCompleteness.Source ds (env := StandardLibrary.model) .body ctx p source (fun _ _ _ _ => native) code quotation

/-- Independent source/static evidence for this connected fragment. It does
not call either frontend parser or inspect a generated Entry. -/
private def fixedSourceView (ds : FixedMemory.Declarations) (ctx : List Lean4Lean.VExpr) (p : Inputs) (current : p.s = .bvar 0)
    (source : Lean.Expr) : Option (FixedSourceView ds ctx p source) := do
  if let some v := readBinding source then
    if declared : (FixedMemory.lookup ds v.array).isSome = true then
      have shape : source = FixedReadCompleteness.original v.array v.index v.register v.an v.nn v.rn v.binder v.info p := by
        exact v.shape.trans (by simp only [FixedReadCompleteness.original,FixedReadCompleteness.continuation,
          Inputs.lift,current]; rfl)
      return ⟨_,_,_,shape.symm ▸ FixedSequenceCompleteness.Source.read v.array v.index v.register
        v.an v.nn v.rn declared v.binder v.info⟩
    else none
  else
    match source with
    | .app (.app (.app (.app (.const ``HybridWord.State.copy []) (.bvar 0)) d) o) n =>
      let dv ← NatNotation.view d
      let ov ← NatNotation.view o
      let nv ← NatNotation.view n
      if hd : FixedMemory.lookup ds dv.value = some nv.value then
        if ho : FixedMemory.lookup ds ov.value = some nv.value then
          have args : [d,o,n] = [dv.form.native dv.value,ov.form.native ov.value,nv.form.native nv.value] :=
            (congrArg (fun x => [x,o,n]) dv.shape).trans
              ((congrArg (fun x => [dv.form.native dv.value,x,n]) ov.shape).trans
                (congrArg (fun x => [dv.form.native dv.value,ov.form.native ov.value,x]) nv.shape))
          have same := congrArg (fun args => app ``HybridWord.State.copy (.bvar 0::args)) args
          return ⟨FixedCopyCompleteness.program dv.value ov.value nv.value,
            .copy dv.value ov.value nv.value,
            FixedCopyCompleteness.quotedCode dv.value ov.value nv.value dv.form ov.form nv.form,by
            have derived := FixedSequenceCompleteness.Source.copy (env := StandardLibrary.model) (ctx := ctx) (p := p) dv.value ov.value nv.value
              dv.form ov.form nv.form hd ho
            rw [current] at derived
            change FixedSequenceCompleteness.Source ds (env := StandardLibrary.model) .body ctx p
              (app ``HybridWord.State.copy [.bvar 0,d,o,n]) _ _ _
            change app ``HybridWord.State.copy [.bvar 0,d,o,n] = _ at same
            rw [same]
            exact derived⟩
        else none
      else none
    | .app (.app head first) (.lam binder (.const ``HybridWord.State []) next info) =>
      let headShape ← sameClosedHeader (bindHead state state) head
      let a ← fixedSourceView ds ctx p current first
      let b ← fixedSourceView ds (Certificate.stateType::ctx) {p.lift with s := .bvar 0} rfl next
      return ⟨(fun s => (a.native s).bind b.native),.seq a.code b.code,
        app ``HybridWord.Cmd.seq [a.quotation,b.quotation],by
        rw [headShape.down]
        exact FixedSequenceCompleteness.Source.sequence a.derivation b.derivation binder info⟩
    | .letE binder (.const ``HybridWord.State []) (.bvar 0) next flag =>
      let b ← fixedSourceView ds (Certificate.stateType::ctx) {p.lift with s := .bvar 0} rfl next
      return ⟨b.native,b.code,b.quotation,by
        have derived := FixedSequenceCompleteness.Source.stateAlias (p := p) b.derivation binder flag
        rw [current] at derived
        exact derived⟩
    | _ => none
termination_by syntaxSize source
decreasing_by all_goals simp_all [syntaxSize] <;> omega

def copyRead (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let s ← s.copy 1 0 4
  let v : BitVec 32 ← (s.arrays 1)[2]?
  pure (s.set 0 v)

hls_word copyRead as copyReadHLS
example : copyReadHLS.wordBody = .seq (.copy 1 0 4) (.letValue (.readNat 1 2) (.assign 0 (.local 0))) := rfl

/-- The old scalar remains available after the State changes. Both BV32 and
Word annotations use the same general source-induction rule. -/
def retainAfterWrite (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let old : BitVec 32 := s.regs 0
  let s ← s.write 0 1 old
  pure (s.set 0 old)

hls_word retainAfterWrite as retainAfterWriteHLS
example : retainAfterWriteHLS.wordBody = .letValue (.reg 0)
    (.seq (.store 0 (.lit 1) (.local 0)) (.assign 0 (.local 0))) := rfl

/-- Mixed Word/BV32 arithmetic keeps its actual elaborated header, including
the independently annotated dictionary, in the source-success derivation. -/
def retainedMixedArithmetic (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let old : BitVec 32 := s.regs 0
  let s ← s.write 0 1 (old + 1)
  pure (s.set 0 old)

run_cmd do
  unless (StructuralBody.compileRetained (← getEnv) ``retainedMixedArithmetic).isSome do
    throwError "mixed Word/BV32 arithmetic must use the structural frontend"
hls_word retainedMixedArithmetic as retainedMixedArithmeticHLS
example : retainedMixedArithmeticHLS.wordBody = .letValue (.reg 0)
    (.seq (.store 0 (.lit 1) (.add (.local 0) (.lit 1))) (.assign 0 (.local 0))) := rfl

/-- Explicit BV32 annotation also changes the unary operator's header. -/
def retainedNegation (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let old : BitVec 32 := s.regs 0
  pure (s.set 0 (-old))

hls_word retainedNegation as retainedNegationHLS
example : retainedNegationHLS.wordBody = .letValue (.reg 0) (.assign 0 (.neg (.local 0))) := rfl

/-- The condition itself, including BEq and the zero literal, uses BV32.
This checks the ordinary definition against the general source induction. -/
def retainedCondition (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let old : BitVec 32 := s.regs 0
  if old != 0 then pure (s.set 0 1) else pure s

hls_word retainedCondition as retainedConditionHLS
example : retainedConditionHLS.wordBody = .letValue (.reg 0) (.branch (.local 0) (.assign 0 (.lit 1)) .skip) := rfl

private def fixedSelectionRaw (_ : FixedSequenceCompleteness.Source ds (env := env) mode ctx p raw native code quotation) := raw

/-- BV32 annotation applies to both the predicate and the result of `ite`.
The subsequent let retains this selected value as an ordinary scalar. -/
def retainedSelection (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let old : BitVec 32 := s.regs 0
  let result : BitVec 32 := if old != 0 then old else 1
  pure (s.set 0 result)

hls_word retainedSelection as retainedSelectionHLS
example : retainedSelectionHLS.wordBody =
    .letValue (.reg 0) (.letValue (.select (.local 0) (.local 0) (.lit 1)) (.assign 0 (.local 0))) := rfl

/-- A read continuation can itself read at a dynamic address, then write an
array. The general rule is not restricted to read-then-register examples. -/
def indirectReadWrite (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let address : BitVec 32 ← (s.arrays 0)[0]?
  let value : HybridWord.Word ← (s.arrays 0)[address.toNat]?
  s.write 1 address value

hls_word indirectReadWrite as indirectReadWriteHLS
example : indirectReadWriteHLS.wordBody = .letValue (.readNat 0 0)
    (.letValue (.read 0 (.local 0)) (.store 1 (.local 1) (.local 0))) := rfl


/-- Extract only source syntax and static witnesses. In particular none of
these premises mentions a successful frontend run or a constructed Entry. -/
private def sourceRaw {ds env ctx mode p raw native code quotation}
    (_ : FixedSequenceCompleteness.Source ds (env := env) mode ctx p raw native code quotation) : Lean.Expr := raw

private def sourceMeaning {ds env ctx mode p raw native code quotation}
    (_ : FixedSequenceCompleteness.Source ds (env := env) mode ctx p raw native code quotation) : FixedSequenceCompleteness.Meaning := native

private def sourceCode {ds env ctx mode p raw native code quotation}
    (_ : FixedSequenceCompleteness.Source ds (env := env) mode ctx p raw native code quotation) : HybridWord.Cmd := code

private def sourceQuotation {ds env ctx mode p raw native code quotation}
    (_ : FixedSequenceCompleteness.Source ds (env := env) mode ctx p raw native code quotation) : Lean.Expr := quotation

/-- A runtime count is allowed by the existing natural-range form; generation
success does not depend on its value or on all stores being in bounds. -/
def countedWrites (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  (List.range (s.regs 0).toNat).foldlM (fun t k => t.write 0 (BitVec.ofNat 32 k) 1) s

hls_word countedWrites as countedWritesHLS
example : countedWritesHLS.wordBody = .forRange (.reg 0) (.store 0 (.local 0) (.lit 1)) := rfl

/-- No predicate-typing proof or parser outcome is supplied for this ordinary
Lean conditional. The standard decision argument is derived by the library. -/
def conditionalCopy (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  if s.regs 0 != 0 then s.copy 1 0 4 else pure s

hls_word conditionalCopy as conditionalCopyHLS
example : conditionalCopyHLS.wordBody = .branch (.reg 0) (.copy 1 0 4) .skip := rfl

/-- A conditional inside a loop uses the same recursive source judgment. -/
def conditionalLoop (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  ForIn.forIn (HybridWord.range 0 4 1) s (fun k t =>
    if t.regs 0 != 0 then pure (.yield (t.set 0 k)) else pure (.yield t))

/-- Ordinary arithmetic in static loop bounds is typed structurally; the
frontend neither unfolds the iterations nor evaluates an arbitrary Lean term. -/
def arithmeticBounds (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  ForIn.forIn (HybridWord.range (1 + 1) ((3 * 4) / 2) 1) s
    (fun k t => pure (.yield (t.set 0 k)))

hls_word arithmeticBounds as arithmeticBoundsHLS
example : arithmeticBoundsHLS.wordBody = .forStatic 2 6 1 (.assign 0 (.local 0)) := rfl

hls_word conditionalLoop as conditionalLoopHLS
example : conditionalLoopHLS.wordBody = .forStatic 0 4 1
  (.branch (.reg 0) (.assign 0 (.local 0)) .skip) := rfl

/-- A value-valued conditional composes with a memory update, without a
separate predicate-typing premise in the source derivation. -/
def selectedStore (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  s.write 1 0 (if s.regs 0 != 0 then 1 else 2)

hls_word selectedStore as selectedStoreHLS
example : selectedStoreHLS.wordBody = .store 1 (.lit 0) (.select (.reg 0) (.lit 1) (.lit 2)) := rfl

/-- The actual Nat counter, a BV32 comparison and a selected value share the
same source environment inside foldlM. Their types are derived, not supplied. -/
def countedChoice (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  (List.range (s.regs 0).toNat).foldlM (fun t k =>
    t.write 0 (BitVec.ofNat 32 k)
      (if BitVec.ofNat 32 k != 0 then BitVec.ofNat 32 k else (1 : BitVec 32))) s

hls_word countedChoice as countedChoiceHLS
example : countedChoiceHLS.wordBody = .forRange (.reg 0)
    (.store 0 (.local 0) (.select (.local 0) (.local 0) (.lit 1))) := rfl

/-- Two genuinely used parameters; the helper type is reconstructed from
its body Source rather than handwritten as a separate lambda typing proof. -/
def twoArgumentHelper (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  let put : HybridWord.Word → HybridWord.State → Option HybridWord.State :=
    fun value memory => some (memory.set 0 value)
  put (s.regs 1) s

open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic StructuralBody in
private theorem two_helper_syntax (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (annotation : WordBinder.Annotation) (binder vn sn dn en : Name) (vi si di ei : BinderInfo) (flag : Bool) (conditional : Bool := false) :
    FunctionSyntax.Syntax env context parameters .identity .empty
      (.letE binder (.forallE dn annotation.native (.forallE en state (.app (.const ``Option [.zero]) state) ei) di)
        (.lam vn annotation.native (.lam sn state (Return.Form.some.source
          (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,.bvar 1])) si) vi)
        (if conditional then Branch.source (app ``HybridWord.State.regs [.bvar 1,NatNotation.elaborated.native 1])
          (Branch.nativeBooleanDecision (app ``HybridWord.State.regs [.bvar 1,NatNotation.elaborated.native 1]))
          (.app (.app (.bvar 0) (app ``HybridWord.State.regs [.bvar 1,NatNotation.elaborated.native 1])) (.bvar 1)) (Return.Form.some.source (.bvar 1)) else (.app (.app (.bvar 0) (app ``HybridWord.State.regs [.bvar 1,NatNotation.elaborated.native 1])) (.bvar 1))) flag)
      (FixedSequenceCompleteness.InputConditions #[]) := by
  let inputs := initialInputs library.connection.word library.connection.nilWords
  let fs (a : WordBinder.Annotation) := (a.nextInputs inputs closed library.scalars.toSignatures library.cons).nextState closed
  let fl (a : WordBinder.Annotation) := (a.nextLocals (ScalarSyntax.Locals.empty (env := env) (ctx := context) (p := parameters) rfl) closed).nextState closed
  have functionSource (a : WordBinder.Annotation) : FunctionSyntax.Syntax env
      (stateType::a.core::context) (For.parameters parameters) .identity .empty
      (Return.Form.some.source (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,.bvar 1])) := by
    apply FunctionSyntax.Syntax.plain
    apply ScopedSyntax.Syntax.assign .some (NatNotation.elaborated.argument library.scalars.toSignatures 0)
    exact (ScalarSyntax.Form.localValue (.bvar 1) (.variable 1) 0 rfl
      (by decide) (by decide) (by decide) (by intro j hj; omega)).lexical
  have regForm {ctx : List VExpr} {p : Inputs}
      (separated : ScalarSyntax.Separated p (app ``HybridWord.State.regs [p.s,NatNotation.elaborated.native 1])) :
      LexicalScalarSyntax.Form env ctx p []
        (app ``HybridWord.State.regs [p.s,NatNotation.elaborated.native 1]) := by
    apply LexicalScalarSyntax.Form.register
    · simp only [LexicalScalarSyntax.expand_nil]
    · simpa only [LexicalScalarSyntax.expand_nil] using NatNotation.elaborated.argument (ctx := ctx) library.scalars.toSignatures 1
    · simpa only [LexicalScalarSyntax.expand_nil] using separated
  have typeShape (actualTypes : List VExpr)
      (argumentShapes : List.Forall₂ (fun declared inferred =>
        (declared = stateType ∧ inferred = stateType) ∨
        ∃ a b : WordBinder.Annotation, declared = a.core ∧ inferred = b.core)
        [annotation.core,stateType] actualTypes) :
      ∃ a : WordBinder.Annotation, actualTypes = [a.core,stateType] := by
    cases argumentShapes with
    | cons first remaining =>
      cases remaining with
      | cons second last =>
        cases last
        rcases first with ⟨impossible,_⟩ | ⟨a,b,declared,same⟩
        · cases annotation <;> simp [WordBinder.Annotation.core,wordType,bitvecType,stateType] at impossible
        rcases second with ⟨_,stateSame⟩ | ⟨c,d,impossible,_⟩
        · exact ⟨b,by simp only [same,stateSame]⟩
        · cases c <;> simp [WordBinder.Annotation.core,wordType,bitvecType,stateType] at impossible
  let argumentAnnotation (actualAnnotation : WordBinder.Annotation) (n : Nat) : WordBinder.Annotation := if n = 0 then annotation else actualAnnotation
  have bodyContext (actualAnnotation : WordBinder.Annotation) (n : Nat) (hn : n ≤ 2) :
      (([actualAnnotation.core,stateType].take n ++ [annotation.core,stateType].drop n).reverse ++ context) =
        stateType :: (argumentAnnotation actualAnnotation n).core :: context := by
    cases n with
    | zero => simp [argumentAnnotation]
    | succ n =>
      cases n with
      | zero => simp [argumentAnnotation,WordBinder.Annotation.core]
      | succ n =>
        have zero : n = 0 := by omega
        subst n
        simp [argumentAnnotation,WordBinder.Annotation.core]
  let functionType := VExpr.forallE annotation.core (.forallE stateType (optionType stateType))
  have openArguments : List.Forall₂ (fun domain raw =>
      (domain = stateType ∧ raw = parameters.lift.s) ∨
      ∃ a : WordBinder.Annotation, domain = a.core ∧
        LexicalScalarSyntax.Form env (functionType::context) parameters.lift [] raw ∧
        LexicalScalarSyntax.StaticRegisters raw)
      [annotation.core,stateType]
      [app ``HybridWord.State.regs [parameters.lift.s,NatNotation.elaborated.native 1],parameters.lift.s] :=
    .cons (Or.inr ⟨annotation,rfl,regForm ⟨rfl,rfl,rfl,by intro k; rfl⟩,
      ⟨⟨⟨1,.elaborated,rfl⟩⟩,True.intro⟩⟩) (.cons (Or.inl ⟨rfl,rfl⟩) .nil)
  obtain ⟨continuationCore,continuationRep,continuationTyped⟩ := FixedFunctionCompleteness.boundCallTypingFromSyntax library closed
    (inputs.lift closed functionType) (LexicalScalarCode.ScopeTyped.initial.lift closed functionType)
    openArguments (index := 0) rfl
  have helperBinding : FunctionSyntax.BindingValue .empty context.length .identity
      (.lam vn annotation.native (.lam sn state (Return.Form.some.source (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,.bvar 1])) si) vi) (.captured context.length .identity 2
        (Return.Form.some.source (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,.bvar 1])) .empty) :=
    .lambda (.next (.last (by intros; intro h; cases h)))
  have callTail : FunctionSyntax.Syntax env context parameters
      (StructuralBody.letSubstitution .identity (.lam vn annotation.native (.lam sn state (Return.Form.some.source
          (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,.bvar 1])) si) vi))
      (.push (some (.captured context.length .identity 2 (Return.Form.some.source (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,.bvar 1])) .empty)) .empty) (.app (.app (.bvar 0) (app ``HybridWord.State.regs [.bvar 1,NatNotation.elaborated.native 1])) (.bvar 1))
      (FixedSequenceCompleteness.InputConditions #[]) := by
    apply FixedFunctionCompleteness.retainedArgumentsFromBodyFamily setup library closed fresh exposure
      inputs (ScalarSyntax.Locals.empty rfl) LexicalScalarCode.ScopeTyped.initial ScalarSyntax.ReferenceScope.initial
      (.app (.bvar 0) (app ``HybridWord.State.regs [.bvar 1,NatNotation.elaborated.native 1])) (.bvar 1) (by decide)
      (domain := annotation.core) (tailDomains := [stateType]) (nativeDomains := [annotation.native,state])
      (depth := context.length) (captured := .identity) (arity := 2) (functions := .empty)
      (body := Return.Form.some.source (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,.bvar 1]))
      (functionBody := Return.Form.some.source (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,.bvar 1]))
    · exact (FunctionSyntax.Scope.coherent_empty _ _).functionLet helperBinding
    · exact .reuse rfl
    · rfl
    · exact .cons (Or.inr ⟨annotation,rfl,regForm ⟨rfl,rfl,rfl,by intro k; rfl⟩,
        ⟨⟨⟨1,.elaborated,rfl⟩⟩,True.intro⟩⟩) (.cons (Or.inl ⟨rfl,rfl⟩) .nil)
    · intro actual shapes openStates
      dsimp only
      intro _ _ _ _
      obtain ⟨a,rfl⟩ := typeShape actual shapes
      simp only [FunctionSyntax.parameterLayout_scalar,FunctionSyntax.parameterLayout_state]
      let p1 : Inputs := {parameters.lift with locals := .bvar 0::parameters.lift.locals}
      let frame : List VExpr × Inputs × List Lean.Expr := if openStates then
        (stateType::a.core::context,For.parameters parameters,[.bvar 1,.bvar 0])
        else (a.core::context,p1,[.bvar 0,p1.s])
      let slot := if openStates then 1 else 0
      change FunctionSyntax.Syntax env frame.1 frame.2.1
        (closureSubstitution context.length frame.1.length .identity frame.2.2)
        (FunctionSyntax.Scope.empty.parameters frame.2.2.length)
        (Return.Form.some.source (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,.bvar 1])) _
      apply FunctionSyntax.Syntax.base (.assign .some (by cases openStates <;> rfl))
      have sourceEq : (closureSubstitution context.length frame.1.length .identity frame.2.2).apply
          (Return.Form.some.source (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,.bvar 1])) =
          Return.Form.some.source (app ``HybridWord.State.set [frame.2.1.s,NatNotation.elaborated.native 0,.bvar slot]) := by
        cases openStates <;> rfl
      rw [sourceEq]
      exact .assign .some (NatNotation.elaborated.argument library.scalars.toSignatures 0)
        (.localValue (.variable slot) 0 (by cases openStates <;> rfl)
          (by cases openStates <;> rfl) (by cases openStates <;> rfl) (by cases openStates <;> rfl)
          (by intro j hj; omega))
        (.assign .some .elaborated 0 (by cases openStates <;> trivial))
    · exact .next (.last (by intros; intro h; cases h))
    · exact .cons annotation.represented (.cons (.constant rfl) .nil)
  have skipEvidence : ∃ core, Represents (Return.Form.some.source (.bvar 1)) core ∧
      CastTyping env 0 (SourceCasts env) (functionType::context) core (optionType stateType) := by
    have skip : FunctionSyntax.Syntax env (functionType::context) parameters.lift .identity .empty
        (Return.Form.some.source (.bvar 1)) := .plain (.atom (.returns .some))
    exact skip.sourceTyping setup library closed fresh exposure (inputs.lift closed functionType) (.empty rfl)
  apply FunctionSyntax.Syntax.functionLetFromLambdaPaired .body (by decide) setup library closed fresh exposure
    binder _ _ _ flag
    (functionSource := functionSource annotation) (domain := annotation.core) (domains := [stateType])
  · exact .lambda (.next (.last (by intros; intro h; cases h)))
  · cases conditional with
    | false => exact ⟨callTail,continuationCore,continuationRep,continuationTyped⟩
    | true =>
      apply FunctionSyntax.Syntax.booleanBranchPaired library (inputs.lift closed functionType)
        (LexicalScalarCode.ScopeTyped.initial.lift closed functionType)
        (v := app ``HybridWord.State.regs [.bvar 1,NatNotation.elaborated.native 1])
      · exact ⟨regForm ⟨rfl,rfl,rfl,by intro k; rfl⟩,regForm ⟨rfl,rfl,rfl,by intro k; rfl⟩⟩
      · exact ⟨⟨⟨1,.elaborated,rfl⟩⟩,True.intro⟩
      · exact ⟨callTail,continuationCore,continuationRep,continuationTyped⟩
      · refine ⟨?_,skipEvidence⟩
        apply FunctionSyntax.Syntax.base (.returns .some rfl)
        change ScopedSyntax.Syntax env .body context parameters (Return.Form.some.source parameters.s) _
        have checked := FixedSequenceCompleteness.InputConditions.returnVariable (ds := #[]) .some 0
        exact .atom (.returns .some (checked := checked)) (checked := checked)
      · apply FixedSequenceCompleteness.InputConditions.choice
        simp [LexicalScalarSyntax.StaticRegisters,Branch.nativeCondition,Branch.nativeBooleanDecision,Branch.nativeTestHeader,Step.nativeChoice,Return.Form.source,Return.Form.nativeHeader,app,StructuralBody.letSubstitution,Substitution.apply,Substitution.reference,LeanBindings.substitute,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB,word,state,option,Arithmetic.nativeWidth,Arithmetic.nativeLiteral]
        exact ⟨⟨⟨1,.elaborated,rfl⟩⟩,by trivial,⟨⟨1,.elaborated,rfl⟩⟩⟩

  · exact fs annotation
  · exact fl annotation
  · exact .next (.last (by intros; intro h; cases h))
  · exact .cons annotation.represented (.cons (.constant rfl) .nil)
  · intro d hd
    rcases List.mem_cons.mp hd with rfl|hd
    · exact ⟨_,(annotation.type_typed library.scalars.toSignatures).withCasts _⟩
    · have same : d = stateType := by simpa using hd
      subst d
      exact ⟨_,CastTyping.constant library.steps.state (by simp) rfl⟩
  · exact .forallE annotation.represented (.forallE (.constant rfl) (.app (.constant rfl) (.constant rfl)))

hls_word twoArgumentHelper as twoArgumentHelperHLS
example : twoArgumentHelperHLS.wordBody = .letValue (.reg 1) (.assign 0 (.local 0)) := rfl
example : (fun s => some (s.set 0 (s.regs 1))) = twoArgumentHelper 0 0 0 := rfl

/-- The open continuation has a branch containing an abstract local call.
Its typing is composed from source rules, not supplied as a handwritten core. -/
def conditionalHelper (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  let put : HybridWord.Word → HybridWord.State → Option HybridWord.State :=
    fun value memory => some (memory.set 0 value)
  if s.regs 1 != 0 then put (s.regs 1) s else some s

run_cmd do
  let some input := NativeEnvironment.input (← getEnv) ``conditionalHelper | throwError "conditional two-argument helper environment"
  let .letE bn (.forallE dn _ (.forallE en _ _ ei) di) (.lam vn _ (.lam sn _ _ si) vi) _ flag := input.header.body
    | throwError "expected ordinary conditional two-argument helper"
  let expected := Lean.Expr.letE bn (.forallE dn word (.forallE en state (.app (.const ``Option [.zero]) state) ei) di)
    (.lam vn word (.lam sn state (Certificate.Return.Form.some.source
      (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,.bvar 1])) si) vi)
    (Certificate.Branch.source (app ``HybridWord.State.regs [.bvar 1,NatNotation.elaborated.native 1]) (Certificate.Branch.nativeBooleanDecision (app ``HybridWord.State.regs [.bvar 1,NatNotation.elaborated.native 1])) (.app (.app (.bvar 0) (app ``HybridWord.State.regs [.bvar 1,NatNotation.elaborated.native 1])) (.bvar 1)) (Certificate.Return.Form.some.source (.bvar 1))) flag
  let some shape := sameClosedHeader expected input.header.body | throwError "conditional two-argument source shape"
  let _ := FixedFunctionCompleteness.generatesRetainedSyntaxInstalled (ds := #[]) input (by
        intro env setup library installed closed fresh exposure
        rw [shape.down]
        exact two_helper_syntax setup library closed fresh exposure .word bn vn sn dn en vi si di ei flag true)
    (by rw [shape.down]; rfl) (by decide) [] (by decide) 0 .rolled
  logInfo "retained conditional State/scalar helper → one parameterized body family and general mixed layout → compileRetained → RTL generation"

hls_word conditionalHelper as conditionalHelperHLS
example : conditionalHelperHLS.wordBody = .branch (.reg 1) (.letValue (.reg 1) (.assign 0 (.local 0))) .skip := rfl

/-- The function expects BitVec 32 while the supplied register value infers
Word. The same source construction proves generation for both annotations. -/
def mixedArgumentHelper (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  let put : BitVec 32 → HybridWord.State → Option HybridWord.State :=
    fun value memory => some (memory.set 0 value)
  put (s.regs 1) s

hls_word mixedArgumentHelper as mixedArgumentHelperHLS
example : mixedArgumentHelperHLS.wordBody = .letValue (.reg 1) (.assign 0 (.local 0)) := rfl
example : (fun s => some (s.set 0 (s.regs 1))) = mixedArgumentHelper 0 0 0 := rfl

/-- The opposite alias direction: the argument infers BV32 and the helper
expects Word. The source rule derives all argument/body typing conditions. -/
def inlineMixedHelper (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  (fun (value : HybridWord.Word) => some (s.set 0 value)) (1 : BitVec 32)

-- Apply the retained-entry theorem to the same ordinary mixed-annotation
-- definition. This check supplies source syntax; neither the retained code
-- nor a successful parser run is a theorem premise.
run_cmd do
  let some input := NativeEnvironment.input (← getEnv) ``inlineMixedHelper | throwError "retained inline helper environment"
  let .app (.lam bn _ _ bi) _ := input.header.body | throwError "retained inline scalar helper"
  let actual := AnnotatedLiteral.native .bitvec 1
  let body := Certificate.Return.Form.some.source
    (app ``HybridWord.State.set [.bvar 1,NatNotation.elaborated.native 0,.bvar 0])
  let expected := Lean.Expr.app (.lam bn word body bi) actual
  let some shape := sameClosedHeader expected input.header.body | throwError "retained inline helper shape"
  let _ := FixedFunctionCompleteness.generatesRetainedSyntaxInstalled (ds := #[]) input (by
    intro env setup library installed closed fresh exposure
    rw [shape.down]
    let inputs := Certificate.initialInputs library.connection.word library.connection.nilWords
    let locals := ScalarSyntax.Locals.empty (env := env) (ctx := context) (p := parameters) rfl
    let p1 : Inputs := {parameters.lift with locals := .bvar 0::parameters.lift.locals}
    have value : LexicalScalarSyntax.Form env context parameters [] actual :=
      .annotatedLiteral .bitvec 1 ⟨by decide,by decide,by decide,by intro k; rfl⟩
    have openValue (a : WordBinder.Annotation) : LexicalScalarSyntax.Form env (a.core::context) p1 [] (.bvar 0) :=
      .localValue (.variable 0) 0 rfl (by decide) (by decide) (by decide) (by intro j hj; omega)
    apply FixedFunctionCompleteness.retainedScalarCallFromOpenBody setup library closed fresh exposure inputs locals
      LexicalScalarCode.ScopeTyped.initial .word (.lam bn word body bi) actual (by decide)
      (actual := actual) (depth := context.length) (captured := StructuralBody.Substitution.identity)
      (functions := FunctionSyntax.Scope.empty) (body := body)
      (functionBody := body)
    · exact FunctionSyntax.Scope.coherent_empty _ _
    · exact .lambda (.last (by intros; intro h; dsimp [body,Certificate.Return.Form.source,app] at h; cases h))
    · rfl
    · exact value
    · trivial
    · decide
    · intro a
      apply FunctionSyntax.Syntax.base (.assign .some rfl)
      change ScopedSyntax.Syntax env .body (a.core::context) p1 body (FixedSequenceCompleteness.InputConditions #[])
      exact .assign .some (NatNotation.elaborated.argument library.scalars.toSignatures 0) (openValue a)
        (.assign .some .elaborated 0 (by trivial))
    · exact .last (by intros; intro h; dsimp [body,Certificate.Return.Form.source,app] at h; cases h))
    (by rw [shape.down]; rfl) (by decide) [] (by decide) 0 .rolled
  logInfo "one open body, retained mixed-annotation helper → recursive Syntax/Source → compileRetained → Entry/RTL generation; code and type-conversion success are conclusions"

/-- The only supplied helper-body derivation includes a State binding.
Its original lambda type is reconstructed from that same retained body. -/
def retainedOpenStateHelper (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  (fun (value : HybridWord.Word) =>
    let t := s.set 0 7
    some (t.set 1 value)) (s.regs 0)

run_cmd do
  let some input := NativeEnvironment.input (← getEnv) ``retainedOpenStateHelper | throwError "open State helper environment"
  let .app (.lam bn _ (.letE tn _ _ _ flag) bi) _ := input.header.body | throwError "open State helper shape"
  let actual := app ``HybridWord.State.regs [parameters.s,NatNotation.elaborated.native 0]
  let body := Certificate.StateLet.source tn
    (app ``HybridWord.State.set [.bvar 1,NatNotation.elaborated.native 0,AnnotatedLiteral.native .word 7])
    (Certificate.Return.Form.some.source (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 1,.bvar 1])) flag
  let expected := Lean.Expr.app (.lam bn word body bi) actual
  let some same := sameClosedHeader expected input.header.body | throwError "open State helper elaboration"
  let _ := FixedFunctionCompleteness.generatesRetainedSyntaxInstalled (ds := #[]) input (by
    intro env setup library installed closed fresh exposure
    rw [same.down]
    let inputs := Certificate.initialInputs library.connection.word library.connection.nilWords
    let locals := ScalarSyntax.Locals.empty (env := env) (ctx := context) (p := parameters) rfl
    let p1 : Inputs := {parameters.lift with locals := .bvar 0::parameters.lift.locals}
    let p2 : Inputs := {p1.lift with s := .bvar 0}
    apply FixedFunctionCompleteness.retainedScalarCallFromOpenBody setup library closed fresh exposure inputs locals
      LexicalScalarCode.ScopeTyped.initial .word (.lam bn word body bi) actual (by decide)
      (actual := actual) (depth := context.length) (captured := StructuralBody.Substitution.identity)
      (functions := FunctionSyntax.Scope.empty) (body := body) (functionBody := body)
    · exact FunctionSyntax.Scope.coherent_empty _ _
    · exact .lambda (.last (by intros; intro h; dsimp [body,Certificate.StateLet.source] at h; cases h))
    · rfl
    · apply LexicalScalarSyntax.Form.register rfl
      · exact NatNotation.elaborated.argument library.scalars.toSignatures 0
      · exact ⟨rfl,rfl,rfl,by intro k; rfl⟩
    · exact ⟨⟨⟨0,.elaborated,rfl⟩⟩,by trivial⟩
    · rfl
    · intro a
      apply FunctionSyntax.Syntax.stateLet (binder := tn) (flag := flag)
      · refine FunctionSyntax.Syntax.valueAssign 0 .elaborated rfl ?_ (.valueAssign .elaborated 0 (by trivial))
        exact .annotatedLiteral .word 7 ⟨rfl,rfl,rfl,by intro k; cases k <;> rfl⟩
      · apply FunctionSyntax.Syntax.base (.assign .some rfl)
        change ScopedSyntax.Syntax env .body (Certificate.stateType::a.core::context) p2
          (Certificate.Return.Form.some.source (app ``HybridWord.State.set [p2.s,NatNotation.elaborated.native 1,.bvar 1])) _
        exact .assign .some (NatNotation.elaborated.argument library.scalars.toSignatures 1)
          (.localValue (.variable 1) 0 rfl (by decide) (by decide) (by decide) (by intro j hj; omega))
          (.assign .some .elaborated 1 (by trivial))
      · rfl
    · exact .last (by intros; intro h; dsimp [body,Certificate.StateLet.source] at h; cases h))
    (by rw [same.down]; rfl) (by decide) [] (by decide) 0 .rolled
  logInfo "one arbitrary open body with State update → original helper type and retained call → compileRetained → RTL generation"

hls_word retainedOpenStateHelper as retainedOpenStateHelperHLS
example : retainedOpenStateHelperHLS.wordBody =
    .letValue (.reg 0) (.seq (.assign 0 (.lit 7)) (.assign 1 (.local 0))) := rfl
example (s : HybridWord.State) :
    ((retainedOpenStateHelper 0 0 0 s).getD s).regs 1 = s.regs 0 := rfl

/-- Two call-time snapshots, mixed annotations, a captured State update and
an Option-valued read all use the arbitrary-arity open-body theorem. -/
def retainedTwoOpenBindings (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  (fun (first : HybridWord.Word) (second : BitVec 32) => do
    let t := s.set 0 7
    let old ← (t.arrays 0)[first.toNat]?
    let u := t.set 2 old
    some (u.set 1 second)) (s.regs 0) (s.regs 1)

run_cmd do
  let some input := NativeEnvironment.input (← getEnv) ``retainedTwoOpenBindings | throwError "two open bindings environment"
  let .app (.app (.lam firstName _ (.lam secondName _ (.letE tn _ _ readBody tflag) secondInfo) firstInfo) _) _ := input.header.body
    | throwError "two open bindings shape"
  let .lam oldName _ (.letE un _ _ _ uflag) oldInfo := readBody.getAppArgs.back!
    | throwError "two open bindings continuation"
  let first := app ``HybridWord.State.regs [parameters.s,NatNotation.elaborated.native 0]
  let second := app ``HybridWord.State.regs [parameters.s,NatNotation.elaborated.native 1]
  let body := Certificate.StateLet.source tn
    (app ``HybridWord.State.set [.bvar 2,NatNotation.elaborated.native 0,AnnotatedLiteral.native .word 7])
    (WordBinder.readSource .word (Read.wordSource (.bvar 0) (NatNotation.elaborated.native 0) (.bvar 2))
      (.lam oldName word (Certificate.StateLet.source un
        (app ``HybridWord.State.set [.bvar 1,NatNotation.elaborated.native 2,.bvar 0])
        (Certificate.Return.Form.some.source (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 1,.bvar 3])) uflag) oldInfo)) tflag
  let head := Lean.Expr.lam firstName word (.lam secondName WordBinder.Annotation.bitvec.native body secondInfo) firstInfo
  let expected := Lean.Expr.app (.app head first) second
  let some same := sameClosedHeader expected input.header.body | throwError "two open bindings elaboration"
  let _ := FixedFunctionCompleteness.generatesRetainedSyntaxInstalled (ds := #[(0,4)]) input (by
    intro env setup library installed closed fresh exposure
    rw [same.down]
    let inputs := Certificate.initialInputs library.connection.word library.connection.nilWords
    let locals := ScalarSyntax.Locals.empty (env := env) (ctx := context) (p := parameters) rfl
    apply FixedFunctionCompleteness.retainedScalarArgumentsFromOpenBody setup library closed fresh exposure inputs locals
      LexicalScalarCode.ScopeTyped.initial ScalarSyntax.ReferenceScope.initial .word [.bitvec]
      (.app head first) second (by decide)
      (depth := context.length) (captured := StructuralBody.Substitution.identity)
      (functions := FunctionSyntax.Scope.empty) (body := body) (functionBody := body)
    · exact FunctionSyntax.Scope.coherent_empty _ _
    · exact .lambda (.next (.last (by intros; intro h; dsimp [body,Certificate.StateLet.source] at h; cases h)))
    · rfl
    · intro raw member
      change raw ∈ [first,second] at member
      rcases List.mem_cons.mp member with sameRaw | member
      · subst raw
        refine ⟨.register rfl (NatNotation.elaborated.argument library.scalars.toSignatures 0) ?_,?_⟩
        · exact ⟨rfl,rfl,rfl,by intro k; rfl⟩
        · exact ⟨⟨⟨0,.elaborated,rfl⟩⟩,by trivial⟩
      · have same : raw = second := List.mem_singleton.mp member
        subst raw
        refine ⟨.register rfl (NatNotation.elaborated.argument library.scalars.toSignatures 1) ?_,?_⟩
        · exact ⟨rfl,rfl,rfl,by intro k; rfl⟩
        · exact ⟨⟨⟨1,.elaborated,rfl⟩⟩,by trivial⟩
    · intro annotations count
      rcases annotations with _ | ⟨a,rest⟩
      · simp at count
      rcases rest with _ | ⟨b,rest⟩
      · simp at count
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using count)
      subst rest
      simp only [List.map_cons,List.map_nil,FunctionSyntax.parameterInputs_scalar]
      let p0 : Inputs := {parameters.lift.lift with locals := [.bvar 0,.bvar 1]}
      let p1 : Inputs := {p0.lift with s := .bvar 0}
      let p2 : Inputs := {p1.lift with locals := .bvar 0::p1.lift.locals}
      let p3 : Inputs := {p2.lift with s := .bvar 0}
      apply FunctionSyntax.Syntax.stateLet (binder := tn) (flag := tflag)
      · exact FunctionSyntax.Syntax.valueAssign 0 .elaborated rfl
          (.annotatedLiteral .word 7 ⟨rfl,rfl,rfl,by intro k; cases k with | zero => rfl | succ k => cases k <;> rfl⟩)
          (.valueAssign .elaborated 0 (by trivial))
      · apply FunctionSyntax.Syntax.bindValue .word (binder := oldName) (info := oldInfo) (checked := ?_)
        · change ScopedSyntax.ReadForm env (Certificate.stateType::b.core::a.core::context) p1
            (Read.wordSource p1.s (NatNotation.elaborated.native 0) (.bvar 2))
          exact .word (NatNotation.elaborated.argument library.scalars.toSignatures 0)
            (.localValue (.variable 2) 1 rfl rfl rfl rfl
              (by
                intro j hj
                have h : j = 0 := by omega
                subst j
                rfl))
        · apply FunctionSyntax.Syntax.stateLet (binder := un) (flag := uflag)
          · exact FunctionSyntax.Syntax.valueAssign 2 .elaborated rfl
              (.localValue (.variable 0) 0 rfl rfl rfl rfl (by intro j hj; omega))
              (.valueAssign .elaborated 2 (by trivial))
          · apply FunctionSyntax.Syntax.base (.assign .some rfl)
            change ScopedSyntax.Syntax env .body (Certificate.stateType::Certificate.wordType::Certificate.stateType::b.core::a.core::context) p3
              (Certificate.Return.Form.some.source (app ``HybridWord.State.set [p3.s,NatNotation.elaborated.native 1,.bvar 3])) _
            exact .assign .some (NatNotation.elaborated.argument library.scalars.toSignatures 1)
              (.localValue (.variable 3) 1 rfl rfl rfl rfl
                (by
                intro j hj
                have h : j = 0 := by omega
                subst j
                rfl))
              (.assign .some .elaborated 1 (by trivial))
          · rfl
        · apply FixedSequenceCompleteness.InputConditions.readBind .word
          · exact FixedReadSourceCompleteness.Conditions.word .word 0 .elaborated (by decide) (by trivial)
          · trivial
      · rfl
    · exact .next (.last (by intros; intro h; dsimp [body,Certificate.StateLet.source] at h; cases h)))
    (by rw [same.down]; rfl) (by decide) [] (by decide) 0 .rolled
  logInfo "arbitrary-arity open-body theorem: two mixed-annotation snapshots + captured State + read binding → compileRetained → RTL generation"

hls_word retainedTwoOpenBindings as retainedTwoOpenBindingsHLS
example : retainedTwoOpenBindingsHLS.wordBody =
    .letValue (.reg 0) (.letValue (.reg 1)
      (.seq (.assign 0 (.lit 7)) (.letValue (.read 0 (.local 1))
        (.seq (.assign 2 (.local 0)) (.assign 1 (.local 1)))))) := rfl

example (s : HybridWord.State) : retainedTwoOpenBindings 0 0 0 s =
    ((s.arrays 0)[(s.regs 0).toNat]?).map
      (fun old => ((s.set 0 7).set 2 old).set 1 (s.regs 1)) := by
  simp only [retainedTwoOpenBindings,HybridWord.State.set]
  cases (s.arrays 0)[(s.regs 0).toNat]? <;> rfl

/-- The State formal contributes no retained scalar slot. The same body
construction works in both lambda and retained parameter placements. -/
def retainedMixedRead (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  (fun (first : HybridWord.Word) (second : BitVec 32) (memory : HybridWord.State) => do
    let t := memory.set 0 7
    let old ← (t.arrays 0)[first.toNat]?
    let u := t.set 2 old
    some (u.set 1 second)) (s.regs 0) (s.regs 1) s

run_cmd do
  let some input := NativeEnvironment.input (← getEnv) ``retainedMixedRead | throwError "mixed read environment"
  let .app (.app (.app (.lam fn _ (.lam sn _ (.lam mn _ (.letE tn _ _ readBody tf) mi) si) fi) _) _) _ := input.header.body
    | throwError "mixed read source shape"
  let .lam on _ (.letE un _ _ _ uf) oi := readBody.getAppArgs.back! | throwError "mixed read continuation"
  let first := app ``HybridWord.State.regs [parameters.s,NatNotation.elaborated.native 0]
  let second := app ``HybridWord.State.regs [parameters.s,NatNotation.elaborated.native 1]
  let body := Certificate.StateLet.source tn
    (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,AnnotatedLiteral.native .word 7])
    (WordBinder.readSource .word (Read.wordSource (.bvar 0) (NatNotation.elaborated.native 0) (.bvar 3))
      (.lam on word (Certificate.StateLet.source un
        (app ``HybridWord.State.set [.bvar 1,NatNotation.elaborated.native 2,.bvar 0])
        (Certificate.Return.Form.some.source (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 1,.bvar 4])) uf) oi)) tf
  let head := Lean.Expr.lam fn word (.lam sn WordBinder.Annotation.bitvec.native (.lam mn state body mi) si) fi
  let expected := Lean.Expr.app (.app (.app head first) second) parameters.s
  let some same := sameClosedHeader expected input.header.body | throwError "mixed read elaboration"
  let _ := FixedFunctionCompleteness.generatesRetainedSyntaxInstalled (ds := #[(0,4)]) input (by
    intro env setup library installed closed fresh exposure
    rw [same.down]
    let inputs := Certificate.initialInputs library.connection.word library.connection.nilWords
    apply FixedFunctionCompleteness.retainedArgumentsFromBodyFamily setup library closed fresh exposure
      inputs (ScalarSyntax.Locals.empty rfl) LexicalScalarCode.ScopeTyped.initial ScalarSyntax.ReferenceScope.initial
      (.app (.app head first) second) parameters.s (by decide)
      (domain := WordBinder.Annotation.word.core)
      (tailDomains := [WordBinder.Annotation.bitvec.core,Certificate.stateType])
      (nativeDomains := [word,WordBinder.Annotation.bitvec.native,state])
      (depth := context.length) (captured := StructuralBody.Substitution.identity) (arity := 3)
      (functions := FunctionSyntax.Scope.empty) (body := body) (functionBody := body)
    · exact FunctionSyntax.Scope.coherent_empty _ _
    · exact .lambda (.next (.next (.last (by intros; intro h; dsimp [body,Certificate.StateLet.source] at h; cases h))))
    · rfl
    · exact .cons (Or.inr ⟨.word,rfl,
          .register rfl (NatNotation.elaborated.argument library.scalars.toSignatures 0) ⟨rfl,rfl,rfl,by intro k; rfl⟩,
          ⟨⟨⟨0,.elaborated,rfl⟩⟩,by trivial⟩⟩)
        (.cons (Or.inr ⟨.bitvec,rfl,
          .register rfl (NatNotation.elaborated.argument library.scalars.toSignatures 1) ⟨rfl,rfl,rfl,by intro k; rfl⟩,
          ⟨⟨⟨1,.elaborated,rfl⟩⟩,by trivial⟩⟩) (.cons (Or.inl ⟨rfl,rfl⟩) .nil))
    · intro actual shapes openStates
      dsimp only
      intro _ _ _ _
      cases shapes with
      | cons firstShape tail => cases tail with
        | cons secondShape tail => cases tail with
          | cons stateShape tail =>
            cases tail
            rcases firstShape with ⟨bad,_⟩ | ⟨_,a,_,rfl⟩
            · simp [WordBinder.Annotation.core,Certificate.wordType,Certificate.stateType] at bad
            rcases secondShape with ⟨bad,_⟩ | ⟨_,b,_,rfl⟩
            · simp [WordBinder.Annotation.core,Arithmetic.bitvecType,Certificate.stateType] at bad
            rcases stateShape with ⟨_,rfl⟩ | ⟨c,d,bad,_⟩
            · simp only [FunctionSyntax.parameterLayout_scalar,FunctionSyntax.parameterLayout_state]
              let scalarInputs : Inputs := {parameters.lift.lift with locals := [.bvar 0,.bvar 1]}
              let frame : List Lean4Lean.VExpr × Inputs × List Lean.Expr := if openStates then
                (Certificate.stateType::b.core::a.core::context,{scalarInputs.lift with s := .bvar 0},[.bvar 2,.bvar 1,.bvar 0])
                else (b.core::a.core::context,scalarInputs,[.bvar 1,.bvar 0,scalarInputs.s])
              let p1 : Inputs := {frame.2.1.lift with s := .bvar 0}
              let p2 : Inputs := {p1.lift with locals := .bvar 0::p1.lift.locals}
              let p3 : Inputs := {p2.lift with s := .bvar 0}
              let firstIndex := if openStates then 3 else 2
              let secondIndex := if openStates then 4 else 3
              change FunctionSyntax.Syntax env frame.1 frame.2.1
                (StructuralBody.closureSubstitution context.length frame.1.length .identity frame.2.2)
                (FunctionSyntax.Scope.empty.parameters frame.2.2.length) body _
              apply FunctionSyntax.Syntax.stateLet (binder := tn) (flag := tf)
              · exact FunctionSyntax.Syntax.valueAssign 0 .elaborated (by cases openStates <;> rfl)
                  (.annotatedLiteral .word 7 ⟨by cases openStates <;> rfl,by cases openStates <;> rfl,
                    by cases openStates <;> rfl,by intro k; cases openStates <;> cases k with
                      | zero => rfl
                      | succ k => cases k <;> rfl⟩)
                  (.valueAssign .elaborated 0 (by cases openStates <;> trivial))
              · apply FunctionSyntax.Syntax.bindValue .word (binder := on) (info := oi) (checked := ?_)
                · have read : ScopedSyntax.ReadForm env (Certificate.stateType::frame.1) p1
                      (Read.wordSource p1.s (NatNotation.elaborated.native 0) (.bvar firstIndex)) :=
                    .word (NatNotation.elaborated.argument library.scalars.toSignatures 0)
                      (.localValue (.variable firstIndex) 1 (by cases openStates <;> rfl)
                        (by cases openStates <;> rfl) (by cases openStates <;> rfl) (by cases openStates <;> rfl)
                        (by
                          intro j hj
                          have h : j = 0 := by omega
                          subst j
                          cases openStates <;> rfl))
                  refine Eq.mp ?_ read
                  congr 1 <;> cases openStates <;> rfl
                · apply FunctionSyntax.Syntax.stateLet (binder := un) (flag := uf)
                  · exact FunctionSyntax.Syntax.valueAssign 2 .elaborated rfl
                      (.localValue (.variable 0) 0 rfl (by cases openStates <;> rfl)
                        (by cases openStates <;> rfl) (by cases openStates <;> rfl) (by intro j hj; omega))
                      (.valueAssign .elaborated 2 (by trivial))
                  · apply FunctionSyntax.Syntax.base (.assign .some rfl)
                    have last : ScopedSyntax.Syntax env .body
                        (Certificate.stateType::Certificate.wordType::Certificate.stateType::frame.1) p3
                        (Certificate.Return.Form.some.source
                          (app ``HybridWord.State.set [p3.s,NatNotation.elaborated.native 1,.bvar secondIndex]))
                        (FixedSequenceCompleteness.InputConditions #[(0,4)]) :=
                      .assign .some (NatNotation.elaborated.argument library.scalars.toSignatures 1)
                        (.localValue (.variable secondIndex) 1 (by cases openStates <;> rfl)
                          (by cases openStates <;> rfl) (by cases openStates <;> rfl) (by cases openStates <;> rfl)
                          (by
                            intro j hj
                            have h : j = 0 := by omega
                            subst j
                            cases openStates <;> rfl))
                        (.assign .some .elaborated 1 (by cases openStates <;> trivial))
                    refine Eq.mp ?_ last
                    congr 1 <;> cases openStates <;> rfl
                  · rfl
                · apply FixedSequenceCompleteness.InputConditions.readBind .word
                  · exact FixedReadSourceCompleteness.Conditions.word .word 0 .elaborated (by decide) (by cases openStates <;> trivial)
                  · cases openStates <;> trivial
              · cases openStates <;> rfl
            · cases c <;> simp [WordBinder.Annotation.core,Certificate.wordType,Arithmetic.bitvecType,Certificate.stateType] at bad
    · exact .next (.next (.last (by intros; intro h; dsimp [body,Certificate.StateLet.source] at h; cases h)))
    · exact .cons WordBinder.Annotation.word.represented
        (.cons WordBinder.Annotation.bitvec.represented (.cons (.constant rfl) .nil)))
    (by rw [same.down]; rfl) (by decide) [] (by decide) 0 .rolled
  logInfo "mixed State/scalar source + read/State bindings → one body family → compileRetained → RTL generation"

hls_word retainedMixedRead as retainedMixedReadHLS
example : retainedMixedReadHLS.wordBody = retainedTwoOpenBindingsHLS.wordBody := rfl
example (s : HybridWord.State) : retainedMixedRead 0 0 0 s = retainedTwoOpenBindings 0 0 0 s := rfl

/-- A named helper remains abstract while its continuation updates State,
reads an array, binds the result, updates State again, and calls the helper. -/
def helperReadContinuation (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let finish := fun (t : HybridWord.State) => some (t.set 2 (t.regs 1))
  let t := s.set 0 7
  let old ← (t.arrays 0)[(0 : HybridWord.Word).toNat]?
  let u := t.set 1 old
  finish u

run_cmd do
  let some input := NativeEnvironment.input (← getEnv) ``helperReadContinuation | throwError "paired continuation environment"
  let .letE fn fty (.lam tn _ _ ti) (.letE sn _ _ readBody sf) ff := input.header.body
    | throwError "paired continuation header"
  let .forallE dn _ _ di := fty | throwError "paired helper type"
  let fty := Lean.Expr.forallE dn state (.app (.const ``Option [.zero]) state) di
  let .lam vn _ (.letE un _ _ _ uf) vi := readBody.getAppArgs.back! | throwError "paired read continuation"
  let fbody := Certificate.Return.Form.some.source
    (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 2,
      app ``HybridWord.State.regs [.bvar 0,NatNotation.elaborated.native 1]])
  let value := Lean.Expr.lam tn state fbody ti
  let call := Lean.Expr.app (.bvar 3) (.bvar 0)
  let next := Certificate.StateLet.source un
    (app ``HybridWord.State.set [.bvar 1,NatNotation.elaborated.native 1,.bvar 0]) call uf
  let read := WordBinder.readSource .word
    (Read.wordSource (.bvar 0) (NatNotation.elaborated.native 0) (AnnotatedLiteral.native .word 0))
    (.lam vn word next vi)
  let tail := Certificate.StateLet.source sn
    (app ``HybridWord.State.set [.bvar 1,NatNotation.elaborated.native 0,AnnotatedLiteral.native .word 7]) read sf
  let expected := Lean.Expr.letE fn fty value tail ff
  let some same := sameClosedHeader expected input.header.body | throwError "paired continuation elaboration"
  let _ := FixedFunctionCompleteness.generatesRetainedSyntaxInstalled (ds := #[(0,4)]) input (by
    intro env setup library installed closed fresh exposure
    rw [same.down]
    have one : Nonempty (NatNotation.View (NatNotation.elaborated.native 1)) := ⟨⟨1,.elaborated,rfl⟩⟩
    let inputs := Certificate.initialInputs library.connection.word library.connection.nilWords
    let functionType := Lean4Lean.VExpr.forallE Certificate.stateType (Certificate.optionType Certificate.stateType)
    let p1 : Inputs := {parameters.lift with s := .bvar 0}
    let p2 : Inputs := {p1.lift with locals := .bvar 0::p1.lift.locals}
    let p3 : Inputs := {p2.lift with s := .bvar 0}
    let o0 : Inputs := parameters.lift
    let o1 : Inputs := {o0.lift with s := .bvar 0}
    let o2 : Inputs := {o1.lift with locals := .bvar 0::o1.lift.locals}
    let o3 : Inputs := {o2.lift with s := .bvar 0}
    let oi0 := inputs.lift closed functionType
    let oi1 := oi0.nextState closed
    let oi2 := WordBinder.Annotation.word.nextInputs oi1 closed library.scalars.toSignatures library.cons
    let oi3 := oi2.nextState closed
    let ol0 : ScalarSyntax.Locals env (functionType::context) o0 := .empty rfl
    let ol1 := ol0.nextState closed
    let ol2 := WordBinder.Annotation.word.nextLocals ol1 closed
    let ol3 := ol2.nextState closed
    have binding : FunctionSyntax.BindingValue .empty context.length .identity value
        (.captured context.length .identity 1 fbody .empty) := .lambda (.last (by intros; intro h; dsimp [fbody,Certificate.Return.Form.source,Certificate.Return.Form.nativeHeader,app] at h; cases h))
    have functionSource : FunctionSyntax.Syntax env (Certificate.stateType::context) p1
        .identity .empty fbody := by
      apply FunctionSyntax.Syntax.base (.assign .some rfl)
      exact .assign .some (NatNotation.elaborated.argument library.scalars.toSignatures 2)
        (.register rfl (NatNotation.elaborated.argument library.scalars.toSignatures 1)
          (ScalarSyntax.ReferenceScope.initial.state.separated rfl (by decide)))
    apply FunctionSyntax.Syntax.functionLetFromLambdaPaired .body (by decide) setup library closed fresh exposure
      fn fty value tail ff (domain := Certificate.stateType) (domains := [])
      (functionSource := functionSource)
    · exact binding
    · apply FunctionSyntax.Syntax.stateLetPaired library .body (by decide)
      · apply FunctionSyntax.Syntax.valueAssignPaired setup library closed fresh exposure oi0 ol0 0 .elaborated rfl rfl
        · exact ⟨.annotatedLiteral .word 7 (ScalarSyntax.ReferenceScope.initial.separated rfl (by decide)),
            .annotatedLiteral .word 7 (ScalarSyntax.ReferenceScope.initial.lift.separated rfl (by decide))⟩
        · exact .valueAssign .elaborated 0 (by trivial)
      · apply FunctionSyntax.Syntax.bindValuePaired setup library closed fresh exposure oi1 ol1 .word (binder := vn) (info := vi)
        · exact ⟨.word (NatNotation.elaborated.argument library.scalars.toSignatures 0)
              (.annotatedLiteral .word 0 (ScalarSyntax.ReferenceScope.initial.state.separated rfl (by decide))),
            .word (NatNotation.elaborated.argument library.scalars.toSignatures 0)
              (.annotatedLiteral .word 0 (ScalarSyntax.ReferenceScope.initial.lift.state.separated rfl (by decide)))⟩
        · apply FunctionSyntax.Syntax.stateLetPaired library .body (by decide)
          · apply FunctionSyntax.Syntax.valueAssignPaired setup library closed fresh exposure oi2 ol2 1 .elaborated rfl rfl
            · exact ⟨.localValue (.variable 0) 0 rfl rfl rfl rfl (by intro j hj; omega),
                .localValue (.variable 0) 0 rfl rfl rfl rfl (by intro j hj; omega)⟩
            · exact .valueAssign .elaborated 1 (by trivial)
          · refine ⟨?_,?_⟩
            · apply FixedFunctionCompleteness.retainedArgumentsFromBodyFamily setup library closed fresh exposure
                ((WordBinder.Annotation.word.nextInputs (inputs.nextState closed) closed library.scalars.toSignatures library.cons).nextState closed)
                ((WordBinder.Annotation.word.nextLocals ((ScalarSyntax.Locals.empty rfl).nextState closed) closed).nextState closed)
                ((LexicalScalarCode.ScopeTyped.initial.nextState closed).nextWord closed .word |>.nextState closed)
                ScalarSyntax.ReferenceScope.initial.state.scalar.state (.bvar 3) (.bvar 0) (by decide)
                (domain := Certificate.stateType) (tailDomains := []) (nativeDomains := [state])
                (depth := context.length) (captured := StructuralBody.Substitution.identity) (arity := 1)
                (functions := FunctionSyntax.Scope.empty) (body := fbody) (functionBody := fbody)
              · exact (((FunctionSyntax.Scope.coherent_empty _ _).functionLet binding).under.under.under)
              · exact .reuse rfl
              · rfl
              · exact .cons (Or.inl ⟨rfl,rfl⟩) .nil
              · intro actual shapes openStates
                cases shapes with
                | cons shape rest =>
                  cases rest
                  rcases shape with ⟨_,rfl⟩ | ⟨a,b,bad,_⟩
                  · dsimp only
                    intro fi fl ft refs
                    cases openStates <;> apply FunctionSyntax.Syntax.base (.assign .some rfl)
                    all_goals
                      exact .assign .some (NatNotation.elaborated.argument library.scalars.toSignatures 2)
                        (.register rfl (NatNotation.elaborated.argument library.scalars.toSignatures 1)
                          (refs.separated rfl (by decide)))
                        (.assign .some .elaborated 2 (by
                          change LexicalScalarSyntax.StaticRegisters (Certificate.Return.Form.some.source
                            (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 2,
                              app ``HybridWord.State.regs [.bvar 0,NatNotation.elaborated.native 1]]))
                          simp [LexicalScalarSyntax.StaticRegisters,Certificate.Return.Form.source,
                            Certificate.Return.Form.nativeHeader,app,one] <;> trivial))
                  · cases a <;> simp [WordBinder.Annotation.core,Certificate.wordType,Arithmetic.bitvecType,Certificate.stateType] at bad
              · exact .last (by intros; intro h; dsimp [fbody,Certificate.Return.Form.source,Certificate.Return.Form.nativeHeader,app] at h; cases h)
              · exact .cons (.constant rfl) .nil
            · exact FixedFunctionCompleteness.boundCallTypingFromSyntax library closed oi3
                (((LexicalScalarCode.ScopeTyped.initial.lift closed functionType).nextState closed).nextWord closed .word |>.nextState closed)
                (domains := [Certificate.stateType]) (rawArgs := [.bvar 0]) (index := 3)
                (.cons (Or.inl ⟨rfl,rfl⟩) .nil) rfl
          · rfl
        · apply FixedSequenceCompleteness.InputConditions.readBind .word
          · exact FixedReadSourceCompleteness.Conditions.word .word 0 .elaborated (by decide) (by trivial)
          · simp [LexicalScalarSyntax.StaticRegisters,WordBinder.readSource,bindHead,Read.wordSource,Read.source,Read.nativeHeader,
              Read.nativeArray,Read.nativeValidity,Read.wordIndex,AnnotatedLiteral.native,
              next,call,value,fbody,Certificate.StateLet.source,Certificate.Return.Form.source,Certificate.Return.Form.nativeHeader,
              app,StructuralBody.letSubstitution,StructuralBody.under,StructuralBody.Substitution.apply,
              StructuralBody.Substitution.reference,LeanBindings.substitute,LeanBindings.underSubst,word,state,
              Lean.mkApp2,Lean.mkAppB,Arithmetic.nativeWidth,WordBinder.Annotation.native,LeanBindings.rename,one] <;> trivial
      · rfl
    · exact inputs.nextState closed
    · exact .empty rfl
    · exact .last (by intros; intro h; dsimp [fbody,Certificate.Return.Form.source,Certificate.Return.Form.nativeHeader,app] at h; cases h)
    · exact .cons (.constant rfl) .nil
    · intro d hd
      have same : d = Certificate.stateType := by simpa using hd
      subst d
      exact ⟨_,LeanTypeInference.CastTyping.constant library.returns.state (by simp) rfl⟩
    · change LeanTyped.Represents fty (.forallE Certificate.stateType (Certificate.optionType Certificate.stateType))
      exact .forallE (.constant rfl) (.app (.constant rfl) (.constant rfl)))
    (by rw [same.down]; rfl) (by decide) [] (by decide) 0 .rolled
  logInfo "function-let with State/read/State continuation → paired general composition → compileRetained → RTL generation"

hls_word helperReadContinuation as helperReadContinuationHLS
example (s : HybridWord.State) : helperReadContinuation 0 0 0 s =
    ((s.arrays 0)[0]?).map (fun v => ((s.set 0 7).set 1 v).set 2 v) := by
  cases h : (s.arrays 0)[0]? <;> simp [helperReadContinuation,HybridWord.State.set,h]

/-- The helper is bound outside the loop. Its abstract source slot and the
retained closure remain aligned across the counter, State and do binders. -/
def helperLoopContinuation (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  let helper : HybridWord.State → Option HybridWord.State := fun u => some u
  ForIn.forIn (HybridWord.range 0 3 1) s (fun k t => do
    let u ← helper t
    pure (.yield (u.set 0 k)))

open Certificate in
run_cmd do
  let some input := NativeEnvironment.input (← getEnv) ``helperLoopContinuation | throwError "paired loop environment"
  let .letE fn (.forallE dn _ _ di) (.lam hn _ _ hi) loop ff := input.header.body
    | throwError "paired loop helper"
  let .lam kn _ (.lam tn _ seq ti) ki := loop.getAppArgs.back! | throwError "paired loop body"
  let .lam un _ _ ui := seq.getAppArgs.back! | throwError "paired loop bind"
  let fbody := Certificate.Return.Form.some.source (.bvar 0)
  let value := Lean.Expr.lam hn state fbody hi
  let fty := Lean.Expr.forallE dn state (.app (.const ``Option [.zero]) state) di
  let call := Lean.Expr.app (.bvar 2) (.bvar 0)
  let step := StructuralStep.sequenceSource call (.lam un state
    (Step.yieldSource (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,.bvar 2])) ui)
  let tail := For.source (For.nativeNatural 0) (For.nativeNatural 3) (For.nativeNatural 1) (.bvar 1)
    (.lam kn word (.lam tn state step ti) ki)
  let expected := Lean.Expr.letE fn fty value tail ff
  let some same := sameClosedHeader expected input.header.body | throwError "paired loop elaboration"
  let _ := FixedFunctionCompleteness.generatesRetainedSyntaxInstalled (ds := #[]) input (by
    intro env setup library installed closed fresh exposure
    rw [same.down]
    let inputs := Certificate.initialInputs library.connection.word library.connection.nilWords
    let functionType := Lean4Lean.VExpr.forallE Certificate.stateType (Certificate.optionType Certificate.stateType)
    let oi0 := inputs.lift closed functionType
    let oi1 := For.nextInputs oi0 closed library.scalars.word library.cons
    let ol0 : ScalarSyntax.Locals env (functionType::context) parameters.lift := .empty rfl
    let ol1 := (ol0.nextWord closed).nextState closed
    have binding : FunctionSyntax.BindingValue .empty context.length .identity value
        (.captured context.length .identity 1 fbody .empty) :=
      .lambda (.last (by intros; intro h; dsimp [fbody,Certificate.Return.Form.source,Certificate.Return.Form.nativeHeader,app] at h; cases h))
    have functionSource : FunctionSyntax.Syntax env (Certificate.stateType::context)
        {parameters.lift with s := .bvar 0} .identity .empty fbody :=
      .base (.returns .some rfl) (.atom (.returns .some))
    apply FunctionSyntax.Syntax.functionLetFromLambdaPaired .body (by decide) setup library closed fresh exposure
      fn fty value tail ff (domain := Certificate.stateType) (domains := []) (functionSource := functionSource)
    · exact binding
    · apply FunctionSyntax.Syntax.forStaticPaired library oi0
        ⟨For.Bound.natural library.bounds 0,For.Bound.natural library.bounds 0⟩
        ⟨For.Bound.natural library.bounds 3,For.Bound.natural library.bounds 3⟩
        ⟨For.Bound.natural library.bounds 1,For.Bound.natural library.bounds 1⟩ rfl rfl
        (kn := kn) (tn := tn) (ki := ki) (ti := ti)
      · apply FunctionSyntax.Syntax.stepSequencePaired library (binder := un) (info := ui)
        · refine ⟨?_,?_⟩
          · apply FixedFunctionCompleteness.retainedArgumentsFromBodyFamily setup library closed fresh exposure
              (For.nextInputs inputs closed library.scalars.word library.cons)
              (((show ScalarSyntax.Locals env context parameters from .empty rfl).nextWord closed).nextState closed)
              (LexicalScalarCode.ScopeTyped.initial.forStatic closed) ScalarSyntax.ReferenceScope.initial.forStatic
              (.bvar 2) (.bvar 0) (by decide)
              (domain := Certificate.stateType) (tailDomains := []) (nativeDomains := [state])
              (depth := context.length) (captured := StructuralBody.Substitution.identity) (arity := 1)
              (functions := FunctionSyntax.Scope.empty) (body := fbody) (functionBody := fbody)
            · exact ((FunctionSyntax.Scope.coherent_empty _ _).functionLet binding).under.under
            · exact .reuse rfl
            · rfl
            · exact .cons (Or.inl ⟨rfl,rfl⟩) .nil
            · intro actual shapes openStates
              cases shapes with
              | cons shape rest =>
                cases rest
                rcases shape with ⟨_,rfl⟩ | ⟨a,b,bad,_⟩
                · dsimp only
                  intro _ _ _ _
                  cases openStates <;> apply FunctionSyntax.Syntax.base (.returns .some rfl)
                  all_goals
                    have checked := FixedSequenceCompleteness.InputConditions.returnVariable (ds := #[]) .some 0
                    exact .atom (.returns .some (checked := checked)) (checked := checked)
                · cases a <;> simp [WordBinder.Annotation.core,Certificate.wordType,Arithmetic.bitvecType,Certificate.stateType] at bad
            · exact .last (by intros; intro h; dsimp [fbody,Certificate.Return.Form.source,Certificate.Return.Form.nativeHeader,app] at h; cases h)
            · exact .cons (.constant rfl) .nil
          · exact FixedFunctionCompleteness.boundCallTypingFromSyntax library closed oi1
              ((LexicalScalarCode.ScopeTyped.initial.lift closed functionType).forStatic closed)
              (domains := [Certificate.stateType]) (rawArgs := [.bvar 0]) (index := 2)
              (.cons (Or.inl ⟨rfl,rfl⟩) .nil) rfl
        · apply FunctionSyntax.Syntax.yieldPaired library
          apply FunctionSyntax.Syntax.valueAssignPaired setup library closed fresh exposure
            (oi1.nextState closed) (ol1.nextState closed) 0 .elaborated rfl rfl
          · exact ⟨.localValue (.variable 2) 0 rfl rfl rfl rfl (by intro j hj; omega),
              .localValue (.variable 2) 0 rfl rfl rfl rfl (by intro j hj; omega)⟩
          · exact .valueAssign .elaborated 0 (by trivial)
      · exact FixedSequenceCompleteness.InputConditions.forStatic
          (.natural 0) (.natural 3) (.natural 1) (by repeat constructor)
    · exact inputs.nextState closed
    · exact .empty rfl
    · exact .last (by intros; intro h; dsimp [fbody,Certificate.Return.Form.source,Certificate.Return.Form.nativeHeader,app] at h; cases h)
    · exact .cons (.constant rfl) .nil
    · intro d hd
      have same : d = Certificate.stateType := by simpa using hd
      subst d
      exact ⟨_,LeanTypeInference.CastTyping.constant library.returns.state (by simp) rfl⟩
    · exact .forallE (.constant rfl) (.app (.constant rfl) (.constant rfl)))
    (by rw [same.down]; rfl) (by decide) [] (by decide) 0 .rolled
  logInfo "function-let → loop with captured call, do bind and State update → paired general rules → compileRetained → RTL generation"

hls_word helperLoopContinuation as helperLoopContinuationHLS
example : helperLoopContinuationHLS.wordBody = .forStatic 0 3 1 (.seq .skip (.assign 0 (.local 0))) := rfl

/-- The two native iterator layouts exercise the same paired loop rule. The
runtime bound is read before entering the loop, not unfolded during parsing. -/
def naturalForIdentity (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  ForIn.forIn (List.range (s.regs 0).toNat) s (fun _ t => pure (.yield t))

def naturalFoldIdentity (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  (List.range (s.regs 0).toNat).foldlM (fun t _ => some t) s

open Certificate in
run_cmd do
  for (name,kind) in [(``naturalForIdentity,NaturalLoop.Kind.forIn),(``naturalFoldIdentity,NaturalLoop.Kind.fold)] do
    let some input := NativeEnvironment.input (← getEnv) name | throwError "natural paired environment"
    let nativeFn := match kind with
      | .forIn => input.header.body.getAppArgs.back!
      | .fold => input.header.body.getAppArgs[4]!
    let .lam kn _ (.lam tn _ _ ti) ki := nativeFn | throwError "natural paired binders"
    let count := app ``HybridWord.State.regs [parameters.s,NatNotation.elaborated.native 0]
    let raw := match kind with
      | .forIn => Step.yieldSource (.bvar 0)
      | .fold => Return.Form.some.source (.bvar 1)
    let expected := kind.source count parameters.s (kind.nativeLambda kn tn ki ti raw)
    let some same := sameClosedHeader expected input.header.body | throwError "natural paired elaboration"
    let _ := FixedFunctionCompleteness.generatesRetainedSyntaxInstalled (ds := #[]) input (by
      intro env setup library installed closed fresh exposure
      rw [same.down]
      let inputs := initialInputs library.connection.word library.connection.nilWords
      let locals : ScalarSyntax.Locals env context parameters := .empty rfl
      have nextInputs := kind.nextInputs inputs closed library.scalars.toSignatures library.naturalLoops library.cons
      have nextLocals := kind.nextLocals locals closed library.scalars.toSignatures library.naturalLoops
      have countForm : LexicalScalarSyntax.Form env context parameters [] count :=
        .register rfl (NatNotation.elaborated.argument library.scalars.toSignatures 0)
          (ScalarSyntax.ReferenceScope.initial.separated rfl (by decide))
      have static : LexicalScalarSyntax.StaticRegisters count := by
        change Nonempty (NatNotation.View (NatNotation.elaborated.native 0)) ∧ _
        exact ⟨⟨⟨0,.elaborated,rfl⟩⟩,by trivial⟩
      have paired : FunctionSyntax.Syntax env (mode := kind.mode)
          (kind.context context) (kind.parameters parameters)
          (StructuralBody.under (StructuralBody.under .identity)) (.push none (.push none .empty)) raw
          (FixedSequenceCompleteness.InputConditions #[]) ∧
          ∃ core, LeanTyped.Represents raw core ∧
            LeanTypeInference.CastTyping env 0 (Arithmetic.SourceCasts env) (kind.context context) core
              (FunctionSyntax.sourceResultType kind.mode) := by
        cases kind with
        | forIn =>
          exact FunctionSyntax.Syntax.yieldPaired (τ := StructuralBody.Substitution.identity) library
            (FunctionSyntax.Syntax.valueCurrentPaired (τ := StructuralBody.Substitution.identity) (raw := .bvar 0) nextInputs rfl rfl)
        | fold =>
          have form : FunctionSyntax.Syntax env (mode := .body)
              (NaturalLoop.Kind.fold.context context) (NaturalLoop.Kind.fold.parameters parameters)
              (StructuralBody.under (StructuralBody.under .identity)) (.push none (.push none .empty)) raw
              (FixedSequenceCompleteness.InputConditions #[]) :=
            .base (.returns .some rfl) (.atom (.returns .some (.returnVariable .some 1)) (.returnVariable .some 1))
          exact ⟨form,form.sourceTyping setup library closed fresh exposure nextInputs nextLocals⟩
      have zeroView : Nonempty (NatNotation.View (NatNotation.elaborated.native 0)) := ⟨⟨0,.elaborated,rfl⟩⟩
      have built := FunctionSyntax.Syntax.forRangePaired (σ := StructuralBody.Substitution.identity)
        (τ := StructuralBody.Substitution.identity) library inputs LexicalScalarCode.ScopeTyped.initial kind
        ⟨countForm,countForm⟩ static rfl rfl paired kn tn ki ti
        (FixedSequenceCompleteness.InputConditions.forRange kind (by
          cases kind <;>
            simp [expected,count,raw,NaturalLoop.Kind.source,NaturalLoop.Kind.nativeHeader,NaturalLoop.nativeFoldHeader,
              NaturalLoop.Kind.nativeLambda,NaturalLoop.Kind.first,NaturalLoop.Kind.second,NaturalLoop.nativeRange,
              For.Header.At.nativeHeader,Step.yieldSource,Return.nativePureInstance,stepType,Return.Form.source,
              Return.Form.nativeHeader,Read.wordIndex,LexicalScalarSyntax.StaticRegisters,app,
              parameters,state,Arithmetic.nativeWidth,zeroView] <;> trivial))
      exact built.1)
      (by rw [same.down]; cases kind <;> rfl) (by decide) [] (by decide) 0 .rolled
    logInfo m!"{name}: native iterator layout → paired arbitrary-body rule → compileRetained → RTL generation"

hls_word naturalForIdentity as naturalForIdentityHLS
hls_word naturalFoldIdentity as naturalFoldIdentityHLS
example : naturalForIdentityHLS.wordBody = naturalFoldIdentityHLS.wordBody := rfl

hls_word inlineMixedHelper as inlineMixedHelperHLS
example : inlineMixedHelperHLS.wordBody = .letValue (.lit 1) (.assign 0 (.local 0)) := rfl
example : (fun s => some (s.set 0 1)) = inlineMixedHelper 0 0 0 := rfl

/-- The input proof below supplies syntax, typing and source scope only.
Its native-computation index and generated Source/Entry are derived. -/
def sourceConstructedState (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 (let value : BitVec 32 := s.regs 1; value))

open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic in
private theorem register_identity_form (annotation : WordBinder.Annotation) (register : Nat)
    (rn : NatNotation) (binder : Lean.Name) (flag : Bool) :
    LexicalScalarSyntax.Form StandardLibrary.model context parameters []
      (.letE binder annotation.native (app ``HybridWord.State.regs [parameters.s,rn.native register]) (.bvar 0) flag) := by
  apply LexicalScalarSyntax.Form.letFromOpen (vs := []) StandardLibrary.library.scalars StandardLibrary.library.decisions StandardLibrary.closed
    (initialInputs StandardLibrary.library.connection.word StandardLibrary.library.connection.nilWords)
    LexicalScalarCode.ScopeTyped.initial ScalarSyntax.ReferenceScope.initial (by intro e h; cases h) annotation
  · apply LexicalScalarSyntax.Form.register rfl
      (by simpa only [LexicalScalarCode.sources,List.map_nil,LexicalScalarSyntax.expand_nil] using rn.argument (ctx := context) StandardLibrary.library.scalars.toSignatures register)
    simp only [LexicalScalarCode.sources,List.map_nil,LexicalScalarSyntax.expand_nil]
    cases rn <;> exact ⟨rfl,rfl,rfl,by intro k; rfl⟩
  · exact ⟨⟨⟨register,rn,rfl⟩⟩,trivial⟩
  · intro a
    exact .reference rfl
  · trivial

hls_word sourceConstructedState as sourceConstructedStateHLS
example : sourceConstructedStateHLS.wordBody = .assign 0 (.reg 1) := rfl

/-- A nested lexical value is used by mixed-annotation arithmetic. Only the
computation-free syntax and its source scope are supplied to generation. -/
def sourceConstructedMixed (_i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State :=
  some (s.set 0 ((let value : BitVec 32 := s.regs 1; value) + 1))

hls_word sourceConstructedMixed as sourceConstructedMixedHLS
example : sourceConstructedMixedHLS.wordBody = .assign 0 (.add (.reg 1) (.lit 1)) := rfl

open Certificate in
private theorem transfer_input_conditions : FixedSequenceCompleteness.InputConditions #[(0,4),(1,4)]
    (app ``HybridWord.State.copy [parameters.s,NatNotation.elaborated.native 1,NatNotation.elaborated.native 0,NatNotation.elaborated.native 4]) := by
  constructor
  · simp [LexicalScalarSyntax.StaticRegisters,app,parameters,NatNotation.native]
  · intro tag st r v h
    cases tag <;> simp [Return.Form.source,Return.Form.nativeHeader,app,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro st r v h; simp [app,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro st a k v h; simp [app,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro st d o n h
    simp only [app,List.foldl_cons,List.foldl_nil,Lean.Expr.app.injEq,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
    obtain ⟨⟨⟨⟨_,_⟩,hd⟩,ho⟩,hn⟩ := h
    exact ⟨1,0,4,.elaborated,.elaborated,.elaborated,hd.symm,ho.symm,hn.symm,rfl,rfl⟩
  · intro annotation v fn h; cases annotation <;> simp [app,WordBinder.readSource,bindHead,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro annotation v fn h; cases annotation <;> simp [app,WordBinder.stepReadSource,bindHead,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h
  · intro a b c st fn h; simp [app,For.source,For.nativeHeader,Lean.mkApp5,Lean.mkApp4,Lean.mkApp3,Lean.mkApp2,Lean.mkApp,Lean.mkAppB] at h

run_cmd do
  let some input := NativeEnvironment.input (← getEnv) ``transfer
    | throwError "transfer environment could not be prepared"
  have form : ScopedSyntax.Form StandardLibrary.model context parameters
      (app ``HybridWord.State.copy [parameters.s,NatNotation.elaborated.native 1,NatNotation.elaborated.native 0,NatNotation.elaborated.native 4])
      (FixedSequenceCompleteness.InputConditions regions) :=
    .atom (.copy
      (NatNotation.elaborated.argument StandardLibrary.library.scalars.toSignatures 1)
      (NatNotation.elaborated.argument StandardLibrary.library.scalars.toSignatures 0)
      (NatNotation.elaborated.argument StandardLibrary.library.scalars.toSignatures 4)
      transfer_input_conditions) transfer_input_conditions
  let expected := app ``HybridWord.State.copy [parameters.s,NatNotation.elaborated.native 1,NatNotation.elaborated.native 0,NatNotation.elaborated.native 4]
  let some same := sameClosedHeader expected input.header.body
    | throwError "transfer source spelling differs from its source syntax"
  have inputForm := Eq.mp (congrArg (fun raw => ScopedSyntax.Form StandardLibrary.model context parameters raw
      (FixedSequenceCompleteness.InputConditions regions)) same.down.symm) form
  have scope_ok : LeanScalar.wellScoped 1 input.header.body = true := by rw [same.down]; rfl
  have head : StructuralSyntax.HeadForm .identity parameters input.header.body := by
    rw [same.down]
    exact .copy rfl
  let _ := FixedFunctionCompleteness.generatesRetainedSyntax input (.base head inputForm) scope_ok
    (by decide) [1] (by decide) 0 .rolled
  logInfo "ordinary copy source → syntax/static conditions → compileRetained → Entry → RTL; no parser-success or generated-Entry premise"

open Certificate in
run_cmd do
  let some input := NativeEnvironment.input (← getEnv) ``arithmeticBounds
    | throwError "arithmetic-bound loop environment could not be prepared"
  let p := For.parameters parameters
  have index : LexicalScalarSyntax.Form StandardLibrary.model (stateType::wordType::context) p [] (.bvar 1) :=
    .localValue (.variable 1) 0 rfl (by decide) (by decide) (by decide) (by intro j h; omega)
  have value : FunctionSyntax.Syntax StandardLibrary.model (mode := .value) (stateType::wordType::context) p .identity (.push none (.push none .empty))
      (app ``HybridWord.State.set [p.s,NatNotation.elaborated.native 0,.bvar 1])
      (FixedSequenceCompleteness.InputConditions regions) :=
    .valueAssign 0 .elaborated rfl index
      (.valueAssign .elaborated 0 (by repeat constructor))
  have child := FunctionSyntax.Syntax.yield value
  have start : FixedSequenceCompleteness.StaticBound
      (For.nativeBinary .add (For.nativeNatural 1) (For.nativeNatural 1)) 2 := .binary .add (.natural 1) (.natural 1)
  have stop : FixedSequenceCompleteness.StaticBound
      (For.nativeBinary .div (For.nativeBinary .mul (For.nativeNatural 3) (For.nativeNatural 4)) (For.nativeNatural 2)) 6 :=
    .binary .div (.binary .mul (.natural 3) (.natural 4)) (.natural 2)
  have stride : FixedSequenceCompleteness.StaticBound (For.nativeNatural 1) 1 := .natural 1
  have rootConditions := FixedSequenceCompleteness.InputConditions.forStatic (ds := regions) start stop stride
    (st := parameters.s) (fn := .lam `k word (.lam `t state
      (Step.yieldSource (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,.bvar 1])) .default) .default)
    (by repeat constructor)
  let expected := For.source (For.nativeBinary .add (For.nativeNatural 1) (For.nativeNatural 1))
    (For.nativeBinary .div (For.nativeBinary .mul (For.nativeNatural 3) (For.nativeNatural 4)) (For.nativeNatural 2))
    (For.nativeNatural 1) parameters.s (.lam `k word (.lam `t state
      (Step.yieldSource (app ``HybridWord.State.set [.bvar 0,NatNotation.elaborated.native 0,.bvar 1])) .default) .default)
  have form : FunctionSyntax.Syntax StandardLibrary.model context parameters .identity .empty expected
      (FixedSequenceCompleteness.InputConditions regions) := by
    obtain ⟨startTyped⟩ := start.typed (ctx := context) StandardLibrary.library.bounds StandardLibrary.library.scalars.toSignatures
    obtain ⟨stopTyped⟩ := stop.typed (ctx := context) StandardLibrary.library.bounds StandardLibrary.library.scalars.toSignatures
    obtain ⟨strideTyped⟩ := stride.typed (ctx := context) StandardLibrary.library.bounds StandardLibrary.library.scalars.toSignatures
    exact .forStatic startTyped stopTyped strideTyped rfl child `k `t .default .default rootConditions
  let some same := sameClosedHeader expected input.header.body
    | throwError "arithmetic loop spelling differs from the independent source syntax"
  have inputForm := Eq.mp (congrArg (fun raw => FunctionSyntax.Syntax StandardLibrary.model context parameters .identity .empty raw
      (FixedSequenceCompleteness.InputConditions regions)) same.down.symm) form
  have scope_ok : LeanScalar.wellScoped 1 input.header.body = true := by rw [same.down]; rfl
  let _ := FixedFunctionCompleteness.generatesRetainedSyntax input inputForm scope_ok
    (by decide) [0] (by decide) 0 .rolled
  logInfo "ordinary arithmetic-bound loop → independent source syntax/static conditions → compileRetained → general Entry/RTL theorem; no nativeSame or generated Cmd supplied"

end IRComparison.FrontendGenerationConditions
