import IRComparison.Frontend.WordLexicalSourceTyping

/-! Source/static scalar derivations with exact generated code. This proof-only
relation complements the broader lexical syntax judgment; it does not change
which ordinary Lean definitions the frontend accepts. -/
namespace IRComparison.WordFrontend.FixedScalarCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 1800000

abbrev Meaning := HybridWord.Word → HybridWord.Word → HybridWord.Word →
  HybridWord.State → List HybridWord.Word → Option HybridWord.Word

abbrev binaryCode := LexicalScalarCode.binaryCode
abbrev binaryValue := LexicalScalarCode.binaryValue

/-- The indices record the source computation and quotation, fixed by syntax.
Scope conditions are independent of any parser run. -/
inductive Source (p : Inputs) : Lean.Expr → Meaning → HybridWord.Expr → Lean.Expr → Prop where
  | literal (n : Nat) (scope : ScalarSyntax.Separated p (nativeLiteral n)) :
      Source p (nativeLiteral n) (fun _ _ _ _ _ => some (BitVec.ofNat 32 n))
        (.lit (BitVec.ofNat 32 n)) (app ``HybridWord.Expr.lit [nativeLiteral n])
  | index (shape : ScalarSyntax.LocalOccurrence p.i) :
      Source p p.i (fun i _ _ _ _ => some i) .index (.const ``HybridWord.Expr.index [])
  | parameter (side : ScalarSyntax.Side) (shape : ScalarSyntax.LocalOccurrence (side.source p))
      (notIndex : sameTerm (side.source p) p.i = false)
      (notLeft : side = .right → sameTerm (side.source p) p.x = false) :
      Source p (side.source p) (fun _ x y _ _ => some (match side with | .left => x | .right => y))
        (match side with | .left => .left | .right => .right) (.const side.target [])
  | localValue (shape : ScalarSyntax.LocalOccurrence raw) (k : Nat)
      (selected : p.locals[k]? = some raw)
      (notIndex : sameTerm raw p.i = false) (notLeft : sameTerm raw p.x = false)
      (notRight : sameTerm raw p.y = false)
      (first : ∀ j < k, (p.locals[j]?.map (sameTerm raw)).getD false = false) :
      Source p raw (fun _ _ _ _ ls => ls[k]?) (.local k)
        (app ``HybridWord.Expr.local [(ClosedTerm.bindingIndex k).val])
  | register (r : Nat) (rn : NatNotation)
      (scope : ScalarSyntax.Separated p (app ``HybridWord.State.regs [p.s,rn.native r])) :
      Source p (app ``HybridWord.State.regs [p.s,rn.native r]) (fun _ _ _ s _ => some (s.regs r))
        (.reg r) (app ``HybridWord.Expr.reg [rn.native r])
  | binary (op : Binary) (left : Source p a f ac aq) (right : Source p b g bc bq)
      (scope : ScalarSyntax.Separated p (Lean.mkApp2 op.nativeHeader a b)) :
      Source p (Lean.mkApp2 op.nativeHeader a b)
        (fun i x y s ls => (f i x y s ls).bind (fun u => (g i x y s ls).bind (fun v => some (binaryValue op u v))))
        (binaryCode op ac bc) (app op.target [aq,bq])
  | select (value : Source p v f vc vq) (yes : Source p a g ac aq) (no : Source p b h bc bq)
      (scope : ScalarSyntax.Separated p (Branch.Select.source v (Branch.nativeBooleanDecision v) a b)) :
      Source p (Branch.Select.source v (Branch.nativeBooleanDecision v) a b)
        (fun i x y s ls => (f i x y s ls).bind (fun v => if v != 0 then g i x y s ls else h i x y s ls))
        (.select vc ac bc) (app ``HybridWord.Expr.select [vq,aq,bq])
  | neg (value : Source p v f vc vq)
      (scope : ScalarSyntax.Separated p (.app nativeNegHeader v)) :
      Source p (.app nativeNegHeader v) (fun i x y s ls => (f i x y s ls).bind (fun v => some (-v)))
        (.neg vc) (app ``HybridWord.Expr.neg [vq])

/-- The compact rules are the empty lexical scope of the same source language.
This lets source typing share the lexical induction, without a second parser. -/
theorem Source.lexical (source : Source p raw native code quotation) :
    LexicalScalarCode.Source env ctx p [] raw native code quotation := by
  induction source with
  | literal n separated => exact .literal n separated
  | index shape => exact .index shape (by simp [LexicalScalarCode.expand]) (.empty _)
  | parameter side shape ni nl =>
    cases side with
    | left => exact .parameter (vs := []) .left shape (by simp [LexicalScalarCode.expand]) (.empty _) ni nl
    | right => exact .parameter (vs := []) .right shape (by simp [LexicalScalarCode.expand]) (.empty _) ni nl
  | localValue shape k selected ni nl nr first =>
    apply LexicalScalarCode.Source.localValue (vs := []) shape k (.empty _)
    all_goals simpa [LexicalScalarCode.expand] using ‹_›
  | register r rn separated => exact .register r rn (by simp [LexicalScalarCode.expand]) (by simp [LexicalScalarCode.expand]) (by simpa [LexicalScalarCode.expand] using separated)
  | binary op _ _ separated left right =>
    exact .binary op left right (by simpa [LexicalScalarCode.expand] using separated)
  | select _ _ _ separated value yes no =>
    exact .booleanSelect value yes no (by simpa [LexicalScalarCode.expand] using separated)
  | neg _ separated value => exact .neg value (by simpa [LexicalScalarCode.expand] using separated)

/-- Both facts are inherited from the lexical source induction. The compact
syntax is an input convenience, not a second semantics proof. -/
theorem Source.declared (source : Source p raw native code quotation) :
    FixedMemory.exprDeclared ds code = true :=
  (source.lexical (env := .empty) (ctx := []).computation
    (by intro v hv; cases hv)).1 ds

theorem Source.computation (source : Source p raw native code quotation) :
    ∀ i x y s ls, code.eval i x y s ls = native i x y s ls :=
  (source.lexical (env := .empty) (ctx := []).computation
    (by intro v hv; cases hv)).2

theorem Source.complete (source : Source p raw native command quotation)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    ∃ piece, ScalarEnvironment.parse env setup.conversion exposure ctx p raw = some piece ∧
      Nonempty (ScalarCasts inputs piece (SourceCasts env) (For.Casts setup)) ∧ piece.code = quotation := by
  exact source.lexical.parse_complete setup library closed fresh exposure inputs locals

/-- The existing compact scalar rules and fully lexical rules share one
source interface. Context is explicit only where source typing needs it. -/
inductive Scoped (env : VEnv) (ctx : List VExpr) (p : Inputs)
    (raw : Lean.Expr) (native : Meaning) (code : HybridWord.Expr) (quotation : Lean.Expr) : Prop where
  | core : Source p raw native code quotation → Scoped env ctx p raw native code quotation
  | lexical : LexicalScalarCode.Source env ctx p [] raw native code quotation →
      Scoped env ctx p raw native code quotation

theorem Scoped.asLexical (source : Scoped env ctx p raw native code quotation) :
    LexicalScalarCode.Source env ctx p [] raw native code quotation := by
  cases source with
  | core h => exact h.lexical
  | lexical h => exact h

/-- The computation-free lexical judgment determines generated code; callers
need not supply the code or its native-computation index in advance. -/
theorem Scoped.fromSyntax (form : LexicalScalarSyntax.Form env ctx p [] raw)
    (static : LexicalScalarSyntax.StaticRegisters raw) :
    ∃ native code quotation, Scoped env ctx p raw native code quotation := by
  obtain ⟨native,code,quotation,source⟩ := form.constructSource static [] rfl
  exact ⟨native,code,quotation,.lexical source⟩

theorem Scoped.independent (source : Scoped env ctx p raw native code quotation)
    (external : LexicalScalarCode.ExternalAt bound p)
    (scope_ok : LeanScalar.wellScoped bound raw = true) :
    ∀ i x y s ls, native i x y s ls = native 0 0 0 s ls := by
  exact source.asLexical.independent external (by intro v h; cases h) (by simpa using scope_ok)

theorem Scoped.evidence (source : Scoped env ctx p raw native code quotation)
    (library : ScalarSyntax.Library env) (decisions : Branch.BooleanLibrary env)
    (inputs : InputsTyped env ctx p) (typing : LexicalScalarCode.ScopeTyped env ctx p) :
    LexicalScalarCode.Evidence env ctx raw := by
  simpa [LexicalScalarCode.expand] using source.asLexical.evidence library decisions inputs typing (by intro v h; cases h)

theorem Scoped.declared (source : Scoped env ctx p raw native code quotation) :
    FixedMemory.exprDeclared ds code = true :=
  (source.asLexical.computation (by intro v hv; cases hv)).1 ds

theorem Scoped.computation (source : Scoped env ctx p raw native code quotation) :
    ∀ i x y s ls, code.eval i x y s ls = native i x y s ls :=
  (source.asLexical.computation (by intro v hv; cases hv)).2

theorem Scoped.complete (source : Scoped env ctx p raw native code quotation)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    ∃ piece, ScalarEnvironment.parse env setup.conversion exposure ctx p raw = some piece ∧
      Nonempty (ScalarCasts inputs piece (SourceCasts env) (For.Casts setup)) ∧ piece.code = quotation := by
  exact source.asLexical.parse_complete setup library closed fresh exposure inputs locals

theorem Scoped.install (source : Scoped before ctx p raw native code quotation)
    (installed : SignatureExtension before after) : Scoped after ctx p raw native code quotation := by
  cases source with
  | core h => exact .core h
  | lexical h => exact .lexical (h.install installed)

end IRComparison.WordFrontend.FixedScalarCompleteness

namespace IRComparison.WordFrontend.ScalarSyntax
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic

/-- Basic scalar syntax is the empty-cache specialization of the existing
lexical syntax; static source reconstruction therefore uses one induction. -/
theorem Form.lexical (form : Form env ctx p raw) : LexicalScalarSyntax.Form env ctx p [] raw := by
  induction form with
  | parameter side n bound ni nl =>
    exact .parameter side (bound ▸ LocalOccurrence.variable n) (by simp) ni nl
  | index n bound => exact .index (bound ▸ LocalOccurrence.variable n) (by simp)
  | localValue raw shape k selected ni nl nr first =>
    apply LexicalScalarSyntax.Form.localValue shape k
    all_goals simpa only [LexicalScalarSyntax.expand_nil] using ‹_›
  | literal n scope => exact .literal n scope
  | binary op left right scope il ir => exact .binary op il ir (by simpa using scope)
  | neg value scope ih => exact .neg ih (by simpa using scope)
  | register number scope => exact .register (by simp) (by simpa using number) (by simpa using scope)
  | select value decision yes no scope iv ia ib =>
    exact .select iv (by simpa using decision.mono (fun _ _ _ h => SourceCasts.arithmetic h)) ia ib (by simpa using scope)

end IRComparison.WordFrontend.ScalarSyntax
