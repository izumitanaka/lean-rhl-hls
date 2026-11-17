import IRComparison.Frontend.WordFixedReadCompleteness
import IRComparison.Frontend.WordFixedScalarCompleteness

/-! Independent source/static rules for reads used by the fixed-source
success induction. The continuation is handled separately by the ordinary
binding rule; reads are not restricted to a following register assignment. -/
namespace IRComparison.WordFrontend.FixedReadSourceCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 1800000

def naturalSource (annotation : WordBinder.Annotation) (s a n : Lean.Expr) : Lean.Expr :=
  match annotation with
  | .word => Read.source s a n
  | .bitvec => Read.bitsSource s a n

def wordSource (annotation : WordBinder.Annotation) (s a k : Lean.Expr) : Lean.Expr :=
  naturalSource annotation s a (Read.wordIndex k)

inductive Source (ds : FixedMemory.Declarations) {env : VEnv} {ctx : List VExpr} (p : Inputs) :
    Lean.Expr → FixedScalarCompleteness.Meaning → HybridWord.Expr → Lean.Expr → Prop where
  | natural (annotation : WordBinder.Annotation) (array index : Nat) (an nn : NatNotation)
      (declared : (FixedMemory.lookup ds array).isSome = true) :
      Source ds (env := env) (ctx := ctx) p (naturalSource annotation p.s (an.native array) (nn.native index))
        (fun _ _ _ s _ => (s.arrays array)[index]?) (.readNat array index)
        (app ``HybridWord.Expr.readNat [an.native array,nn.native index])
  | word (annotation : WordBinder.Annotation) (array : Nat) (an : NatNotation)
      (declared : (FixedMemory.lookup ds array).isSome = true)
      (index : FixedScalarCompleteness.Scoped env ctx p k f kc kq) :
      Source ds (env := env) (ctx := ctx) p (wordSource annotation p.s (an.native array) k)
        (fun i x y s ls => (f i x y s ls).bind (fun k => (s.arrays array)[k.toNat]?))
        (.read array kc) (app ``HybridWord.Expr.read [an.native array,kq])

theorem Source.declared (source : Source ds (env := env) (ctx := ctx) p raw native code quotation) :
    FixedMemory.exprDeclared ds code = true := by
  cases source with
  | natural annotation array index an nn declared => exact declared
  | word annotation array an declared index => simp [FixedMemory.exprDeclared,declared,index.declared]

theorem Source.computation (source : Source ds (env := env) (ctx := ctx) p raw native code quotation) :
    ∀ i x y s ls, code.eval i x y s ls = native i x y s ls := by
  cases source with
  | natural => intros; rfl
  | word annotation array an declared index => intros; simp [HybridWord.Expr.eval,index.computation]

theorem Source.independent (source : Source ds (env := env) (ctx := ctx) p raw native code quotation)
    (external : LexicalScalarCode.ExternalAt bound p)
    (scope_ok : LeanScalar.wellScoped bound raw = true) :
    ∀ i x y s ls, native i x y s ls = native 0 0 0 s ls := by
  cases source with
  | natural => intros; rfl
  | word annotation array an declared index =>
    have same := index.independent external (by
      cases annotation <;> exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp scope_ok).2).2)
    intros; simp only [same]

theorem Source.valueForm (source : Source ds (env := env) (ctx := ctx) p raw native code quotation)
    (fresh : ScopedSyntax.Fresh setup) (represented : Represents raw core) : ValueForm setup ctx core ty := by
  have head : raw.getAppFn = .const ``GetElem?.getElem? [.zero,.zero,.zero] := by
    cases source with
    | natural annotation => cases annotation <;> rfl
    | word annotation => cases annotation <;> rfl
  obtain ⟨levels,h⟩ := ScopedSyntax.represented_head represented head
  exact .constant h fresh.read (by decide)

theorem Source.complete (source : Source ds (env := env) (ctx := ctx) p raw native code quotation)
    (setup : AliasSetup env) (library : ScopedSyntax.Library env)
    (closed : ClosedConstantTypes env) (fresh : ScopedSyntax.Fresh setup) (exposure : Exposure env)
    (inputs : InputsTyped env ctx p) (locals : ScalarSyntax.Locals env ctx p) :
    ∃ piece, readStep env setup.conversion exposure ctx p
      (ScalarEnvironment.parse env setup.conversion exposure ctx p) raw = some piece ∧
      Nonempty (Read.ReadCasts inputs piece (SourceCasts env) (For.Casts setup)) ∧ piece.code = quotation := by
  have coverage := For.Casts.covered setup library.scalars.toSignatures library.steps closed
    library.cons library.eq library.eval fresh.state fresh.eq fresh.lift
  have embed : ∀ scope a b, SourceCasts env scope a b → For.Casts setup scope a b :=
    fun _ _ _ h => .base (.base (.source h))
  cases source with
  | natural annotation array index an nn declared =>
    let aa := an.argument (ctx := ctx) library.scalars.toSignatures array
    let na := nn.argument (ctx := ctx) library.scalars.toSignatures index
    have natural : Read.NaturalIndex (nn.native index) := by
      cases nn with | raw => exact .inl rfl | elaborated => exact .inr rfl
    cases annotation with
    | word =>
      obtain ⟨piece,h,⟨typed⟩,q⟩ := Read.nat_step_invariant_complete_code library.reads inputs aa na natural
        library.readNatFact library.readNatConstructor setup.conversion exposure
        (setup.covers_source library.scalars.toSignatures closed) _
      exact ⟨piece,h,⟨⟨typed.sourceCore,typed.value,typed.target,typed.proof.mono embed⟩⟩,q⟩
    | bitvec =>
      exact Read.bits_nat_complete_code setup library.scalars.toSignatures library.reads library.scalarCertificates
        inputs aa na natural (ScopedSyntax.natural_value_form setup fresh natural na.represented.property)
        fresh.read (fresh.readAux _ (by simp)) (fresh.readAux _ (by simp))
        library.readNatFact library.readNatConstructor coverage exposure _
  | word annotation array an declared index =>
    obtain ⟨k,hk,⟨tk⟩,kq⟩ := index.complete setup library closed fresh exposure inputs locals
    let aa := an.argument (ctx := ctx) library.scalars.toSignatures array
    cases annotation with
    | word =>
      obtain ⟨piece,h,t,q⟩ := Read.word_step_split_complete_code library.reads library.scalars.toSignatures
        inputs aa tk library.readFact library.readConstructor embed coverage exposure _ hk
      exact ⟨piece,h,t,by rw [q,kq]⟩
    | bitvec =>
      obtain ⟨piece,h,t,q⟩ := Read.bits_word_complete_code setup library.scalars.toSignatures library.reads
        library.scalarCertificates inputs aa tk fresh.read (fresh.readAux _ (by simp))
        (fresh.readAux _ (by simp)) (fresh.readAux _ (by simp)) library.readFact library.readConstructor
        coverage exposure _ hk
      exact ⟨piece,h,t,by rw [q,kq]⟩

theorem Source.install (source : Source ds (env := before) (ctx := ctx) p raw native code quotation)
    (installed : SignatureExtension before after) : Source ds (env := after) (ctx := ctx) p raw native code quotation := by
  cases source with
  | natural annotation array index an nn declared => exact .natural annotation array index an nn declared
  | word annotation array an declared index => exact .word annotation array an declared (index.install installed)

end IRComparison.WordFrontend.FixedReadSourceCompleteness

namespace IRComparison.WordFrontend.FixedReadSourceCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic

/-- Independent fixed-memory conditions on a read expression. These inspect
source array identifiers and index notation, never parser results or code. -/
structure Conditions (ds : FixedMemory.Declarations) (raw : Lean.Expr) : Prop where
  registers : LexicalScalarSyntax.StaticRegisters raw
  array : ∀ annotation st a n, raw = naturalSource annotation st a n →
    ∃ id an, a = NatNotation.native an id ∧ (FixedMemory.lookup ds id).isSome = true
  natural : ∀ annotation st a n, raw = naturalSource annotation st a n →
    Read.NaturalIndex n → Nonempty (NatNotation.View n)

/-- Static declarations for a Word-indexed read are independent of the
continuation, parser and generated code. Both Word/BV32 spellings share it. -/
theorem Conditions.word (annotation : WordBinder.Annotation) (array : Nat) (an : NatNotation)
    (declared : (FixedMemory.lookup ds array).isSome = true)
    (registers : LexicalScalarSyntax.StaticRegisters (wordSource annotation st (an.native array) k)) :
    Conditions ds (wordSource annotation st (an.native array) k) := by
  constructor
  · exact registers
  · intro other state id n h
    cases annotation <;> cases other <;>
      simp only [wordSource,naturalSource,Read.source,Read.bitsSource,Lean.mkApp2,
        Lean.mkApp,Lean.mkAppB,app,List.foldl_cons,List.foldl_nil,Lean.Expr.app.injEq] at h
    all_goals first | contradiction | exact ⟨array,an,h.1.2.2.symm,declared⟩
  · intro other state id n h natural
    cases annotation <;> cases other <;>
      simp only [wordSource,naturalSource,Read.source,Read.bitsSource,Lean.mkApp2,
        Lean.mkApp,Lean.mkAppB,app,List.foldl_cons,List.foldl_nil,Lean.Expr.app.injEq] at h
    all_goals first | contradiction | exact False.elim (natural.not_word (by rw [← h.2]; rfl))

/-- All four existing read forms construct their code and computation from
source syntax plus declarations. The scalar index may contain arbitrary
nesting covered by the lexical source judgment. -/
theorem constructSource (form : ScopedSyntax.ReadForm env ctx p raw) (conditions : Conditions ds raw) :
    ∃ native code quotation, Source ds (env := env) (ctx := ctx) p raw native code quotation := by
  cases form with
  | @natural a n array index shape =>
    obtain ⟨id,an,eq,declared⟩ := conditions.array .word p.s a n rfl
    obtain ⟨view⟩ := conditions.natural .word p.s a n rfl shape
    subst a
    rw [view.shape]
    exact ⟨_,_,_,.natural .word id view.value an view.form declared⟩
  | @bitsNatural a n array index shape =>
    obtain ⟨id,an,eq,declared⟩ := conditions.array .bitvec p.s a n rfl
    obtain ⟨view⟩ := conditions.natural .bitvec p.s a n rfl shape
    subst a
    rw [view.shape]
    exact ⟨_,_,_,.natural .bitvec id view.value an view.form declared⟩
  | @word a k array index =>
    obtain ⟨id,an,eq,declared⟩ := conditions.array .word p.s a (Read.wordIndex k) rfl
    have static : LexicalScalarSyntax.StaticRegisters k := conditions.registers.2.2
    obtain ⟨f,c,q,index⟩ := FixedScalarCompleteness.Scoped.fromSyntax index static
    subst a
    exact ⟨_,_,_,.word .word id an declared index⟩
  | @bitsWord a k array index =>
    obtain ⟨id,an,eq,declared⟩ := conditions.array .bitvec p.s a (Read.wordIndex k) rfl
    have static : LexicalScalarSyntax.StaticRegisters k := conditions.registers.2.2
    obtain ⟨f,c,q,index⟩ := FixedScalarCompleteness.Scoped.fromSyntax index static
    subst a
    exact ⟨_,_,_,.word .bitvec id an declared index⟩

end IRComparison.WordFrontend.FixedReadSourceCompleteness
