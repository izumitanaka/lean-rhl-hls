import IRComparison.Frontend.WordScopedSyntax

/-! Shared signature transport below function syntax. Argument retention and
lexical scalar proofs use these same lemmas without depending on the whole
function-grammar induction. -/
namespace IRComparison.LeanTypeInference
open Lean4Lean

abbrev SignatureExtension (before after : VEnv) : Prop :=
  ∀ name signature, before.constants name = some signature → after.constants name = some signature

theorem DirectTyping.install (typed : DirectTyping before U ctx e ty)
    (installed : SignatureExtension before after) : DirectTyping after U ctx e ty := by
  induction typed with
  | bvar h => exact .bvar h
  | sort h => exact .sort h
  | constant h levels arity => exact .constant (installed _ _ h) levels arity
  | application _ _ f a => exact .application f a
  | lambda _ _ d b => exact .lambda d b
  | forallType _ _ d b => exact .forallType d b

theorem CastTyping.install (typed : CastTyping before U casts ctx e ty)
    (installed : SignatureExtension before after)
    (converted : ∀ scope a b, casts scope a b → other scope a b) :
    CastTyping after U other ctx e ty := by
  induction typed with
  | bvar h => exact .bvar h
  | sort h => exact .sort h
  | constant h levels arity => exact .constant (installed _ _ h) levels arity
  | application _ _ f a => exact .application f a
  | convertedApplication _ _ cast f a => exact .convertedApplication f a (converted _ _ _ cast)
  | functionApplication _ view cast _ f a => exact .functionApplication f view (converted _ _ _ cast) a
  | lambda _ _ d b => exact .lambda d b
  | forallType _ _ d b => exact .forallType d b

theorem CheckedTyping.install (typed : CheckedTyping before U casts ctx e ty)
    (installed : SignatureExtension before after)
    (converted : ∀ scope a b, casts scope a b → other scope a b) :
    CheckedTyping after U other ctx e ty := by
  cases typed with
  | exact h => exact .exact (h.install installed converted)
  | converted h cast => exact .converted (h.install installed converted) (converted _ _ _ cast)

theorem ArgumentsCasts_install
    (typed : LeanTypeReduction.ArgumentsCasts before U casts ctx ty args resultType)
    (installed : SignatureExtension before after)
    (converted : ∀ scope a b, casts scope a b → other scope a b) :
    LeanTypeReduction.ArgumentsCasts after U other ctx ty args resultType := by
  induction typed with
  | nil => exact .nil
  | cons arg rest ih => exact .cons (arg.install installed converted) ih

end IRComparison.LeanTypeInference

namespace IRComparison.WordFrontend
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic

theorem Certificate.Arithmetic.SourceCasts.install (cast : SourceCasts before ctx a b)
    (installed : SignatureExtension before after) : SourceCasts after ctx a b := by
  cases cast with
  | arithmetic h => exact .arithmetic h
  | heterogeneous op a b c d e f => exact .heterogeneous op a b c d e f
  | readDictionary d =>
    exact .readDictionary {
      function := d.function, domain := d.domain, predicate := d.predicate,
      kind := d.kind, resultKind := d.resultKind, annotation := d.annotation,
      annotationClosed := d.annotationClosed, sameKind := d.sameKind, levels := d.levels, head := d.head,
      prefixTyped := d.prefixTyped.install installed, domainTyped := d.domainTyped.install installed,
      predicateTyped := d.predicateTyped.install installed, predicateLambda := d.predicateLambda,
      domainClosed := d.domainClosed, kindClosed := d.kindClosed, resultClosed := d.resultClosed }
  | decisionInstance declared => exact .decisionInstance (installed _ _ declared)
  | decisionFunction equality decidable boolean =>
    exact .decisionFunction (installed _ _ equality) (installed _ _ decidable)
      (installed _ _ boolean)
  | wordValue => exact .wordValue
  | bitvecOption declared => exact .bitvecOption (installed _ _ declared)
  | wordOption declared => exact .wordOption (installed _ _ declared)
  | wordFunction resultTyped => exact .wordFunction (resultTyped.install installed)
  | levelEquality a b h => exact .levelEquality a b h
  | parameter arg typed a b h => exact .parameter _ (typed.install installed) a b h

def Certificate.NatArgument.install (value : NatArgument before ctx n)
    (installed : SignatureExtension before after) : NatArgument after ctx n :=
  ⟨value.represented,value.typed.install installed,value.closed⟩

theorem ScalarSyntax.Decision.install (value : ScalarSyntax.Decision before ctx v d)
    (installed : SignatureExtension before after) : ScalarSyntax.Decision after ctx v d := by
  rcases value with ⟨vc,dc,vr,dr,pt,dt⟩
  exact ⟨vc,dc,vr,dr,pt.install installed (fun _ _ _ h => h),dt.install installed (fun _ _ _ h => h)⟩


theorem ScalarSyntax.Decision.installSource
    (value : ScalarSyntax.Decision before ctx v d (Arithmetic.SourceCasts before))
    (installed : SignatureExtension before after) :
    ScalarSyntax.Decision after ctx v d (Arithmetic.SourceCasts after) := by
  rcases value with ⟨vc,dc,vr,dr,pt,dt⟩
  exact ⟨vc,dc,vr,dr,
    pt.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed),
    dt.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed)⟩


theorem LexicalScalarSyntax.ValueShape.install (shape : LexicalScalarSyntax.ValueShape before ctx e ty)
    (installed : SignatureExtension before after) : LexicalScalarSyntax.ValueShape after ctx e ty := by
  cases shape with
  | bound => exact .bound
  | constant head member => exact .constant head member
  | beta annotation resultAnnotation typed => exact .beta annotation resultAnnotation (typed.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed))

theorem LexicalScalarSyntax.Form.install (form : LexicalScalarSyntax.Form before ctx p values e)
    (installed : SignatureExtension before after) : LexicalScalarSyntax.Form after ctx p values e := by
  induction form with
  | reference selected => exact .reference selected
  | parameter shape side same ni nl => exact .parameter shape side same ni nl
  | index shape same => exact .index shape same
  | localValue shape k selected ni nl nr first => exact .localValue shape k selected ni nl nr first
  | literal n scope => exact .literal n scope
  | binary op _ _ scope a b => exact .binary op a b scope
  | neg _ scope ih => exact .neg ih scope
  | register same r scope => exact .register same (r.install installed) scope
  | select _ d _ _ scope v a b => exact .select v (d.installSource installed) a b scope
  | annotatedLiteral annotation n scope => exact .annotatedLiteral annotation n scope
  | annotatedBinary op aa ab ac ad oa ob _ _ lr rr lt rt lf rf scope left right =>
    exact .annotatedBinary op aa ab ac ad oa ob left right lr rr
      (lt.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed))
      (rt.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed))
      (lf.install installed) (rf.install installed) scope
  | annotatedNeg annotation operand _ represented typed form scope value =>
    exact .annotatedNeg annotation operand value represented
      (typed.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed)) (form.install installed) scope
  | annotatedSelect resultAnnotation annotation operand oa ob value yes no vr ar br vt typedLeft bt vf af bf scope iv ia ib =>
    exact .annotatedSelect resultAnnotation annotation operand oa ob iv ia ib vr ar br
      (vt.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed))
      (typedLeft.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed))
      (bt.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed))
      (vf.install installed) (af.install installed) (bf.install installed) scope
  | letValue annotation resultAnnotation _ _ arg body typed shape name flag value tail =>
    exact .letValue annotation resultAnnotation value tail arg body (typed.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed)) (by obtain ⟨actual,shape⟩ := shape; exact ⟨actual,shape.install installed⟩) name flag
  | beta annotation resultAnnotation _ _ arg body typed shape name info value tail =>
    exact .beta annotation resultAnnotation value tail arg body (typed.install installed (fun _ _ _ h => Certificate.Arithmetic.SourceCasts.install h installed)) (by obtain ⟨actual,shape⟩ := shape; exact ⟨actual,shape.install installed⟩) name info


theorem ScalarSyntax.Form.install (form : ScalarSyntax.Form before ctx p e)
    (installed : SignatureExtension before after) : ScalarSyntax.Form after ctx p e := by
  induction form with
  | parameter side n bound ni nl => exact .parameter side n bound ni nl
  | index n bound => exact .index n bound
  | localValue source shape k selected ni nl nr first => exact .localValue source shape k selected ni nl nr first
  | literal n scope => exact .literal n scope
  | binary op _ _ scope a b => exact .binary op a b scope
  | neg _ scope ih => exact .neg ih scope
  | register r scope => exact .register (r.install installed) scope
  | select _ d _ _ scope v a b => exact .select v (d.install installed) a b scope

end IRComparison.WordFrontend
