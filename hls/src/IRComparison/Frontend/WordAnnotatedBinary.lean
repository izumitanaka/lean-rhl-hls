import IRComparison.Frontend.WordBinder

/-! Fixed arithmetic headers produced with Word/BitVec annotations. Source
operands remain arbitrary scalar expressions; no arithmetic normalization is
used to replace their source or their typeclass dictionaries. -/
namespace IRComparison.WordFrontend.AnnotatedBinary
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic
set_option maxHeartbeats 1800000

def dictionary (op : Binary) (annotation : WordBinder.Annotation) : VExpr :=
  applications (.const op.liftedInstance [.zero])
    [annotation.core,.app (.const op.instanceName []) width]
def nativeDictionary (op : Binary) (annotation : WordBinder.Annotation) : Lean.Expr :=
  Lean.mkApp2 (.const op.liftedInstance [.zero]) annotation.native (app op.instanceName [nativeWidth])
def header (op : Binary) (a b c d : WordBinder.Annotation) : VExpr :=
  applications (.const op.method [.zero,.zero,.zero]) [a.core,b.core,c.core,dictionary op d]
def nativeHeader (op : Binary) (a b c d : WordBinder.Annotation) : Lean.Expr :=
  Lean.mkApp4 (.const op.method [.zero,.zero,.zero]) a.native b.native c.native (nativeDictionary op d)

theorem spelling (annotation : WordBinder.Annotation) : WordSpelling annotation.core := by
  cases annotation <;> constructor

theorem represented (op : Binary) (a b c d : WordBinder.Annotation) :
    Represents (nativeHeader op a b c d) (header op a b c d) :=
  .app (.app (.app (.app (.constant rfl) a.represented) b.represented) c.represented)
    (.app (.app (.constant rfl) d.represented) (.app (.constant rfl) width_represents))

theorem dictionary_typed (library : Signatures env) (op : Binary) (annotation : WordBinder.Annotation) :
    CastTyping env 0 (SourceCasts env) ctx (dictionary op annotation)
      (op.classApplication annotation.core annotation.core annotation.core) := by
  cases annotation with
  | word => exact (library.dictionary_typed op).mono (fun _ _ _ h => .arithmetic h)
  | bitvec =>
    have instanceTyped : DirectTyping env 0 ctx (.const op.instanceName []) op.instanceSignature :=
      .constant (library.instances op) (by simp) rfl
    have inst := DirectTyping.application instanceTyped library.width_typed
    simp only [Binary.instanceSignature,natType,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_lower] at inst
    have lifted : CastTyping env 0 (SourceCasts env) ctx (.const op.liftedInstance [.zero])
        (.forallE (.sort (.succ .zero)) (.forallE (.app (.const op.className [.zero]) (.bvar 0))
          (op.classApplication (.bvar 1) (.bvar 1) (.bvar 1)))) :=
      .constant (library.lifted op) (by simp [VLevel.WF]) rfl
    have first := CastTyping.application lifted (library.bitvec_typed.withCasts (SourceCasts env))
    have bc : bitvecType.ClosedN 0 := WordSpelling.closed .bitvec
    simp only [Binary.classApplication,applications,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,
      VExpr.instVar_lower,bc.lift_eq,bc.instN_eq (Nat.zero_le _),Nat.reduceAdd,VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_false,ite_true] at first
    have result := CastTyping.application first (inst.withCasts (SourceCasts env))
    simpa only [bc.lift_eq,bc.instN_eq (Nat.zero_le _),VExpr.inst] using result

theorem header_typed (library : Signatures env) (op : Binary) (a b c d : WordBinder.Annotation) :
    CastTyping env 0 (SourceCasts env) ctx (header op a b c d)
      (.forallE a.core (.forallE b.core c.core)) := by
  have method : CastTyping env 0 (SourceCasts env) ctx (.const op.method [.zero,.zero,.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.sort (.succ .zero))
        (.forallE resultParameter (.forallE
          (op.classApplication (.bvar 2) (.bvar 1) (.bvar 0))
          (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 3))))))) :=
    .constant (library.methods op) (by simp [VLevel.WF]) rfl
  have first := CastTyping.application method ((a.type_typed library).withCasts (SourceCasts env))
  simp only [Binary.classApplication,applications,resultParameter,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.instVar_lower,a.closed.liftN_eq (Nat.zero_le _),Nat.reduceAdd,VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_false,ite_true] at first
  have second := CastTyping.application first ((b.type_typed library).withCasts (SourceCasts env))
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    a.closed.instN_eq (Nat.zero_le _),b.closed.liftN_eq (Nat.zero_le _),Nat.reduceAdd,VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_false,ite_true] at second
  have third := CastTyping.convertedApplication second ((c.type_typed library).withCasts (SourceCasts env))
    (SourceCasts.arithmetic Casts.resultType)
  simp only [VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,
    a.closed.instN_eq (Nat.zero_le _),b.closed.instN_eq (Nat.zero_le _),c.closed.liftN_eq (Nat.zero_le _),Nat.reduceAdd,VExpr.lift,VExpr.liftN,liftVar,Nat.reduceLT,ite_false,ite_true] at third
  have result := CastTyping.convertedApplication third (dictionary_typed library op d)
    (SourceCasts.heterogeneous op (spelling d) (spelling d) (spelling d) (spelling a) (spelling b) (spelling c))
  simpa only [VExpr.inst,a.closed.instN_eq (Nat.zero_le _),b.closed.instN_eq (Nat.zero_le _),
    c.closed.instN_eq (Nat.zero_le _)] using result

theorem value_typed (library : Signatures env) (op : Binary) (a b c d : WordBinder.Annotation)
    (left : CheckedTyping env 0 (SourceCasts env) ctx u wordType)
    (right : CheckedTyping env 0 (SourceCasts env) ctx v wordType) :
    CheckedTyping env 0 (SourceCasts env) ctx (.app (.app (header op a b c d) u) v) wordType := by
  apply c.result
  have first := CastTyping.checkedApplication (header_typed library op a b c d) (a.argument left)
  simp only [VExpr.inst,b.closed.instN_eq (Nat.zero_le _),c.closed.instN_eq (Nat.zero_le _)] at first
  have result := CastTyping.checkedApplication first (b.argument right)
  simpa only [c.closed.instN_eq (Nat.zero_le _)] using result

end IRComparison.WordFrontend.AnnotatedBinary
