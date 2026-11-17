import IRComparison.Frontend.WordCertificateCompleteness
import IRComparison.Frontend.LeanReductionCompleteness

/-! Fixed arithmetic declarations used by ordinary elaborated Lean notation.
These are descriptions of existing Lean terms, not replacement arithmetic
operations or an HLS input AST. -/
namespace IRComparison.WordFrontend.Arithmetic
open Lean4Lean LeanTyped LeanTypeInference Certificate

structure Signatures (env : VEnv) : Prop where
  negClass : env.constants ``Neg = some negClassSignature
  negInstance : env.constants ``BitVec.instNeg = some ⟨0,negInstanceSignature⟩
  negMethod : env.constants ``Neg.neg = some negMethodSignature
  natural : env.constants ``Nat = some ⟨0,.sort (.succ .zero)⟩
  word : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩
  literals : NatSignatures env
  ofNatClass : env.constants ``OfNat = some ofNatClassSignature
  bitvecOfNat : env.constants ``BitVec.instOfNat = some ⟨0,bitvecOfNatSignature⟩
  ofNat : env.constants ``OfNat.ofNat = some ofNatSignature
  natInstance : env.constants ``instOfNatNat = some ⟨0,natInstanceSignature⟩
  bitvec : env.constants ``BitVec = some ⟨0,.forallE natType (.sort (.succ .zero))⟩
  classes : ∀ op : Binary, env.constants op.className = some op.classSignature
  instances : ∀ op : Binary, env.constants op.instanceName = some ⟨0,op.instanceSignature⟩
  lifted : ∀ op : Binary, env.constants op.liftedInstance = some op.liftedSignature
  methods : ∀ op : Binary, env.constants op.method = some op.methodSignature
  heterogeneous : ∀ op : Binary, env.constants op.heterogeneous = some op.heterogeneousSignature

theorem Signatures.natural_notation_typed (signatures : Signatures env) (value : Nat) :
    DirectTyping env 0 ctx (applications (.const ``OfNat.ofNat [.zero])
      [natType,numeral value,.app (.const ``instOfNatNat []) (numeral value)]) natType := by
  have natTyped : DirectTyping env 0 ctx natType (.sort (.succ .zero)) :=
    .constant signatures.natural (by simp) rfl
  have n := signatures.literals.numeral_typed (ctx := ctx) (U := 0) value
  have fact : DirectTyping env 0 ctx (.const ``OfNat.ofNat [.zero])
      (.forallE (.sort (.succ .zero)) (.forallE natType
        (.forallE (applications (.const ``OfNat [.zero]) [.bvar 1,.bvar 0]) (.bvar 2)))) :=
    .constant signatures.ofNat (by simp [VLevel.WF]) rfl
  have a1 := DirectTyping.application fact natTyped
  simp only [natType,applications,Nat.reduceAdd,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.lift,VExpr.liftN] at a1
  have a2 := DirectTyping.application a1 n
  simp only [Nat.reduceAdd,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.lift,VExpr.liftN] at a2
  have inst : DirectTyping env 0 ctx (.const ``instOfNatNat []) natInstanceSignature :=
    .constant signatures.natInstance (by simp) rfl
  have applied := DirectTyping.application inst n
  simp only [natInstanceSignature,natType,applications,Nat.reduceAdd,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero] at applied
  exact .application a2 applied

theorem Signatures.width_typed (signatures : Signatures env) :
    DirectTyping env 0 ctx width natType := signatures.natural_notation_typed 32

theorem Signatures.bitvec_typed (signatures : Signatures env) :
    DirectTyping env 0 ctx bitvecType (.sort (.succ .zero)) :=
  .application (.constant signatures.bitvec (by simp) rfl) signatures.width_typed

theorem WordSpelling.typed (spelling : WordSpelling value) (library : Signatures env) :
    DirectTyping env 0 ctx value (.sort (.succ .zero)) := by
  cases spelling
  · exact .constant library.word (by simp) rfl
  · exact library.bitvec_typed

/-- The closed dictionary type occurring in an elaborated array read. Only
its element annotation changes; collection, index and validity stay fixed. -/
structure ReadDictionary (env : VEnv) where
  function : VExpr
  domain : VExpr
  predicate : VExpr
  kind : VLevel
  resultKind : VLevel
  annotation : VLevel
  annotationClosed : annotation.WF 0
  sameKind : kind.eval [] = annotation.eval []
  levels : List VLevel
  head : LeanTypeReduction.constantHead function = some (``GetElem?, levels)
  prefixTyped : DirectTyping env 0 [] function
    (.forallE resultParameter (.forallE (.app (.const ``outParam [annotation]) domain) (.sort resultKind)))
  domainTyped : DirectTyping env 0 [] domain (.sort kind)
  predicateTyped : DirectTyping env 0 [] predicate domain
  predicateLambda : ∃ a b, predicate = .lam a b
  domainClosed : domain.ClosedN 0
  kindClosed : kind.WF 0
  resultClosed : resultKind.WF 0

def decEqSignature : VConstant := ⟨1,.forallE (.sort (.param 0))
  (.sort (.max (.succ .zero) (.param 0)))⟩
def decidableSignature : VConstant := ⟨0,.forallE (.sort .zero) (.sort (.succ .zero))⟩
def boolType : VExpr := .const ``Bool []
def decEqFunction (ty : VExpr) : VExpr := .forallE ty (.forallE ty.lift
  (.app (.const ``Decidable []) (applications (.const ``Eq [.succ .zero])
    [ty.liftN 2,.bvar 1,.bvar 0])))

theorem decEqTail_typed
    (equality : env.constants ``Eq = some eqSignature)
    (decidable : env.constants ``Decidable = some decidableSignature) :
    DirectTyping env 0 (.sort (.succ .zero)::ctx) (decEqFunction (.bvar 0))
      (.sort (.imax (.succ .zero) (.imax (.succ .zero) (.succ .zero)))) := by
  refine .forallType (.bvar .zero) (.forallType (.bvar (.succ .zero)) ?_)
  have eq : DirectTyping env 0 (.bvar 1::.bvar 0::.sort (.succ .zero)::ctx) (.const ``Eq [.succ .zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) :=
    .constant equality (by simp [VLevel.WF]) rfl
  have a : DirectTyping env 0 (.bvar 1::.bvar 0::.sort (.succ .zero)::ctx)
      (.bvar 2) (.sort (.succ .zero)) := .bvar (.succ (.succ .zero))
  have x : DirectTyping env 0 (.bvar 1::.bvar 0::.sort (.succ .zero)::ctx)
      (.bvar 1) (.bvar 2) := .bvar (.succ .zero)
  have y : DirectTyping env 0 (.bvar 1::.bvar 0::.sort (.succ .zero)::ctx)
      (.bvar 0) (.bvar 2) := .bvar .zero
  have e1 := DirectTyping.application eq a
  simp only [VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.lift,VExpr.liftN,liftVar,Nat.reduceAdd] at e1
  have e2 := DirectTyping.application e1 x
  simp only [VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.lift,VExpr.liftN,liftVar,Nat.reduceAdd] at e2
  have e3 := DirectTyping.application e2 y
  have d : DirectTyping env 0 (.bvar 1::.bvar 0::.sort (.succ .zero)::ctx)
      (.const ``Decidable []) (.forallE (.sort .zero) (.sort (.succ .zero))) :=
    .constant decidable (by simp) rfl
  exact .application d e3

/-- Closed type annotations used outside arithmetic, notably array indexing.
The alias constructor is justified by an independent typing derivation of its
argument and equality of universe values, never by checker success. -/
inductive SourceCasts (env : VEnv) : TypeCasts where
  | arithmetic : Casts ctx actual expected → SourceCasts env ctx actual expected
  | heterogeneous (op : Binary) (a : WordSpelling a1) (b : WordSpelling b1) (c : WordSpelling c1)
      (d : WordSpelling a2) (e : WordSpelling b2) (f : WordSpelling c2) :
      SourceCasts env ctx (op.classApplication a1 b1 c1) (op.classApplication a2 b2 c2)
  | readDictionary (d : ReadDictionary env) :
      SourceCasts env ctx (.app (.app d.function wordType) d.predicate)
        (.app (.app d.function bitvecType) d.predicate)
  | decisionInstance (declared : env.constants ``DecidableEq = some decEqSignature) :
      SourceCasts env ctx (.app (.const ``DecidableEq [.succ .zero]) bitvecType)
        (.app (.const ``DecidableEq [.succ .zero]) wordType)
  | decisionFunction (equality : env.constants ``Eq = some eqSignature)
      (decidable : env.constants ``Decidable = some decidableSignature)
      (boolean : env.constants ``Bool = some ⟨0,.sort (.succ .zero)⟩) :
      SourceCasts env ctx (.app (.const ``DecidableEq [.succ .zero]) boolType)
        (decEqFunction boolType)
  | wordValue : SourceCasts env ctx wordType bitvecType
  | wordOption (declared : env.constants ``Option = some optionSignature) :
      SourceCasts env ctx (optionType wordType) (optionType bitvecType)
  | bitvecOption (declared : env.constants ``Option = some optionSignature) :
      SourceCasts env ctx (optionType bitvecType) (optionType wordType)
  | wordFunction (resultTyped : DirectTyping env 0 [] (optionType valueType) (.sort (.succ .zero))) :
      SourceCasts env ctx (.forallE bitvecType (optionType valueType)) (.forallE wordType (optionType valueType))
  | levelEquality (actualClosed : actual.WF 0) (expectedClosed : expected.WF 0)
      (sameUniverse : actual.eval [] = expected.eval []) :
      SourceCasts env ctx (.sort actual) (.sort expected)
  | parameter (argument : VExpr) (typed : DirectTyping env 0 [] argument (.sort actual))
      (actualClosed : actual.WF 0) (expectedClosed : expected.WF 0)
      (sameUniverse : actual.eval [] = expected.eval []) :
      SourceCasts env ctx argument (.app (.const ``outParam [expected]) argument)

instance : Includes (SourceCasts env) := ⟨fun _ _ _ h => .arithmetic h⟩

def SourceCasts.bitvecValue : SourceCasts env ctx bitvecType wordType := .arithmetic .bitvecValue

theorem SourceCasts.closed : ClosedCasts (SourceCasts env) := by
  intro ctx actual expected cast
  cases cast with
  | arithmetic cast =>
    obtain ⟨a,b,stable⟩ := casts_closed _ _ _ cast
    exact ⟨a,b,fun scope => .arithmetic (stable scope)⟩
  | heterogeneous op a b c d e f =>
    exact ⟨⟨⟨⟨by trivial,a.closed⟩,b.closed⟩,c.closed⟩,
      ⟨⟨⟨by trivial,d.closed⟩,e.closed⟩,f.closed⟩,fun _ => .heterogeneous op a b c d e f⟩
  | readDictionary d =>
    have pc := d.prefixTyped.closed_term
    have ac := d.predicateTyped.closed_term
    exact ⟨⟨⟨pc,by trivial⟩,ac⟩,⟨⟨pc,⟨by trivial,width_closed⟩⟩,ac⟩,fun _ => .readDictionary d⟩
  | decisionInstance declared =>
    exact ⟨⟨by trivial,⟨by trivial,width_closed⟩⟩,by trivial,fun _ => .decisionInstance declared⟩
  | decisionFunction equality decidable boolean =>
    exact ⟨by trivial,by simp [decEqFunction,boolType,applications,VExpr.ClosedN,VExpr.lift,VExpr.liftN],fun _ => .decisionFunction equality decidable boolean⟩
  | wordValue => exact ⟨by trivial,⟨by trivial,width_closed⟩,fun _ => .wordValue⟩
  | wordOption declared => exact ⟨by trivial,⟨by trivial,⟨by trivial,width_closed⟩⟩,fun _ => .wordOption declared⟩
  | bitvecOption declared => exact ⟨⟨by trivial,⟨by trivial,width_closed⟩⟩,by trivial,fun _ => .bitvecOption declared⟩
  | wordFunction resultTyped =>
    have resultClosed := resultTyped.closed_term
    exact ⟨⟨⟨by trivial,width_closed⟩,resultClosed.mono (by decide)⟩,
      ⟨by trivial,resultClosed.mono (by decide)⟩,fun _ => .wordFunction resultTyped⟩
  | levelEquality actualClosed expectedClosed sameUniverse =>
    exact ⟨by trivial,by trivial,fun _ => .levelEquality actualClosed expectedClosed sameUniverse⟩
  | parameter argument typed actualClosed expectedClosed sameUniverse =>
    exact ⟨typed.closed_term,⟨by trivial,typed.closed_term⟩,
      fun _ => .parameter _ typed actualClosed expectedClosed sameUniverse⟩

def Binary.dictionary (op : Binary) : VExpr :=
  applications (.const op.liftedInstance [.zero])
    [wordType,.app (.const op.instanceName []) width]
def Binary.header (op : Binary) : VExpr :=
  applications (.const op.method [.zero,.zero,.zero]) [wordType,wordType,wordType,op.dictionary]
def Binary.nativeHeader (op : Binary) : Lean.Expr :=
  [word,word,word,
    [word,app op.instanceName [nativeWidth]].foldl Lean.Expr.app (.const op.liftedInstance [.zero])].foldl
      Lean.Expr.app (.const op.method [.zero,.zero,.zero])

theorem Binary.header_represents (op : Binary) : Represents op.nativeHeader op.header := by
  exact app_represents (.constant rfl) (.cons (.constant rfl) (.cons (.constant rfl)
    (.cons (.constant rfl) (.cons
      (app_represents (.constant rfl) (.cons (.constant rfl)
        (.cons (.app (.constant rfl) width_represents) .nil))) .nil))))

theorem Binary.header_closed (op : Binary) : op.header.ClosedN 0 := by
  apply op.header_represents.closed 0
  cases op <;> rfl

theorem Signatures.dictionary_typed (signatures : Signatures env) (op : Binary) :
    CastTyping env 0 Casts ctx op.dictionary
      (applications (.const op.heterogeneous [.zero,.zero,.zero]) [wordType,wordType,wordType]) := by
  have wt : DirectTyping env 0 ctx wordType (.sort (.succ .zero)) :=
    .constant signatures.word (by simp) rfl
  have it : DirectTyping env 0 ctx (.const op.instanceName []) op.instanceSignature :=
    .constant (signatures.instances op) (by simp) rfl
  have instantiated := DirectTyping.application it signatures.width_typed
  simp only [Binary.instanceSignature,natType,Nat.reduceAdd,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero] at instantiated
  have liftTyped : CastTyping env 0 Casts ctx (.const op.liftedInstance [.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.app (.const op.className [.zero]) (.bvar 0))
        (applications (.const op.heterogeneous [.zero,.zero,.zero]) [.bvar 1,.bvar 1,.bvar 1]))) :=
    .constant (signatures.lifted op) (by simp [VLevel.WF]) rfl
  have a1 := CastTyping.application liftTyped (wt.withCasts Casts)
  simp only [applications,wordType,Nat.reduceAdd,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.lift,VExpr.liftN] at a1
  exact .convertedApplication a1 (instantiated.withCasts Casts) (.wordInstance op)

theorem Signatures.header_typed (signatures : Signatures env) (op : Binary) :
    CastTyping env 0 Casts ctx op.header (.forallE wordType (.forallE wordType wordType)) := by
  have wt : CastTyping env 0 Casts ctx wordType (.sort (.succ .zero)) :=
    .constant signatures.word (by simp) rfl
  have method : CastTyping env 0 Casts ctx (.const op.method [.zero,.zero,.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.sort (.succ .zero))
        (.forallE resultParameter (.forallE
          (applications (.const op.heterogeneous [.zero,.zero,.zero]) [.bvar 2,.bvar 1,.bvar 0])
          (.forallE (.bvar 3) (.forallE (.bvar 3) (.bvar 3))))))) :=
    .constant (signatures.methods op) (by simp [VLevel.WF]) rfl
  have a1 := CastTyping.application method wt
  simp only [resultParameter,wordType,applications,Nat.reduceAdd,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.instVar_lower,VExpr.lift,VExpr.liftN] at a1
  have a2 := CastTyping.application a1 wt
  simp only [Nat.reduceAdd,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,VExpr.lift,VExpr.liftN] at a2
  have a3 := CastTyping.convertedApplication a2 wt Casts.resultType
  simp only [Nat.reduceAdd,VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,VExpr.instVar_lower,VExpr.lift,VExpr.liftN] at a3
  exact .application a3 (signatures.dictionary_typed op)

def negHeader : VExpr := applications (.const ``Neg.neg [.zero])
  [wordType,.app (.const ``BitVec.instNeg []) width]
def nativeNegHeader : Lean.Expr := Lean.mkApp2 (.const ``Neg.neg [.zero]) word
  (app ``BitVec.instNeg [nativeWidth])

theorem negHeader_represents : Represents nativeNegHeader negHeader :=
  .app (.app (.constant rfl) (.constant rfl)) (.app (.constant rfl) width_represents)

theorem negHeader_closed : negHeader.ClosedN 0 := negHeader_represents.closed 0 rfl

theorem Signatures.negHeader_typed (signatures : Signatures env) :
    CastTyping env 0 Casts ctx negHeader (.forallE wordType wordType) := by
  have instanceTyped : DirectTyping env 0 ctx (.const ``BitVec.instNeg []) negInstanceSignature :=
    .constant signatures.negInstance (by simp) rfl
  have dictionary := DirectTyping.application instanceTyped signatures.width_typed
  simp only [negInstanceSignature,natType,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,Nat.reduceAdd] at dictionary
  have fact : CastTyping env 0 Casts ctx (.const ``Neg.neg [.zero])
      (.forallE (.sort (.succ .zero)) (.forallE (.app (.const ``Neg [.zero]) (.bvar 0))
        (.forallE (.bvar 1) (.bvar 2)))) :=
    .constant signatures.negMethod (by simp [VLevel.WF]) rfl
  have wordTyped : CastTyping env 0 Casts ctx wordType (.sort (.succ .zero)) :=
    .constant signatures.word (by simp) rfl
  have first := CastTyping.application fact wordTyped
  simp only [wordType,VExpr.inst,VExpr.instVar_zero,VExpr.instVar_succ,Nat.reduceAdd,VExpr.lift,VExpr.liftN] at first
  exact .convertedApplication first (dictionary.withCasts Casts) .negInstance

/-- Ordinary elaborated BV32 numeral, for every natural literal magnitude. -/
def nativeLiteral (n : Nat) : Lean.Expr :=
  Lean.mkApp3 (.const ``OfNat.ofNat [.zero]) word (.lit (.natVal n))
    (app ``BitVec.instOfNat [nativeWidth,.lit (.natVal n)])
def literalTerm (n : Nat) : VExpr :=
  applications (.const ``OfNat.ofNat [.zero])
    [wordType,numeral n,applications (.const ``BitVec.instOfNat []) [width,numeral n]]

theorem literal_represents (n : Nat) : Represents (nativeLiteral n) (literalTerm n) :=
  .app (.app (.app (.constant rfl) (.constant rfl)) .natural)
    (.app (.app (.constant rfl) width_represents) .natural)

theorem literal_closed (n : Nat) : isClosed (nativeLiteral n) = true := rfl

theorem Signatures.literal_typed (signatures : Signatures env) (n : Nat) :
    CastTyping env 0 Casts ctx (literalTerm n) wordType := by
  have wt : CastTyping env 0 Casts ctx wordType (.sort (.succ .zero)) :=
    .constant signatures.word (by simp) rfl
  have nt := signatures.literals.numeral_typed (ctx := ctx) (U := 0) n
  have dictionary : DirectTyping env 0 ctx (.const ``BitVec.instOfNat []) bitvecOfNatSignature :=
    .constant signatures.bitvecOfNat (by simp) rfl
  have d1 := DirectTyping.application dictionary signatures.width_typed
  simp only [bitvecOfNatSignature,natType,applications,VExpr.inst,Nat.reduceAdd,
    VExpr.instVar_succ,VExpr.instVar_zero,VExpr.instVar_lower] at d1
  have d2 := DirectTyping.application d1 nt
  simp only [VExpr.inst,VExpr.inst_lift,VExpr.instVar_zero] at d2
  have fact : CastTyping env 0 Casts ctx (.const ``OfNat.ofNat [.zero])
      (.forallE (.sort (.succ .zero)) (.forallE natType
        (.forallE (applications (.const ``OfNat [.zero]) [.bvar 1,.bvar 0]) (.bvar 2)))) :=
    .constant signatures.ofNat (by simp [VLevel.WF]) rfl
  have a1 := CastTyping.application fact wt
  simp only [natType,wordType,applications,VExpr.inst,Nat.reduceAdd,VExpr.instVar_lower,
    VExpr.instVar_zero,VExpr.instVar_succ,VExpr.lift,VExpr.liftN] at a1
  have a2 := CastTyping.application a1 (nt.withCasts Casts)
  simp only [VExpr.inst,VExpr.instVar_lower,VExpr.instVar_zero,VExpr.instVar_succ,
    VExpr.lift,VExpr.liftN] at a2
  exact .convertedApplication a2 (d2.withCasts Casts) (.literalInstance n)

end IRComparison.WordFrontend.Arithmetic
