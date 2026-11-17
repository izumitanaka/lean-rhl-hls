import IRComparison.Frontend.WordNativeEnvironment

/-! Construct the finite native-environment conditions needed by source
induction. These checks produce evidence; callers do not provide one proof
per declaration. The independent specifications are not parser-success tests. -/
namespace IRComparison.WordFrontend.NativeEnvironment
open Lean4Lean LeanTypeInference

/-- Only the selected signature closure matters for binder weakening. -/
def Closed (native : Lean.Environment) (names : List Lean.Name) : Prop :=
  ∀ n ∈ names, ∀ d : LeanLibrary.Declaration native n,
    LeanScalar.wellScoped 0 d.info.type = true

def checkClosed (native : Lean.Environment) : (names : List Lean.Name) → Option (PLift (Closed native names))
  | [] => some ⟨by intro n h; cases h⟩
  | n::rest => do
    let d ← LeanLibrary.load native n
    if closed : LeanScalar.wellScoped 0 d.info.type = true then
      let tail ← checkClosed native rest
      return ⟨by
        intro m member other
        rcases List.mem_cons.mp member with rfl | member
        · have same : other.info = d.info := Option.some.inj (other.found.symm.trans d.found)
          simpa only [same] using closed
        · exact tail.down m member other⟩
    else none

theorem checkClosed_complete
    (present : ∀ n ∈ names, Nonempty (LeanLibrary.Declaration native n))
    (closed : Closed native names) :
    ∃ result, checkClosed native names = some result := by
  induction names with
  | nil => exact ⟨_,rfl⟩
  | cons n rest ih =>
    obtain ⟨d⟩ := present n (by simp)
    obtain ⟨loaded,success⟩ := d.load_complete
    have head := closed n (by simp) loaded
    obtain ⟨tail,done⟩ := ih
      (fun m hm => present m (List.mem_cons_of_mem _ hm))
      (fun m hm => closed m (List.mem_cons_of_mem _ hm))
    simp only [checkClosed,success,bind,Option.bind,dif_pos head,done]
    exact ⟨_,rfl⟩

/-- The one actual Word declaration determines all views of that declaration;
callers do not prove the universally quantified alias condition by hand. -/
theorem wordShape (definition : LeanTypeReduction.Definition native ``HybridWord.Word)
    (arity : definition.declaration.levelParams.length = 0)
    (body : definition.body.val.instL [] = Arithmetic.bitvecType)
    (type : definition.type.val.instL [] = .sort (.succ .zero)) :
    Arithmetic.WordDeclaration native := by
  intro other
  have same : other.declaration = definition.declaration :=
    Lean.ConstantInfo.defnInfo.inj (Option.some.inj (other.found.symm.trans definition.found))
  have mono : definition.declaration.levelParams = [] := List.length_eq_zero_iff.mp arity
  have monomorphic {value : Lean.Expr} {core : VExpr}
      (rep : LeanLibrary.Represents definition.declaration.levelParams value core) :
      LeanLibrary.Represents [] value core :=
    Eq.mp (congrArg (fun levels => LeanLibrary.Represents levels value core) mono) rep
  have otherBody := Eq.mp (congrArg (fun declaration : Lean.DefinitionVal =>
    LeanLibrary.Represents declaration.levelParams declaration.value other.body.val) same) other.body.property
  have otherType := Eq.mp (congrArg (fun declaration : Lean.DefinitionVal =>
    LeanLibrary.Represents declaration.levelParams declaration.type other.type.val) same) other.type.property
  have bodySame := (monomorphic otherBody).monomorphic.unique (monomorphic definition.body.property).monomorphic
  have typeSame := (monomorphic otherType).monomorphic.unique (monomorphic definition.type.property).monomorphic
  exact ⟨by simpa [same] using arity,by simpa [bodySame] using body,by simpa [typeSame] using type⟩

def checkWordShape (definition : LeanTypeReduction.Definition native ``HybridWord.Word) :
    Option (PLift (Arithmetic.WordDeclaration native)) :=
  if arity : definition.declaration.levelParams.length = 0 then
    if body : definition.body.val.instL [] = Arithmetic.bitvecType then
      if type : definition.type.val.instL [] = .sort (.succ .zero) then
        some ⟨wordShape definition arity body type⟩
      else none
    else none
  else none

theorem checkWordShape_complete (definition : LeanTypeReduction.Definition native ``HybridWord.Word)
    (shape : Arithmetic.WordDeclaration native) :
    ∃ result, checkWordShape definition = some result := by
  obtain ⟨arity,body,type⟩ := shape definition
  exact ⟨⟨wordShape definition arity body type⟩,by simp [checkWordShape,arity,body,type]⟩

/-- The fixed alias condition is recovered from the actual declaration;
source users do not provide it per branch. -/
theorem decEqShape (definition : LeanTypeReduction.Definition native ``DecidableEq)
    (arity : definition.declaration.levelParams.length = 1)
    (body : definition.body.val.instL [.succ .zero] = Arithmetic.decEqBody)
    (type : definition.type.val.instL [.succ .zero] = Arithmetic.decEqKind) :
    Arithmetic.DecEqDeclaration native := by
  intro other
  have same : other.declaration = definition.declaration :=
    Lean.ConstantInfo.defnInfo.inj (Option.some.inj (other.found.symm.trans definition.found))
  have otherBody := Eq.mp (congrArg (fun declaration : Lean.DefinitionVal =>
    LeanLibrary.Represents declaration.levelParams declaration.value other.body.val) same) other.body.property
  have otherType := Eq.mp (congrArg (fun declaration : Lean.DefinitionVal =>
    LeanLibrary.Represents declaration.levelParams declaration.type other.type.val) same) other.type.property
  obtain ⟨a,ha,ea⟩ := otherBody.translate_complete
  obtain ⟨b,hb,eb⟩ := definition.body.property.translate_complete
  have bodySame : other.body.val = definition.body.val := by
    rw [ha] at hb
    cases hb
    exact ea.symm.trans eb
  obtain ⟨c,hc,ec⟩ := otherType.translate_complete
  obtain ⟨d,hd,ed⟩ := definition.type.property.translate_complete
  have typeSame : other.type.val = definition.type.val := by
    rw [hc] at hd
    cases hd
    exact ec.symm.trans ed
  exact ⟨by simpa [same] using arity,by simpa [bodySame] using body,by simpa [typeSame] using type⟩

def checkDecEqShape (definition : LeanTypeReduction.Definition native ``DecidableEq) :
    Option (PLift (Arithmetic.DecEqDeclaration native)) :=
  if arity : definition.declaration.levelParams.length = 1 then
    if body : definition.body.val.instL [.succ .zero] = Arithmetic.decEqBody then
      if type : definition.type.val.instL [.succ .zero] = Arithmetic.decEqKind then
        some ⟨decEqShape definition arity body type⟩
      else none
    else none
  else none

theorem checkDecEqShape_complete (definition : LeanTypeReduction.Definition native ``DecidableEq)
    (shape : Arithmetic.DecEqDeclaration native) :
    ∃ result, checkDecEqShape definition = some result := by
  obtain ⟨arity,body,type⟩ := shape definition
  exact ⟨⟨decEqShape definition arity body type⟩,by simp [checkDecEqShape,arity,body,type]⟩

open Arithmetic in
theorem fresh_of_not_library (absent : name ∉ declarations) : NativeCompleteness.NameFresh name := by
  constructor
  · intro h; exact absent (h ▸ (by decide : ``HybridWord.Word ∈ declarations))
  · intro h; exact absent (h ▸ (by decide : ``BitVec ∈ declarations))
  · intro h; exact absent (h ▸ (by decide : ``OfNat ∈ declarations))
  · intro n hn h
    subst n
    exact absent ((by decide : [``Nat.zero,``Nat.succ,``Nat.mul] ⊆ declarations) hn)
  · intro op h
    apply absent
    rw [← h]
    cases op <;> decide
  · intro op h
    apply absent
    rw [← h]
    cases op <;> decide
  · intro h; exact absent (h ▸ (by decide : ``Neg ∈ declarations))
  · intro n hn h
    subst n
    exact absent ((by decide : LexicalScalarSyntax.valueHeads ⊆ declarations) hn)
  · intro n hn h
    subst n
    exact absent ((by decide : [``HybridWord.State,``Eq,``Option.some,``Pure.pure,
      ``HybridWord.State.write,``HybridWord.State.copy,``ite,``Bind.bind,``ForIn.forIn,
      ``WordLoopFacts.lift,``PUnit,``Nat,``List.foldlM,``Option,``GetElem?.getElem?,``GetElem?,``Array.instGetElem?NatLtSize,``HybridWord.State.arrays,``BitVec.toNat,``ForInStep,``bne,``Decidable,``instDecidableEqBool] ⊆ declarations) hn)

/-- A certificate built from the actual source and its finite dependencies.
It does not include a parsed body, a generated command, or an Entry. -/
structure Prepared (native : Lean.Environment) (name : Lean.Name) where
  source : LeanTypeReduction.Definition native name
  identity : LeanTypeAliases.Alias native ``outParam
  optional : LeanTypeReduction.Definition native ``optParam
  decEq : LeanTypeReduction.Definition native ``DecidableEq
  wordDef : LeanTypeReduction.Definition native ``HybridWord.Word
  wordShape : Arithmetic.WordDeclaration native
  decEqShape : Arithmetic.DecEqDeclaration native
  names : List Lean.Name
  signatures : SignatureClosure native (libraryRoots name source.declaration.value) names
  standard : StandardLibrary.NativeEntries native StandardLibrary.entries
  closed : Closed native names

def prepare (native : Lean.Environment) (name : Lean.Name) : Option (Prepared native name) := do
  let source ← LeanTypeReduction.load native name
  let identity ← LeanTypeAliases.load native ``outParam
  let optional ← LeanTypeReduction.load native ``optParam
  let decEq ← LeanTypeReduction.load native ``DecidableEq
  let wordDef ← LeanTypeReduction.load native ``HybridWord.Word
  let shape ← checkWordShape wordDef
  let equalityShape ← checkDecEqShape decEq
  let names ← scope native (libraryRoots name source.declaration.value)
  let standard ← StandardLibrary.checkEntries native StandardLibrary.entries
  let closed ← checkClosed native names.val
  return ⟨source,identity,optional,decEq,wordDef,shape.down,equalityShape.down,names.val,names.property,standard.down,closed.down⟩

/-- Preparation succeeds from independently specified declarations, signature
closure and lexical scope. No body parser is invoked by this construction. -/
theorem prepare_complete (valid : Prepared native name) :
    ∃ result, prepare native name = some result := by
  obtain ⟨source,sourceLoaded⟩ := valid.source.load_complete
  obtain ⟨identity,identityLoaded⟩ := valid.identity.load_complete
  obtain ⟨optional,optionalLoaded⟩ := valid.optional.load_complete
  obtain ⟨decEq,decEqLoaded⟩ := valid.decEq.load_complete
  obtain ⟨wordDef,wordLoaded⟩ := valid.wordDef.load_complete
  obtain ⟨shape,shapeChecked⟩ := checkWordShape_complete wordDef valid.wordShape
  obtain ⟨equalityShape,equalityShapeChecked⟩ := checkDecEqShape_complete decEq valid.decEqShape
  have same : source.declaration = valid.source.declaration :=
    Lean.ConstantInfo.defnInfo.inj (Option.some.inj (source.found.symm.trans valid.source.found))
  have signatures : SignatureClosure native (libraryRoots name source.declaration.value) valid.names :=
    same ▸ valid.signatures
  obtain ⟨selected,scopeLoaded⟩ := scope_complete signatures
  obtain ⟨standard,standardChecked⟩ := StandardLibrary.checkEntries_complete valid.standard
  obtain ⟨closed,closedChecked⟩ := checkClosed_complete selected.property.available
    (fun n hn => valid.closed n (signatures.selected_subset selected.walked hn))
  simp only [prepare,sourceLoaded,identityLoaded,optionalLoaded,decEqLoaded,wordLoaded,
    shapeChecked,equalityShapeChecked,scopeLoaded,standardChecked,closedChecked,bind,Option.bind]
  exact ⟨_,rfl⟩

/-- The administrative source header records the actual binder names; it does
not rename the user's body or ask the body parser whether it is supported. -/
structure Header (value : Lean.Expr) where
  body : Lean.Expr
  ni : Lean.Name
  nx : Lean.Name
  ny : Lean.Name
  ns : Lean.Name
  bi : Lean.BinderInfo
  bx : Lean.BinderInfo
  byInfo : Lean.BinderInfo
  bs : Lean.BinderInfo
  shape : LeanSourceEntry.strip value =
    .lam ni word (.lam nx word (.lam ny word (.lam ns state body bs) byInfo) bx) bi

def header (value : Lean.Expr) : Option (Header value) :=
  match h : LeanSourceEntry.strip value with
  | .lam ni (.const ``HybridWord.Word [])
      (.lam nx (.const ``HybridWord.Word [])
        (.lam ny (.const ``HybridWord.Word [])
          (.lam ns (.const ``HybridWord.State []) body bs) byInfo) bx) bi =>
    some ⟨body,ni,nx,ny,ns,bi,bx,byInfo,bs,h⟩
  | _ => none

theorem header_complete (value : Header source) :
    ∃ result, header source = some result := by
  unfold header
  split
  · exact ⟨_,rfl⟩
  · rename_i miss
    exact False.elim (miss value.ni value.nx value.ny value.ns value.body value.bs value.byInfo value.bx value.bi value.shape)

/-- Independently checked native environment and source header. Syntax and
fixed-array conditions are supplied by the source judgment, not stored as a
successful parse or an already constructed backend entry. -/
structure Input (native : Lean.Environment) (name : Lean.Name) where
  environment : Prepared native name
  header : Header environment.source.declaration.value
  fresh : name ∉ declarations
  monomorphic : environment.source.declaration.levelParams = []
  sourceType : environment.source.type.val = sourceFunctionType

def input (native : Lean.Environment) (name : Lean.Name) : Option (Input native name) := do
  let environment ← prepare native name
  let header ← header environment.source.declaration.value
  if fresh : name ∉ declarations then
    if mono : environment.source.declaration.levelParams = [] then
      if sourceType : environment.source.type.val = sourceFunctionType then
        return ⟨environment,header,fresh,mono,sourceType⟩
      else none
    else none
  else none

theorem input_complete (valid : Input native name) :
    ∃ result, input native name = some result := by
  obtain ⟨prepared,ready⟩ := prepare_complete valid.environment
  have same : prepared.source.declaration = valid.environment.source.declaration :=
    Lean.ConstantInfo.defnInfo.inj
      (Option.some.inj (prepared.source.found.symm.trans valid.environment.source.found))
  have mono : prepared.source.declaration.levelParams = [] := same ▸ valid.monomorphic
  have headerShape : Header prepared.source.declaration.value := same ▸ valid.header
  obtain ⟨head,found⟩ := header_complete headerShape
  have typeSame : prepared.source.type.val = valid.environment.source.type.val := by
    have left := prepared.source.type.property
    have right := valid.environment.source.type.property
    generalize leftCore : prepared.source.type.val = lc at left ⊢
    generalize rightCore : valid.environment.source.type.val = rc at right ⊢
    rw [same,valid.monomorphic] at left
    rw [valid.monomorphic] at right
    exact left.monomorphic.unique right.monomorphic
  have sourceType := typeSame.trans valid.sourceType
  simp only [input,ready,found,bind,Option.bind,dif_pos valid.fresh,dif_pos mono,dif_pos sourceType]
  exact ⟨_,rfl⟩

/-- Internal connection preserving a source-derived property of the emitted
command. The callback is discharged by source induction; it is not a public
supported-language condition or an assumed successful parse. -/
theorem Input.compilesInstalledCodeWith (parseBody : (env : VEnv) → Conversion env → Exposure env →
      (ctx : List VExpr) → (p : Inputs) → (source : Lean.Expr) →
      Option (Piece env ctx p source bodyExpected))
    (source : Input native name) (property : Lean.Expr → Prop)
    (rule : ∀ (env : VEnv) (setup : Arithmetic.AliasSetup env) (library : ScopedSyntax.Library env),
      SignatureExtension StandardLibrary.model env → ClosedConstantTypes env → ScopedSyntax.Fresh setup → ∀ exposure : Exposure env,
      ∃ piece, parseBody env setup.conversion exposure context parameters source.header.body = some piece ∧
        ∃ typed : Certificate.BodyCasts
          (Certificate.initialInputs library.connection.word library.connection.nilWords) piece
          (Arithmetic.SourceCasts env) (Certificate.For.Casts setup), property piece.code) :
    ∃ result, compileWith parseBody native name = some result ∧ result.CodeTyped ∧ property result.code := by
  let prepared := source.environment
  obtain ⟨lib,loaded⟩ := load_complete prepared.source prepared.identity prepared.optional prepared.decEq
    prepared.wordDef prepared.signatures
  have same : lib.source.declaration = prepared.source.declaration :=
    Lean.ConstantInfo.defnInfo.inj (Option.some.inj (lib.source.found.symm.trans prepared.source.found))
  let table := StandardLibrary.sourceTable prepared.standard name prepared.source.declaration.value
  have installed := table.installed loaded (congrArg Lean.DefinitionVal.value same)
  have typeSame : lib.source.type.val = prepared.source.type.val := by
    have left := lib.source.type.property
    have right := prepared.source.type.property
    generalize leftCore : lib.source.type.val = lc at left ⊢
    generalize rightCore : prepared.source.type.val = rc at right ⊢
    rw [same,source.monomorphic] at left
    rw [source.monomorphic] at right
    exact left.monomorphic.unique right.monomorphic
  have closed := loaded_types_closed_in_scope loaded (same ▸ prepared.signatures) prepared.closed
  have fresh := fresh_of_not_library source.fresh
  have library := StandardLibrary.library.install installed
  exact ScopedSyntax.compile_of_parser_rule_with_code parseBody lib loaded library closed prepared.wordShape prepared.decEqShape
    fresh.word fresh.bitvec fresh.ofNat fresh.numerals fresh.classes fresh.heterogeneous fresh.neg fresh.scalarHeads fresh.heads
    (same ▸ source.monomorphic)
    ((congrArg (fun d : Lean.DefinitionVal => LeanSourceEntry.strip d.value) same).trans source.header.shape)
    (typeSame.trans source.sourceType)
    property (fun setup fresh => rule lib.model setup library installed closed fresh lib.exposure)
end IRComparison.WordFrontend.NativeEnvironment
