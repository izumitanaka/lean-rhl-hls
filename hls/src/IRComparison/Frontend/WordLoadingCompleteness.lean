import IRComparison.Frontend.WordFrontend
import IRComparison.Frontend.LeanReductionCompleteness
import IRComparison.Frontend.WordCertificateCompleteness

namespace IRComparison.WordFrontend
open Lean4Lean

/-- The binder invariant's closure premise comes from the native declarations
already tracked by provenance. It is not a restriction on program nesting. -/
theorem loaded_constant_types_closed (faithful : LeanEnvironmentProvenance.Faithful native env)
    (closed : ∀ name (d : LeanLibrary.Declaration native name),
      LeanScalar.wellScoped 0 d.info.type = true) :
    LeanTypeInference.ClosedConstantTypes env := by
  intro name signature found
  obtain ⟨declaration,same⟩ := faithful.constants name signature found
  rw [same]
  exact declaration.type.property.closed 0 (closed name declaration)

/-- Abstracting and applying the four administrative parameters leaves the
original body intact, also below its own nested binders. -/
theorem reapply_parameters (e : VExpr) (scope : e.ClosedN (depth+4)) :
    ((((e.inst (.bvar 3) (depth+3)).inst (.bvar 2) (depth+2)).inst
      (.bvar 1) (depth+1)).inst (.bvar 0) depth) = e := by
  induction e generalizing depth with
  | bvar i =>
    change i < depth+4 at scope
    by_cases before : i < depth
    · simp [VExpr.inst,VExpr.instVar,before,show i < depth+1 by omega,
        show i < depth+2 by omega,show i < depth+3 by omega]
    · have cases : i = depth ∨ i = depth+1 ∨ i = depth+2 ∨ i = depth+3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;>
        simp [VExpr.inst,VExpr.instVar,VExpr.liftN,liftVar,Nat.add_assoc]
      all_goals
        repeat first
        | omega
        | simp [VExpr.inst,VExpr.instVar,VExpr.liftN,liftVar,Nat.add_assoc]
        | split
  | sort | const => rfl
  | app f a ihf iha =>
    simp only [VExpr.inst,ihf scope.1,iha scope.2]
  | lam ty body iht ihb | forallE ty body iht ihb =>
    have hb := ihb (depth := depth+1) (by simpa [Nat.add_assoc] using scope.2)
    simp only [Nat.add_assoc] at hb
    simp only [VExpr.inst,Nat.add_assoc,iht scope.1,hb]

def sourceFunctionType : VExpr :=
  .forallE Certificate.wordType (.forallE Certificate.wordType (.forallE Certificate.wordType
    (.forallE Certificate.stateType optionState)))
def sourceFunctionBody (body : VExpr) : VExpr :=
  .lam Certificate.wordType (.lam Certificate.wordType (.lam Certificate.wordType
    (.lam Certificate.stateType body)))

theorem source_function_cast_typed
    (wordDeclared : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (stateDeclared : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩)
    (closed : LeanTypeInference.ClosedConstantTypes env)
    (stable : LeanTypeInference.ClosedCasts casts)
    {body : VExpr} (typed : LeanTypeInference.CastTyping env 0 casts context body optionState) :
    LeanTypeInference.CastTyping env 0 casts context (sourceFunctionBody body) sourceFunctionType := by
  have wordTyped (ctx : List VExpr) : LeanTypeInference.CastTyping env 0 casts ctx
      Certificate.wordType (.sort (.succ .zero)) := .constant wordDeclared (by simp) rfl
  have stateTyped (ctx : List VExpr) : LeanTypeInference.CastTyping env 0 casts ctx
      Certificate.stateType (.sort (.succ .zero)) := .constant stateDeclared (by simp) rfl
  have functionTyped : LeanTypeInference.CastTyping env 0 casts []
      (sourceFunctionBody body) sourceFunctionType :=
    .lambda (wordTyped _) (.lambda (wordTyped _) (.lambda (wordTyped _) (.lambda (stateTyped _) typed)))
  exact functionTyped.in_context closed stable (by trivial) context

theorem apply_source_parameters {body : VExpr} (scope : body.ClosedN 4) :
    [.bvar 3,.bvar 2,.bvar 1,.bvar 0].foldl LeanTypeReduction.applyReduced
      (sourceFunctionBody body) = body := by
  simpa only [sourceFunctionBody,List.foldl_cons,List.foldl_nil,LeanTypeReduction.applyReduced,
    Certificate.wordType,Certificate.stateType,VExpr.inst,Nat.reduceAdd] using
    reapply_parameters body (depth := 0) scope

/-- The final named-source step returns precisely the parsed body's source,
not merely a definitionally equal term or a successful reduction flag. -/
theorem named_source_step_cast_complete
    {body : VExpr}
    (rule : LeanTypeReduction.Rule env)
    (monomorphic : rule.definition.declaration.levelParams = [])
    (sourceType : rule.definition.type.val = sourceFunctionType)
    (sourceBody : rule.definition.body.val = sourceFunctionBody body)
    (scope : body.ClosedN 4)
    (typed : LeanTypeInference.CastTyping env 0 casts context rule.definition.body.val rule.definition.type.val)
    (closed : LeanTypeInference.ClosedConstantTypes env)
    (stable : LeanTypeInference.ClosedCasts casts)
    (coverage : LeanTypeInference.Conversion.Covers conv 0 casts)
    (exposure : LeanTypeInference.Exposure env) :
    ∃ result, LeanTypeReduction.step [rule] conv 0 context exposure (sourceApplication rule.name).val = some result ∧
      result.val = (body,optionState) := by
  have arguments : LeanTypeReduction.ArgumentsCasts env 0 casts context sourceFunctionType
      [.bvar 3,.bvar 2,.bvar 1,.bvar 0] optionState :=
    .cons (.bvar (.succ (.succ (.succ .zero))))
      (.cons (.bvar (.succ (.succ .zero))) (.cons (.bvar (.succ .zero)) (.cons (.bvar .zero) .nil)))
  obtain ⟨result,success,typeSame,_,termSame⟩ := LeanTypeReduction.named_application_cast_complete
    rule monomorphic typed (sourceType.symm ▸ arguments) closed stable coverage exposure
  refine ⟨result,success,Prod.ext ?_ typeSame⟩
  simpa only [sourceBody,apply_source_parameters scope] using termSame

/-- The loaded native body and the parser's stripped body share the same
representation, including every binder. This follows from the declaration
itself, rather than assuming another successful body translation. -/
theorem source_body_represents (source : LeanTypeReduction.Definition native name)
    (monomorphic : source.declaration.levelParams = [])
    (shape : LeanSourceEntry.strip source.declaration.value =
      .lam ni wi (.lam nx wx (.lam ny wy (.lam ns st original bs) byInfo) bx) bi) :
    ∃ ci cx cy cs body,
      LeanTyped.Represents wi ci ∧ LeanTyped.Represents wx cx ∧
      LeanTyped.Represents wy cy ∧ LeanTyped.Represents st cs ∧
      LeanTyped.Represents original body ∧
      source.body.val = .lam ci (.lam cx (.lam cy (.lam cs body))) := by
  have represented : LeanLibrary.Represents [] source.declaration.value source.body.val :=
    Eq.mp (congrArg (fun names => LeanLibrary.Represents names source.declaration.value source.body.val)
      monomorphic) source.body.property
  have stripped := LeanSourceEntry.represents_stripped represented.monomorphic
  rw [shape] at stripped
  generalize coreSame : source.body.val = core at stripped
  cases stripped with
  | lam hi rest => cases rest with
    | lam hx rest => cases rest with
      | lam hy rest => cases rest with
        | lam hs hb => exact ⟨_,_,_,_,_,hi,hx,hy,hs,hb,rfl⟩

theorem compatible_same (actualRep : LeanTyped.Represents actual core)
    (expectedRep : LeanTyped.Represents expected core)
    (env : VEnv) (conv : LeanTypeInference.Conversion env) (ctx : List VExpr) :
    compatible env conv ctx actual expected = true := by
  simp [compatible,sameTerm_complete actualRep expectedRep]

/-- Connect finite transparent-type expansion to the actual frontend binder
check. For Word/BitVec this uses the installed Word definition, not a type
comparison oracle or an added equation for an external primitive. -/
theorem compatible_alias_right
    (leadingRules trailingRules : List (LeanTypeReduction.Rule env)) (rule : LeanTypeReduction.Rule env)
    (absent : ∀ r ∈ leadingRules, rule.name ≠ r.name)
    (wf : ∀ u ∈ levels, u.WF 0)
    (arity : levels.length = rule.definition.declaration.levelParams.length)
    (head : LeanTypeReduction.constantHead (rule.definition.body.val.instL levels) = some (headName,headLevels))
    (irreducible : ∀ r ∈ leadingRules ++ rule :: trailingRules, headName ≠ r.name)
    (kind : rule.definition.type.val.instL levels = .sort u)
    (actualRep : LeanTyped.Represents actual (rule.definition.body.val.instL levels))
    (expectedRep : LeanTyped.Represents expected (.const rule.name levels))
    (base : LeanTypeInference.Conversion env) (exposure : LeanTypeInference.Exposure env)
    (ctx : List VExpr) :
    compatible env (LeanStructuralConversion.conversion env
      (LeanTypeReduction.conversion (leadingRules ++ rule :: trailingRules) base) exposure)
      ctx actual expected = true := by
  obtain ⟨⟨ac,ap⟩,ha,ea⟩ := actualRep.translate_complete
  obtain ⟨⟨bc,bp⟩,hb,eb⟩ := expectedRep.translate_complete
  dsimp only at ea eb
  subst ac; subst bc
  obtain ⟨converted,success⟩ := LeanTypeReduction.conversion_alias_right_complete
    leadingRules trailingRules rule absent wf arity head irreducible kind base (ctx := ctx)
  cases same : sameTerm actual expected <;>
    simp [compatible,same,ha,hb,LeanStructuralConversion.conversion,LeanStructuralConversion.ordinary,success]

private theorem distinct_subset_length {xs ys : List Lean.Name}
    (unique : xs.Nodup) (subset : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    have member := subset (by simp : x ∈ x::xs)
    have bound := ih (List.nodup_cons.mp unique).2 (ys:=ys.erase x) (by
      intro y hy
      have different : y ≠ x := by
        intro eqn
        subst y
        exact (List.nodup_cons.mp unique).1 hy
      exact (List.mem_erase_of_ne different).mpr (subset (List.mem_cons_of_mem _ hy)))
    rw [List.length_erase_of_mem member] at bound
    have positive := List.length_pos_of_mem member
    simp only [List.length_cons]
    omega

/-- A finite, closed collection of the signatures actually needed by a source
and the fixed proof library. Unrelated declarations need not be representable.
These are input graph/type conditions, not successful loader invocations. -/
structure SignatureClosure (native : Lean.Environment) (roots names : List Lean.Name) : Prop where
  unique : names.Nodup
  listed : names ⊆ declarationNames native
  roots : ∀ n ∈ roots, n ∈ names
  available : ∀ n ∈ names, Nonempty (LeanLibrary.Declaration native n)
  closed : ∀ n ∈ names, ∀ info, native.find? n = some info →
    ∀ d ∈ LeanEntryEnvironment.constants info.type, d ∈ names

/-- Dependency traversal and formal signature installation both succeed.
The actual traversal removes duplicates, so installation cannot collide. -/
theorem SignatureClosure.install_complete {roots names : List Lean.Name} {native : Lean.Environment}
    (scope : SignatureClosure native roots names) :
    ∃ selected base, dependencies native roots [] = some selected ∧
      LeanLibrary.installTypes native VEnv.empty selected = some base := by
  have available : ∀ n ∈ names, ∃ ds, typeDependencies native n = some ds ∧
      ∀ d ∈ ds, d ∈ ([] : List Lean.Name) ∨ d ∈ names := by
    intro n hn
    obtain ⟨declaration⟩ := scope.available n hn
    refine ⟨LeanEntryEnvironment.constants declaration.info.type,?_,?_⟩
    · simp only [typeDependencies,declaration.found,bind,Option.bind,pure,Option.pure_def]
    · intro d hd
      exact Or.inr (scope.closed n hn declaration.info declaration.found d hd)
  obtain ⟨selected,walked⟩ := DependencyClosure.complete (typeDependencies native) names roots []
    (declarationNames native).length (distinct_subset_length scope.unique scope.listed)
    (fun n hn => Or.inr (scope.roots n hn)) available
  have inventory := DependencyClosure.walk_inventory (typeDependencies native)
    (declarationNames native).length roots [] (fun n => n ∈ names) (by simp) (by simp)
    scope.roots (by
      intro n hn ds found d hd
      obtain ⟨expected,generated,closed⟩ := available n hn
      have eqn := Option.some.inj (found.symm.trans generated)
      subst ds
      simpa using closed d hd) walked
  obtain ⟨base,installed⟩ := LeanLibrary.installTypes_complete (base:=VEnv.empty) selected inventory.1
    (fun n hn => scope.available n (inventory.2 n hn)) (fun _ _ => rfl)
  exact ⟨selected,base,walked,installed⟩

/-- Traversal stays inside the independent finite signature scope. -/
theorem SignatureClosure.selected_subset {roots names : List Lean.Name}
    (scope : SignatureClosure native roots names)
    (walked : dependencies native roots [] = some selected) : selected ⊆ names := by
  exact (DependencyClosure.walk_inventory (typeDependencies native)
    (declarationNames native).length roots [] (fun n => n ∈ names)
    (by simp) (by simp) scope.roots (by
      intro n hn ds found d hd
      obtain ⟨declaration⟩ := scope.available n hn
      have same : ds = LeanEntryEnvironment.constants declaration.info.type := by
        simpa [typeDependencies,declaration.found] using found.symm
      exact scope.closed n hn declaration.info declaration.found d (same ▸ hd)) walked).2

/-- Formal initialization succeeds when the required native declarations have
their specified structural form. No type-conversion or parser-success premise. -/
theorem load_complete
    (source : LeanTypeReduction.Definition native name)
    (identity : LeanTypeAliases.Alias native ``outParam)
    (optional : LeanTypeReduction.Definition native ``optParam)
    (decEq : LeanTypeReduction.Definition native ``DecidableEq)
    (wordDef : LeanTypeReduction.Definition native ``HybridWord.Word)
    (scope : SignatureClosure native (libraryRoots name source.declaration.value) names) :
    ∃ result, load native name = some result := by
  obtain ⟨actual,sourceFound⟩ := source.load_complete
  have same : actual.declaration = source.declaration := by
    have eqn := Option.some.inj (actual.found.symm.trans source.found)
    exact Lean.ConstantInfo.defnInfo.inj eqn
  obtain ⟨selected,base,dependenciesFound,installed⟩ := scope.install_complete
  obtain ⟨identity,identityFound⟩ := identity.load_complete
  obtain ⟨optional,optionalFound⟩ := optional.load_complete
  obtain ⟨decEq,decEqFound⟩ := decEq.load_complete
  obtain ⟨wordDef,wordFound⟩ := wordDef.load_complete
  simp only [load,sourceFound,bind,Option.bind,same,dependenciesFound,installed,
    identityFound,optionalFound,decEqFound,wordFound]
  split
  · rename_i missing
    rw [installed] at missing
    contradiction
  · exact ⟨_,rfl⟩

/-- The installed signature table and the dependency walk are the ones
used by the returned loader result, including source-specific dependencies. -/
theorem loaded_dependencies (loaded : load native name = some lib) :
    ∃ selected base, dependencies native (libraryRoots name lib.source.declaration.value) [] = some selected ∧
      LeanLibrary.installTypes native VEnv.empty selected = some base ∧
      lib.model.constants = base.constants := by
  unfold load at loaded
  cases sourceFound : LeanTypeReduction.load native name with
  | none => simp [sourceFound] at loaded
  | some source =>
    simp only [sourceFound,bind,Option.bind] at loaded
    cases dependenciesFound : dependencies native (libraryRoots name source.declaration.value) [] with
    | none => simp [dependenciesFound] at loaded
    | some names =>
      simp only [dependenciesFound,bind,Option.bind] at loaded
      split at loaded
      · contradiction
      · rename_i base installed
        cases identityFound : LeanTypeAliases.load native ``outParam with
        | none => simp [identityFound] at loaded
        | some identity =>
          simp only [identityFound,bind,Option.bind] at loaded
          cases optionalFound : LeanTypeReduction.load native ``optParam with
          | none => simp [optionalFound] at loaded
          | some optional =>
            simp only [optionalFound,bind,Option.bind] at loaded
            cases decEqFound : LeanTypeReduction.load native ``DecidableEq with
            | none => simp [decEqFound] at loaded
            | some decEq =>
              simp only [decEqFound,bind,Option.bind] at loaded
              cases wordFound : LeanTypeReduction.load native ``HybridWord.Word with
              | none => simp [wordFound] at loaded
              | some wordDefinition =>
                simp only [wordFound,bind,Option.bind,pure,Option.pure_def,Option.some.injEq] at loaded
                subst lib
                exact ⟨names,base,dependenciesFound,installed,rfl⟩

private theorem installed_type_origin (names : List Lean.Name)
    (installed : LeanLibrary.installTypes native base names = some env)
    (found : env.constants n = some signature) :
    base.constants n = some signature ∨ n ∈ names := by
  induction names generalizing base with
  | nil => cases installed; exact Or.inl found
  | cons name names ih =>
    simp only [LeanLibrary.installTypes] at installed
    cases hd : LeanLibrary.load native name with
    | none => simp [hd] at installed
    | some d =>
      cases he : d.install base with
      | none => simp [hd,he] at installed
      | some next =>
        simp only [hd,he,bind,Option.bind] at installed
        rcases ih installed with old | member
        · unfold LeanLibrary.Declaration.install VEnv.addConst at he
          split at he
          · contradiction
          · cases he
            by_cases eqn : name = n
            · exact Or.inr (by simp [eqn])
            · exact Or.inl (by simpa [eqn] using old)
        · exact Or.inr (List.mem_cons_of_mem _ member)

/-- Closure is needed only for the finite declarations actually selected by
this source, not every unrelated definition in the native environment. -/
theorem loaded_types_closed_in_scope
    (loaded : load native name = some lib)
    (scope : SignatureClosure native (libraryRoots name lib.source.declaration.value) names)
    (closed : ∀ n ∈ names, ∀ d : LeanLibrary.Declaration native n,
      LeanScalar.wellScoped 0 d.info.type = true) :
    LeanTypeInference.ClosedConstantTypes lib.model := by
  obtain ⟨selected,base,walked,installed,same⟩ := loaded_dependencies loaded
  intro n signature found
  have selectedMember : n ∈ selected := by
    have baseFound : base.constants n = some signature := by rw [← same]; exact found
    rcases installed_type_origin selected installed baseFound with impossible | member
    · cases impossible
    · exact member
  obtain ⟨d,eqn⟩ := lib.faithful.constants n signature found
  rw [eqn]
  exact d.type.property.closed 0 (closed n (scope.selected_subset walked selectedMember) d)

/-- Reachability and provenance derive the installed signature, including
constants that occur only in the source definition. -/
theorem loaded_source_signature
    (loaded : load native name = some lib)
    (declaration : LeanLibrary.Declaration native n)
    (reachable : DependencyClosure.Reachable (typeDependencies native)
      (libraryRoots name lib.source.declaration.value) n) :
    lib.model.constants n = some declaration.signature := by
  obtain ⟨selected,base,walked,installed,same⟩ := loaded_dependencies loaded
  have included := DependencyClosure.walk_reachable walked reachable
  obtain ⟨signature,found⟩ := (LeanLibrary.installTypes_present selected installed).2 n included
  rw [← same] at found
  obtain ⟨actual,eqn⟩ := lib.faithful.constants n signature found
  rw [eqn,actual.signature_unique declaration] at found
  exact found

/-- The fixed proof library is the source-independent root subset. -/
theorem loaded_reachable_signature
    (loaded : load native name = some lib)
    (declaration : LeanLibrary.Declaration native n)
    (reachable : DependencyClosure.Reachable (typeDependencies native) declarations n) :
    lib.model.constants n = some declaration.signature :=
  loaded_source_signature loaded declaration
    (reachable.mono (by intro n hn; simp [libraryRoots,hn]))

/-- A directly listed declaration is the zero-edge case of signature loading. -/
theorem loaded_library_signature
    (loaded : load native name = some lib)
    (declaration : LeanLibrary.Declaration native n) (member : n ∈ declarations) :
    lib.model.constants n = some declaration.signature :=
  loaded_reachable_signature loaded declaration (.root member)

/-- Closing the four administrative parameters is total once the fixed data
and state type declarations are installed. This introduces no source binder
restriction and invokes the actual formal checker. -/
theorem closeArtifact_complete (a : Artifact env context expected)
    (wordType : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩)
    (stateType : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩) :
    ∃ result, closeArtifact env a = some result := by
  have object (name : Lean.Name) (ctx : List VExpr)
      (declared : env.constants name = some ⟨0,.sort (.succ .zero)⟩) :
      ∃ result, LeanTypeInference.check env 0 ctx (.const name []) (.sort (.succ .zero)) = some result := by
    have typed : LeanTypeInference.DirectTyping env 0 ctx (.const name []) (.sort (.succ .zero)) := by
      simpa only [VExpr.instL,VLevel.inst] using
        (LeanTypeInference.DirectTyping.constant (ctx:=ctx) (levels:=[]) declared (by simp) rfl)
    exact typed.check_complete (LeanTypeInference.noConversion env) (LeanTypeInference.noExposure env)
  obtain ⟨w0,hw0⟩ := object ``HybridWord.Word [] wordType
  obtain ⟨w1,hw1⟩ := object ``HybridWord.Word [.const ``HybridWord.Word []] wordType
  obtain ⟨w2,hw2⟩ := object ``HybridWord.Word [.const ``HybridWord.Word [],.const ``HybridWord.Word []] wordType
  obtain ⟨s3,hs3⟩ := object ``HybridWord.State
    [.const ``HybridWord.Word [],.const ``HybridWord.Word [],.const ``HybridWord.Word []] stateType
  simp only [closeArtifact,hw0,hw1,hw2,hs3,bind,Option.bind]
  exact ⟨_,rfl⟩

/-- Fixed library declarations used after parsing the body. Their types are
checked against the real library by the frontend regression, including the
polymorphic Eq/Option/List signatures. -/
structure ConnectionSignatures (env : VEnv) : Prop where
  word : env.constants ``HybridWord.Word = some ⟨0,.sort (.succ .zero)⟩
  state : env.constants ``HybridWord.State = some ⟨0,.sort (.succ .zero)⟩
  nilWords : env.constants ``List.nil = some Certificate.nilSignature
  eval : env.constants ``HybridWord.Cmd.eval = some ⟨0,Certificate.evalSignature⟩
  option : env.constants ``Option = some Certificate.optionSignature
  equality : env.constants ``Eq = some Certificate.eqSignature

/-- Once body parsing supplies the typing invariants, every remaining check
in the actual named-source frontend succeeds. This compositional lemma does
not claim that the full source grammar already supplies those invariants. -/
theorem compile_of_cast_body
    (parseBody : (env : VEnv) → LeanTypeInference.Conversion env → LeanTypeInference.Exposure env →
      (ctx : List VExpr) → (p : Inputs) → (source : Lean.Expr) →
      Option (Piece env ctx p source bodyExpected))
    (lib : LeanEntryEnvironment.Loaded native name)
    (loaded : load native name = some lib)
    (signatures : ConnectionSignatures lib.model)
    (closed : LeanTypeInference.ClosedConstantTypes lib.model)
    (stable : LeanTypeInference.ClosedCasts casts)
    (coverage : LeanTypeInference.Conversion.Covers lib.conversion 0 casts)
    (monomorphic : lib.source.declaration.levelParams = [])
    (shape : LeanSourceEntry.strip lib.source.declaration.value =
      .lam ni word (.lam nx word (.lam ny word (.lam ns state original bs) byInfo) bx) bi)
    (sourceType : lib.source.type.val = sourceFunctionType)
    (represented : LeanTyped.Represents original bodyCore)
    (bodyTyped : LeanTypeInference.CastTyping lib.model 0 casts context bodyCore optionState)
    (piece : Piece lib.model context parameters original bodyExpected)
    (parsed : parseBody lib.model lib.conversion lib.exposure context parameters original = some piece)
    (targetTyped : LeanTypeInference.CastTyping lib.model 0 casts context piece.represented.val Certificate.cmdType) :
    ∃ result, compileWith parseBody native name = some result ∧ result.CodeTyped ∧ result.code = piece.code := by
  let rule : LeanTypeReduction.Rule lib.model := ⟨native,name,lib.source,lib.registered⟩
  have nativeRep : LeanLibrary.Represents [] lib.source.declaration.value lib.source.body.val :=
    Eq.mp (congrArg (fun names => LeanLibrary.Represents names lib.source.declaration.value
      lib.source.body.val) monomorphic) lib.source.body.property
  have stripped := LeanSourceEntry.represents_stripped nativeRep.monomorphic
  rw [shape] at stripped
  have sourceBody : lib.source.body.val = sourceFunctionBody bodyCore := stripped.unique
    (.lam (.constant rfl) (.lam (.constant rfl) (.lam (.constant rfl) (.lam (.constant rfl) represented))))
  have sourceScope : bodyCore.ClosedN 4 := bodyTyped.closed_term
  have sourceTyped : LeanTypeInference.CastTyping lib.model 0 casts context lib.source.body.val lib.source.type.val := by
    rw [sourceBody,sourceType]
    exact source_function_cast_typed signatures.word signatures.state closed stable bodyTyped
  obtain ⟨⟨⟨term,ty⟩,reduction⟩,stepped,values⟩ := named_source_step_cast_complete rule monomorphic
    sourceType sourceBody sourceScope sourceTyped closed stable coverage lib.exposure
  dsimp only at values
  cases values
  dsimp only [rule] at stepped
  obtain ⟨heq,eqChecked⟩ := Certificate.equality_head_check_complete
    (ctx := context) signatures.state signatures.option signatures.equality
  obtain ⟨ht,targetChecked⟩ := Certificate.target_check_cast_complete signatures.word signatures.nilWords signatures.eval
    piece.represented targetTyped coverage lib.exposure
  have before : piece.checked.core.val = equality (targetEvaluation piece.code piece.represented).val bodyCore :=
    piece.checked.core.property.unique (Certificate.bodyExpected_represents
      (Certificate.initialInputs signatures.word signatures.nilWords) piece.represented.property represented)
  have cast := result_congr heq.down ht.down reduction
  let named : Artifact lib.model context
      (bodyExpected parameters piece.code (app name [parameters.i,parameters.x,parameters.y,parameters.s])) :=
    ⟨piece.code,piece.checked.proof,namedEquality name piece.code piece.represented,piece.checked.proofCore,
      .defeq cast.symm (before ▸ piece.checked.correct)⟩
  obtain ⟨proof,proofClosed⟩ := closeArtifact_complete named signatures.word signatures.state
  have wordSame := compatible_same (actual := word) (expected := word) (LeanTyped.Represents.constant rfl)
    (LeanTyped.Represents.constant rfl) lib.model lib.conversion []
  have stateSame := compatible_same (actual := state) (expected := state) (LeanTyped.Represents.constant rfl)
    (LeanTyped.Represents.constant rfl) lib.model lib.conversion []
  have codeClosed := piece.represented.property.closed 0 piece.closed
  have standalone := targetTyped.closed_context stable codeClosed []
  obtain ⟨⟨actual,codeTyped⟩,_,inferred⟩ := standalone.infer_complete
    (known := LeanTypeInference.noKnownTypes lib.model 0)
    (by intro scope e result impossible; cases impossible) coverage lib.exposure
  change actual = Certificate.cmdType at inferred
  subst actual
  refine ⟨⟨lib,piece.code,piece.closed,proof⟩,?_,⟨piece.represented.val,piece.represented.property,codeTyped⟩,rfl⟩
  simp only [compileWith,loaded,bind,Option.bind,shape,closeLambda,wordSame,stateSame,
    Bool.not_true,Bool.or_self,Bool.false_eq_true,ite_false,parsed,
    stepped,eqChecked,targetChecked,dif_pos rfl,dif_pos before]
  change (closeArtifact lib.model named).bind _ = _
  rw [proofClosed]
  rfl

end IRComparison.WordFrontend
