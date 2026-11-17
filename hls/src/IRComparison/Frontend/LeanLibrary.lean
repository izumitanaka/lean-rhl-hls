import IRComparison.Frontend.LeanTypeInference

namespace IRComparison.LeanLibrary
open Lean4Lean

/-- Universe names are bound by the declaration, in declaration order. -/
def parameter (names : List Lean.Name) (name : Lean.Name) : Option Nat :=
  match names with
  | [] => none
  | first :: rest => if name = first then some 0 else (parameter rest name).map Nat.succ

def level (names : List Lean.Name) : Lean.Level → Option VLevel
  | .zero => some .zero
  | .succ u => return .succ (← level names u)
  | .max u v => return .max (← level names u) (← level names v)
  | .imax u v => return .imax (← level names u) (← level names v)
  | .param name => return .param (← parameter names name)
  | .mvar _ => none

/-- Structural correspondence for declaration types with universe binders.
    This imports types only, not definition bodies or reduction equations. -/
inductive Represents (names : List Lean.Name) : Lean.Expr → VExpr → Prop where
  | bvar : Represents names (.bvar n) (.bvar n)
  | sort (h : level names u = some v) : Represents names (.sort u) (.sort v)
  | constant (h : us.mapM (level names) = some vs) :
      Represents names (.const name us) (.const name vs)
  | app : Represents names f f' → Represents names a a' → Represents names (.app f a) (.app f' a')
  | lam : Represents names ty ty' → Represents names b b' →
      Represents names (.lam name ty b info) (.lam ty' b')
  | forallE : Represents names ty ty' → Represents names b b' →
      Represents names (.forallE name ty b info) (.forallE ty' b')
  | letE : Represents names ty ty' → Represents names value value' → Represents names b b' →
      Represents names (.letE name ty value b flag) (.app (.lam ty' b') value')
  | metadata : Represents names b b' → Represents names (.mdata data b) b'
  | natural : Represents names (.lit (.natVal n)) (LeanTyped.numeral n)

theorem level_monomorphic (u : Lean.Level) : level [] u = LeanTyped.level u := by
  induction u <;> simp_all [level,LeanTyped.level,parameter]

/-- Loading a monomorphic native declaration already supplies exactly the
representation used by body parsing. No second interpretation of its source
or new trusted connection is required. -/
theorem Represents.monomorphic (rep : Represents [] source core) :
    LeanTyped.Represents source core := by
  have same : level [] = LeanTyped.level := funext level_monomorphic
  induction rep with
  | bvar => exact .bvar
  | sort h => exact .sort (by simpa only [same] using h)
  | constant h => exact .constant (by simpa only [same] using h)
  | app _ _ hf ha => exact .app hf ha
  | lam _ _ ht hb => exact .lam ht hb
  | forallE _ _ ht hb => exact .forallE ht hb
  | letE _ _ _ ht hv hb => exact .letE ht hv hb
  | metadata _ hb => exact .metadata hb
  | natural => exact .natural

/-- Declaration universe parameters do not affect lexical scope. A closed
native declaration type remains closed in the existing proof calculus. -/
theorem Represents.closed (rep : Represents names source core) (depth : Nat)
    (scope : LeanScalar.wellScoped depth source = true) : core.ClosedN depth := by
  have natural (n depth : Nat) : (LeanTyped.numeral n).ClosedN depth :=
    LeanTyped.Represents.closed (.natural (n := n)) depth rfl
  induction rep generalizing depth <;>
    simp_all [LeanScalar.wellScoped,VExpr.ClosedN,natural]
  all_goals grind

def translate (names : List Lean.Name) : (e : Lean.Expr) → Option {v // Represents names e v}
  | .bvar n => some ⟨.bvar n, .bvar⟩
  | .sort u =>
      match h : level names u with
      | some v => some ⟨.sort v, .sort h⟩
      | none => none
  | .const name us =>
      match h : us.mapM (level names) with
      | some vs => some ⟨.const name vs, .constant h⟩
      | none => none
  | .app f a => do
      let ⟨f', hf⟩ ← translate names f
      let ⟨a', ha⟩ ← translate names a
      return ⟨.app f' a', .app hf ha⟩
  | .lam _ ty b _ => do
      let ⟨ty', ht⟩ ← translate names ty
      let ⟨b', hb⟩ ← translate names b
      return ⟨.lam ty' b', .lam ht hb⟩
  | .forallE _ ty b _ => do
      let ⟨ty', ht⟩ ← translate names ty
      let ⟨b', hb⟩ ← translate names b
      return ⟨.forallE ty' b', .forallE ht hb⟩
  | .letE _ ty value b _ => do
      let ⟨ty', ht⟩ ← translate names ty
      let ⟨value', hv⟩ ← translate names value
      let ⟨b', hb⟩ ← translate names b
      return ⟨.app (.lam ty' b') value', .letE ht hv hb⟩
  | .mdata _ b => do
      let ⟨b', hb⟩ ← translate names b
      return ⟨b', .metadata hb⟩
  | .lit (.natVal n) => some ⟨LeanTyped.numeral n, .natural⟩
  | _ => none

/-- The source-to-proof-calculus translation is complete for its independent
representation judgment, including binders, metadata and compact numerals. -/
theorem Represents.translate_complete (rep : Represents names source core) :
    ∃ result, translate names source = some result ∧ result.val = core := by
  induction rep with
  | bvar => exact ⟨_,rfl,rfl⟩
  | sort level =>
    refine ⟨⟨_,.sort level⟩,?_,rfl⟩
    simp only [translate]
    split
    · rename_i v found
      have same := Option.some.inj (found.symm.trans level)
      subst v
      rfl
    · rename_i missing
      rw [level] at missing
      contradiction
  | constant levels =>
    refine ⟨⟨_,.constant levels⟩,?_,rfl⟩
    simp only [translate]
    split
    · rename_i vs found
      have same := Option.some.inj (found.symm.trans levels)
      subst vs
      rfl
    · rename_i missing
      rw [levels] at missing
      contradiction
  | app f a ihf iha =>
    obtain ⟨⟨f',hf⟩,first,ef⟩ := ihf
    obtain ⟨⟨a',ha⟩,second,ea⟩ := iha
    dsimp only at ef ea
    subst f'; subst a'
    simp only [translate,first,second,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩
  | lam ty body iht ihb | forallE ty body iht ihb =>
    obtain ⟨⟨t',ht⟩,first,et⟩ := iht
    obtain ⟨⟨b',hb⟩,second,eb⟩ := ihb
    dsimp only at et eb
    subst t'; subst b'
    simp only [translate,first,second,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩
  | letE ty value body iht ihv ihb =>
    obtain ⟨⟨t',ht⟩,first,et⟩ := iht
    obtain ⟨⟨v',hv⟩,second,ev⟩ := ihv
    obtain ⟨⟨b',hb⟩,third,eb⟩ := ihb
    dsimp only at et ev eb
    subst t'; subst v'; subst b'
    simp only [translate,first,second,third,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩
  | metadata body ih =>
    obtain ⟨⟨b',hb⟩,success,eq⟩ := ih
    dsimp only at eq
    subst b'
    simp only [translate,success,bind,Option.bind]
    exact ⟨_,rfl,rfl⟩
  | natural => exact ⟨_,rfl,rfl⟩


structure Declaration (nativeEnv : Lean.Environment) (name : Lean.Name) where
  info : Lean.ConstantInfo
  found : nativeEnv.find? name = some info
  named : info.name = name
  type : {v // Represents info.levelParams info.type v}

def load (nativeEnv : Lean.Environment) (name : Lean.Name) : Option (Declaration nativeEnv name) :=
  match found : nativeEnv.find? name with
  | none => none
  | some info => do
      if named : info.name = name then
        let type ← translate info.levelParams info.type
        return ⟨info, found, named, type⟩
      else none

/-- A well-formed native signature is loadable; this premise is the existing
structural representation relation, not a successful loader invocation. -/
theorem Declaration.load_complete (d : Declaration native name) :
    ∃ result, load native name = some result := by
  obtain ⟨ty,translated,same⟩ := d.type.property.translate_complete
  unfold load
  split
  · rename_i missing
    rw [d.found] at missing
    contradiction
  · rename_i info found
    have eqn := Option.some.inj (found.symm.trans d.found)
    subst info
    simp only [dif_pos d.named,translated,bind,Option.bind]
    exact ⟨_,rfl⟩

def Declaration.signature (d : Declaration nativeEnv name) : VConstant :=
  ⟨d.info.levelParams.length, d.type.val⟩

def Declaration.install (d : Declaration nativeEnv name) (base : VEnv) : Option VEnv :=
  base.addConst name d.signature

theorem Declaration.installed (d : Declaration nativeEnv name)
    (h : d.install base = some env) :
    env.constants name = some d.signature ∧ Represents d.info.levelParams d.info.type d.signature.type :=
  ⟨VEnv.addConst_self h, d.type.property⟩

/-- Register types selected from the actual environment. This does not prove
    Ordered or import the semantics of constants by adding arbitrary equations. -/
def installTypes (nativeEnv : Lean.Environment) (base : VEnv) : List Lean.Name → Option VEnv
  | [] => some base
  | name :: rest => do
      let d ← load nativeEnv name
      let next ← d.install base
      installTypes nativeEnv next rest

/-- Installing a finite set of distinct, well-formed native declarations
cannot fail on a duplicate. Library loading does not require type-checker
success as an input assumption. -/
theorem installTypes_complete (names : List Lean.Name)
    (unique : names.Nodup)
    (available : ∀ n ∈ names, Nonempty (Declaration native n))
    (fresh : ∀ n ∈ names, base.constants n = none) :
    ∃ env, installTypes native base names = some env := by
  induction names generalizing base with
  | nil => exact ⟨base,rfl⟩
  | cons name names ih =>
    obtain ⟨witness⟩ := available name (by simp)
    obtain ⟨d,loaded⟩ := witness.load_complete
    let next : VEnv := { base with constants := fun n => if name = n then some d.signature else base.constants n }
    have installed : d.install base = some next := by
      simp only [Declaration.install,VEnv.addConst,fresh name (by simp)]
      rfl
    have tailFresh : ∀ n ∈ names, next.constants n = none := by
      intro n member
      have different : name ≠ n := by
        intro eqn
        subst n
        exact (List.nodup_cons.mp unique).1 member
      simpa only [next,if_neg different] using fresh n (by simp [member])
    obtain ⟨env,done⟩ := ih (List.nodup_cons.mp unique).2
      (fun n member => available n (by simp [member])) tailFresh
    exact ⟨env,by simp only [installTypes,loaded,installed,bind,Option.bind,done]⟩

/-- Successful installation preserves old declarations and includes every
requested name. Used to derive, rather than assume, the frontend environment. -/
theorem installTypes_present (names : List Lean.Name)
    (installed : installTypes native base names = some env) :
    base ≤ env ∧ ∀ n ∈ names, ∃ signature, env.constants n = some signature := by
  induction names generalizing base with
  | nil => cases installed; exact ⟨⟨id,id⟩,by simp⟩
  | cons name names ih =>
    simp only [installTypes] at installed
    cases hd : load native name with
    | none => simp [hd] at installed
    | some d =>
      cases he : d.install base with
      | none => simp [hd,he] at installed
      | some next =>
        simp only [hd,he,bind,Option.bind] at installed
        obtain ⟨extension,present⟩ := ih installed
        refine ⟨(VEnv.addConst_le he).trans extension,?_⟩
        intro n member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨d.signature,extension.constants (d.installed he).1⟩
        · exact present n member

theorem Declaration.signature_unique (a b : Declaration native name) : a.signature = b.signature := by
  have same : a.info = b.info := Option.some.inj (a.found.symm.trans b.found)
  obtain ⟨x,hx,ex⟩ := a.type.property.translate_complete
  obtain ⟨y,hy,ey⟩ := b.type.property.translate_complete
  have ax : (translate a.info.levelParams a.info.type).map Subtype.val = some a.type.val := by
    rw [hx]; simpa using congrArg some ex
  have byy : (translate b.info.levelParams b.info.type).map Subtype.val = some b.type.val := by
    rw [hy]; simpa using congrArg some ey
  have mapped := congrArg (fun info : Lean.ConstantInfo =>
    (translate info.levelParams info.type).map (fun value => value.val)) same
  have values := Option.some.inj (ax.symm.trans (mapped.trans byy))
  exact (congrArg (fun info : Lean.ConstantInfo => VConstant.mk info.levelParams.length a.type.val) same).trans
    (congrArg (VConstant.mk b.info.levelParams.length) values)

/-- Every imported signature is the translation of that exact native
    declaration. This is provenance, not an assumed source/target equality. -/
def Faithful (native : Lean.Environment) (env : VEnv) : Prop :=
  ∀ name signature, env.constants name = some signature →
    ∃ d : Declaration native name, signature = d.signature

theorem faithful_empty : Faithful native VEnv.empty := by
  intro name signature h
  cases h

theorem Declaration.install_faithful (d : Declaration native name)
    (baseFaithful : Faithful native base) (installed : d.install base = some env) :
    Faithful native env := by
  unfold Declaration.install VEnv.addConst at installed
  split at installed
  · cases installed
  · cases installed
    intro other signature found
    by_cases same : name = other
    · subst other
      simp only [ite_true, Option.some.injEq] at found
      exact ⟨d,found.symm⟩
    · simp only [same, ite_false] at found
      exact baseFaithful other signature found

theorem installTypes_faithful (names : List Lean.Name)
    (baseFaithful : Faithful native base)
    (installed : installTypes native base names = some env) : Faithful native env := by
  induction names generalizing base with
  | nil => cases installed; exact baseFaithful
  | cons name names ih =>
      simp only [installTypes] at installed
      cases hd : load native name with
      | none => simp [hd] at installed
      | some d =>
        cases he : d.install base with
        | none => simp [hd,he] at installed
        | some next =>
          simp [hd,he] at installed
          exact ih (d.install_faithful baseFaithful he) installed

theorem installTypes_no_equations (names : List Lean.Name)
    (baseEmpty : ∀ equation, ¬ base.defeqs equation)
    (installed : installTypes native base names = some env) : ∀ equation, ¬ env.defeqs equation := by
  induction names generalizing base with
  | nil => cases installed; exact baseEmpty
  | cons name names ih =>
      simp only [installTypes] at installed
      cases hd : load native name with
      | none => simp [hd] at installed
      | some d =>
        cases he : d.install base with
        | none => simp [hd,he] at installed
        | some next =>
          simp [hd,he] at installed
          apply ih (base := next) _ installed
          unfold Declaration.install VEnv.addConst at he
          split at he
          · cases he
          · cases he; exact baseEmpty

end IRComparison.LeanLibrary
