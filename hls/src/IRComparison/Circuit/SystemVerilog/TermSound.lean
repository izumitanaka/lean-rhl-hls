import IRComparison.Circuit.SystemVerilog.EmissionSound
import IRComparison.Circuit.SystemVerilog.TemplateSound

namespace IRComparison.Circuit.SystemVerilog

/-- Physical storage must correspond for the references actually used by the
term and its children. This does not assume any temporary net's meaning. -/
def PhysicalTree (a : Artifact) (r : Runtime) (env : Environment) (e : RTL.Term) : Prop :=
  PhysicalNode a r env e ∧ ∀ child ∈ e.children, PhysicalTree a r env child
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ ‹_›

/-- Concrete declaration equations in a fixed environment. The right-hand
side is the actual SystemVerilog assignment evaluator, not RTL.Term.eval. -/
def Realizes (env : Environment) (emission : Emission) : Prop :=
  ∀ wire ∈ emission.text.toList,
    env.type wire.name = ⟨wire.width,true⟩ ∧
    (wire.value.assignment env wire.width).map BitVec.toInt = env.scalar wire.name

def CacheMeaning (env : Environment) (r : Runtime) (emission : Emission) : Prop :=
  ∀ entry ∈ emission.cache.toList,
    SignedMeaning env (.reference entry.2.name) entry.2.width (entry.1.eval r)

theorem Realizes.restrict (h : Realizes env after) (grows : before.Extends after) : Realizes env before := by
  obtain ⟨extra,he⟩ := grows.declarations
  intro wire member
  apply h wire
  simp [he,member]

theorem CacheMeaning.empty : CacheMeaning env r {} := by intro entry member; simp at member

theorem recordTerm_correct (before : Emission) (previous : CacheMeaning env r before)
    (meaning : AssignedMeaning env rhs width (e.eval r))
    (success : recordTerm e rhs width before = .ok (signal,after))
    (realized : Realizes env after) :
    CacheMeaning env r after ∧ SignedMeaning env (.reference signal.name) signal.width (e.eval r) := by
  unfold recordTerm at success
  split at success
  · rename_i positive
    cases success
    have actual := realized ⟨.temporary before.cache.size,width,rhs,positive⟩ (by simp)
    have stored : env.scalar (.temporary before.cache.size) = some (e.eval r) := by
      rw [meaning.assignment,Option.map_some,meaning.fits] at actual
      exact actual.2.symm
    have value := SignedMeaning.reference env (.temporary before.cache.size) positive actual.1 stored meaning.fits
    refine ⟨?_,value⟩
    intro entry member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with member | rfl
    · exact previous entry member
    · exact value
  · cases success

/-- Sequence term compilation without losing which source child produced
which signal, or the meaning of a previously generated shared signal. -/
theorem mapM_correct (items : List α) (action : α → EmitM Signal) (source : α → RTL.Term)
    (structureOK : ∀ item ∈ items, Builds (action item) (fun _ _ => True))
    (each : ∀ item ∈ items, ∀ before, before.WellFormed → CacheMeaning env r before →
      ∀ signal after, action item before = .ok (signal,after) → Realizes env after →
      CacheMeaning env r after ∧ SignedMeaning env (.reference signal.name) signal.width ((source item).eval r))
    (good : before.WellFormed) (previous : CacheMeaning env r before)
    (success : items.mapM action before = .ok (signals,after)) (realized : Realizes env after) :
    CacheMeaning env r after ∧ Paired (fun item signal =>
      SignedMeaning env (.reference signal.name) signal.width ((source item).eval r)) items signals := by
  induction items generalizing before signals after with
  | nil =>
    obtain ⟨rfl,rfl⟩ := pure_success [] success
    exact ⟨previous,.nil⟩
  | cons item rest ih =>
    rw [List.mapM_cons] at success
    obtain ⟨head,middle,first,restResult⟩ := bind_success _ _ success
    obtain ⟨tail,last,next,returned⟩ := bind_success _ _ restResult
    obtain ⟨rfl,rfl⟩ := pure_success (head::tail) returned
    have midGood := (structureOK item (by simp) before good head middle first).1
    have afterExtends : middle.Extends after := by
      have helper : ∀ xs : List α, (∀ x ∈ xs, Preserves (action x)) → Preserves (xs.mapM action) := by
        intro xs each
        induction xs with
        | nil => exact preserves_pure _
        | cons x xs induction =>
          rw [List.mapM_cons]
          exact preserves_bind _ _ (each x (by simp)) (fun _ =>
            preserves_bind _ _ (induction (fun v hv => each v (by simp [hv]))) (fun _ => preserves_pure _))
      exact (helper rest (fun x hx => structureOK x (by simp [hx])) middle midGood tail after next).2.1
    obtain ⟨middleMeaning,headMeaning⟩ := each item (by simp) before good previous head middle first
      (realized.restrict afterExtends)
    obtain ⟨afterMeaning,tailMeaning⟩ := ih (fun x hx => structureOK x (by simp [hx]))
      (fun x hx => each x (by simp [hx])) midGood middleMeaning next realized
    exact ⟨afterMeaning,.cons headMeaning tailMeaning⟩


theorem Paired.map_left (h : Paired (fun a b => relation (f a) b) xs ys) :
    Paired relation (xs.map f) ys := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

/-- Correctness of the actual memoizing term compiler, not a separate checked
reimplementation. The physical references must correspond, and the emitted
continuous assignments must hold; no temporary/source equality is assumed. -/
theorem termText_correct (a : Artifact) (r : Runtime) (e : RTL.Term)
    (physical : PhysicalTree a r env e) (before : Emission) (good : before.WellFormed)
    (previous : CacheMeaning env r before) (signal : Signal) (after : Emission)
    (success : termText a e before = .ok (signal,after)) (realized : Realizes env after) :
    CacheMeaning env r after ∧ SignedMeaning env (.reference signal.name) signal.width (e.eval r) := by
  rw [termText.eq_def,get_bind] at success
  cases found : before.cache.toList.find? (fun p => p.1 == e) with
  | some pair =>
    simp only [found] at success
    change Except.ok (_,before) = Except.ok (signal,after) at success
    cases success
    have member := List.mem_of_find?_eq_some found
    have matched := List.find?_some found
    simp only [beq_iff_eq] at matched
    refine ⟨previous,?_⟩
    simpa only [← matched] using previous pair member
  | none =>
    simp only [found,pure_bind] at success
    obtain ⟨args,middle,children,rest⟩ := bind_success _ _ success
    have structureOK : ∀ child ∈ e.children.attach,
        Builds (termText a child.val) (fun sig state => sig.name.Before state.text.size) := by
      intro child _
      exact (termText_builds a child.val).weaken (fun _ _ h => h.1)
    obtain ⟨middleGood,grows,argScope⟩ := mapM_builds _ _ structureOK before good args middle children
    obtain ⟨pair,last,compiled,stored⟩ := bind_success _ _ rest
    obtain ⟨templateResult,stateEq⟩ := lift_success (termTemplate a e args) compiled
    subst last
    have rhsScope := termTemplate_scope a e args argScope templateResult
    obtain ⟨afterGood,growsAgain,_⟩ := recordTerm_sound middle middleGood rhsScope stored
    have each : ∀ child ∈ e.children.attach, ∀ b, b.WellFormed → CacheMeaning env r b →
        ∀ sig next, termText a child.val b = .ok (sig,next) → Realizes env next →
        CacheMeaning env r next ∧ SignedMeaning env (.reference sig.name) sig.width (child.val.eval r) := by
      intro child _ b good previous sig next success realized
      have childPhysical : PhysicalTree a r env child.val := by
        rw [PhysicalTree.eq_def] at physical
        exact physical.2 child.val child.property
      exact termText_correct a r child.val childPhysical b good previous sig next success realized
    obtain ⟨middleMeaning,argMeanings⟩ := mapM_correct e.children.attach (fun child => termText a child.val)
      Subtype.val (fun child member => (structureOK child member).preserves) each good previous children
      (realized.restrict growsAgain)
    have inputs : Paired (fun child sig => SignedMeaning env (.reference sig.name) sig.width (child.eval r)) e.children args := by
      simpa using (Paired.map_left (f:=Subtype.val)
        (relation:=fun (child : RTL.Term) (sig : Signal) => SignedMeaning env (.reference sig.name) sig.width (child.eval r)) argMeanings)
    have physicalNode : PhysicalNode a r env e := by
      rw [PhysicalTree.eq_def] at physical
      exact physical.1
    exact recordTerm_correct middle middleMeaning (termTemplate_correct a r e physicalNode inputs templateResult) stored realized
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ child.property


theorem Ordered.name_at {k : Nat} {wire : Wire} (ordered : Ordered start declarations)
    (entry : declarations[k]? = some wire) : wire.name = .temporary (start+k) := by
  induction declarations generalizing start k with
  | nil => simp at entry
  | cons head rest ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at entry
      subst wire
      simpa using ordered.1
    | succ k =>
      have h := ih ordered.2.2 entry
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem Satisfies.equations (satisfied : Satisfies base values start declarations)
    (member : wire ∈ declarations) :
    (wire.value.assignment (base.withTemporaries values) wire.width).map BitVec.toInt =
      (base.withTemporaries values).scalar wire.name := by
  induction declarations generalizing start with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · obtain ⟨named,⟨bits,assigned,stored⟩,_⟩ := satisfied
      rw [assigned,Option.map_some]
      simp only [named,Environment.withTemporaries,stored]
    · exact ih satisfied.2.2 member

/-- The actual topological evaluator supplies the declaration equations used
by `termText_correct`; this is not a separate user-supplied certificate. -/
theorem evaluateWires_realizes (a : Artifact) (r : FiniteRuntime a.storageShape) (emission : Emission)
    (ordered : Ordered 0 emission.text.toList)
    (evaluated : evaluateWires a r emission.text = some values) :
    Realizes ((environment a r emission.text #[]).withTemporaries values) emission := by
  intro wire member
  have satisfied := evaluateWires_satisfies a r emission.text ordered evaluated
  refine ⟨?_,satisfied.equations member⟩
  obtain ⟨k,entry⟩ := List.mem_iff_getElem?.mp member
  have named := ordered.name_at entry
  simp only [Nat.zero_add] at named
  have indexed : emission.text[k]? = some wire := by simpa using entry
  simp [Environment.withTemporaries,environment,environmentFor,named,indexed]

def PhysicalCache (a : Artifact) (r : Runtime) (env : Environment) (emission : Emission) : Prop :=
  ∀ entry ∈ emission.cache.toList, PhysicalTree a r env entry.1

theorem PhysicalCache.restrict (h : PhysicalCache a r env after) (grows : before.Extends after) :
    PhysicalCache a r env before := by
  obtain ⟨extra,he⟩ := grows.entries
  intro entry member
  apply h entry
  simp [he,member]

/-- Preservation of all compiled terms in a fixed final signal environment.
The physical premise ranges only over terms actually generated by the pass. -/
def SemanticPreserves (a : Artifact) (r : Runtime) (env : Environment) (action : EmitM α) : Prop :=
  Preserves action ∧ ∀ before, before.WellFormed → CacheMeaning env r before →
    ∀ result after, action before = .ok (result,after) → Realizes env after →
      PhysicalCache a r env after → CacheMeaning env r after

@[simp] theorem semantic_pure (result : α) : SemanticPreserves a r env (pure result : EmitM α) := by
  refine ⟨preserves_pure _,?_⟩
  intro before good previous returned after success _ _
  obtain ⟨rfl,rfl⟩ := pure_success result success
  exact previous

@[simp] theorem semantic_lift (action : Except String α) : SemanticPreserves a r env (StateT.lift action : EmitM α) := by
  refine ⟨preserves_lift _,?_⟩
  intro before good previous returned after success _ _
  obtain ⟨_,rfl⟩ := lift_success action success
  exact previous

@[simp] theorem semantic_bind {action : EmitM α} {next : α → EmitM β} (first : SemanticPreserves a r env action)
    (following : ∀ result, SemanticPreserves a r env (next result)) :
    SemanticPreserves a r env (action >>= next) := by
  refine ⟨preserves_bind _ _ first.1 (fun result => (following result).1),?_⟩
  intro before good previous result after success realized physical
  obtain ⟨mid,middle,firstStep,lastStep⟩ := bind_success _ _ success
  obtain ⟨middleGood,_,_⟩ := first.1 before good mid middle firstStep
  obtain ⟨_,grows,_⟩ := (following mid).1 middle middleGood result after lastStep
  have middleMeaning := first.2 before good previous mid middle firstStep
    (realized.restrict grows) (physical.restrict grows)
  exact (following mid).2 middle middleGood middleMeaning result after lastStep realized physical

@[simp] theorem semantic_map (f : α → β) (h : SemanticPreserves a r env action) :
    SemanticPreserves a r env (f <$> action) := by
  rw [map_eq_pure_bind]
  exact semantic_bind h (fun _ => semantic_pure _)

@[simp] theorem semantic_liftM (action : Except String α) : SemanticPreserves a r env (liftM action : EmitM α) := semantic_lift action

@[simp] theorem semantic_throw (message : String) : SemanticPreserves a r env (throw message : EmitM α) := by
  refine ⟨preserves_throw _,?_⟩
  intro before good previous result after success
  cases success

@[simp] theorem semantic_require (condition : Bool) (message : String) :
    SemanticPreserves a r env (require condition message) := by
  cases condition <;> simp [require]

@[simp] theorem semantic_termText (artifact : Artifact) (e : RTL.Term) :
    SemanticPreserves artifact r env (termText artifact e) := by
  refine ⟨preserves_termText _ _,?_⟩
  intro before good previous signal after success realized physical
  have member := (termText_builds artifact e before good signal after success).2.2.2
  exact (termText_correct artifact r e (physical (e,signal) member) before good previous signal after success realized).1

@[simp] theorem semantic_validityText (artifact : Artifact) (v : RTL.Validity) :
    SemanticPreserves artifact r env (validityText artifact v) := by
  induction v <;> simp_all (config := {maxDischargeDepth := 20}) [validityText]

@[simp] theorem semantic_expression (artifact : Artifact) (e : RTL.Combinational) :
    SemanticPreserves artifact r env (expression artifact e) := by simp [expression]

@[simp] theorem semantic_wordValue (artifact : Artifact) (e : RTL.Combinational) :
    SemanticPreserves artifact r env (wordValue artifact e) := semantic_require _ _

@[simp] theorem semantic_scalarCode (artifact : Artifact) (e : RTL.Scalar RTL.Combinational) :
    SemanticPreserves artifact r env (scalarCode artifact e) := by cases e <;> simp [scalarCode]

@[simp] theorem semantic_testCode (artifact : Artifact) (e : RTL.Test RTL.Combinational) :
    SemanticPreserves artifact r env (testCode artifact e) := by induction e <;> simp_all [testCode]

@[simp] theorem semantic_statementCode (artifact : Artifact) (s : RTL.Statement RTL.Combinational) :
    SemanticPreserves artifact r env (statementCode artifact s) := by
  induction s with
  | skip => exact semantic_pure _
  | assign target rhs => cases target <;> cases rhs <;> simp (config := {maxDischargeDepth := 20}) [statementCode]
  | memory target rhs => cases rhs <;> simp (config := {maxDischargeDepth := 20}) [statementCode]
  | queue target rhs => cases rhs <;> simp (config := {maxDischargeDepth := 20}) [statementCode]
  | seq first second ihFirst ihSecond => simp (config := {maxDischargeDepth := 20}) [statementCode,ihFirst,ihSecond]
  | branch condition yes no ihYes ihNo => simp (config := {maxDischargeDepth := 20}) [statementCode,ihYes,ihNo]

theorem semantic_mapM (items : List α) (action : α → EmitM β)
    (each : ∀ item ∈ items, SemanticPreserves a r env (action item)) :
    SemanticPreserves a r env (items.mapM action) := by
  induction items with
  | nil => exact semantic_pure _
  | cons item rest ih =>
    rw [List.mapM_cons]
    exact semantic_bind (each item (by simp)) (fun _ =>
      semantic_bind (ih (fun x hx => each x (by simp [hx]))) (fun _ => semantic_pure _))

/-- Value preservation for every shared term produced by the complete real
generator. Statement effects and physical-storage correspondence are separate
obligations, not hidden inside this theorem. -/
theorem generateCode_cache_correct (a : Artifact) (r : Runtime)
    (generated : generateCode a = .ok (statements,emission))
    (realized : Realizes env emission) (physical : PhysicalCache a r env emission) :
    CacheMeaning env r emission := by
  have sound := semantic_mapM (RTL.artifactProgram a).cases.toList (statementCode a)
    (fun item _ => semantic_statementCode a item (r:=r) (env:=env))
  exact sound.2 {} Emission.empty_wellFormed CacheMeaning.empty statements emission generated realized physical

/-- After concrete wire evaluation, each cached value is the source term's
value. Evaluation success and physical reference correspondence remain explicit;
this does not yet claim code-generation totality or whole-module correctness. -/
theorem generateCode_values_correct (a : Artifact) (r : FiniteRuntime a.storageShape)
    (generated : generateCode a = .ok (statements,emission))
    (evaluated : evaluateWires a r emission.text = some values)
    (physical : PhysicalCache a r.decode ((environment a r emission.text #[]).withTemporaries values) emission) :
    CacheMeaning ((environment a r emission.text #[]).withTemporaries values) r.decode emission :=
  generateCode_cache_correct a r.decode generated
    (evaluateWires_realizes a r emission (generateCode_ordered a generated) evaluated) physical

end IRComparison.Circuit.SystemVerilog
