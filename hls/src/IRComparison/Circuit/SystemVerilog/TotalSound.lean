import IRComparison.Circuit.SystemVerilog.ReferenceSound

namespace IRComparison.Circuit.SystemVerilog

/-- Proof-only record of how the actual memoizing generator assembled its
netlist. It records calls to the existing template and allocation functions;
no alternate compiler or runtime certificate checker is introduced. -/
inductive EmissionTrace (a : Artifact) : Emission → Prop where
  | empty : EmissionTrace a {}
  | step : EmissionTrace a before → before.WellFormed →
      Paired (fun child sig => (child,sig) ∈ before.cache.toList) e.children args →
      termTemplate a e args = .ok (rhs,width) →
      recordTerm e rhs width before = .ok (signal,after) → EmissionTrace a after

theorem extends_cache_member {before after : Emission} (grows : before.Extends after)
    (member : entry ∈ before.cache.toList) : entry ∈ after.cache.toList := by
  obtain ⟨extra,he⟩ := grows.entries
  simp [he,member]

theorem Paired.imp (h : Paired relation xs ys) (weaker : ∀ x y, relation x y → other x y) :
    Paired other xs ys := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (weaker _ _ head) ih

theorem mapM_cached (items : List α) (action : α → EmitM Signal) (source : α → RTL.Term)
    (each : ∀ item ∈ items, Builds (action item) (fun sig state => (source item,sig) ∈ state.cache.toList))
    (good : before.WellFormed) (success : items.mapM action before = .ok (signals,after)) :
    after.WellFormed ∧ before.Extends after ∧
      Paired (fun item sig => (source item,sig) ∈ after.cache.toList) items signals := by
  induction items generalizing before signals after with
  | nil =>
    obtain ⟨rfl,rfl⟩ := pure_success [] success
    exact ⟨good,Emission.Extends.refl _,.nil⟩
  | cons item rest ih =>
    rw [List.mapM_cons] at success
    obtain ⟨head,middle,first,remaining⟩ := bind_success _ _ success
    obtain ⟨middleGood,grows,headMember⟩ := each item (by simp) before good head middle first
    obtain ⟨tail,last,next,returned⟩ := bind_success _ _ remaining
    obtain ⟨rfl,rfl⟩ := pure_success (head::tail) returned
    obtain ⟨afterGood,restGrows,tailMembers⟩ := ih (fun x hx => each x (by simp [hx])) middleGood next
    exact ⟨afterGood,grows.trans restGrows,.cons (extends_cache_member restGrows headMember) tailMembers⟩

def TracePreserves (a : Artifact) (action : EmitM α) : Prop :=
  Preserves action ∧ ∀ before, before.WellFormed → EmissionTrace a before →
    ∀ result after, action before = .ok (result,after) → EmissionTrace a after

@[simp] theorem trace_pure (result : α) : TracePreserves a (pure result : EmitM α) := by
  refine ⟨preserves_pure _,?_⟩
  intro before good previous returned after success
  obtain ⟨rfl,rfl⟩ := pure_success result success
  exact previous
@[simp] theorem trace_lift (action : Except String α) : TracePreserves a (StateT.lift action : EmitM α) := by
  refine ⟨preserves_lift _,?_⟩
  intro before good previous returned after success
  obtain ⟨_,rfl⟩ := lift_success action success
  exact previous
@[simp] theorem trace_bind {action : EmitM α} {next : α → EmitM β}
    (first : TracePreserves a action) (following : ∀ result, TracePreserves a (next result)) :
    TracePreserves a (action >>= next) := by
  refine ⟨preserves_bind _ _ first.1 (fun result => (following result).1),?_⟩
  intro before good previous result after success
  obtain ⟨mid,middle,firstStep,lastStep⟩ := bind_success _ _ success
  have middleGood := (first.1 before good mid middle firstStep).1
  exact (following mid).2 middle middleGood (first.2 before good previous mid middle firstStep) result after lastStep
@[simp] theorem trace_map (f : α → β) (h : TracePreserves a action) : TracePreserves a (f <$> action) := by
  rw [map_eq_pure_bind]
  exact trace_bind h (fun _ => trace_pure _)
@[simp] theorem trace_liftM (action : Except String α) : TracePreserves a (liftM action : EmitM α) := trace_lift action
@[simp] theorem trace_throw (message : String) : TracePreserves a (throw message : EmitM α) := by
  refine ⟨preserves_throw _,?_⟩
  intro before good previous result after success
  cases success
@[simp] theorem trace_require (condition : Bool) (message : String) : TracePreserves a (require condition message) := by
  cases condition <;> simp [require]

theorem trace_mapM (items : List α) (action : α → EmitM β)
    (each : ∀ item ∈ items, TracePreserves a (action item)) : TracePreserves a (items.mapM action) := by
  induction items with
  | nil => exact trace_pure _
  | cons item rest ih =>
    rw [List.mapM_cons]
    exact trace_bind (each item (by simp)) (fun _ =>
      trace_bind (ih (fun x hx => each x (by simp [hx]))) (fun _ => trace_pure _))

@[simp] theorem trace_termText (a : Artifact) (e : RTL.Term) : TracePreserves a (termText a e) := by
  refine ⟨preserves_termText a e,?_⟩
  intro before good previous signal after success
  rw [termText.eq_def,get_bind] at success
  cases found : before.cache.toList.find? (fun p => p.1 == e) with
  | some pair =>
    simp only [found] at success
    change Except.ok (_,before) = Except.ok (signal,after) at success
    cases success
    exact previous
  | none =>
    simp only [found,pure_bind] at success
    obtain ⟨args,middle,children,rest⟩ := bind_success _ _ success
    have childPass := trace_mapM e.children.attach (fun child => termText a child.val)
      (fun child _ => trace_termText a child.val)
    have middleTrace := childPass.2 before good previous args middle children
    have each : ∀ child ∈ e.children.attach,
        Builds (termText a child.val) (fun sig state => (child.val,sig) ∈ state.cache.toList) := by
      intro child _
      exact (termText_builds a child.val).weaken (fun _ _ h => h.2)
    obtain ⟨middleGood,_,members⟩ := mapM_cached _ _ Subtype.val each good children
    have paired : Paired (fun child sig => (child,sig) ∈ middle.cache.toList) e.children args := by
      simpa using (Paired.map_left (f:=Subtype.val)
        (relation:=fun (child : RTL.Term) (sig : Signal) => (child,sig) ∈ middle.cache.toList) members)
    obtain ⟨pair,last,compiled,stored⟩ := bind_success _ _ rest
    obtain ⟨templateResult,stateEq⟩ := lift_success (termTemplate a e args) compiled
    subst last
    exact .step middleTrace middleGood paired templateResult stored
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ child.property

@[simp] theorem trace_validityText (a : Artifact) (v : RTL.Validity) : TracePreserves a (validityText a v) := by
  induction v <;> simp_all (config := {maxDischargeDepth := 20}) [validityText]
@[simp] theorem trace_expression (a : Artifact) (e : RTL.Combinational) : TracePreserves a (expression a e) := by
  simp (config := {maxDischargeDepth := 20}) [expression]
@[simp] theorem trace_wordValue (a : Artifact) (e : RTL.Combinational) : TracePreserves a (wordValue a e) := trace_require _ _
@[simp] theorem trace_scalarCode (a : Artifact) (e : RTL.Scalar RTL.Combinational) : TracePreserves a (scalarCode a e) := by
  cases e <;> simp [scalarCode]
@[simp] theorem trace_testCode (a : Artifact) (e : RTL.Test RTL.Combinational) : TracePreserves a (testCode a e) := by
  induction e <;> simp_all (config := {maxDischargeDepth := 20}) [testCode]
@[simp] theorem trace_statementCode (a : Artifact) (s : RTL.Statement RTL.Combinational) : TracePreserves a (statementCode a s) := by
  induction s with
  | skip => exact trace_pure _
  | assign target rhs => cases target <;> cases rhs <;> simp (config := {maxDischargeDepth := 20}) [statementCode]
  | memory target rhs => cases rhs <;> simp (config := {maxDischargeDepth := 20}) [statementCode]
  | queue target rhs => cases rhs <;> simp (config := {maxDischargeDepth := 20}) [statementCode]
  | seq first second ihFirst ihSecond => simp_all (config := {maxDischargeDepth := 20}) [statementCode]
  | branch condition yes no ihYes ihNo => simp_all (config := {maxDischargeDepth := 20}) [statementCode]

theorem generateCode_trace (a : Artifact) (generated : generateCode a = .ok (statements,emission)) :
    EmissionTrace a emission := by
  have h := trace_mapM (RTL.artifactProgram a).cases.toList (statementCode a) (fun item _ => trace_statementCode a item)
  exact h.2 {} Emission.empty_wellFormed .empty statements emission generated


theorem SignedMeaning.agrees (meaning : SignedMeaning before e width v) (scope : e.Before limit)
    (same : Environment.AgreesBefore limit before after) : SignedMeaning after e width v := by
  refine ⟨meaning.positive,?_,meaning.fits,?_⟩
  · rw [← e.type_agrees scope same]
    exact meaning.typed
  · intro contextWidth
    rw [← e.eval_agrees scope same]
    exact meaning.contexts contextWidth

theorem appendWires_append (base : Environment) (first second : List Wire) (values : Array Int) :
    appendWires base (first ++ second) values =
      (appendWires base first values >>= fun middle => appendWires base second middle) := by
  induction first generalizing values with
  | nil => rfl
  | cons wire rest ih =>
    simp only [List.cons_append,appendWires]
    split
    · cases assigned : wire.value.assignment (base.withTemporaries values) wire.width <;>
        simp [assigned,ih,bind,Option.bind]
    · simp [bind,Option.bind]

def Declared (base : Environment) (emission : Emission) : Prop :=
  ∀ wire ∈ emission.text.toList, base.type wire.name = ⟨wire.width,true⟩

/-- Physical reads do not depend on temporary values. Only the finite set
of generated source terms is quantified here, not every possible identifier. -/
def PhysicalFor (a : Artifact) (r : Runtime) (base : Environment) (emission : Emission) : Prop :=
  ∀ entry ∈ emission.cache.toList, ∀ values, PhysicalNode a r (base.withTemporaries values) entry.1

/-- Evaluate the actual declaration sequence and simultaneously establish the
meaning of its shared values. No evaluation-success premise is used. -/
theorem EmissionTrace.total (trace : EmissionTrace a emission)
    (declared : Declared base emission) (physical : PhysicalFor a r base emission) :
    ∃ values, appendWires base emission.text.toList #[] = some values ∧
      values.size = emission.text.size ∧ CacheMeaning (base.withTemporaries values) r emission := by
  induction trace with
  | empty => exact ⟨#[],rfl,rfl,CacheMeaning.empty⟩
  | @step before args e rhs width signal after prior good paired compiled stored ih =>
    unfold recordTerm at stored
    split at stored
    · rename_i positive
      cases stored
      have declaredBefore : Declared base before := by
        intro wire member
        exact declared wire (by simp [member])
      have physicalBefore : PhysicalFor a r base before := by
        intro entry member values
        exact physical entry (by simp [member]) values
      obtain ⟨values,evaluated,size,previous⟩ := ih declaredBefore physicalBefore
      have operands : Paired (fun child sig =>
          SignedMeaning (base.withTemporaries values) (.reference sig.name) sig.width (child.eval r)) e.children args :=
        paired.imp (fun child sig member => previous (child,sig) member)
      have parent := physical (e,⟨.temporary before.cache.size,.bit true,width,positive⟩) (by simp) values
      have meaning := termTemplate_correct a r e parent operands compiled
      have nextType : base.type (.temporary before.cache.size) = ⟨width,true⟩ :=
        declared ⟨.temporary before.cache.size,width,rhs,positive⟩ (by simp)
      have count : before.cache.size = values.size := good.lengths.trans size.symm
      refine ⟨values.push (e.eval r),?_,by simp [size],?_⟩
      · rw [Array.toList_push,appendWires_append,evaluated]
        simp only [bind,Option.bind,appendWires,count,beq_self_eq_true,Bool.not_true,
          Bool.false_eq_true,↓reduceIte,pure,PUnit.unit,meaning.assignment,meaning.fits]
      · intro entry member
        simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
        rcases member with member | rfl
        · have scope : (Expr.reference entry.2.name).Before values.size := by
            simpa only [Expr.Before,size] using good.cached entry member
          have same := base.temporaries_append values #[e.eval r]
          simpa only [Array.push_eq_append] using (previous entry member).agrees scope same
        · apply SignedMeaning.reference (base.withTemporaries (values.push (e.eval r)))
            (.temporary before.cache.size) positive nextType _ meaning.fits
          simp [Environment.withTemporaries,count]
    · cases stored

/-- The declaration environment installed by the real evaluator gives each
ordered generated wire exactly its printed width. -/
theorem declared_environment (a : Artifact) (r : FiniteRuntime a.storageShape)
    (emission : Emission) (ordered : Ordered 0 emission.text.toList) :
    Declared (environment a r emission.text #[]) emission := by
  intro wire member
  obtain ⟨k,entry⟩ := List.mem_iff_getElem?.mp member
  have named := ordered.name_at entry
  simp only [Nat.zero_add] at named
  have indexed : emission.text[k]? = some wire := by simpa using entry
  simp [environment,environmentFor,named,indexed]

/-- Successful generation from a checked layout always yields a defined
concrete SystemVerilog wire evaluation, preserving every cached source value.
This removes the evaluation-success premise from the preceding value theorem. -/
theorem generateCode_total (a : Artifact) (certificate : StorageCertificate a)
    (r : FiniteRuntime a.storageShape)
    (generated : generateCode a = .ok (statements,emission)) :
    ∃ values, evaluateWires a r emission.text = some values ∧
      CacheMeaning ((environment a r emission.text #[]).withTemporaries values) r.decode emission := by
  have closed := generateCode_references a certificate generated
  have physical : PhysicalFor a r.decode (environment a r emission.text #[]) emission := by
    intro entry member values
    exact physicalNode_finite a r emission.text values entry.1 (closed entry member)
  obtain ⟨values,evaluated,_,meaning⟩ := (generateCode_trace a generated).total
    (declared_environment a r emission (generateCode_ordered a generated)) physical
  exact ⟨values,evaluated,meaning⟩

end IRComparison.Circuit.SystemVerilog
