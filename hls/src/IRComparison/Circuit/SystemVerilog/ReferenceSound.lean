import IRComparison.Circuit.SystemVerilog.PhysicalSound

namespace IRComparison.Circuit.SystemVerilog

@[simp] theorem references_literal : ReferencesIn s (.literal n) := by
  rw [ReferencesIn.eq_def]
  simp [RTL.Term.children]
@[simp] theorem references_wire : ReferencesIn s (.wire n) ↔ n < s.wires.size := by
  rw [ReferencesIn.eq_def]
  simp [RTL.Term.children]
@[simp] theorem references_register : ReferencesIn s (.register n) ↔ n < s.registers := by
  rw [ReferencesIn.eq_def]
  simp [RTL.Term.children]
@[simp] theorem references_length : ReferencesIn s (.length n) ↔ n < s.memories := by
  rw [ReferencesIn.eq_def]
  simp [RTL.Term.children]
@[simp] theorem references_cell : ReferencesIn s (.cell n j) ↔ n < s.memories ∧ ReferencesIn s j := by
  rw [ReferencesIn.eq_def]
  simp [RTL.Term.children]
@[simp] theorem references_binary : ReferencesIn s (.binary op u v) ↔ ReferencesIn s u ∧ ReferencesIn s v := by
  rw [ReferencesIn.eq_def]
  simp [RTL.Term.children]
@[simp] theorem references_resize : ReferencesIn s (.resize k v) ↔ ReferencesIn s v := by
  rw [ReferencesIn.eq_def]
  simp [RTL.Term.children]
@[simp] theorem references_nonnegative : ReferencesIn s (.nonnegative v) ↔ ReferencesIn s v := by
  rw [ReferencesIn.eq_def]
  simp [RTL.Term.children]
@[simp] theorem references_mux : ReferencesIn s (.mux c u v) ↔ ReferencesIn s c ∧ ReferencesIn s u ∧ ReferencesIn s v := by
  rw [ReferencesIn.eq_def]
  simp [RTL.Term.children,and_assoc]

def CacheAll (predicate : RTL.Term → Prop) (emission : Emission) : Prop :=
  ∀ entry ∈ emission.cache.toList, predicate entry.1

def CachePreserves (predicate : RTL.Term → Prop) (action : EmitM α) : Prop :=
  Preserves action ∧ ∀ before, before.WellFormed → CacheAll predicate before →
    ∀ result after, action before = .ok (result,after) → CacheAll predicate after

@[simp] theorem cache_pure (result : α) : CachePreserves predicate (pure result : EmitM α) := by
  refine ⟨preserves_pure _,?_⟩
  intro before good previous returned after success
  obtain ⟨rfl,rfl⟩ := pure_success result success
  exact previous

@[simp] theorem cache_lift (action : Except String α) : CachePreserves predicate (StateT.lift action : EmitM α) := by
  refine ⟨preserves_lift _,?_⟩
  intro before good previous returned after success
  obtain ⟨_,rfl⟩ := lift_success action success
  exact previous

@[simp] theorem cache_bind {action : EmitM α} {next : α → EmitM β}
    (first : CachePreserves predicate action) (following : ∀ result, CachePreserves predicate (next result)) :
    CachePreserves predicate (action >>= next) := by
  refine ⟨preserves_bind _ _ first.1 (fun result => (following result).1),?_⟩
  intro before good previous result after success
  obtain ⟨mid,middle,firstStep,lastStep⟩ := bind_success _ _ success
  have middleGood := (first.1 before good mid middle firstStep).1
  exact (following mid).2 middle middleGood (first.2 before good previous mid middle firstStep) result after lastStep

@[simp] theorem cache_map (f : α → β) (h : CachePreserves predicate action) :
    CachePreserves predicate (f <$> action) := by
  rw [map_eq_pure_bind]
  exact cache_bind h (fun _ => cache_pure _)
@[simp] theorem cache_liftM (action : Except String α) : CachePreserves predicate (liftM action : EmitM α) := cache_lift action
@[simp] theorem cache_throw (message : String) : CachePreserves predicate (throw message : EmitM α) := by
  refine ⟨preserves_throw _,?_⟩
  intro before good previous result after success
  cases success
@[simp] theorem cache_require (condition : Bool) (message : String) : CachePreserves predicate (require condition message) := by
  cases condition <;> simp [require]

theorem cache_mapM (items : List α) (action : α → EmitM β)
    (each : ∀ item ∈ items, CachePreserves predicate (action item)) :
    CachePreserves predicate (items.mapM action) := by
  induction items with
  | nil => exact cache_pure _
  | cons item rest ih =>
    rw [List.mapM_cons]
    exact cache_bind (each item (by simp)) (fun _ =>
      cache_bind (ih (fun x hx => each x (by simp [hx]))) (fun _ => cache_pure _))

theorem cache_recordTerm (holds : predicate e) (previous : CacheAll predicate before)
    (success : recordTerm e rhs width before = .ok (signal,after)) : CacheAll predicate after := by
  unfold recordTerm at success
  split at success
  · cases success
    intro entry member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with member | rfl
    · exact previous entry member
    · exact holds
  · cases success

/-- Any predicate closed under child terms is preserved by the actual
memoizing traversal. This will be instantiated with layout bounds. -/
theorem cache_termText (a : Artifact) (e : RTL.Term) (holds : predicate e)
    (childrenClosed : ∀ parent, predicate parent → ∀ child ∈ parent.children, predicate child) :
    CachePreserves predicate (termText a e) := by
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
    have childPass : CachePreserves predicate (e.children.attach.mapM fun child => termText a child.val) :=
      cache_mapM _ _ (fun child _ => cache_termText a child.val
        (childrenClosed e holds child.val child.property) childrenClosed)
    have middleGood := (childPass.1 before good args middle children).1
    have middleAll := childPass.2 before good previous args middle children
    obtain ⟨pair,last,compiled,stored⟩ := bind_success _ _ rest
    obtain ⟨_,stateEq⟩ := lift_success (termTemplate a e args) compiled
    subst last
    exact cache_recordTerm holds middleAll stored
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ child.property

@[simp] theorem cache_termText_references (a : Artifact) (e : RTL.Term) (holds : ReferencesIn shape e) :
    CachePreserves (ReferencesIn shape) (termText a e) := by
  apply cache_termText a e holds
  intro parent closed child member
  rw [ReferencesIn.eq_def] at closed
  exact closed.2 child member


def ValidityReferences (shape : StorageShape) : RTL.Validity → Prop
  | .yes | .no => True
  | .and u v => ValidityReferences shape u ∧ ValidityReferences shape v
  | .address n j => n < shape.memories ∧ ReferencesIn shape j
  | .mux c u v => ReferencesIn shape c ∧ ValidityReferences shape u ∧ ValidityReferences shape v

def CombinationalReferences (shape : StorageShape) (e : RTL.Combinational) : Prop :=
  ReferencesIn shape e.value ∧ ValidityReferences shape e.valid

@[simp] theorem validityReferences_both (ha : ValidityReferences shape a)
    (hb : ValidityReferences shape b) : ValidityReferences shape (RTL.Validity.both a b) := by
  cases a <;> cases b <;> simp_all [RTL.Validity.both,ValidityReferences]

@[simp] theorem validityReferences_choose (hc : ReferencesIn shape c)
    (ha : ValidityReferences shape a) (hb : ValidityReferences shape b) :
    ValidityReferences shape (RTL.Validity.choose c a b) := by
  cases a <;> cases b <;> simp_all [RTL.Validity.choose,ValidityReferences]

def ScalarReferences (shape : StorageShape) : RTL.Scalar RTL.Combinational → Prop
  | .value e => CombinationalReferences shape e
  | _ => True

def TestReferences (shape : StorageShape) : RTL.Test RTL.Combinational → Prop
  | .valid e | .nonzero e => CombinationalReferences shape e
  | .address n e => n < shape.memories ∧ CombinationalReferences shape e
  | .and u v => TestReferences shape u ∧ TestReferences shape v
  | _ => True

def StatementReferences (shape : StorageShape) : RTL.Statement RTL.Combinational → Prop
  | .skip => True
  | .assign _ e => ScalarReferences shape e
  | .memory _ (.set _ j v) => CombinationalReferences shape j ∧ CombinationalReferences shape v
  | .memory .. => True
  | .queue _ (.append _ v) => CombinationalReferences shape v
  | .queue .. => True
  | .seq u v => StatementReferences shape u ∧ StatementReferences shape v
  | .branch c u v => TestReferences shape c ∧ StatementReferences shape u ∧ StatementReferences shape v

@[simp] theorem cache_validityText (a : Artifact) (v : RTL.Validity) (closed : ValidityReferences shape v) :
    CachePreserves (ReferencesIn shape) (validityText a v) := by
  induction v <;> simp_all (config := {maxDischargeDepth := 20}) [validityText,ValidityReferences]

@[simp] theorem cache_expression (a : Artifact) (e : RTL.Combinational) (closed : CombinationalReferences shape e) :
    CachePreserves (ReferencesIn shape) (expression a e) := by
  simp (config := {maxDischargeDepth := 20}) [expression,closed.1,closed.2]

@[simp] theorem cache_wordValue (a : Artifact) (e : RTL.Combinational) :
    CachePreserves (ReferencesIn shape) (wordValue a e) := cache_require _ _

@[simp] theorem cache_scalarCode (a : Artifact) (e : RTL.Scalar RTL.Combinational) (closed : ScalarReferences shape e) :
    CachePreserves (ReferencesIn shape) (scalarCode a e) := by
  cases e <;> simp_all [scalarCode,ScalarReferences]

@[simp] theorem cache_testCode (a : Artifact) (e : RTL.Test RTL.Combinational) (closed : TestReferences shape e) :
    CachePreserves (ReferencesIn shape) (testCode a e) := by
  induction e <;> simp_all (config := {maxDischargeDepth := 20}) [testCode,TestReferences]

@[simp] theorem cache_statementCode (a : Artifact) (s : RTL.Statement RTL.Combinational) (closed : StatementReferences shape s) :
    CachePreserves (ReferencesIn shape) (statementCode a s) := by
  induction s with
  | skip => exact cache_pure _
  | assign target rhs => cases target <;> cases rhs <;> simp_all (config := {maxDischargeDepth := 20}) [statementCode,StatementReferences,ScalarReferences]
  | memory target rhs => cases rhs <;> simp_all (config := {maxDischargeDepth := 20}) [statementCode,StatementReferences]
  | queue target rhs => cases rhs <;> simp_all (config := {maxDischargeDepth := 20}) [statementCode,StatementReferences]
  | seq first second ihFirst ihSecond => simp_all (config := {maxDischargeDepth := 20}) [statementCode,StatementReferences]
  | branch condition yes no ihYes ihNo => simp_all (config := {maxDischargeDepth := 20}) [statementCode,StatementReferences]

@[simp] theorem combinational_references (wr : Nat → Interval) (e : Circuit.Expr) (closed : e.inStorage shape) :
    CombinationalReferences shape (RTL.combinational wr e) := by
  induction e <;> simp_all [Circuit.Expr.inStorage,RTL.combinational,CombinationalReferences,ValidityReferences,StorageShape.hasMemory]

theorem lowerNode_references (wr : Nat → Interval) (node : Node) (closed : node.inStorage shape) :
    StatementReferences shape ((RTL.lowerNode node).mapExpressions (RTL.combinational wr)) := by
  cases node <;>
    simp_all (config := {maxDischargeDepth := 20}) [Node.inStorage,StorageShape.hasMemory,
      RTL.lowerNode,RTL.halt,RTL.advance,RTL.guarded,RTL.fault,
      RTL.Statement.mapExpressions,RTL.Test.mapExpressions,RTL.Scalar.mapExpressions,
      RTL.MemoryRhs.mapExpressions,RTL.QueueRhs.mapExpressions,
      StatementReferences,TestReferences,ScalarReferences]

/-- Reference bounds follow from the already accepted storage certificate,
through lowering and the real memoizing output pass. No new input check is added. -/
theorem generateCode_references (a : Artifact) (certificate : StorageCertificate a)
    (generated : generateCode a = .ok (statements,emission)) :
    CacheAll (ReferencesIn a.storageShape) emission := by
  have each : ∀ body ∈ (RTL.artifactProgram a).cases.toList,
      CachePreserves (ReferencesIn a.storageShape) (statementCode a body) := by
    intro body member
    simp only [RTL.artifactProgram,RTL.lowerCombinational,Array.toList_map,List.mem_map] at member
    obtain ⟨node,member,rfl⟩ := member
    exact cache_statementCode a _ (lowerNode_references _ node (certificate.closed node member))
  have h := cache_mapM _ _ each
  exact h.2 {} Emission.empty_wellFormed (by intro entry member; simp at member) statements emission generated

/-- General shared-value preservation using the existing storage certificate.
Only concrete evaluation success remains to be discharged for totality. -/
theorem generateCode_checked_values (a : Artifact) (certificate : StorageCertificate a)
    (r : FiniteRuntime a.storageShape)
    (generated : generateCode a = .ok (statements,emission))
    (evaluated : evaluateWires a r emission.text = some values) :
    CacheMeaning ((environment a r emission.text #[]).withTemporaries values) r.decode emission :=
  generateCode_finite_values a r generated evaluated (generateCode_references a certificate generated)

end IRComparison.Circuit.SystemVerilog
