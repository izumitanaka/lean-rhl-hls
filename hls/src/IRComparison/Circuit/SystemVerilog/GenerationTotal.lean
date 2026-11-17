import IRComparison.Circuit.SystemVerilog.ReferenceSound

/-! Generation success from structural conditions on the target syntax.
These conditions do not mention successful compilation or source execution.
They are intermediate obligations for the compiler, not new source restrictions. -/
namespace IRComparison.Circuit.SystemVerilog.Generation

abbrev Total (action : EmitM α) : Prop :=
  ∀ before, ∃ value after, action before = .ok (value,after)

@[simp] theorem lift_ok (v : α) (s : Emission) :
    (liftM (Except.ok v : Except String α) : EmitM α) s = .ok (v,s) := rfl

theorem total_pure (v : α) : Total (pure v) := fun s => ⟨v,s,rfl⟩

theorem total_bind {action : EmitM α} {next : α → EmitM β} (ha : Total action) (hb : ∀ value, Total (next value)) :
    Total (action >>= next) := by
  intro s
  obtain ⟨value,middle,first⟩ := ha s
  obtain ⟨result,last,second⟩ := hb value middle
  exact ⟨result,last,by simp [bind,StateT.bind,Except.bind,first,second]⟩

theorem total_mapM (xs : List α) (action : α → EmitM β)
    (each : ∀ x ∈ xs, Total (action x)) (before : Emission) :
    ∃ values after, xs.mapM action before = .ok (values,after) ∧ values.length = xs.length := by
  induction xs generalizing before with
  | nil => exact ⟨[],before,rfl,rfl⟩
  | cons x xs ih =>
    obtain ⟨v,middle,first⟩ := each x (by simp) before
    obtain ⟨vs,last,rest,len⟩ := ih (fun y hy => each y (by simp [hy])) middle
    exact ⟨v::vs,last,by simp [List.mapM_cons,bind,StateT.bind,Except.bind,first,rest,pure,StateT.pure,Except.pure],by simp [len]⟩

theorem memorySize_total {a : Artifact} {id : Nat} (h : a.storageShape.hasMemory id) :
    memorySize a id = .ok (a.storageShape.memorySize id) := by
  have live := h.2
  change a.memories.any (fun p => p.1 == id) = true at live
  have found : (a.memories.toList.find? (fun p => p.1 == id)).isSome = true := by
    rw [List.isSome_find?,Array.any_toList]
    exact live
  cases eq : a.memories.toList.find? (fun p => p.1 == id) with
  | none => simp [eq] at found
  | some p =>
    change memorySize a id = .ok (((a.memories.toList.find? (fun p => p.1 == id)).map Prod.snd).getD 0)
    simp only [memorySize,eq,Option.map_some,Option.getD_some]
    rfl

/-- Every referenced bank exists, and every explicit resize has positive width. -/
def TermReady (a : Artifact) (e : RTL.Term) : Prop :=
  (match e with
    | .wire n => n < a.wires.size
    | .length n | .cell n _ => a.storageShape.hasMemory n
    | .resize w _ => 0 < w
    | _ => True) ∧ ∀ child ∈ e.children, TermReady a child
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ ‹_›

theorem template_total (e : RTL.Term) (ready : TermReady a e)
    (args : List Signal) (count : args.length = e.children.length) :
    ∃ rhs width, termTemplate a e args = .ok (rhs,width) ∧ 0 < width := by
  rw [TermReady.eq_def] at ready
  cases e with
  | literal n =>
    have eq : args = [] := List.eq_nil_of_length_eq_zero count
    subst args
    exact ⟨_,_,rfl,by omega⟩
  | wire n =>
    have eq : args = [] := List.eq_nil_of_length_eq_zero count
    subst args
    refine ⟨.reference (.holding n),signedWidth (a.wires[n]?.getD wordRange),?_,?_⟩
    · simp [termTemplate,ready.1,pure,Except.pure,bind,Except.bind]
    · unfold signedWidth; omega
  | register n =>
    have eq : args = [] := List.eq_nil_of_length_eq_zero count
    subst args
    exact ⟨_,_,rfl,by decide⟩
  | length n =>
    have eq : args = [] := List.eq_nil_of_length_eq_zero count
    subst args
    refine ⟨.unsigned (.reference (.length n)),bits (a.storageShape.memorySize n)+1,?_,by omega⟩
    simp [termTemplate,memorySize_total ready.1,pure,Except.pure,bind,Except.bind]
  | cell n j =>
    obtain ⟨v,rfl⟩ := List.length_eq_one_iff.mp count
    simp only [termTemplate,memorySize_total ready.1]
    exact ⟨_,33,rfl,by decide⟩
  | resize w e =>
    obtain ⟨v,rfl⟩ := List.length_eq_one_iff.mp count
    exact ⟨widen v w ready.1,w,by simp [termTemplate,ready.1,pure,Except.pure],ready.1⟩
  | wrap32 e =>
    obtain ⟨v,rfl⟩ := List.length_eq_one_iff.mp count
    exact ⟨_,33,rfl,by decide⟩
  | nonnegative e =>
    obtain ⟨v,rfl⟩ := List.length_eq_one_iff.mp count
    exact ⟨_,_,rfl,v.positive⟩
  | binary op u v =>
    rw [List.eq_getElem_of_length_eq_two args count]
    exact ⟨_,_,rfl,by omega⟩
  | mux c u v =>
    rw [List.eq_getElem_of_length_eq_three args count]
    exact ⟨_,_,rfl,by have := (args[1]'(by simp only [RTL.Term.children,List.length_cons,List.length_nil] at count; omega)).positive; omega⟩


theorem termText_total (e : RTL.Term) (ready : TermReady a e) : Total (termText a e) := by
  intro before
  rw [termText.eq_def,get_bind]
  cases found : before.cache.toList.find? (fun p => p.1 == e) with
  | some pair => exact ⟨pair.2,before,rfl⟩
  | none =>
    simp only [pure_bind]
    have each : ∀ child ∈ e.children.attach, Total (termText a child.val) := by
      intro child _
      exact termText_total child.val (((TermReady.eq_def a e) ▸ ready).2 child.val child.property)
    obtain ⟨args,middle,children,count⟩ := total_mapM e.children.attach _ each before
    have count' : args.length = e.children.length := by simpa using count
    obtain ⟨rhs,width,compiled,positive⟩ := template_total e ready args count'
    let signal : Signal := ⟨.temporary middle.text.size,.bit true,width,positive⟩
    refine ⟨signal,⟨middle.text.push ⟨signal.name,width,rhs,positive⟩,middle.cache.push (e,signal)⟩,?_⟩
    simp only [bind,StateT.bind,Except.bind,children]
    simp [recordTerm,positive,compiled,signal]
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ child.property


theorem total_map (f : α → β) (h : Total action) : Total (f <$> action) := by
  simpa only [map_eq_pure_bind] using total_bind h (fun v => total_pure (f v))

theorem total_return (f : α → β) (h : Total action) : Total (do let v ← action; pure (f v)) :=
  total_bind h (fun v => total_pure (f v))

theorem total_lift_bind {action : Except String α} {next : α → EmitM β}
    (h : action = .ok v) (following : Total (next v)) :
    Total (do let value ← action; next value) := by
  subst action
  intro s
  exact following s

theorem total_lift {action : Except String α} (h : action = .ok v) :
    Total (liftM action) := by
  subst action
  intro s
  exact ⟨v,s,rfl⟩

theorem total_require (h : condition = true) : Total (require condition message) := by
  simp only [require,h,↓reduceIte]
  exact total_pure ()

def ValidityReady (a : Artifact) : RTL.Validity → Prop
  | .yes | .no => True
  | .and u v => ValidityReady a u ∧ ValidityReady a v
  | .address n j => a.storageShape.hasMemory n ∧ TermReady a j
  | .mux c u v => TermReady a c ∧ ValidityReady a u ∧ ValidityReady a v

def CombinationalReady (a : Artifact) (e : RTL.Combinational) : Prop :=
  TermReady a e.value ∧ ValidityReady a e.valid

theorem validityText_total (v : RTL.Validity) (h : ValidityReady a v) : Total (validityText a v) := by
  induction v with
  | yes => exact total_pure _
  | no => exact total_pure _
  | and u v hu hv =>
    exact total_bind (hu h.1) (fun _ => total_map _ (hv h.2))
  | address n j =>
    exact total_bind (total_lift (memorySize_total h.1)) (fun _ => total_return _ (termText_total j h.2))
  | mux c u v hu hv =>
    exact total_bind (termText_total c h.1) (fun _ =>
      total_bind (hu h.2.1) (fun _ => total_map _ (hv h.2.2)))

theorem expression_total (e : RTL.Combinational) (h : CombinationalReady a e) : Total (expression a e) :=
  total_bind (termText_total e.value h.1) (fun _ => total_return _ (validityText_total e.valid h.2))

def QueueDeclared (a : Artifact) (q : Nat) : Prop :=
  (a.machine.capacities.toList.find? (fun p => p.1 == q)).isSome = true

def WordBounds (e : RTL.Combinational) : Prop := 0 ≤ e.bounds.lo ∧ e.bounds.hi ≤ 4294967295

theorem wordValue_total (h : WordBounds e) : Total (wordValue a e) :=
  total_require (by simpa [WordBounds] using h)

def ScalarReady (a : Artifact) : RTL.Scalar RTL.Combinational → Prop
  | .literal _ => True
  | .value e => CombinationalReady a e
  | .queueHead q => QueueDeclared a q

def TestReady (a : Artifact) : RTL.Test RTL.Combinational → Prop
  | .valid e | .nonzero e => CombinationalReady a e
  | .address n e => a.storageShape.hasMemory n ∧ CombinationalReady a e
  | .room q | .nonempty q => QueueDeclared a q
  | .and u v => TestReady a u ∧ TestReady a v

theorem scalarCode_total (e : RTL.Scalar RTL.Combinational) (h : ScalarReady a e) : Total (scalarCode a e) := by
  cases e with
  | literal n => exact total_pure _
  | value e => exact total_return _ (expression_total e h)
  | queueHead q => exact total_bind (total_require h) (fun _ => total_pure _)

theorem testCode_total (e : RTL.Test RTL.Combinational) (h : TestReady a e) : Total (testCode a e) := by
  induction e with
  | valid e => exact total_map _ (expression_total e h)
  | nonzero e => exact total_return _ (expression_total e h)
  | address n e => exact total_bind (total_lift (memorySize_total h.1)) (fun _ => total_return _ (expression_total e h.2))
  | room q => exact total_bind (total_require h) (fun _ => total_pure _)
  | nonempty q => exact total_bind (total_require h) (fun _ => total_pure _)
  | and u v hu hv => exact total_bind (hu h.1) (fun _ => total_map _ (hv h.2))

def AssignmentReady (a : Artifact) (target : RTL.Register) (rhs : RTL.Scalar RTL.Combinational) : Prop :=
  ScalarReady a rhs ∧ match target with
    | .wire k => k < a.wires.size
    | .data _ => match rhs with | .value e => WordBounds e | _ => True
    | _ => True

def StatementReady (a : Artifact) : RTL.Statement RTL.Combinational → Prop
  | .skip => True
  | .seq u v => StatementReady a u ∧ StatementReady a v
  | .branch c u v => TestReady a c ∧ StatementReady a u ∧ StatementReady a v
  | .assign target rhs => AssignmentReady a target rhs
  | .memory n rhs => a.storageShape.hasMemory n ∧ match rhs with
      | .empty => True
      | .copy src => a.storageShape.hasMemory src ∧ a.storageShape.memorySize n = a.storageShape.memorySize src
      | .set src j v => src = n ∧ WordBounds v ∧ CombinationalReady a j ∧ CombinationalReady a v
  | .queue q rhs => QueueDeclared a q ∧ match rhs with
      | .empty => True
      | .tail src => src = q
      | .append src e => src = q ∧ WordBounds e ∧ CombinationalReady a e

theorem statementCode_total (s : RTL.Statement RTL.Combinational) (h : StatementReady a s) :
    Total (statementCode a s) := by
  induction s with
  | skip => exact total_pure _
  | seq u v hu hv => exact total_bind (hu h.1) (fun _ => total_map _ (hv h.2))
  | branch c u v hu hv =>
    exact total_bind (testCode_total c h.1) (fun _ => total_bind (hu h.2.1) (fun _ => total_map _ (hv h.2.2)))
  | assign target rhs =>
    apply total_bind (scalarCode_total rhs h.1)
    intro value
    cases target with
    | pc | done | error => exact total_pure _
    | wire k => exact total_bind (total_require (by simpa using h.2)) (fun _ => total_pure _)
    | data k =>
      cases rhs with
      | literal _ | queueHead _ => exact total_pure _
      | value e => exact total_bind (wordValue_total h.2) (fun _ => total_pure _)
  | memory n rhs =>
    apply total_lift_bind (memorySize_total h.1)
    cases rhs with
    | empty => exact total_pure _
    | copy src =>
      apply total_lift_bind (memorySize_total h.2.1)
      exact total_bind (total_require (by simpa using h.2.2)) (fun _ => total_pure _)
    | set src j v =>
      exact total_bind (total_require (by simpa using h.2.1)) (fun _ =>
        total_bind (wordValue_total h.2.2.1) (fun _ =>
          total_bind (expression_total j h.2.2.2.1) (fun _ =>
            total_return _ (expression_total v h.2.2.2.2))))
  | queue q rhs =>
    apply total_bind (total_require h.1)
    intro ignored
    cases rhs with
    | empty => exact total_pure _
    | tail src => exact total_bind (total_require (by simpa using h.2)) (fun _ => total_pure _)
    | append src e =>
      exact total_bind (total_require (by simpa using h.2.1)) (fun _ =>
        total_bind (wordValue_total h.2.2.1) (fun _ => total_return _ (expression_total e h.2.2.2)))


/-- A loop of successful metadata checks succeeds; no execution fuel is used. -/
theorem forIn_unit (xs : List α) (f : α → PUnit → Except String (ForInStep PUnit))
    (each : ∀ x ∈ xs, f x PUnit.unit = .ok (.yield PUnit.unit)) :
    forIn xs PUnit.unit f = .ok PUnit.unit := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons,each x (by simp)]
    simpa only [bind,Except.bind] using ih (fun y hy => each y (by simp [hy]))

structure ModuleReady (a : Artifact) : Prop where
  interface : InterfaceLayout a
  entry : a.machine.entry < a.machine.nodes.size
  memories : (a.memories.toList.map Prod.fst).eraseDups.length = a.memories.size
  queues : (a.machine.capacities.toList.map Prod.fst).eraseDups.length = a.machine.capacities.size
  closed : ∀ n ∈ a.machine.nodes.toList, n.inStorage a.storageShape

private theorem forIn_unit_then (xs : List α) (f : α → PUnit → Except String (ForInStep PUnit))
    (each : ∀ x ∈ xs, f x PUnit.unit = .ok (.yield PUnit.unit)) :
    (do let _ ← forIn xs PUnit.unit f; pure ()) = (Except.ok () : Except String Unit) := by
  rw [forIn_unit xs f each]
  rfl

theorem checkModuleArtifact_total (h : ModuleReady a) : checkModuleArtifact a = .ok () := by
  simp only [checkModuleArtifact,h.interface,h.entry,h.memories,h.queues,↓reduceIte,pure,Except.pure,bind,Except.bind]
  rw [← Array.forIn_toList]
  apply forIn_unit_then
  intro n hn
  have closed := h.closed n hn
  cases n <;> simp_all [Node.inStorage,Artifact.storageShape]

theorem checkReadOutputs_total (h : ∀ n ∈ outputs, a.storageShape.hasMemory n) :
    checkReadOutputs a outputs = .ok () := by
  unfold checkReadOutputs
  apply forIn_unit_then
  intro n hn
  simp [memorySize_total (h n hn),bind,Except.bind,pure,Except.pure]

theorem generateCode_total (h : ∀ s ∈ (RTL.artifactProgram a).cases.toList, StatementReady a s) :
    ∃ cases emission, generateCode a = .ok (cases,emission) := by
  obtain ⟨cases,emission,generated,_⟩ := total_mapM (RTL.artifactProgram a).cases.toList
    (statementCode a) (fun s hs => statementCode_total s (h s hs)) {}
  exact ⟨cases,emission,generated⟩

/-- The actual emitter, including metadata validation and read ports, succeeds
under explicit structural and finite-width conditions on its target program. -/
theorem generateModule_total (module : ModuleReady a)
    (body : ∀ s ∈ (RTL.artifactProgram a).cases.toList, StatementReady a s)
    (ports : ∀ n ∈ outputs, a.storageShape.hasMemory n) :
    ∃ result, generateModule a outputs = .ok result := by
  obtain ⟨cases,emission,generated⟩ := generateCode_total body
  exact ⟨moduleCode a outputs cases emission.text,by
    simp [generateModule,checkModuleArtifact_total module,generated,checkReadOutputs_total ports,
      bind,Except.bind,pure,Except.pure]⟩

theorem emit_total (module : ModuleReady a)
    (body : ∀ s ∈ (RTL.artifactProgram a).cases.toList, StatementReady a s)
    (ports : ∀ n ∈ outputs, a.storageShape.hasMemory n) :
    ∃ text, Circuit.emit a outputs = .ok text := by
  obtain ⟨result,generated⟩ := generateModule_total module body ports
  exact ⟨result.text,by simp [Circuit.emit,generated,bind,Except.bind,pure,Except.pure]⟩


@[simp] theorem ready_literal (n : Int) : TermReady a (.literal n) := by
  rw [TermReady.eq_def]; simp [RTL.Term.children]
@[simp] theorem ready_register (n : Nat) : TermReady a (.register n) := by
  rw [TermReady.eq_def]; simp [RTL.Term.children]
@[simp] theorem ready_wire (h : n < a.wires.size) : TermReady a (.wire n) := by
  rw [TermReady.eq_def]; simp [RTL.Term.children,h]
@[simp] theorem ready_resize (positive : 0 < w) (h : TermReady a e) : TermReady a (.resize w e) := by
  rw [TermReady.eq_def]; simpa [RTL.Term.children] using And.intro positive h
@[simp] theorem ready_binary (hu : TermReady a u) (hv : TermReady a v) : TermReady a (.binary op u v) := by
  rw [TermReady.eq_def]; simp [RTL.Term.children,hu,hv]
@[simp] theorem ready_cell (hm : a.storageShape.hasMemory n) (hj : TermReady a j) : TermReady a (.cell n j) := by
  rw [TermReady.eq_def]; simp [RTL.Term.children,hm,hj]
@[simp] theorem ready_wrap32 (h : TermReady a e) : TermReady a (.wrap32 e) := by
  rw [TermReady.eq_def]
  simpa [RTL.Term.children] using h

@[simp] theorem ready_nonnegative (h : TermReady a e) : TermReady a (.nonnegative e) := by
  rw [TermReady.eq_def]; simp [RTL.Term.children,h]
@[simp] theorem ready_mux (hc : TermReady a c) (hu : TermReady a u) (hv : TermReady a v) : TermReady a (.mux c u v) := by
  rw [TermReady.eq_def]; simp [RTL.Term.children,hc,hu,hv]

@[simp] theorem ready_both (hu : ValidityReady a u) (hv : ValidityReady a v) :
    ValidityReady a (RTL.Validity.both u v) := by
  cases u <;> cases v <;> simp_all [RTL.Validity.both,ValidityReady]
@[simp] theorem ready_choose (hc : TermReady a c) (hu : ValidityReady a u) (hv : ValidityReady a v) :
    ValidityReady a (RTL.Validity.choose c u v) := by
  cases u <;> cases v <;> simp_all [RTL.Validity.choose,ValidityReady]

theorem combinational_ready (e : Circuit.Expr) (h : e.inStorage a.storageShape) :
    CombinationalReady a (RTL.combinational wr e) := by
  have positive (r : Interval) : 0 < signedWidth r := by unfold signedWidth; omega
  induction e <;> simp_all [CombinationalReady,RTL.combinational,Expr.inStorage,
    ValidityReady,show a.storageShape.wires = a.wires from rfl]

/-- Remaining local obligations of an integer circuit node: declared queues,
equal-capacity snapshots, and BV32-valued writes. These are computed metadata
properties; no successful emitter or source/target equivalence is assumed. -/
def NodeReady (a : Artifact) (n : Node) : Prop :=
  n.inStorage a.storageShape ∧ match n with
    | .snapshot dst src _ => a.storageShape.memorySize dst = a.storageShape.memorySize src
    | .assign _ e _ | .store _ _ e _ => isWord (range a.storageShape.wireRange e) = true
    | .send q e _ => QueueDeclared a q ∧ isWord (range a.storageShape.wireRange e) = true
    | .clear q _ | .receive q _ _ => QueueDeclared a q
    | _ => True

@[simp] theorem wordBounds_combinational (h : isWord (range wr e) = true) :
    WordBounds (RTL.combinational wr e) := by
  cases e <;> simpa [WordBounds,RTL.combinational,isWord] using h

theorem lowerNode_ready (n : Node) (h : NodeReady a n) :
    StatementReady a ((RTL.lowerNode n).mapExpressions (RTL.combinational a.storageShape.wireRange)) := by
  cases n <;> simp_all [NodeReady,Node.inStorage,RTL.lowerNode,RTL.guarded,
    RTL.advance,RTL.fault,RTL.halt,RTL.Statement.mapExpressions,RTL.Test.mapExpressions,
    RTL.Scalar.mapExpressions,RTL.MemoryRhs.mapExpressions,RTL.QueueRhs.mapExpressions,
    StatementReady,AssignmentReady,ScalarReady,TestReady,
    combinational_ready,wordBounds_combinational,show a.storageShape.wires = a.wires from rfl]


theorem artifactProgram_ready (nodes : ∀ n ∈ a.machine.nodes.toList, NodeReady a n) :
    ∀ s ∈ (RTL.artifactProgram a).cases.toList, StatementReady a s := by
  intro s hs
  simp only [RTL.artifactProgram,RTL.lowerCombinational,Array.toList_map,List.mem_map] at hs
  obtain ⟨n,hn,rfl⟩ := hs
  exact lowerNode_ready n (nodes n hn)

theorem emit_of_nodes (module : ModuleReady a)
    (nodes : ∀ n ∈ a.machine.nodes.toList, NodeReady a n)
    (ports : ∀ n ∈ outputs, a.storageShape.hasMemory n) :
    ∃ text, Circuit.emit a outputs = .ok text :=
  emit_total module (artifactProgram_ready nodes) ports


instance (a : Artifact) (n : Node) : Decidable (NodeReady a n) := by
  cases n <;> unfold NodeReady QueueDeclared <;> infer_instance

instance (a : Artifact) : Decidable (ModuleReady a) :=
  decidable_of_iff
    (InterfaceLayout a ∧ a.machine.entry < a.machine.nodes.size ∧
      (a.memories.toList.map Prod.fst).eraseDups.length = a.memories.size ∧
      (a.machine.capacities.toList.map Prod.fst).eraseDups.length = a.machine.capacities.size ∧
      ∀ n ∈ a.machine.nodes.toList, n.inStorage a.storageShape)
    ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩,
      fun h => ⟨h.interface,h.entry,h.memories,h.queues,h.closed⟩⟩

end IRComparison.Circuit.SystemVerilog.Generation
