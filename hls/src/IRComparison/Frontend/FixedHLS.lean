import IRComparison.Frontend.AutomaticStages

namespace IRComparison.FixedHLS
open CertifiedHLS Circuit

/-- A native function and its predeclared array regions. No execution operation
can allocate a region or replace its length. Copies require matching lengths. -/
structure Entry (native : Program) where
  program : ProgramEntry native
  declarations : FixedMemory.Declarations
  unique : FixedMemory.unique declarations = true
  declared : FixedMemory.declared declarations program.code = true

/-- The legacy stage adapter needs an input-array identifier even when the
native function does not use one. Select an actual declaration; for scalar-only
programs use a private zero-length placeholder, never a new source array. -/
def Entry.anchor (e : Entry native) : Nat :=
  match e.declarations.toList with
  | [] => 0
  | (a,_)::_ => a

def Entry.layout (e : Entry native) : Array (Nat × Nat) :=
  if e.declarations.isEmpty then #[(0,0)] else e.declarations

theorem Entry.layout_unique (e : Entry native) : (e.layout.toList.map Prod.fst).Nodup := by
  have unique : (e.declarations.toList.map Prod.fst).Nodup := by
    simpa only [FixedMemory.unique,decide_eq_true_eq] using e.unique
  unfold layout
  split
  · simp
  · exact unique

theorem Entry.declaration_in_layout (e : Entry native)
    (h : (a,n) ∈ e.declarations.toList) : (a,n) ∈ e.layout.toList := by
  unfold layout
  split
  · have empty := Array.empty_of_isEmpty (by assumption : e.declarations.isEmpty)
    simp [empty] at h
  · exact h

theorem Entry.anchor_in_layout (e : Entry native) :
    ∃ n, (e.anchor,n) ∈ e.layout.toList := by
  cases h : e.declarations.toList with
  | nil =>
    have empty := Array.toList_eq_nil_iff.mp h
    exact ⟨0,by simp [anchor,layout,empty]⟩
  | cons p rest =>
    obtain ⟨a,n⟩ := p
    refine ⟨n,e.declaration_in_layout ?_⟩
    simp [anchor,h]

theorem Entry.lower_arrays_in_layout (e : Entry native)
    (h : a ∈ allCommandArrays e.program.code.lower.target) :
    ∃ n, (a,n) ∈ e.layout.toList := by
  have found := List.all_eq_true.mp (FixedMemory.lower_declared e.program.code e.declared) a h
  cases value : FixedMemory.lookup e.declarations a with
  | none => simp [value] at found
  | some n => exact ⟨n,e.declaration_in_layout (FixedMemory.lookup_mem value)⟩

theorem Entry.outputs_safe (e : Entry native) {outputs : List Nat}
    (declared : outputs.all (fun a => (FixedMemory.lookup e.declarations a).isSome) = true) :
    ∀ a ∈ outputs, a < layoutLimit e.layout := by
  intro a ha
  have found := List.all_eq_true.mp declared a ha
  cases value : FixedMemory.lookup e.declarations a with
  | none => simp [value] at found
  | some n => exact layout_member_bound (e.declaration_in_layout (FixedMemory.lookup_mem value))

/-- Every fixed source declaration survives the actual circuit allocator,
including sparse identifiers, zero-length banks, and the scalar-only layout. -/
theorem Entry.generated_metadata (e : Entry native) (code : HybridUnifiedPipeline.Code) :
    let generated := scheduleWith CountedBackend.named.build e.layout code
    let graph := (Pipelining.structuredTree generated.schedule).assemble generated.build.queues
    Allocation.MetadataReady (graph.artifact generated.build.wires generated.build.memories e.layout) :=
  Pipelining.structured_metadata e.layout e.layout_unique code

theorem Entry.generated_outputs (e : Entry native) (code : HybridUnifiedPipeline.Code)
    {outputs : List Nat}
    (declared : outputs.all (fun a => (FixedMemory.lookup e.declarations a).isSome) = true) :
    let generated := scheduleWith CountedBackend.named.build e.layout code
    let graph := (Pipelining.structuredTree generated.schedule).assemble generated.build.queues
    let artifact := graph.artifact generated.build.wires generated.build.memories e.layout
    checkReadOutputs artifact outputs = .ok () := by
  apply SystemVerilog.Generation.checkReadOutputs_total
  apply (e.generated_metadata code).ports
  intro a ha
  have found := List.all_eq_true.mp declared a ha
  cases value : FixedMemory.lookup e.declarations a with
  | none => simp [value] at found
  | some n => exact ⟨n,e.declaration_in_layout (FixedMemory.lookup_mem value)⟩

/-- Source-ordered stage extraction is part of the ordinary fixed-array entry. -/
def Entry.stages (e : Entry native) : List CertifiedHLS.Stage :=
  (AutomaticStages.pieces e.program.code).map (fun p => p.stage e.declarations e.anchor (HybridEffects.writes e.program.code.lower))

def Entry.staged (e : Entry native) : CertifiedHLS.Entry e.stages :=
  AutomaticStages.entry e.declarations e.anchor (HybridEffects.writes e.program.code.lower) (AutomaticStages.pieces e.program.code)

theorem Entry.staged_correct (e : Entry native) (s : HybridWord.State) :
    CertifiedHLS.runSource e.stages 0 0 s = native s := by
  rw [stages,AutomaticStages.source_eq,AutomaticStages.pieces_correct,e.program.correct]

theorem Entry.staged_closed (e : Entry native) :
    ∀ k ∈ e.staged.kernels, (∃ n, (k.array,n) ∈ e.layout.toList) ∧
      k.body.lower.target.ArraysWithin (fun a => ∃ n, (a,n) ∈ e.layout.toList) :=
  AutomaticStages.entry_closed _
    (fun p hp => AutomaticStages.pieces_declared e.program.code e.declared p hp)
    e.anchor_in_layout (fun _ _ mem => e.declaration_in_layout mem)

/-- Extraction preserves declarations; the existing backend totality proof
applies to every extracted stage, including pieces kept in memory. -/
theorem Entry.memory_and_range_checks (e : Entry native) (outputs : List Nat) :
    ∃ p table, HybridWord.compileProgram outputs (FixedMemory.sizes e.declarations) e.staged.kernels = some p ∧
      checkLayout e.layout (HybridUnifiedPipeline.lower p) = .ok () ∧
      checkSendBudgets (HybridUnifiedPipeline.lower p) = .ok () ∧
      checkCommunication (HybridUnifiedPipeline.lower p) = .ok () ∧
      inferInvariant (lowerWith CountedBackend.named.build e.layout (HybridUnifiedPipeline.lower p)) = .ok table ∧
      validInvariant (lowerWith CountedBackend.named.build e.layout (HybridUnifiedPipeline.lower p)) table = true :=
  compile_rolled_checks outputs (FixedMemory.sizes e.declarations) _ e.layout e.layout_unique e.staged_closed

abbrev Entry.Compiled (e : Entry native) (outputs : List Nat) (fuel : Nat) :=
  CertifiedHLS.Compiled
    e.staged
    outputs (FixedMemory.sizes e.declarations) e.layout fuel

def Entry.compile (e : Entry native) (outputs : List Nat) (fuel : Nat := 4096)
    (strategy : Pipelining.LoopStrategy := .rolled) : Except String (e.Compiled outputs fuel) :=
  if outputs.all (fun a => (FixedMemory.lookup e.declarations a).isSome) then
    CertifiedHLS.compile e.staged outputs (FixedMemory.sizes e.declarations) e.layout fuel strategy
  else .error "fixed-memory output array is not declared"

/-- The same automatically extracted stages, with optional SMT routing search.
External search failures retain the total pure compilation path. -/
def Entry.compileWithSMT (e : Entry native) (outputs : List Nat) (directory : System.FilePath)
    (fuel : Nat := 4096) (strategy : Pipelining.LoopStrategy := .rolled) :
    IO (Except String (e.Compiled outputs fuel)) := do
  if outputs.all (fun a => (FixedMemory.lookup e.declarations a).isSome) then
    try
      match ← CertifiedHLS.compileWithSMT e.staged outputs
          (FixedMemory.sizes e.declarations) e.layout directory fuel strategy with
      | .ok result => return .ok result
      | .error _ => return e.compile outputs fuel strategy
    catch _ => return e.compile outputs fuel strategy
  else return .error "fixed-memory output array is not declared"

/-- Both pure and SMT-assisted compilation return the same proof-carrying
artifact, whose observation refers to the original whole Lean function. -/
theorem Entry.artifact_correct (e : Entry native) (outputs : List Nat) (fuel : Nat)
    (c : e.Compiled outputs fuel)
    (s : HybridWord.State) (input : c.InputConditions s 0 0)
    (r : RTL.InterfaceState c.backend.artifact.storageShape) (running : r.Running)
    (same : StorageAgreement c.backend.artifact.storageShape r.core.decode (c.backend.initial s 0 0)) :
    ∃ cycles result,
      SystemVerilog.runText c.text c.backend.artifact.storageShape cycles r = some result ∧
      Observation c.backend.artifact.storageShape outputs result.core.decode (native s) := by
  simpa only [e.staged_correct] using c.correct s 0 0 input r running same

/-- Once the ordinary Lean frontend has supplied its typed entry, every
fixed-declaration program produces RTL. The only output premise is membership
in the source declarations; no backend test, budget or successful run is assumed. -/
theorem Entry.compile_total (e : Entry native) (outputs : List Nat) (fuel : Nat)
    (strategy : Pipelining.LoopStrategy)
    (outputsDeclared : outputs.all (fun a => (FixedMemory.lookup e.declarations a).isSome) = true) :
    ∃ c, e.compile outputs fuel strategy = .ok c := by
  simp only [Entry.compile,outputsDeclared,↓reduceIte]
  apply CertifiedHLS.compile_total _ _ _ _ _ _ e.layout_unique
  · exact e.staged_closed
  · intro a member
    have found := List.all_eq_true.mp outputsDeclared a member
    cases value : FixedMemory.lookup e.declarations a with
    | none => simp [value] at found
    | some n => exact ⟨n,e.declaration_in_layout (FixedMemory.lookup_mem value)⟩

theorem Entry.compile_correct (e : Entry native) (outputs : List Nat) (fuel : Nat)
    {c : e.Compiled outputs fuel} {strategy : Pipelining.LoopStrategy}
    (success : e.compile outputs fuel strategy = .ok c)
    (s : HybridWord.State) (input : c.InputConditions s 0 0)
    (r : RTL.InterfaceState c.backend.artifact.storageShape) (running : r.Running)
    (same : StorageAgreement c.backend.artifact.storageShape r.core.decode (c.backend.initial s 0 0)) :
    ∃ cycles result,
      SystemVerilog.runText c.text c.backend.artifact.storageShape cycles r = some result ∧
      Observation c.backend.artifact.storageShape outputs result.core.decode (native s) := by
  unfold Entry.compile at success
  split at success
  · simpa only [e.staged_correct] using
      CertifiedHLS.compile_correct e.staged success s 0 0 input r running same
  · contradiction

/-- Generation and correctness in one statement, for the typed fixed-memory
entry. Parsing ordinary Lean definitions into this entry is a separate boundary. -/
theorem Entry.generates_correct (e : Entry native) (outputs : List Nat) (fuel : Nat)
    (strategy : Pipelining.LoopStrategy)
    (outputsDeclared : outputs.all (fun a => (FixedMemory.lookup e.declarations a).isSome) = true) :
    ∃ c : e.Compiled outputs fuel, e.compile outputs fuel strategy = .ok c ∧
      ∀ (s : HybridWord.State), c.InputConditions s 0 0 →
      ∀ (r : RTL.InterfaceState c.backend.artifact.storageShape), r.Running →
      StorageAgreement c.backend.artifact.storageShape r.core.decode (c.backend.initial s 0 0) →
      ∃ cycles result,
        SystemVerilog.runText c.text c.backend.artifact.storageShape cycles r = some result ∧
        Observation c.backend.artifact.storageShape outputs result.core.decode (native s) := by
  obtain ⟨c,success⟩ := e.compile_total outputs fuel strategy outputsDeclared
  exact ⟨c,success,fun s input r running same =>
    e.compile_correct outputs fuel success s input r running same⟩

theorem Entry.preserves_sizes (e : Entry native) (h : native s = some t) :
    FixedMemory.SameSizes s t := by
  apply FixedMemory.eval_sizes (i := 0) (x := 0) (y := 0) (ls := []) e.program.code
  rw [e.program.correct]
  exact h

end IRComparison.FixedHLS
