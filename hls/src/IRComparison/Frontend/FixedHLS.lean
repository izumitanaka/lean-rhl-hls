import IRComparison.Frontend.HLSGeneration
import IRComparison.Frontend.FixedLowering

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

/-- The fixed-source declarations discharge the layout premises of the actual
memory optimizer and the rolled numerical analysis. This theorem is uniform
in the native body; it is not a list of successful compilation examples. -/
theorem Entry.memory_and_range_checks (e : Entry native) (outputs : List Nat) :
    let kernels := (e.program.program (FixedMemory.sizes e.declarations e.anchor) e.anchor 0 1 1 (fun _ => [])).kernels
    ∃ p table, HybridWord.compileProgram outputs (FixedMemory.sizes e.declarations) kernels = some p ∧
      checkLayout e.layout (HybridUnifiedPipeline.lower p) = .ok () ∧
      checkSendBudgets (HybridUnifiedPipeline.lower p) = .ok () ∧
      checkCommunication (HybridUnifiedPipeline.lower p) = .ok () ∧
      inferInvariant (lowerWith CountedBackend.named.build e.layout (HybridUnifiedPipeline.lower p)) = .ok table ∧
      validInvariant (lowerWith CountedBackend.named.build e.layout (HybridUnifiedPipeline.lower p)) table = true := by
  apply compile_rolled_checks outputs (FixedMemory.sizes e.declarations) _ e.layout e.layout_unique
  intro k member
  simp only [BodyEntry.program,CertifiedHLS.Entry.kernels,List.mem_singleton] at member
  subst k
  refine ⟨e.anchor_in_layout,?_⟩
  apply (commandArrays_closed e.program.code.lower.target).mpr
  exact fun a member => e.lower_arrays_in_layout member

abbrev Entry.Compiled (e : Entry native) (outputs : List Nat) (fuel : Nat) :=
  CertifiedHLS.Compiled
    (e.program.program (FixedMemory.sizes e.declarations e.anchor) e.anchor 0 1 1 (fun _ => []))
    outputs (FixedMemory.sizes e.declarations) e.layout fuel

def Entry.compile (e : Entry native) (outputs : List Nat) (fuel : Nat := 4096)
    (strategy : Pipelining.LoopStrategy := .rolled) : Except String (e.Compiled outputs fuel) :=
  if outputs.all (fun a => (FixedMemory.lookup e.declarations a).isSome) then
    BodyEntry.compile e.program (FixedMemory.sizes e.declarations e.anchor) e.anchor 0 1 1
      (fun _ => []) outputs (FixedMemory.sizes e.declarations) e.layout fuel strategy
  else .error "fixed-memory output array is not declared"

/-- Once the ordinary Lean frontend has supplied its typed entry, every
fixed-declaration program produces RTL. The only output premise is membership
in the source declarations; no backend test, budget or successful run is assumed. -/
theorem Entry.compile_total (e : Entry native) (outputs : List Nat) (fuel : Nat)
    (strategy : Pipelining.LoopStrategy)
    (outputsDeclared : outputs.all (fun a => (FixedMemory.lookup e.declarations a).isSome) = true) :
    ∃ c, e.compile outputs fuel strategy = .ok c := by
  simp only [Entry.compile,outputsDeclared,↓reduceIte,BodyEntry.compile]
  apply CertifiedHLS.compile_total _ _ _ _ _ _ e.layout_unique
  · intro k member
    simp only [BodyEntry.program,CertifiedHLS.Entry.kernels,List.mem_singleton] at member
    subst k
    refine ⟨e.anchor_in_layout,?_⟩
    apply (commandArrays_closed e.program.code.lower.target).mpr
    exact fun a member => e.lower_arrays_in_layout member
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
  · simpa [HybridWord.runSource] using BodyEntry.compile_correct e.program
      (FixedMemory.sizes e.declarations e.anchor) e.anchor 0 1 1 (fun _ => [])
      outputs (FixedMemory.sizes e.declarations) e.layout fuel success s 0 0 input r running same
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
