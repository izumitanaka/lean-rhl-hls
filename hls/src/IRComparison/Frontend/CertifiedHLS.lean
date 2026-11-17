import IRComparison.Circuit.Pipelining.IntegratedSound
import IRComparison.Circuit.SystemVerilog.PortContract

namespace IRComparison.CertifiedHLS
open Circuit Circuit.Pipelining

abbrev Body := HybridWord.Word → HybridWord.Word → HybridWord.Word →
  HybridWord.State → Option HybridWord.State

/-- Exported by the ordinary-Lean frontend. The user supplies no equivalence
premise: the frontend constructs this proof and Lean checks its declaration. -/
structure BodyEntry (native : Body) where
  code : HybridWord.Cmd
  correct : ∀ i x y s, code.eval i x y s [] = native i x y s

/-- Source configuration contains native Lean functions, not source IR. -/
structure Stage where
  native : Body
  size : Nat
  array : Nat
  start : Int
  stride : Int
  count : Nat
  supplier : Unit → List Int

def Stage.run (stage : Stage) (x y : HybridWord.Word) (s : HybridWord.State) :=
  HybridWord.runSource stage.native x y stage.stride stage.count stage.start s

def runSource (source : List Stage) (x y : HybridWord.Word) : HybridWord.State → Option HybridWord.State
  | s => match source with
    | [] => some s
    | stage :: rest => (stage.run x y s).bind (runSource rest x y)

inductive Entry : List Stage → Type where
  | nil : Entry []
  | cons {stage : Stage} {rest : List Stage} : BodyEntry stage.native → Entry rest → Entry (stage :: rest)

def BodyEntry.kernel {stage : Stage} (entry : BodyEntry stage.native) : HybridWord.Kernel :=
  { body := entry.code, native := stage.native, correct := entry.correct,
    size := stage.size, array := stage.array, start := stage.start,
    stride := stage.stride, count := stage.count, supplier := stage.supplier }

def Entry.kernels : Entry source → List HybridWord.Kernel
  | .nil => []
  | .cons body rest => body.kernel :: rest.kernels

theorem Entry.source_eq (entry : Entry source) (x y : HybridWord.Word) (s : HybridWord.State) :
    HybridWord.source x y entry.kernels s = runSource source x y s := by
  induction entry generalizing s with
  | nil => rfl
  | cons body rest ih =>
    simp only [Entry.kernels,HybridWord.source,HybridWord.Kernel.source,BodyEntry.kernel,
      runSource,Stage.run]
    cases HybridWord.runSource _ _ _ _ _ _ s <;> simp_all

/-- Successful artifacts retain the actual memory plan and backend equations. -/
structure Compiled (entry : Entry source) (outputs : List Nat) (sizes : Nat → Nat)
    (layout : Array (Nat × Nat)) (fuel : Nat) where
  plan : HybridWord.Plan outputs sizes entry.kernels
  backend : Integrated plan layout fuel
  outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout
  outputPorts : ∀ a ∈ outputs, backend.artifact.storageShape.hasMemory a

/-- Optional host-interface certification. Internal Nat IDs are unchanged;
callers exporting the 32-bit configuration/read protocol must check this
additional contract. The internal compilation-totality theorem is separate. -/
def Compiled.checkExternalPorts (c : Compiled entry outputs sizes layout fuel) :
    Except String (PLift (SystemVerilog.ExternalPorts.Fits c.backend.artifact outputs)) :=
  SystemVerilog.ExternalPorts.check c.backend.artifact outputs

/-- Common certified backend for both static and SMT-assisted rule selection. -/
def finish (entry : Entry source) (outputs : List Nat) (sizes : Nat → Nat)
    (layout : Array (Nat × Nat)) (fuel : Nat) (strategy : LoopStrategy)
    (plan : HybridWord.Plan outputs sizes entry.kernels) :
    Except String (Compiled entry outputs sizes layout fuel) := do
  let backend ← integrate plan layout fuel strategy
  if safe : ∀ a ∈ outputs, a < layoutLimit layout then
    if ports : ∀ a ∈ outputs, backend.artifact.storageShape.hasMemory a then
      return ⟨plan,backend,safe,ports⟩
    else throw "public output is absent from the RTL interface"
  else throw "public output is outside the source layout"

def compile (entry : Entry source) (outputs : List Nat) (sizes : Nat → Nat)
    (layout : Array (Nat × Nat)) (fuel : Nat := 4096) (strategy : LoopStrategy := .rolled) :
    Except String (Compiled entry outputs sizes layout fuel) := do
  let some plan := HybridWord.compileProgram outputs sizes entry.kernels
    | throw "memory optimization could not construct a plan"
  finish entry outputs sizes layout fuel strategy plan

/-- Solver IO selects a proof-carrying rule derivation. The resulting artifact
has exactly the same `Compiled.correct` theorem as the pure entry point. -/
def compileWithSMT (entry : Entry source) (outputs : List Nat) (sizes : Nat → Nat)
    (layout : Array (Nat × Nat)) (directory : System.FilePath)
    (fuel : Nat := 4096) (strategy : LoopStrategy := .rolled) :
    IO (Except String (Compiled entry outputs sizes layout fuel)) := do
  let some plan ← HybridWord.compileProgramWithSMT outputs sizes entry.kernels directory
    | return .error "memory optimization could not construct a plan"
  return finish entry outputs sizes layout fuel strategy plan

variable {source : List Stage} {entry : Entry source} {outputs : List Nat}
  {sizes : Nat → Nat} {layout : Array (Nat × Nat)} {fuel : Nat}

def Compiled.text (c : Compiled entry outputs sizes layout fuel) : String := c.backend.text

/-- Every declared public array is observed, not only arrays that happen to
survive lowering. Compilation checks that all these ports actually exist. -/
def Observation (shape : StorageShape) (outputs : List Nat) (r : Circuit.Runtime)
    (expected : Option HybridWord.State) : Prop :=
  ResultObservation shape.registers
    (fun actual final => ∀ a ∈ outputs, actual.arrays a = final.arrays a)
    r (expected.map HybridWord.State.encode)

theorem observation_of_public (ports : ∀ a ∈ outputs, shape.hasMemory a)
    (h : PublicObservation shape outputs r (expected.map HybridWord.State.encode)) :
    Observation shape outputs r expected := by
  cases expected with
  | none => exact h
  | some s => exact ⟨h.1,h.2.1,h.2.2.1,fun a ha => h.2.2.2 a ha (ports a ha)⟩

/-- Explicit source and initialization preconditions; there is no target-run
or source/RTL equivalence hidden in this predicate. -/
structure Compiled.InputConditions (c : Compiled entry outputs sizes layout fuel)
    (s : HybridWord.State) (x y : HybridWord.Word) : Prop where
  sized : PipelineShapes.Layout sizes s.encode
  ready : c.plan.Ready (HybridWord.encode x) (HybridWord.encode y) s.encode
  fits : c.backend.artifact.InputFits s.encode

/-- Native Lean computations → memory optimization → all backend routes →
parsed SystemVerilog. Termination is a conclusion, for every admissible input.
This is a post-start functional theorem, not a reset or physical-timing theorem. -/
theorem Compiled.correct (c : Compiled entry outputs sizes layout fuel)
    (s : HybridWord.State) (x y : HybridWord.Word) (input : c.InputConditions s x y)
    (r : RTL.InterfaceState c.backend.artifact.storageShape) (running : r.Running)
    (same : StorageAgreement c.backend.artifact.storageShape r.core.decode (c.backend.initial s x y)) :
    ∃ cycles result,
      SystemVerilog.runText c.text c.backend.artifact.storageShape cycles r = some result ∧
      Observation c.backend.artifact.storageShape outputs result.core.decode
        (runSource source x y s) := by
  obtain ⟨cycles,result,executed,observed⟩ := c.backend.correct c.outputsSafe s x y
    input.sized input.ready input.fits r running same
  exact ⟨cycles,result,executed,observation_of_public c.outputPorts
    (by simpa only [Entry.source_eq] using observed)⟩

theorem compile_correct (entry : Entry source)
    {c : Compiled entry outputs sizes layout fuel}
    {strategy : LoopStrategy}
    (_success : compile entry outputs sizes layout fuel strategy = .ok c)
    (s : HybridWord.State) (x y : HybridWord.Word) (input : c.InputConditions s x y)
    (r : RTL.InterfaceState c.backend.artifact.storageShape) (running : r.Running)
    (same : StorageAgreement c.backend.artifact.storageShape r.core.decode (c.backend.initial s x y)) :
    ∃ cycles result,
      SystemVerilog.runText c.text c.backend.artifact.storageShape cycles r = some result ∧
      Observation c.backend.artifact.storageShape outputs result.core.decode
        (runSource source x y s) :=
  c.correct s x y input r running same

def BodyEntry.stage {native : Body} (_entry : BodyEntry native)
    (size array : Nat) (start stride : Int) (count : Nat) (supplier : Unit → List Int) : Stage :=
  ⟨native,size,array,start,stride,count,supplier⟩

def BodyEntry.program {native : Body} (entry : BodyEntry native)
    (size array : Nat) (start stride : Int) (count : Nat) (supplier : Unit → List Int) :
    Entry [entry.stage size array start stride count supplier] := .cons entry .nil

def BodyEntry.compile {native : Body} (entry : BodyEntry native)
    (size array : Nat) (start stride : Int) (count : Nat) (supplier : Unit → List Int)
    (outputs : List Nat) (sizes : Nat → Nat) (layout : Array (Nat × Nat)) (fuel : Nat := 4096) (strategy : LoopStrategy := .rolled) :=
  CertifiedHLS.compile (entry.program size array start stride count supplier) outputs sizes layout fuel strategy

/-- This is the statement exported under each ordinary Lean definition's
generated namespace. Its conclusion mentions the ORIGINAL native function. -/
theorem BodyEntry.compile_correct {native : Body} (entry : BodyEntry native)
    (size array : Nat) (start stride : Int) (count : Nat) (supplier : Unit → List Int)
    (outputs : List Nat) (sizes : Nat → Nat) (layout : Array (Nat × Nat)) (fuel : Nat)
    {c : Compiled (entry.program size array start stride count supplier) outputs sizes layout fuel}
    {strategy : LoopStrategy}
    (success : entry.compile size array start stride count supplier outputs sizes layout fuel strategy = .ok c)
    (s : HybridWord.State) (x y : HybridWord.Word) (input : c.InputConditions s x y)
    (r : RTL.InterfaceState c.backend.artifact.storageShape) (running : r.Running)
    (same : StorageAgreement c.backend.artifact.storageShape r.core.decode (c.backend.initial s x y)) :
    ∃ cycles result,
      SystemVerilog.runText c.text c.backend.artifact.storageShape cycles r = some result ∧
      Observation c.backend.artifact.storageShape outputs result.core.decode
        (HybridWord.runSource native x y stride count start s) := by
  obtain ⟨cycles,result,executed,observed⟩ := CertifiedHLS.compile_correct
    (entry.program size array start stride count supplier) success s x y input r running same
  refine ⟨cycles,result,executed,?_⟩
  simpa [runSource,Stage.run,BodyEntry.stage] using observed

/-- A complete native computation: loops and sequencing belong to the function,
not to a separately supplied stage schedule. Arrays are already in the state. -/
abbrev Program := HybridWord.State → Option HybridWord.State
abbrev ProgramEntry (native : Program) := BodyEntry (fun _ _ _ s => native s)

def ProgramEntry.compile {native : Program} (entry : ProgramEntry native)
    (outputs : List Nat) (sizes : Nat → Nat) (layout : Array (Nat × Nat))
    (fuel : Nat := 4096) (strategy : Circuit.Pipelining.LoopStrategy := .rolled) :=
  BodyEntry.compile entry (sizes 0) 0 0 1 1 (fun _ => []) outputs sizes layout fuel strategy

/-- Conditional soundness for the original complete Lean function, including
its loops and source order. The source is executed once, not externally iterated. -/
theorem ProgramEntry.compile_correct {native : Program} (entry : ProgramEntry native)
    (outputs : List Nat) (sizes : Nat → Nat) (layout : Array (Nat × Nat)) (fuel : Nat)
    {c : Compiled (entry.program (sizes 0) 0 0 1 1 (fun _ => [])) outputs sizes layout fuel}
    {strategy : Circuit.Pipelining.LoopStrategy}
    (success : ProgramEntry.compile entry outputs sizes layout fuel strategy = .ok c)
    (s : HybridWord.State) (input : c.InputConditions s 0 0)
    (r : Circuit.RTL.InterfaceState c.backend.artifact.storageShape) (running : r.Running)
    (same : Circuit.StorageAgreement c.backend.artifact.storageShape r.core.decode (c.backend.initial s 0 0)) :
    ∃ cycles result,
      Circuit.SystemVerilog.runText c.text c.backend.artifact.storageShape cycles r = some result ∧
      Observation c.backend.artifact.storageShape outputs result.core.decode (native s) := by
  simpa [HybridWord.runSource] using
    BodyEntry.compile_correct entry (sizes 0) 0 0 1 1 (fun _ => []) outputs sizes layout fuel
      success s 0 0 input r running same

end IRComparison.CertifiedHLS
