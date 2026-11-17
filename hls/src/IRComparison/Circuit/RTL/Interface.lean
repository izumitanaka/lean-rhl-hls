import IRComparison.Circuit.RTL.InterfaceSyntax
import IRComparison.Circuit.RTL.PipelineSound

namespace IRComparison.Circuit.RTL

/-- Physical interface state. Unused cells are retained by configuration and
start; they are not replaced by fresh nondeterministic choices. -/
structure InterfaceState (shape : StorageShape) where
  core : FiniteRuntime shape
  busy : Bool

def originalSize (a : Artifact) (id : Nat) : Option Nat :=
  (a.originalMemories.toList.find? (fun p => p.1 == id)).map Prod.snd

/-- The emitter's metadata contract, restated with finite-storage names. -/
abbrev InterfaceLayout (a : Artifact) := SystemVerilog.InterfaceLayout a

/-- Restore the externally declared lengths when beginning an invocation.
The minimum is the finite encoding; accepted layouts require these lengths
to fit, so it never clips a valid interface declaration. -/
def restoreLengths (a : Artifact) (r : FiniteRuntime a.storageShape) : FiniteRuntime a.storageShape :=
  { r with arrays := fun id => match originalSize a id.val with
      | none => r.arrays id
      | some size => { r.arrays id with used := ⟨min size (a.storageShape.memorySize id.val),by omega⟩ } }

/-- Read the fixed BV32 words at an invocation boundary as the source input.
Only the live prefix is observable; no value is assigned by this operation. -/
def _root_.IRComparison.Circuit.FiniteRuntime.inputSource (r : FiniteRuntime shape) : HybridWord.State where
  regs := fun id => if h : id < shape.registers then r.regs ⟨id,h⟩ else 0
  arrays := fun id => if h : id < shape.memories then
    Array.ofFn fun i : Fin (r.arrays ⟨id,h⟩).used.val =>
      (r.arrays ⟨id,h⟩).cells ⟨i.val,by have := i.isLt; have := (r.arrays ⟨id,h⟩).used.isLt; omega⟩
    else #[]

theorem _root_.IRComparison.Circuit.FiniteRuntime.inputSource_encode (r : FiniteRuntime shape) :
    r.inputSource.encode = r.decode.data := by
  unfold HybridWord.State.encode FiniteRuntime.inputSource Circuit.FiniteRuntime.decode
  congr 1
  · funext id
    by_cases h : id < shape.registers <;> simp [h,HybridWord.encode]
  · funext id
    by_cases h : id < shape.memories
    · simp only [h,↓reduceDIte,WordBuffer.contents,Array.map_ofFn]
      rfl
    · simp [h]

def beginInvocation (a : Artifact) (r : FiniteRuntime a.storageShape) (x y : BitVec 32) : FiniteRuntime a.storageShape :=
  let r := restoreLengths a r
  { r with
    pc := BitVec.ofNat (bits (a.storageShape.states-1)) a.machine.entry
    wires := fun n => BitVec.ofInt (signedWidth (a.storageShape.wireRange n.val))
      (if n.val = 0 then (x.toNat : Int) else if n.val = 1 then (y.toNat : Int) else 0)
    queues := fun q => {r.queues q with used := ⟨0,by omega⟩}
    done := false
    error := false }

def resetInterface (r : FiniteRuntime shape) : InterfaceState shape :=
  ⟨{r with
    pc := 0
    regs := fun _ => 0
    wires := fun _ => 0
    arrays := fun a => ⟨fun _ => 0,⟨shape.memorySize a.val,by omega⟩⟩
    queues := fun q => {r.queues q with used := ⟨0,by omega⟩}
    done := false
    error := false},false⟩

/-- Writes target physical cells, even if the previous invocation shortened
that bank's live prefix. Start restores the original declared length. -/
def configureInterface (a : Artifact) (p : Ports) (r : FiniteRuntime a.storageShape) : FiniteRuntime a.storageShape :=
  if p.register then
    {r with regs := fun id => if id.val = p.id.toNat ∧ id.val ∈ a.machine.nodes.toList.flatMap Node.registers
      then p.value else r.regs id}
  else
    {r with arrays := fun id => if id.val = p.id.toNat then
      match originalSize a id.val with
      | none => r.arrays id
      | some size => if p.address.toNat < size then
          {r.arrays id with cells := fun j => if j.val = p.address.toNat then p.value else (r.arrays id).cells j}
        else r.arrays id
      else r.arrays id}

/-- The controller tree is also consumed by the SystemVerilog renderer.
The compute callback is the proved finite RTL structure. -/
def interfaceTick (a : Artifact) (p : Ports) (r : InterfaceState a.storageShape) : InterfaceState a.storageShape :=
  match controller.select p r.busy with
  | .reset => resetInterface r.core
  | .start => ⟨beginInvocation a r.core p.x p.y,true⟩
  | .configure => ⟨configureInterface a p r.core,false⟩
  | .hold => r
  | .execute =>
    let next := (artifactProgram a).finiteTick a.storageShape r.core
    ⟨next,!next.done⟩

theorem start_edge (a : Artifact) (p : Ports) (r : InterfaceState a.storageShape)
    (idle : r.busy = false) (hr : p.reset = false) (hs : p.start = true) :
    interfaceTick a p r = ⟨beginInvocation a r.core p.x p.y,true⟩ := by
  simp only [interfaceTick,idle,controller_start p hr hs]

theorem reset_edge (a : Artifact) (p : Ports) (r : InterfaceState a.storageShape) (h : p.reset = true) :
    interfaceTick a p r = resetInterface r.core := by
  simp only [interfaceTick,controller_reset p r.busy h]

theorem configure_lengths (a : Artifact) (p : Ports) (r : FiniteRuntime a.storageShape) (id) :
    ((configureInterface a p r).arrays id).used = (r.arrays id).used := by
  unfold configureInterface
  split
  · rfl
  · simp only
    split
    · split
      · rfl
      · split <;> rfl
    · rfl

theorem configure_cell (a : Artifact) (p : Ports) (r : FiniteRuntime a.storageShape)
    (id : Fin a.storageShape.memories) (j : Fin (a.storageShape.memorySize id.val))
    (memory : p.register = false) (selected : id.val = p.id.toNat)
    (declared : originalSize a id.val = some size) (inside : p.address.toNat < size)
    (address : j.val = p.address.toNat) :
    ((configureInterface a p r).arrays id).cells j = p.value := by
  simp only [configureInterface,memory,Bool.false_eq_true,↓reduceIte,selected,↓reduceIte]
  rw [← selected,declared]
  simp [inside,address]

theorem beginInvocation_agrees (a : Artifact) (r : FiniteRuntime a.storageShape) (x y : BitVec 32)
    (bounded : StorageBound a.storageShape
      (a.machine.start (restoreLengths a r).inputSource.encode (HybridWord.encode x) (HybridWord.encode y))) :
    StorageAgreement a.storageShape (beginInvocation a r x y).decode
      (a.machine.start (restoreLengths a r).inputSource.encode (HybridWord.encode x) (HybridWord.encode y)) := by
  have data := FiniteRuntime.inputSource_encode (restoreLengths a r)
  constructor
  · change (BitVec.ofNat (bits (a.storageShape.states-1)) a.machine.entry).toNat = a.machine.entry
    simp only [BitVec.toNat_ofNat]
    have hb := bits_fits (a.storageShape.states-1)
    have hp := bounded.pc
    change a.machine.entry < a.storageShape.states at hp
    exact Nat.mod_eq_of_lt (by omega)
  · intro n hn
    rw [data]
    rfl
  · intro id hid
    rw [data]
    rfl
  · intro n hn
    simp only [Circuit.FiniteRuntime.decode,beginInvocation,hn,↓reduceDIte,Machine.start]
    exact signedWidth_preserves (bounded.wires n hn)
  · intro q hq
    simp [Circuit.FiniteRuntime.decode,beginInvocation,hq,WordBuffer.contents,Machine.start]
  · rfl
  · rfl

/-- General single-start connection. The source input is the actual prepared
physical words, not a universally zero-initialized array. -/
theorem startup_pipeline_finishes (p : HybridWord.Plan outputs sizes ks)
    (compiled : compile layout (HybridUnifiedPipeline.lower p) = .ok checked)
    (outputsSafe : ∀ id ∈ outputs, id < layoutLimit layout)
    (outputPorts : ∀ id ∈ outputs, checked.artifact.storageShape.hasMemory id)
    (r : InterfaceState checked.artifact.storageShape) (ports : Ports)
    (idle : r.busy = false) (noReset : ports.reset = false) (start : ports.start = true)
    (sized : PipelineShapes.Layout sizes (restoreLengths checked.artifact r.core).inputSource.encode)
    (ready : p.Ready (HybridWord.encode ports.x) (HybridWord.encode ports.y)
      (restoreLengths checked.artifact r.core).inputSource.encode) :
    let a := checked.artifact
    let s := (restoreLengths a r.core).inputSource
    ∃ cycles, (((artifactProgram a).finiteRun a.storageShape cycles
      (interfaceTick a ports r).core).result s.encode).map (Option.map (PipelineUse.observe outputs)) =
      some ((HybridWord.source ports.x ports.y ks s).map (fun t => PipelineUse.observe outputs t.encode)) := by
  let a := checked.artifact
  let s := (restoreLengths a r.core).inputSource
  have fits : a.InputFits s.encode := by
    intro n hn
    rw [FiniteRuntime.inputSource_encode]
    simp only [Circuit.FiniteRuntime.decode,hn.1,↓reduceDIte]
    exact WordBuffer.contents_size _
  have bounds := storage_reachable checked.storage checked.valid checked.inputs s ports.x ports.y fits 0
  have initial := beginInvocation_agrees a r.core ports.x ports.y bounds
  dsimp only
  rw [start_edge a ports r idle noReset start]
  exact rtl_pipeline_from_initial p compiled outputsSafe outputPorts s ports.x ports.y sized ready fits _ initial

end IRComparison.Circuit.RTL
