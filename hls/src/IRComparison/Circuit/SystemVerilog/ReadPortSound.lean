import IRComparison.Circuit.SystemVerilog.PhysicalRun

namespace IRComparison.Circuit.SystemVerilog

/-- Evaluation of the emitted read-port fragment in its declared unsigned
32-bit bus context. None denotes an undefined selected name/cell; an absent
ID or an address outside the live prefix gives the explicit invalid default.
The port does not modify state or consult the source program. -/
def ReadCode.eval (code : ReadCode) (env : Environment) (p : ReadRequest) : Option ReadReply := do
  if p.register then
    match code.registers.find? (fun entry => entry.1 == p.id.toNat) with
    | none => return {}
    | some (_,name) => return ⟨BitVec.ofInt 32 (← env.scalar name),true⟩
  else
    match code.arrays.find? (fun entry => entry.1 == p.id.toNat) with
    | none => return {}
    | some (_,length,bank) =>
      let size ← env.scalar length
      if p.address.toNat < size.toNat then
        return ⟨BitVec.ofInt 32 (← env.cell bank p.address.toNat),true⟩
      else return {}

theorem find_mapped_id (ids : List Nat) (f : Nat → α) (id : Nat) :
    ((ids.map (fun n => (n,f n))).find? (fun entry => entry.1 == id)) =
      if id ∈ ids then some (id,f id) else none := by
  induction ids with
  | nil => simp
  | cons n ns ih =>
    by_cases h : n = id
    · subst n; simp
    · simp [h,ih,Ne.symm h]

/-- Expected port observation of a source state. The bus exposes only
declared registers and public output arrays, with invalid reads returning 0. -/
def stateReadResult (a : Artifact) (outputs : List Nat) (s : State)
    (p : ReadRequest) : ReadReply :=
  if p.register then
    if p.id.toNat ∈ a.machine.nodes.toList.flatMap Node.registers then
      ⟨BitVec.ofInt 32 (s.regs p.id.toNat),true⟩
    else {}
  else
    if p.id.toNat ∈ outputs then
      match (s.arrays p.id.toNat)[p.address.toNat]? with
      | some value => ⟨BitVec.ofInt 32 value,true⟩
      | none => {}
    else {}

def readResult (a : Artifact) (outputs : List Nat) (r : FiniteRuntime a.storageShape)
    (p : ReadRequest) : ReadReply := stateReadResult a outputs r.decode.data p

theorem declared_register_bound (a : Artifact) (id : Nat)
    (member : id ∈ a.machine.nodes.toList.flatMap Node.registers) :
    id < a.storageShape.registers := by
  simpa only [Artifact.storageShape,idBound,List.foldl_map] using
    (layout_fold_bound ((a.machine.nodes.toList.flatMap Node.registers).map (fun n => (n,0))) 0).2
      (id,0) (List.mem_map.mpr ⟨id,member,rfl⟩)

theorem readCode_correct (a : Artifact) (outputs : List Nat)
    (declared : ∀ id ∈ outputs, a.storageShape.hasMemory id)
    (r : FiniteRuntime a.storageShape) (declarations : Array Wire) (p : ReadRequest) :
    (readCode a outputs).eval (environment a r declarations #[]) p =
      some (readResult a outputs r p) := by
  unfold ReadCode.eval readCode readResult stateReadResult
  simp only [find_mapped_id,List.mem_eraseDups]
  split
  · by_cases selected : p.id.toNat ∈ a.machine.nodes.toList.flatMap Node.registers
    · have inside := declared_register_bound a _ selected
      simp [selected,environment,environmentFor,FiniteRuntime.decode,inside]
    · simp [selected]
  · by_cases selected : p.id.toNat ∈ outputs
    · have inside := (declared _ selected).1
      simp only [selected,↓reduceIte,environment,environmentFor,inside,↓reduceDIte,
        bind,Option.bind,Int.toNat_natCast,pure,FiniteRuntime.decode]
      by_cases live : p.address.toNat < (r.arrays ⟨p.id.toNat,inside⟩).used.val
      · have capacity : p.address.toNat < a.storageShape.memorySize p.id.toNat := by
          have limit : (r.arrays ⟨p.id.toNat,inside⟩).used.val < a.storageShape.memorySize p.id.toNat + 1 :=
            (r.arrays ⟨p.id.toNat,inside⟩).used.isLt
          omega
        simp [live,capacity,WordBuffer.contents]
      · simp [live,WordBuffer.contents]
    · simp [selected]

/-- Public observations are exactly what is required to connect a completed
computation to the external read port, including invalid IDs/addresses. -/
theorem readCode_observed (a : Artifact) (outputs : List Nat)
    (declared : ∀ id ∈ outputs, a.storageShape.hasMemory id)
    (r : FiniteRuntime a.storageShape) (declarations : Array Wire) (initial final : State)
    (observed : PipelineUse.observe outputs (r.readback initial) = PipelineUse.observe outputs final)
    (p : ReadRequest) :
    (readCode a outputs).eval (environment a r declarations #[]) p =
      some (stateReadResult a outputs final p) := by
  rw [readCode_correct a outputs declared]
  apply congrArg some
  unfold readResult stateReadResult
  split
  · by_cases selected : p.id.toNat ∈ a.machine.nodes.toList.flatMap Node.registers
    · have inside := declared_register_bound a _ selected
      have regs := congrFun (congrArg Prod.fst observed) p.id.toNat
      change (r.readback initial).regs p.id.toNat = final.regs p.id.toNat at regs
      simp only [FiniteRuntime.readback,inside,↓reduceIte] at regs
      simp [selected,regs]
    · simp [selected]
  · by_cases selected : p.id.toNat ∈ outputs
    · have arrays := (List.map_inj_left.mp (congrArg Prod.snd observed)) p.id.toNat selected
      change r.decode.data.arrays p.id.toNat = final.arrays p.id.toNat at arrays
      simp [selected,arrays]
    · simp [selected]

/-- The whole computation theorem now exposes its result through the actual
read-port case structure consumed by the renderer. Start remains a modeled
boundary; the theorem does not assert a parser/IEEE conformance result. -/
theorem physical_pipeline_readout (p : HybridWord.Plan outputs sizes ks)
    (compiled : compile layout (HybridUnifiedPipeline.lower p) = .ok checked)
    (generated : generateCode checked.artifact = .ok (codes,emission))
    (outputsSafe : ∀ id ∈ outputs, id < layoutLimit layout)
    (outputPorts : ∀ id ∈ outputs, checked.artifact.storageShape.hasMemory id)
    (prepared : FiniteRuntime checked.artifact.storageShape) (x y : BitVec 32)
    (sized : PipelineShapes.Layout sizes (RTL.restoreLengths checked.artifact prepared).inputSource.encode)
    (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y)
      (RTL.restoreLengths checked.artifact prepared).inputSource.encode) :
    let a := checked.artifact
    let s := (RTL.restoreLengths a prepared).inputSource
    ∃ cycles result,
      physicalRun a codes emission.text cycles ⟨RTL.beginInvocation a prepared x y,true⟩ = some result ∧
      result.core.done = true ∧ result.busy = false ∧
      (∀ final, HybridWord.source x y ks s = some final →
        result.core.error = false ∧ ∀ request,
          (readCode a outputs).eval (environment a result.core emission.text #[]) request =
            some (stateReadResult a outputs final.encode request)) ∧
      (HybridWord.source x y ks s = none → result.core.error = true) := by
  obtain ⟨cycles,result,executed,finished,idle,observed⟩ :=
    physical_pipeline_from_started p compiled generated outputsSafe outputPorts prepared x y sized ready
  refine ⟨cycles,result,executed,finished,idle,?_,?_⟩
  · intro final success
    rw [success] at observed
    cases failed : result.core.error
    · have same : PipelineUse.observe outputs
          (result.core.readback (RTL.restoreLengths checked.artifact prepared).inputSource.encode) =
          PipelineUse.observe outputs final.encode := by
        simpa [FiniteRuntime.result,finished,failed] using observed
      exact ⟨rfl,readCode_observed _ _ outputPorts _ _ _ _ same⟩
    · simp [FiniteRuntime.result,finished,failed] at observed
  · intro failed
    rw [failed] at observed
    cases he : result.core.error <;> simp_all [FiniteRuntime.result]

end IRComparison.Circuit.SystemVerilog
