import IRComparison.Circuit.SystemVerilog.RefinementSound
import IRComparison.Circuit.SystemVerilog.ClockCheck
import IRComparison.Circuit.RTL.InterfaceRunSound

namespace IRComparison.Circuit.SystemVerilog

/-- Commit the pending nonblocking writes into physical words. In particular
unused cells are retained, not reconstructed from logical live contents.
Defaults only totalize observation of absent slots; correspondence below
establishes defined values for every observed field. No reference tick is
used in this executable adapter. -/
def Store.commit (store : Store) (shape : StorageShape) : FiniteRuntime shape where
  pc := BitVec.ofInt (bits (shape.states-1)) ((store.scalar .pc).getD 0)
  regs := fun n => BitVec.ofInt 32 ((store.scalar (.register n.val)).getD 0)
  wires := fun n => BitVec.ofInt (signedWidth (shape.wireRange n.val)) ((store.scalar (.holding n.val)).getD 0)
  arrays := fun n => {
    cells := fun j => BitVec.ofInt 32 ((store.cell (.memory n.val) j.val).getD 0)
    used := ⟨min ((store.scalar (.length n.val)).getD 0).toNat (shape.memorySize n.val),by omega⟩ }
  queues := fun q => {
    cells := fun j => BitVec.ofInt 32 ((store.cell (.queue q.val) j.val).getD 0)
    used := ⟨min ((store.scalar (.used q.val)).getD 0).toNat (shape.queueSize q.val),by omega⟩ }
  done := (BitVec.ofInt 1 ((store.scalar .done).getD 0)).toNat != 0
  error := (BitVec.ofInt 1 ((store.scalar .error).getD 0)).toNat != 0

def Store.busy (store : Store) : Bool :=
  (BitVec.ofInt 1 ((store.scalar .busy).getD 0)).toNat != 0

/-- Concrete execution: evaluate the emitted AST and commit its writes.
This does not execute or reuse the abstract machine's transition function. -/
def physicalTick (a : Artifact) (cases : List Statement) (declarations : Array Wire)
    (ports : RTL.Ports) (r : RTL.InterfaceState a.storageShape) : Option (RTL.InterfaceState a.storageShape) := do
  let writes ← clockCode a cases declarations ports r
  return ⟨writes.commit a.storageShape,writes.busy⟩

/-- Control inputs are deasserted after start, as in the established
single-invocation source theorem. The whole physical state is threaded. -/
def physicalRun (a : Artifact) (cases : List Statement) (declarations : Array Wire) :
    Nat → RTL.InterfaceState a.storageShape → Option (RTL.InterfaceState a.storageShape)
  | 0,r => some r
  | n+1,r => do physicalRun a cases declarations n (← physicalTick a cases declarations {} r)

theorem Store.scalarBits_read {store : Store} {word : BitVec (env.type name).width}
    (h : store.scalarBits env name = some word) :
    BitVec.ofInt (env.type name).width ((store.scalar name).getD 0) = word := by
  cases found : store.scalar name <;> simp [Store.scalarBits,found] at h ⊢
  exact h

/-- Committing concrete writes gives the same live observations as finite
encoding of the reference result. Physical padding is allowed to differ. -/
theorem Store.Matches.commit_packed (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) {store : Store} {logical : Runtime}
    (related : store.Matches ((environment a r final.text #[]).withTemporaries values) a.storageShape logical) :
    StorageAgreement a.storageShape (store.commit a.storageShape).decode (FiniteRuntime.pack a.storageShape logical).decode := by
  constructor
  · have bitsEq := Store.scalarBits_read related.pc
    dsimp [environment,environmentFor,Environment.withTemporaries] at bitsEq
    exact congrArg BitVec.toNat bitsEq
  · intro n hn
    have bitsEq := Store.scalarBits_read (related.regs n hn)
    dsimp [environment,environmentFor,Environment.withTemporaries] at bitsEq
    simp only [FiniteRuntime.decode,Store.commit,FiniteRuntime.pack,hn,↓reduceDIte]
    rw [bitsEq]
  · intro n hn
    apply Array.ext
    · simp [FiniteRuntime.decode,Store.commit,FiniteRuntime.pack,hn.1,hn.2,WordBuffer.contents,WordBuffer.pack,related.memoryLength n hn.1]
    · intro j hj hk
      have live : j < (logical.data.arrays n).size := by
        simp only [FiniteRuntime.decode,FiniteRuntime.pack,hn.1,hn.2,↓reduceDIte,↓reduceIte,
          WordBuffer.contents,WordBuffer.pack,Array.size_ofFn] at hk
        omega
      simp only [FiniteRuntime.decode,Store.commit,FiniteRuntime.pack,hn.1,hn.2,↓reduceDIte,↓reduceIte,
        WordBuffer.contents,WordBuffer.pack,Array.getElem_ofFn]
      rw [related.memoryCells n hn.1 j live,Array.getElem?_eq_getElem live]
      simp only [bind,Option.bind,pure,Option.getD_some,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · intro n hn
    have bitsEq := Store.scalarBits_read (related.wires n hn)
    dsimp [environment,environmentFor,Environment.withTemporaries] at bitsEq
    simp only [FiniteRuntime.decode,Store.commit,FiniteRuntime.pack,hn,↓reduceDIte]
    rw [bitsEq]
  · intro q hq
    apply List.ext_getElem
    · simp [FiniteRuntime.decode,Store.commit,FiniteRuntime.pack,hq,WordBuffer.contents,WordBuffer.pack,related.queueLength q hq]
    · intro j hj hk
      have live : j < (logical.queues q).length := by
        simp only [FiniteRuntime.decode,FiniteRuntime.pack,hq,↓reduceDIte,WordBuffer.contents,WordBuffer.pack,
          Array.length_toList,Array.size_ofFn,List.size_toArray] at hk
        omega
      simp only [FiniteRuntime.decode,Store.commit,FiniteRuntime.pack,hq,↓reduceDIte,WordBuffer.contents,
        WordBuffer.pack,Array.getElem_toList,Array.getElem_ofFn]
      rw [related.queueCells q hq j live]
      simp only [bind,Option.bind,pure,Option.getD_some,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq,
        List.getElem?_toArray,List.getElem?_eq_getElem live]
  · have bitsEq := Store.scalarBits_read related.done
    dsimp [environment,environmentFor,Environment.withTemporaries] at bitsEq
    change ((BitVec.ofInt 1 ((store.scalar .done).getD 0)).toNat != 0) = logical.done
    rw [bitsEq]
    cases logical.done <;> rfl
  · have bitsEq := Store.scalarBits_read related.error
    dsimp [environment,environmentFor,Environment.withTemporaries] at bitsEq
    change ((BitVec.ofInt 1 ((store.scalar .error).getD 0)).toNat != 0) = logical.error
    rw [bitsEq]
    cases logical.error <;> rfl

/-- The existing storage invariant strengthens bit-pattern correspondence
into equality with the mathematical reference state. -/
theorem Store.Matches.commit_agrees (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) {store : Store} {logical : Runtime}
    (related : store.Matches ((environment a r final.text #[]).withTemporaries values) a.storageShape logical)
    (bounded : StorageBound a.storageShape logical) :
    StorageAgreement a.storageShape (store.commit a.storageShape).decode logical :=
  (related.commit_packed a r final values).trans (FiniteRuntime.pack_correct bounded)

theorem commit_environment (shape : StorageShape) (r : FiniteRuntime shape)
    (declarations : Array Wire) (temporaries : Array Int) (busy : Bool) (ports : RTL.Ports) :
    (environmentFor shape r declarations temporaries busy ports).store.commit shape = r := by
  have arrayLength (n : Fin shape.memories) : min ((r.arrays n).used.val) (shape.memorySize n.val) = (r.arrays n).used.val := by
    have bound : (r.arrays n).used.val < shape.memorySize n.val+1 := (r.arrays n).used.isLt
    omega
  have queueLength (q : Fin shape.queues) : min ((r.queues q).used.val) (shape.queueSize q.val) = (r.queues q).used.val := by
    have bound : (r.queues q).used.val < shape.queueSize q.val+1 := (r.queues q).used.isLt
    omega
  simp only [Store.commit,Environment.store,environmentFor,Fin.isLt,↓reduceDIte,Option.getD_some,
    BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.ofInt_toInt,Int.toNat_natCast,arrayLength,queueLength]
  have flag (b : Bool) : ((BitVec.ofInt 1 (if b then 1 else 0)).toNat != 0) = b := by cases b <;> rfl
  rw [flag,flag]

theorem base_store_matches (a : Artifact) (r : FiniteRuntime a.storageShape) (final : Emission) (values : Array Int) :
    (environment a r final.text #[]).store.Matches ((environment a r final.text #[]).withTemporaries values) a.storageShape r.decode := by
  have h := finite_store_matches a r final values
  exact ⟨h.pc,h.done,h.error,h.regs,h.wires,h.memoryLength,h.memoryCells,h.queueLength,h.queueCells⟩

/-- A reusable generated-case contract with the real pending physical store
and the busy/done connection. It follows from the same refinement proof,
not from a second correctness argument for the transformer. -/
theorem generated_cases_control (a : Artifact) (certificate : StorageCertificate a)
    (r : FiniteRuntime a.storageShape) (generated : generateCode a = .ok (codes,emission)) :
    ∃ values, evaluateWires a r emission.text = some values ∧
      Paired (fun body code => ∀ pending,
        pending.Matches ((environment a r emission.text #[]).withTemporaries values) a.storageShape r.decode →
        BusyMatches pending r.decode →
        ∃ writes, code.eval ((environment a r emission.text #[]).withTemporaries values) pending = some writes ∧
          writes.Matches ((environment a r emission.text #[]).withTemporaries values) a.storageShape
            (body.evalWith RTL.Combinational.eval a.machine.capacity r.decode r.decode) ∧
          BusyMatches writes (body.evalWith RTL.Combinational.eval a.machine.capacity r.decode r.decode))
        (RTL.artifactProgram a).cases.toList codes := by
  obtain ⟨values,evaluated,meaning⟩ := generateCode_total a certificate r generated
  refine ⟨values,evaluated,?_⟩
  apply mapM_related (statementCode a) (RTL.artifactProgram a).cases.toList (preserves_statementCode a)
    ?_ Emission.empty_wellFormed generated (Emission.Extends.refl _)
  intro body member before good code after compiled grows pending related busy
  have closed : StatementReferences a.storageShape body := by
    simp only [RTL.artifactProgram,RTL.lowerCombinational,Array.toList_map,List.mem_map] at member
    obtain ⟨node,member,rfl⟩ := member
    exact lowerNode_references _ node (certificate.closed node member)
  obtain ⟨writes,executed,result,control⟩ := statementCode_refines_control a r emission values body closed
    (artifact_ready a certificate r.decode member) good compiled grows meaning pending r.decode related
    (artifact_frame a certificate r.decode member)
  exact ⟨writes,executed,result,control busy⟩

/-- The actual clock evaluator, including case selection, pending writes,
physical commit and busy/done, agrees with the established quiet interface
transition. All physical cells are carried to the following clock. -/
theorem physicalTick_quiet_refines (a : Artifact) (certificate : StorageCertificate a)
    (generated : generateCode a = .ok (codes,emission)) (r : RTL.InterfaceState a.storageShape)
    (running : r.Running) (pcValid : r.core.pc.toNat < a.storageShape.states) :
    ∃ result, physicalTick a codes emission.text {} r = some result ∧
      StorageAgreement a.storageShape result.core.decode (RTL.interfaceTick a {} r).core.decode ∧
      result.busy = (RTL.interfaceTick a {} r).busy := by
  cases active : r.busy with
  | false =>
    refine ⟨r,?_,?_,?_⟩
    · simp only [physicalTick,clockCode,active,RTL.controller,RTL.Controller.select,RTL.PortTest.eval,
        Bool.false_eq_true,↓reduceIte,bind,Option.bind,pure,Statement.eval]
      change some ⟨(environmentFor a.storageShape r.core emission.text #[] false {}).store.commit _,_⟩ = some r
      rw [commit_environment]
      change some ⟨r.core,false⟩ = some r
      cases r with
      | mk core busy => dsimp at active; subst busy; rfl
    · rw [RTL.quiet_tick,active]
      exact StorageAgreement.refl _ _
    · rw [RTL.quiet_tick,active]
      simp only [Bool.false_eq_true,↓reduceIte]
      exact active.symm
  | true =>
    have notDone : r.core.done = false := by
      unfold RTL.InterfaceState.Running at running
      rw [active] at running
      cases hd : r.core.done <;> simp_all
    have inside : r.core.pc.toNat < (RTL.artifactProgram a).cases.size := by
      simpa only [RTL.artifactProgram,RTL.lowerCombinational,Array.size_map,Artifact.storageShape] using pcValid
    let body := (RTL.artifactProgram a).cases[r.core.pc.toNat]'inside
    have found : (RTL.artifactProgram a).cases[r.core.pc.toNat]? = some body := Array.getElem?_eq_getElem inside
    obtain ⟨values,evaluated,paired⟩ := generated_cases_control a certificate r.core generated
    obtain ⟨code,codeFound,correct⟩ := paired.lookup (by simpa using found)
    obtain ⟨writes,executed,related,busy⟩ := correct (environment a r.core emission.text #[]).store
      (base_store_matches a r.core emission values)
      (by simp [BusyMatches,Environment.store,environment,environmentFor,FiniteRuntime.decode,notDone])
    let logical := body.evalWith RTL.Combinational.eval a.machine.capacity r.core.decode r.core.decode
    have reference : (RTL.interfaceTick a {} r).core = FiniteRuntime.pack a.storageShape logical := by
      rw [RTL.quiet_tick,active]
      change (RTL.artifactProgram a).finiteTick a.storageShape r.core = _
      unfold RTL.Program.finiteTick RTL.Program.combinationalTick
      simp only [show r.core.decode.done = false from notDone,Bool.false_eq_true,↓reduceIte]
      change FiniteRuntime.pack _ (match (RTL.artifactProgram a).cases[r.core.pc.toNat]? with | none => _ | some b => _) = _
      rw [found]
      rfl
    have busyEq : writes.busy = !logical.done := by
      unfold BusyMatches at busy
      change writes.scalar .busy = some (if logical.done then 0 else 1) at busy
      simp only [Store.busy,busy,Option.getD_some]
      cases logical.done <;> rfl
    refine ⟨⟨writes.commit a.storageShape,writes.busy⟩,?_,?_,?_⟩
    · simp only [physicalTick,clockCode,active,RTL.controller_execute ({} : RTL.Ports) rfl,evaluated,
        bind,Option.bind,pure,codeFound,Option.getD_some]
      rw [executed]
    · rw [reference]
      exact related.commit_packed a r.core emission values
    · have control := RTL.quiet_tick_running a r running
      change (RTL.interfaceTick a {} r).busy = !(RTL.interfaceTick a {} r).core.done at control
      change writes.busy = _
      rw [control,reference]
      exact busyEq

/-- Whole concrete execution follows the source-level clock model at every
cycle. The induction uses the actual committed physical state, including its
padding, rather than replacing it with the reference finite state. -/
theorem physicalRun_agrees (a : Artifact) (certificate : StorageCertificate a)
    (generated : generateCode a = .ok (codes,emission))
    (logical : Runtime)
    (bounded : ∀ n, StorageBound a.storageShape (a.machine.run n logical))
    (widths : ∀ n, (a.machine.run n logical).done = false →
      InputsBound (a.machine.run n logical).data (a.machine.run n logical).wires a.storageShape.wireRange)
    (r : RTL.InterfaceState a.storageShape) (running : r.Running)
    (same : StorageAgreement a.storageShape r.core.decode logical) (cycles : Nat) :
    ∃ result, physicalRun a codes emission.text cycles r = some result ∧
      StorageAgreement a.storageShape result.core.decode (a.machine.run cycles logical) ∧ result.Running := by
  induction cycles generalizing r logical with
  | zero => exact ⟨r,rfl,same,running⟩
  | succ n ih =>
    have pcValid : r.core.pc.toNat < a.storageShape.states := by
      change r.core.decode.pc < _
      rw [same.pc]
      exact (bounded 0).pc
    obtain ⟨next,executed,core,control⟩ := physicalTick_quiet_refines a certificate generated r running pcValid
    have nextRunning : next.Running := by
      have referenceRunning := RTL.quiet_tick_running a r running
      change next.busy = !next.core.decode.done
      rw [control,core.done]
      exact referenceRunning
    have nextSame := core.trans (RTL.quiet_tick_agrees a certificate.closed r logical running same (bounded 1) (widths 0))
    obtain ⟨result,rest,finalSame,finalRunning⟩ := ih (a.machine.tick logical) (fun k => bounded (k+1))
      (fun k => widths (k+1)) next nextRunning nextSame
    exact ⟨result,by rw [physicalRun,executed]; exact rest,finalSame,finalRunning⟩

/-- Source-to-generated-compute execution, from a prepared invocation state.
All compute clocks use the actual emitted expressions and assignments.
StartupSound separately proves that executing startCode
constructs this state (up to the same live-storage observation relation). -/
theorem physical_pipeline_from_started (p : HybridWord.Plan outputs sizes ks)
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
      (result.core.result s.encode).map (Option.map (PipelineUse.observe outputs)) =
        some ((HybridWord.source x y ks s).map (fun t => PipelineUse.observe outputs t.encode)) := by
  let a := checked.artifact
  let s := (RTL.restoreLengths a prepared).inputSource
  let logical := a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)
  have fits : a.InputFits s.encode := by
    intro n hn
    rw [FiniteRuntime.inputSource_encode]
    simp only [FiniteRuntime.decode,hn.1,↓reduceDIte]
    exact WordBuffer.contents_size _
  have bounded := storage_reachable checked.storage checked.valid checked.inputs s x y fits
  have initial := RTL.beginInvocation_agrees a prepared x y (bounded 0)
  obtain ⟨cycles,result,hr,ho⟩ := word_pipeline_finishes p compiled outputsSafe s x y sized ready
  obtain ⟨actual,executed,same,control⟩ := physicalRun_agrees a checked.storage generated logical bounded
    (fun n => reachable_widths checked.valid checked.inputs s x y n)
    ⟨RTL.beginInvocation a prepared x y,true⟩ rfl initial cycles
  have observed := observation_from_agreement checked.storage.closed logical cycles _ same outputPorts
  rw [checked.execution] at hr
  change (a.machine.run cycles logical).result = some result at hr
  rw [hr,Option.map_some,ho] at observed
  have finished : actual.core.done = true := by
    cases hd : actual.core.done
    · simp [FiniteRuntime.result,hd] at observed
    · rfl
  have idle : actual.busy = false := by
    change actual.busy = !actual.core.done at control
    simpa [finished] using control
  exact ⟨cycles,actual,executed,finished,idle,observed⟩

end IRComparison.Circuit.SystemVerilog
