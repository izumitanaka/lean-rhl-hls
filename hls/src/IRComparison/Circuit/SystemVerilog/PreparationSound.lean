import IRComparison.Circuit.SystemVerilog.StartupSound

namespace IRComparison.Circuit.SystemVerilog

/-- Initialization clears a complete declared bank. The old-state bank is
required to exist; this does not create storage for invalid addresses. -/
theorem zero_bank_eval (env : Environment) (pending : Store) (id size : Nat)
    (allocated : ∀ j, j < size → (env.cell (.memory id) j).isSome = true) :
    (Statement.forRange .loopIndex size
      (.assign (.index (.memory id) (.reference .loopIndex)) (.integer 0))).eval env pending =
      some {pending with cell := fun name j =>
        if name = .memory id ∧ j < size then some 0 else pending.cell name j} := by
  have step (j : Nat) (inside : j < size) (s : Store) :
      (Statement.assign (.index (.memory id) (.reference .loopIndex)) (.integer 0)).eval
        (env.loop .loopIndex size j) s = some (s.setCell (.memory id) j 0) := by
    obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (allocated j inside)
    simp only [Statement.eval,Destination.write,loop_reference_eval env .loopIndex (by omega : j ≤ size),
      bind,Option.bind,Value.integer,Value.ofInt,Bool.false_eq_true,↓reduceIte,
      BitVec.ofInt_natCast,loop_counter_fits (by omega : j ≤ size)]
    have zero := (SignedMeaning.integer (env:=env.loop .loopIndex size j) 0).assignment
      ((env.loop .loopIndex size j).type (.memory id)).width
    simp [Environment.loop] at zero
    simp [Environment.loop,hv,show ¬(j : Int) < 0 by omega,zero]
  rw [forRange_cells env .loopIndex (.memory id) size _ (fun _ => 0) step]
  congr 2
  funext name j
  by_cases h : name = .memory id <;> simp [RTL.writeRange_correct,h]

/-- Reset's mathematical effect on pending storage. Only declared scalar
registers and banks are cleared. Unused FIFO cells are retained. -/
def resetWrites (a : Artifact) (env : Environment) (s : Store) : Store :=
  let s := s.patch [(.pc,0),(.busy,0),(.done,0),(.error,0)]
  let s := s.patch ((List.range a.wires.size).map fun n => (Name.holding n,0))
  let s := s.patch ((a.machine.nodes.toList.flatMap Node.registers).eraseDups.map fun n => (Name.register n,0))
  let s := a.memories.toList.foldl (fun pending e =>
    let pending := pending.setScalar (.length e.1) (BitVec.ofNat (env.type (.length e.1)).width e.2).toNat
    {pending with cell := fun name j =>
      if name = .memory e.1 ∧ j < e.2 then some 0 else pending.cell name j}) s
  s.patch (a.machine.capacities.toList.map fun e => (Name.used e.1,0))

theorem resetCode_eval (a : Artifact) (layout : RTL.InterfaceLayout a)
    (r : FiniteRuntime a.storageShape) (wires : Array Wire) (busy : Bool) (ports : RTL.Ports) (s : Store) :
    let env := environment a r wires #[] busy ports
    (resetCode a).eval env s = some (resetWrites a env s) := by
  let env := environment a r wires #[] busy ports
  have clears {α : Type} (xs : List α) (name : α → Name) (pending : Store) :
      (sequence (xs.map fun n => write (name n) (.integer 0))).eval env pending =
        some (pending.patch (xs.map fun n => (name n,0))) := by
    rw [sequence_map_eval xs _ (fun p n => p.setScalar (name n) 0)
      (by intro n hn p; simpa using write_integer_eval env (name n) 0 p)]
    simp [Store.patch,List.foldl_map]
  have memories (pending : Store) :
      (sequence (a.memories.toList.map fun (id,size) =>
        .seq (write (.length id) (.integer size))
          (.forRange .loopIndex size (.assign (.index (.memory id) (.reference .loopIndex)) (.integer 0))))).eval env pending =
      some (a.memories.toList.foldl (fun p e =>
        let p := p.setScalar (.length e.1) (BitVec.ofNat (env.type (.length e.1)).width e.2).toNat
        {p with cell := fun name j => if name = .memory e.1 ∧ j < e.2 then some 0 else p.cell name j}) pending) := by
    apply sequence_map_eval
    intro e he p
    simp only [Statement.eval,write_integer_eval,Option.bind_some]
    apply zero_bank_eval
    intro j hj
    have bounds := layout.2 e he
    change e.1 < a.storageShape.memories ∧ e.2 = a.storageShape.memorySize e.1 at bounds
    simp [env,environment,environmentFor,bounds.1,show j < a.storageShape.memorySize e.1 by omega]
  change (resetCode a).eval env s = _
  simp only [resetCode,sequence_append_eval,sequence_cons_eval,sequence_nil_eval,
    write_integer_eval,write_bit_eval env .busy false rfl,
    write_bit_eval env .done false rfl,write_bit_eval env .error false rfl,Option.bind_some]
  rw [clears,Option.bind_some,clears,Option.bind_some,memories,Option.bind_some,clears]
  simp [resetWrites,Store.patch_cons,Store.patch_nil,env]


theorem count_eq_integer {n : Nat} (typed : env.type name = ⟨w,false⟩)
    (stored : env.scalar name = some (n : Int)) (fits : n < 2^w) (limit : Nat) :
    BooleanMeaning env (.binary .eq (.reference name) (.integer limit)) (decide (n = limit)) := by
  apply unsigned_comparison (a:=.reference name) (b:=.integer limit) (op:=.eq) (x:=n) (y:=limit) typed rfl rfl rfl
  · simpa only [Nat.max_eq_right (Nat.le_max_left w (bits limit+1))] using
      unsigned_reference_context typed stored fits (max w (bits limit+1))
  · simpa only [Nat.max_eq_right (Nat.le_max_right w (bits limit+1))] using
      integer_unsigned_context (env:=env) limit (max w (bits limit+1))
  · exact Nat.lt_of_lt_of_le fits (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  · exact Nat.lt_of_lt_of_le (bits_fits limit) (Nat.pow_le_pow_right (by decide) (by omega))
  · simp only [arithmetic,Int.ofNat_inj,decide_eq_true_eq]

theorem branch_boolean (meaning : BooleanMeaning env c choice) (yes no : Statement) (s : Store) :
    (Statement.branch c yes no).eval env s = if choice then yes.eval env s else no.eval env s := by
  simp only [Statement.eval,meaning.evaluated,bind,Option.bind,truth_integer]
  cases choice <;> rfl

/-- A configuration edge modifies only the selected declared register or
original-memory word. Invalid selections are no-ops, not new allocations. -/
def configureWrites (a : Artifact) (ports : RTL.Ports) (s : Store) : Store :=
  if ports.register then
    (a.machine.nodes.toList.flatMap Node.registers).eraseDups.foldl (fun pending n =>
      if ports.id.toNat = n then pending.setScalar (.register n) ports.value.toNat else pending) s
  else a.originalMemories.toList.foldl (fun pending e =>
    if ports.id.toNat = e.1 ∧ ports.address.toNat < e.2 then
      pending.setCell (.memory e.1) ports.address.toNat ports.value.toNat else pending) s

theorem configureCode_eval (a : Artifact) (layout : RTL.InterfaceLayout a)
    (r : FiniteRuntime a.storageShape) (wires : Array Wire) (busy : Bool) (ports : RTL.Ports) (s : Store) :
    let env := environment a r wires #[] busy ports
    (configureCode a).eval env s = some (configureWrites a ports s) := by
  let env := environment a r wires #[] busy ports
  have choice : BooleanMeaning env (.reference .configRegister) ports.register := by
    constructor
    · rfl
    · cases hb : ports.register <;>
        simp [Expr.eval,Expr.type,env,environment,environmentFor,hb,Value.inContext,IntegralType.context,Value.ofInt,truth]
      all_goals rfl
  have select (n : Nat) := count_eq_integer (env:=env) (name:=.configId) (w:=32)
    (n:=ports.id.toNat) rfl rfl ports.id.isLt n
  have range (size : Nat) := count_lt_integer (env:=env) (name:=.configAddress) (w:=32)
    (n:=ports.address.toNat) rfl rfl ports.address.isLt size
  have scalar (n : Nat) (pending : Store) :
      (write (.register n) (.reference .configData)).eval env pending =
        some (pending.setScalar (.register n) ports.value.toNat) := by
    have rhs := unsigned_reference_assignment (env:=env) (name:=.configData) (w:=32)
      (n:=ports.value.toNat) rfl rfl ports.value.isLt 32
    simp only [write,Statement.eval,Destination.write]
    change (Expr.assignment env 32 (.reference .configData)).bind _ = _
    rw [rhs]
    simp
    rfl
  have cell (id size : Nat) (member : (id,size) ∈ a.originalMemories.toList)
      (inside : ports.address.toNat < size) (pending : Store) :
      (Statement.assign (.index (.memory id) (.reference .configAddress)) (.reference .configData)).eval env pending =
        some (pending.setCell (.memory id) ports.address.toNat ports.value.toNat) := by
    have bounds := (layout.1 (id,size) member).2
    change id < a.storageShape.memories ∧ size ≤ a.storageShape.memorySize id at bounds
    have allocated : (env.cell (.memory id) ports.address.toNat).isSome = true := by
      simp [env,environment,environmentFor,bounds.1,show ports.address.toNat < a.storageShape.memorySize id by omega]
    obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp allocated
    have address := unsigned_reference_self (env:=env) (name:=.configAddress) (w:=32)
      (n:=ports.address.toNat) rfl rfl ports.address.isLt
    have rhs := unsigned_reference_assignment (env:=env) (name:=.configData) (w:=32)
      (n:=ports.value.toNat) rfl rfl ports.value.isLt 32
    simp only [Statement.eval,Destination.write,address,bind,Option.bind,Value.integer,Value.ofInt,
      Bool.false_eq_true,↓reduceIte,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    simp only [show ¬(ports.address.toNat : Int) < 0 by omega,↓reduceIte,Int.toNat_natCast,read,bind,Option.bind]
    have ty : (env.type (.memory id)).width = 32 := rfl
    rw [ty,rhs]
    simp only [pure,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  change (configureCode a).eval env s = _
  rw [configureCode,branch_boolean choice]
  cases hb : ports.register
  · simp only [Bool.false_eq_true,↓reduceIte,configureWrites,hb]
    apply sequence_map_eval
    intro e he pending
    rw [branch_boolean ((select e.1).and (range e.2))]
    by_cases yes : ports.id.toNat = e.1 ∧ ports.address.toNat < e.2
    · simp only [yes.1,yes.2,decide_true,Bool.true_and,↓reduceIte,if_pos yes]
      exact cell e.1 e.2 he yes.2 pending
    · have no : (decide (ports.id.toNat = e.1) && decide (ports.address.toNat < e.2)) = false := by
        by_cases h : ports.id.toNat = e.1 <;> simp_all
      simp only [no,Bool.false_eq_true,↓reduceIte,if_neg yes,Statement.eval]
  · simp only [↓reduceIte,configureWrites,hb]
    apply sequence_map_eval
    intro n hn pending
    rw [branch_boolean (select n)]
    by_cases yes : ports.id.toNat = n
    · simp only [yes,decide_true,↓reduceIte]; exact scalar n pending
    · simp only [yes,decide_false,Bool.false_eq_true,↓reduceIte,Statement.eval]


/-- Configuration commands supplied by the environment while the circuit is
idle. Signal timing and the intended input values remain its contract. -/
structure Configuration where
  register : Bool
  id : BitVec 32
  address : BitVec 32
  value : BitVec 32
  deriving Repr

def Configuration.ports (c : Configuration) : RTL.Ports :=
  {configure := true,register := c.register,id := c.id,address := c.address,value := c.value}

/-- Mathematical reset state. Sparse unused slots and unused FIFO cells are
retained; no fresh arbitrary value is chosen on each read. -/
def resetPrepared (a : Artifact) (r : RTL.InterfaceState a.storageShape) : RTL.InterfaceState a.storageShape :=
  let env := environment a r.core #[] #[] r.busy {reset := true}
  let writes := resetWrites a env env.store
  ⟨writes.commit a.storageShape,false⟩

def configurePrepared (a : Artifact) (c : Configuration)
    (r : RTL.InterfaceState a.storageShape) : RTL.InterfaceState a.storageShape :=
  let env := environment a r.core #[] #[] false c.ports
  ⟨(configureWrites a c.ports env.store).commit a.storageShape,false⟩

def prepareInputs (a : Artifact) (commands : List Configuration)
    (initial : RTL.InterfaceState a.storageShape) : RTL.InterfaceState a.storageShape :=
  commands.foldl (fun r c => configurePrepared a c r) (resetPrepared a initial)

theorem fold_scalar_preserved (xs : List α) (update : Store → α → Store) (name : Name)
    (same : ∀ p e, (update p e).scalar name = p.scalar name) (s : Store) :
    (xs.foldl update s).scalar name = s.scalar name := by
  induction xs generalizing s with
  | nil => rfl
  | cons e rest ih => rw [List.foldl_cons,ih,same]

theorem configureWrites_busy_scalar (a : Artifact) (ports : RTL.Ports) (s : Store) :
    (configureWrites a ports s).scalar .busy = s.scalar .busy := by
  unfold configureWrites
  split
  · apply fold_scalar_preserved
    intro p e; split <;> simp [Store.setScalar]
  · apply fold_scalar_preserved
    intro p e; split <;> rfl

theorem resetWrites_busy_scalar (a : Artifact) (env : Environment) (s : Store) :
    (resetWrites a env s).scalar .busy = some 0 := by
  unfold resetWrites
  rw [Store.patch_constant]
  simp only [reduceCtorEq,and_false,exists_false,↓reduceIte]
  rw [fold_scalar_preserved _ _ .busy (by intro p e; simp [Store.setScalar])]
  rw [Store.patch_constant,Store.patch_constant]
  simp [Store.patch_cons,Store.patch_nil,Store.setScalar]

theorem prepareInputs_idle (a : Artifact) (commands : List Configuration) (initial) :
    (prepareInputs a commands initial).busy = false := by
  have fold (cs : List Configuration) (r : RTL.InterfaceState a.storageShape) (idle : r.busy = false) :
      (cs.foldl (fun r c => configurePrepared a c r) r).busy = false := by
    induction cs generalizing r with
    | nil => exact idle
    | cons c cs ih => exact ih _ rfl
  exact fold commands _ rfl

theorem moduleCode_reset (a : Artifact) (layout : RTL.InterfaceLayout a)
    (outputs : List Nat) (cases : List Statement) (wires : Array Wire)
    (r : RTL.InterfaceState a.storageShape) :
    (moduleCode a outputs cases wires).tick a.storageShape {reset := true} r = some (resetPrepared a r) := by
  rw [moduleCode_tick]
  unfold physicalTick clockCode
  rw [RTL.controller_reset _ _ rfl]
  simp only [bind,Option.bind,pure]
  rw [resetCode_eval a layout]
  simp only [bind,Option.bind,pure]
  have busy : (resetWrites a (environment a r.core wires #[] r.busy {reset := true})
      (environment a r.core wires #[] r.busy {reset := true}).store).busy = false := by
    unfold Store.busy
    rw [resetWrites_busy_scalar]
    rfl
  rw [busy]
  rfl

theorem moduleCode_configure (a : Artifact) (layout : RTL.InterfaceLayout a)
    (outputs : List Nat) (cases : List Statement) (wires : Array Wire)
    (r : RTL.InterfaceState a.storageShape) (c : Configuration) (idle : r.busy = false) :
    (moduleCode a outputs cases wires).tick a.storageShape c.ports r = some (configurePrepared a c r) := by
  rw [moduleCode_tick]
  unfold physicalTick clockCode
  rw [idle,RTL.controller_configure _ rfl rfl rfl]
  simp only [bind,Option.bind,pure]
  rw [configureCode_eval a layout]
  simp only [bind,Option.bind,pure]
  have busy : (configureWrites a c.ports (environment a r.core wires #[] false c.ports).store).busy = false := by
    unfold Store.busy
    rw [configureWrites_busy_scalar]
    rfl
  rw [busy]
  rfl

theorem emitted_text_reset (emitted : emit a outputs = .ok text) (r : RTL.InterfaceState a.storageShape) :
    tickText text a.storageShape {reset := true} r = some (resetPrepared a r) := by
  obtain ⟨code,parsed,generated,_,readback,_,_,ticks,_⟩ := emit_text_correct emitted
  obtain ⟨cases,es,_,same⟩ := generateModule_components generated
  simp only [tickText,readback,Option.bind_some,ticks,same]
  exact moduleCode_reset a (emitted_interface_layout emitted) _ _ _ _

theorem emitted_text_configure (emitted : emit a outputs = .ok text)
    (r : RTL.InterfaceState a.storageShape) (c : Configuration) (idle : r.busy = false) :
    tickText text a.storageShape c.ports r = some (configurePrepared a c r) := by
  obtain ⟨code,parsed,generated,_,readback,_,_,ticks,_⟩ := emit_text_correct emitted
  obtain ⟨cases,es,_,same⟩ := generateModule_components generated
  simp only [tickText,readback,Option.bind_some,ticks,same]
  exact moduleCode_configure a (emitted_interface_layout emitted) _ _ _ _ _ idle

/-- Interpret the actual emitted characters on every supplied clock edge. -/
def traceText (text : String) (shape : StorageShape) : List RTL.Ports →
    RTL.InterfaceState shape → Option (RTL.InterfaceState shape)
  | [],r => some r
  | ports::rest,r => (tickText text shape ports r).bind (traceText text shape rest)

theorem emitted_text_preparation (emitted : emit a outputs = .ok text)
    (commands : List Configuration) (initial : RTL.InterfaceState a.storageShape) :
    traceText text a.storageShape ({reset := true} :: commands.map Configuration.ports) initial =
      some (prepareInputs a commands initial) := by
  have config (cs : List Configuration) (r : RTL.InterfaceState a.storageShape) (idle : r.busy = false) :
      traceText text a.storageShape (cs.map Configuration.ports) r =
        some (cs.foldl (fun r c => configurePrepared a c r) r) := by
    induction cs generalizing r with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.map_cons,traceText,emitted_text_configure emitted r c idle,Option.bind_some,List.foldl_cons]
      exact ih _ rfl
  rw [traceText,emitted_text_reset emitted,Option.bind_some]
  exact config commands _ rfl

/-- One complete invocation from arbitrary power-on storage, through the
actual reset/configuration/start ports, to source results at the read port.
The environment supplies the commands; no host program is verified here. -/
theorem emitted_text_reset_config_start_readout (p : HybridWord.Plan outputs sizes ks)
    (compiled : compile layout (HybridUnifiedPipeline.lower p) = .ok checked)
    (emitted : emit checked.artifact outputs = .ok text)
    (outputsSafe : ∀ id ∈ outputs, id < layoutLimit layout)
    (outputPorts : ∀ id ∈ outputs, checked.artifact.storageShape.hasMemory id)
    (initial : RTL.InterfaceState checked.artifact.storageShape) (commands : List Configuration)
    (x y : BitVec 32)
    (sized : PipelineShapes.Layout sizes
      (RTL.restoreLengths checked.artifact (prepareInputs checked.artifact commands initial).core).inputSource.encode)
    (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y)
      (RTL.restoreLengths checked.artifact (prepareInputs checked.artifact commands initial).core).inputSource.encode) :
    let a := checked.artifact
    let prepared := prepareInputs a commands initial
    let s := (RTL.restoreLengths a prepared.core).inputSource
    ∃ cycles result,
      ((traceText text a.storageShape ({reset := true} :: commands.map Configuration.ports) initial).bind
        (fun r => (tickText text a.storageShape {start := true,x := x,y := y} r).bind
          (runText text a.storageShape cycles))) = some result ∧
      result.core.done = true ∧ result.busy = false ∧
      (∀ final, HybridWord.source x y ks s = some final →
        result.core.error = false ∧ ∀ request,
          readText text a.storageShape result.core request = some (stateReadResult a outputs final.encode request)) ∧
      (HybridWord.source x y ks s = none → result.core.error = true) := by
  dsimp only
  rw [emitted_text_preparation emitted]
  simp only [Option.bind_some]
  exact emitted_text_invocation_readout p compiled emitted outputsSafe outputPorts
    (prepareInputs checked.artifact commands initial) {start := true,x := x,y := y}
    (prepareInputs_idle _ _ _) rfl rfl sized ready

end IRComparison.Circuit.SystemVerilog
