import IRComparison.Examples.WordFrontendExamples
import IRComparison.Examples.WordWorkloads
import IRComparison.Examples.HLSBenchmarks
import IRComparison.Circuit.Backend
import IRComparison.Circuit.RTL.InterfaceRunSound
import IRComparison.Circuit.SystemVerilog.PreparationSound
open IRComparison
open HybridWord
set_option maxRecDepth 4096
set_option maxHeartbeats 8000000

-- Materialize the functional finite banks once per simulated edge. This is
-- evaluation sharing only; the theorem below proves pointwise identity.
structure FrozenPi {n : Nat} (α : Fin n → Type) where
  values : (i : Fin n) → α i

-- Return a structure, not a function: otherwise Lean's arity optimization
-- can move Array.ofFn beneath the final index argument and recompute it.
@[noinline] def freezePi {n : Nat} {α : Fin n → Type} (f : (i : Fin n) → α i) : FrozenPi α :=
  let values : Array (Sigma α) := Array.ofFn fun i => ⟨i,f i⟩
  ⟨fun i =>
    let v := values[i.val]'(by simp [values])
    have same : v.1 = i := by simp [v,values]
    same ▸ v.2⟩

theorem freezePi_eq {n : Nat} {α : Fin n → Type} (f : (i : Fin n) → α i) : (freezePi f).values = f := by
  funext i
  unfold freezePi
  dsimp only
  apply eq_of_heq
  apply HEq.trans (eqRec_heq _ _)
  rw [Array.getElem_ofFn]

def freezeRuntime (r : Circuit.FiniteRuntime shape) : Circuit.FiniteRuntime shape :=
  {r with
    regs := (freezePi r.regs).values
    wires := (freezePi r.wires).values
    arrays := (freezePi fun id =>
      let b := r.arrays id
      let cells := Array.ofFn b.cells
      {b with cells := fun j => cells[j.val]'(by simpa [cells] using j.isLt)}).values
    queues := (freezePi fun id =>
      let b := r.queues id
      let cells := Array.ofFn b.cells
      {b with cells := fun j => cells[j.val]'(by simpa [cells] using j.isLt)}).values }

theorem freezeRuntime_eq (r : Circuit.FiniteRuntime shape) : freezeRuntime r = r := by
  simp only [freezeRuntime,freezePi_eq,Array.getElem_ofFn]

def preparedTick (a : Circuit.Artifact) (code : Circuit.RTL.Program Circuit.RTL.Combinational)
    (p : Circuit.RTL.Ports) (r : Circuit.RTL.InterfaceState a.storageShape) : Circuit.RTL.InterfaceState a.storageShape :=
  match Circuit.RTL.controller.select p r.busy with
  | .reset => Circuit.RTL.resetInterface r.core
  | .start => ⟨Circuit.RTL.beginInvocation a r.core p.x p.y,true⟩
  | .configure => ⟨Circuit.RTL.configureInterface a p r.core,false⟩
  | .hold => r
  | .execute =>
      let next := code.finiteTick a.storageShape r.core
      ⟨next,!next.done⟩

theorem preparedTick_correct (a : Circuit.Artifact) (p : Circuit.RTL.Ports)
    (r : Circuit.RTL.InterfaceState a.storageShape) :
    preparedTick a (Circuit.RTL.artifactProgram a) p r = Circuit.RTL.interfaceTick a p r := rfl

theorem preparedClockCheck_eq (a : Circuit.Artifact) (cases declarations) (ports : Circuit.RTL.Ports)
    (r : Circuit.RTL.InterfaceState a.storageShape) :
    let expected := preparedTick a (Circuit.RTL.artifactProgram a) ports r
    Circuit.SystemVerilog.checkClockAgainst a cases declarations ports r
      {expected with core := freezeRuntime expected.core} =
      Circuit.SystemVerilog.checkClock a cases declarations ports r := by
  simp [freezeRuntime_eq,preparedTick_correct,Circuit.SystemVerilog.checkClock]

-- Reference evaluation still checks every emitted wire on every compute
-- edge. Resolve immutable child references once, not on every clock.
def referenceNode (r : Circuit.Runtime) : Circuit.RTL.Term → List Int → Option Int
  | .literal n, [] => some n
  | .wire n, [] => some (r.wires n)
  | .register n, [] => some (r.data.regs n)
  | .length a, [] => some ((r.data.arrays a).size : Int)
  | .cell a _, [j] => some (((r.data.arrays a)[j.toNat]?).getD 0)
  | .binary op _ _, [u,v] => some (Circuit.hardwareBin op u v)
  | .nonnegative _, [v] => some (v.toNat : Int)
  | .resize w _, [v] => some ((BitVec.ofInt w v).toInt)
  | .mux _ _ _, [c,y,n] => some (if c != 0 then y else n)
  | _,_ => none

theorem referenceNode_correct (r : Circuit.Runtime) (t : Circuit.RTL.Term) :
    referenceNode r t (t.children.map (Circuit.RTL.Term.eval r)) = some (t.eval r) := by
  cases t <;> simp [referenceNode,Circuit.RTL.Term.children,Circuit.RTL.Term.eval]

structure ReferenceEntry where
  term : Circuit.RTL.Term
  children : List Nat

def prepareReference (code : Circuit.Emission) : Except String (Array ReferenceEntry) := do
  let mut previous : Array Circuit.RTL.Term := #[]
  let mut entries : Array ReferenceEntry := #[]
  for (term,signal) in code.cache do
    unless signal.name == .temporary entries.size do throw "unordered reference cache"
    let children ← term.children.mapM fun child => do
      let some id := previous.toList.findIdx? (· == child) | throw "missing reference child"
      return id
    entries := entries.push ⟨term,children⟩
    previous := previous.push term
  return entries

def checkReference (a : Circuit.Artifact) (r : Circuit.FiniteRuntime a.storageShape)
    (code : Circuit.Emission) (entries : Array ReferenceEntry) : Except String Unit := do
  let some actual := Circuit.SystemVerilog.evaluateWires a r code.text | throw "undefined generated wire"
  let logical := r.decode
  let mut expected : Array Int := #[]
  for entry in entries do
    let some children := entry.children.mapM (fun n => expected[n]?) | throw "unchecked reference child"
    let some value := referenceNode logical entry.term children | throw "invalid reference arity"
    unless actual[expected.size]? == some value do throw s!"wire e{expected.size} differs from reference"
    expected := expected.push value

-- Compare all physical fields, including unused cells, at startup edges.
def comparePrepared (label : String) (r t : Circuit.RTL.InterfaceState shape) : IO Unit := do
  unless r.busy == t.busy && r.core.pc == t.core.pc && r.core.done == t.core.done && r.core.error == t.core.error do
    throw (IO.userError s!"{label}: startup control mismatch")
  for n in [:shape.registers] do
    if h : n < shape.registers then
      unless r.core.regs ⟨n,h⟩ == t.core.regs ⟨n,h⟩ do throw (IO.userError s!"{label}: register mismatch {n}")
  for n in [:shape.wires.size] do
    if h : n < shape.wires.size then
      unless r.core.wires ⟨n,h⟩ == t.core.wires ⟨n,h⟩ do throw (IO.userError s!"{label}: holding mismatch {n}")
  for n in [:shape.memories] do
    if h : n < shape.memories then
      let a := r.core.arrays ⟨n,h⟩
      let b := t.core.arrays ⟨n,h⟩
      unless a.used == b.used && Array.ofFn a.cells == Array.ofFn b.cells do
        throw (IO.userError s!"{label}: memory mismatch {n}")
  for n in [:shape.queues] do
    if h : n < shape.queues then
      let a := r.core.queues ⟨n,h⟩
      let b := t.core.queues ⟨n,h⟩
      unless a.used == b.used && Array.ofFn a.cells == Array.ofFn b.cells do
        throw (IO.userError s!"{label}: queue mismatch {n}")

def initial : HybridWord.State :=
  ⟨fun _ => 0,fun a => if a = 0 then #[4294967295,1,2,3] else #[0,0,0,0]⟩

structure BenchmarkFixture where
  name : String
  family : String
  variant : String
  size : Nat
  x : Word
  y : Word
  inputs : List (Nat × Array Word)
  expected : List (Nat × Array Word)

def parseBanks (j : Lean.Json) : Except String (List (Nat × Array Word)) := do
  let entries ← j.getArr?
  entries.toList.mapM fun entry => do
    let id ← (← entry.getObjVal? "id").getNat?
    let values ← (← entry.getObjVal? "values").getArr?
    let words ← values.mapM fun value => return BitVec.ofNat 32 (← value.getNat?)
    return (id,words)

def parseFixture (j : Lean.Json) : Except String BenchmarkFixture := do
  return ⟨← (← j.getObjVal? "name").getStr?, ← (← j.getObjVal? "family").getStr?,
    ← (← j.getObjVal? "variant").getStr?, ← (← j.getObjVal? "size").getNat?,
    BitVec.ofNat 32 (← (← j.getObjVal? "x").getNat?),
    BitVec.ofNat 32 (← (← j.getObjVal? "y").getNat?),
    ← parseBanks (← j.getObjVal? "inputs"), ← parseBanks (← j.getObjVal? "expected")⟩

def check (name : String) (outputs : List Nat) (ks : List HybridWord.Kernel) (x y : Word := 0) (size : Nat := 4)
    (initialFill : Word := 0) (fixture : Option BenchmarkFixture := none) : IO Unit := do
  if (← IO.getEnv "HLS_LIST_CASES") == some "1" then
    IO.println s!"CASE {name}"
    return
  if let some selected ← IO.getEnv "HLS_CASE" then
    unless selected == name do return
  if let some selected ← IO.getEnv "HLS_CASES" then
    unless (selected.splitOn ",").contains name do return
  let startedAt ← IO.monoMsNow
  let mut phaseAt := startedAt
  let mut phases : List (String × Lean.Json) := []
  let checkpoint := fun (label : String) (previous : Nat) => do
    let now ← IO.monoMsNow
    IO.println s!"{name}: phase {label} {now-previous} ms"
    (← IO.getStdout).flush
    pure now
  IO.println s!"{name}: phase source begin"
  (← IO.getStdout).flush
  let initial : HybridWord.State := ⟨fun _ => 0,fun a => if let some f := fixture then
    ((f.inputs.find? (fun pair => pair.1 == a)).map Prod.snd).getD (Array.replicate size 0)
    else if a = 0 then
    ((List.range size).map (fun j => if j = 0 then (4294967295 : Word) else BitVec.ofNat 32 j)).toArray
    else Array.replicate size initialFill⟩
  let sourceResult := HybridWord.source x y ks initial
  if let some f := fixture then
    let some final := sourceResult | throw (IO.userError s!"{name}: benchmark unexpectedly failed in source")
    unless f.expected.map Prod.fst == outputs do throw (IO.userError s!"{name}: incomplete independent oracle")
    for (id,values) in f.expected do
      unless final.arrays id == values do
        throw (IO.userError s!"{name}: source disagrees with independent Python oracle at array {id}")
  let now ← checkpoint "source" phaseAt
  phases := phases ++ [("source_ms",Lean.toJson (now-phaseAt))]
  phaseAt := now
  let some plan := compileProgram outputs (fun _ => size) ks
    | throw (IO.userError s!"{name}: plan failed")
  let now ← checkpoint "memory-plan" phaseAt
  phases := phases ++ [("memory_plan_ms",Lean.toJson (now-phaseAt))]
  phaseAt := now
  let control := HybridUnifiedPipeline.lower plan
  let now ← checkpoint "control" phaseAt
  phases := phases ++ [("control_ms",Lean.toJson (now-phaseAt))]
  phaseAt := now
  -- Optional diagnostic replay only. The measured regression below still
  -- calls the production Circuit.compile; this does not replace it.
  if (← IO.getEnv "HLS_PROFILE_DEEP") == some "1" then
    let layout := #[(0,size),(1,size),(2,size),(3,size),(5,size),(6,size)]
    let _ ← IO.ofExcept (Circuit.checkLayout layout control)
    let t ← checkpoint "probe-layout" phaseAt
    let _ ← IO.ofExcept (Circuit.checkSendBudgets control)
    let t ← checkpoint "probe-send-budgets" t
    let _ ← IO.ofExcept (Circuit.checkCommunication control)
    let t ← checkpoint "probe-communication" t
    let a := Circuit.lower layout control
    IO.println s!"{name}: probe nodes={a.machine.nodes.size}, wires={a.wires.size}"
    let t ← checkpoint "probe-lower" t
    let _ ← IO.ofExcept (Circuit.checkStorage a)
    let t ← checkpoint "probe-storage" t
    let table ← IO.ofExcept (Circuit.inferInvariant a)
    let t ← checkpoint "probe-infer-invariant" t
    unless Circuit.validInvariant a table do throw (IO.userError "probe invariant rejected")
    let _ ← checkpoint "probe-valid-invariant" t
  let checked ← match Circuit.compile (#[(0,size),(1,size),(2,size),(3,size),(5,size),(6,size)]) control with
    | .ok c => pure c
    | .error why => throw (IO.userError s!"{name}: static circuit check failed: {why}")
  let circuit := checked.artifact
  let now ← checkpoint "circuit-and-certification" phaseAt
  phases := phases ++ [("circuit_and_certification_ms",Lean.toJson (now-phaseAt))]
  phaseAt := now
  if name == "filter-three" then
    let invalid := {circuit with originalMemories := #[(0,circuit.storageShape.memorySize 0+1)]}
    match Circuit.checkModuleArtifact invalid with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "inconsistent startup metadata was accepted")
  IO.println s!"{name}: generating concrete expressions"
  (← IO.getStdout).flush
  let (clockCases,netlist) ← match Circuit.generateCode circuit with
    | .ok result => pure result
    | .error why => throw (IO.userError why)
  let module ← match Circuit.generateModule circuit outputs with
    | .ok code => pure code
    | .error why => throw (IO.userError s!"{name}: module assembly failed: {why}")
  let rtl ← match checked.emit outputs with
    | .ok text => pure text
    | .error why => throw (IO.userError why)
  let some parsed := Circuit.SystemVerilog.Concrete.parseModule rtl
    | throw (IO.userError s!"{name}: generated SystemVerilog did not parse")
  let generatedAt ← IO.monoMsNow
  phases := phases ++ [("emission_and_parse_ms",Lean.toJson (generatedAt-phaseAt))]
  let reference ← IO.ofExcept (prepareReference netlist)
  let referenceProgram := Circuit.RTL.artifactProgram circuit
  let referenceAt ← IO.monoMsNow
  phases := phases ++ [("reference_preparation_ms",Lean.toJson (referenceAt-generatedAt))]
  let mut result := circuit.machine.start initial.encode (encode x) (encode y)
  for (a,_) in circuit.memories do
    unless (initial.arrays a).size ≤ circuit.storageShape.memorySize a do
      throw (IO.userError s!"{name}: input array {a} exceeds its physical bank")
  -- Unused physical cells are deliberately nonzero; no observer may rely on
  -- the canonical zero padding used by `pack`.
  let physical := (Circuit.FiniteRuntime.pack circuit.storageShape result).withUnused
    (fun _ _ => 3735928559) (fun _ _ => 2779096485)
  let verifyClock := fun ports interface => do
    let expected := preparedTick circuit referenceProgram ports interface
    let expected := {expected with core := freezeRuntime expected.core}
    match Circuit.SystemVerilog.checkClockAgainst circuit clockCases netlist.text ports interface expected with
    | .ok () => pure ()
    | .error why => throw (IO.userError s!"{name}: {why}")
  -- Materialize every edge, including long host configuration sequences.
  -- freezeRuntime_eq proves this changes evaluation sharing only.
  let advance := fun ports interface => do
    match parsed.tick circuit.storageShape ports interface with
    | some next => pure {next with core := freezeRuntime next.core}
    | none => throw (IO.userError s!"{name}: concrete physical clock failed")
  let mut interface : Circuit.RTL.InterfaceState circuit.storageShape := ⟨physical,true⟩
  let resetReference := Circuit.SystemVerilog.resetPrepared circuit interface
  verifyClock {reset := true,start := true,configure := true} interface
  interface ← advance {reset := true, start := true, configure := true} interface
  comparePrepared s!"{name}/reset" interface resetReference
  -- Exercise valid scalar configuration and overwrite it with the source's
  -- initial zero before the invocation.
  for n in (circuit.machine.nodes.toList.flatMap Circuit.Node.registers).eraseDups do
    for value in ([4294967295,0] : List Word) do
      let command : Circuit.SystemVerilog.Configuration := ⟨true,BitVec.ofNat 32 n,0,value⟩
      let reference := Circuit.SystemVerilog.configurePrepared circuit command interface
      interface ← advance command.ports interface
      comparePrepared s!"{name}/register-config" interface reference
      if h : n < circuit.storageShape.registers then
        unless interface.core.regs ⟨n,h⟩ == value do throw (IO.userError "configuration did not store the supplied word")
  for (a,size) in circuit.originalMemories do
    for j in [:size] do
      let command : Circuit.SystemVerilog.Configuration :=
        ⟨false,BitVec.ofNat 32 a,BitVec.ofNat 32 j,(initial.arrays a)[j]?.getD 0⟩
      let reference := Circuit.SystemVerilog.configurePrepared circuit command interface
      verifyClock {configure := true,id := BitVec.ofNat 32 a,address := BitVec.ofNat 32 j,value := (initial.arrays a)[j]?.getD 0} interface
      interface ← advance
        {configure := true,id := BitVec.ofNat 32 a,address := BitVec.ofNat 32 j,
         value := (initial.arrays a)[j]?.getD 0} interface
      comparePrepared s!"{name}/configure" interface reference
  -- Invalid selections must not allocate or overwrite storage.
  for command in ([⟨false,4294967295,0,123⟩,⟨false,0,4294967295,123⟩,
      ⟨true,4294967295,0,123⟩] : List Circuit.SystemVerilog.Configuration) do
    let previous := interface
    interface ← advance command.ports interface
    comparePrepared s!"{name}/invalid-config" interface previous
  let startedReference : Circuit.RTL.InterfaceState circuit.storageShape :=
    ⟨Circuit.RTL.beginInvocation circuit interface.core x y,true⟩
  verifyClock {start := true,configure := true,x := x,y := y} interface
  interface ← advance {start := true,configure := true,x := x,y := y} interface
  comparePrepared s!"{name}/start" interface startedReference
  IO.println s!"{name}: checking {netlist.text.size} expressions per clock"
  (← IO.getStdout).flush
  let mut cycles := 0
  let profileClock := (← IO.getEnv "HLS_PROFILE_CLOCK") == some "1"
  while !result.done && cycles < 10000 do
    let t0 ← IO.monoMsNow
    match checkReference circuit interface.core netlist reference with
    | .ok () => pure ()
    | .error why => throw (IO.userError s!"{name}, cycle {cycles}: {why}")
    let t1 ← IO.monoMsNow
    if profileClock && cycles < 2 then
      IO.println s!"{name}: clock {cycles} wire-reference {t1-t0} ms"
      (← IO.getStdout).flush
    verifyClock {} interface
    let t2 ← IO.monoMsNow
    if profileClock && cycles < 2 then
      IO.println s!"{name}: clock {cycles} RTL-model-check {t2-t1} ms"
      (← IO.getStdout).flush
    result := circuit.machine.tick result
    let t3 ← IO.monoMsNow
    if profileClock && cycles < 2 then
      IO.println s!"{name}: clock {cycles} logical-model {t3-t2} ms"
      (← IO.getStdout).flush
    interface ← advance {} interface
    let t4 ← IO.monoMsNow
    if profileClock && cycles < 2 then
      IO.println s!"{name}: clock {cycles} parsed-RTL {t4-t3} ms"
      (← IO.getStdout).flush
    let decoded := interface.core.decode
    unless decoded.pc == result.pc && decoded.done == result.done && decoded.error == result.error do
      throw (IO.userError s!"{name}: finite control differs at cycle {cycles}")
    for r in circuit.machine.nodes.toList.flatMap Circuit.Node.registers do
      unless decoded.data.regs r == result.data.regs r do
        throw (IO.userError s!"{name}: finite register {r} differs at cycle {cycles}")
    for (a,_) in circuit.memories do
      unless decoded.data.arrays a == result.data.arrays a do
        throw (IO.userError s!"{name}: finite memory {a} differs at cycle {cycles}")
    for (q,_) in circuit.machine.capacities do
      unless decoded.queues q == result.queues q do
        throw (IO.userError s!"{name}: finite FIFO {q} differs at cycle {cycles}")
    for n in [:circuit.wires.size] do
      unless decoded.wires n == result.wires n do
        throw (IO.userError s!"{name}: finite holding register {n} differs at cycle {cycles}")
      let b := circuit.wires[n]?.getD Circuit.wordRange
      unless b.lo ≤ result.wires n && result.wires n ≤ b.hi do
        throw (IO.userError s!"{name}: register {n} violates its width invariant at pc {result.pc}: {result.wires n} outside [{b.lo},{b.hi}]")
    cycles := cycles+1
  -- Function-valued register observations are compared on known accessed registers.
  let observe := fun s : IRComparison.State => (outputs.map s.arrays,[s.regs 0,s.regs 2])
  let expected := sourceResult.map (fun t => observe t.encode)
  let actual := (interface.core.result initial.encode).map (Option.map observe)
  unless interface.core.done && !interface.busy do
    throw (IO.userError s!"{name}: concrete execution did not finish with done=true, busy=false")
  unless actual == some expected do throw (IO.userError s!"{name}: mismatch {actual} / {expected}, pc={result.pc}")
  let env := Circuit.SystemVerilog.environment circuit interface.core parsed.wires #[]
  for d in parsed.storage do
    unless (Circuit.SystemVerilog.declaredType parsed.storage d.name) == some (env.type d.name) do
      throw (IO.userError s!"{name}: declaration type mismatch at {d.name.text}")
  let verifyRead := fun (request : Circuit.SystemVerilog.ReadRequest) => do
    let answer := parsed.read.eval env request
    let reference := match sourceResult with
      | some final => Circuit.SystemVerilog.stateReadResult circuit outputs final.encode request
      | none => Circuit.SystemVerilog.readResult circuit outputs interface.core request
    unless answer == some reference do
      throw (IO.userError s!"{name}: read port mismatch at {repr request}: {repr answer} / {repr reference}")
  for id in (outputs ++ [4294967295] : List Nat) do
    for j in [:size+1] do
      verifyRead {id := BitVec.ofNat 32 id,address := BitVec.ofNat 32 j}
    verifyRead {id := BitVec.ofNat 32 id,address := 4294967295}
  for id in ((circuit.machine.nodes.toList.flatMap Circuit.Node.registers).eraseDups ++ [4294967295] : List Nat) do
    verifyRead {register := true,id := BitVec.ofNat 32 id}
  IO.println s!"{name}: {circuit.machine.nodes.size} states, {circuit.wires.size} holding registers, source/clock-model/parsed-SystemVerilog/finite-banks agree"
  (← IO.getStdout).flush
  let directory := System.FilePath.mk "artifacts/circuit" / name
  IO.FS.createDirAll directory
  unless rtl == module.text do throw (IO.userError s!"{name}: emitted text differs from verified module")
  IO.FS.writeFile (directory / "design.sv") rtl
  let mut tb := "module tb; reg clk=0; always #5 clk=~clk; reg rst=1,start=1,cfg_we=1,cfg_reg=0,read_reg=0; reg [31:0] x=0,y=0,cfg_id=0,cfg_addr=0,cfg_data=0,read_id=0,read_addr=0; wire [31:0] read_data; wire read_valid,busy,done,error; integer cycles; hls_top dut(.*); initial begin repeat(2) @(negedge clk); rst=0; start=0; cfg_we=0;\n"
  for (a,size) in circuit.originalMemories do
    for j in [:size] do
      let v := (initial.arrays a)[j]?.getD 0
      tb := tb ++ s!"@(negedge clk); cfg_we=1; cfg_id={a}; cfg_addr={j}; cfg_data=32'd{v.toNat}; @(negedge clk); cfg_we=0;\n"
  tb := tb ++ s!"x=32'd{x.toNat}; y=32'd{y.toNat};\n"
  tb := tb ++ "@(negedge clk); start=1; cfg_we=1; cfg_data=32'hdeadbeef; @(negedge clk); start=0; cfg_we=0; cycles=0; while(!done && cycles<10000) begin @(negedge clk); cycles=cycles+1; end if(!done) $fatal(1,\"timeout\");\n"
  tb := tb ++ s!"if(cycles != {cycles}) $fatal(1,\"cycle count mismatch: %d\",cycles);\n"
  match sourceResult with
  | none => tb := tb ++ "if(!error) $fatal(1,\"expected source error\");\n"
  | some final =>
    tb := tb ++ "if(error) $fatal(1,\"unexpected error\");\n"
    for a in outputs do
      for j in [:(final.arrays a).size] do
        tb := tb ++ s!"read_reg=0; read_id={a}; read_addr={j}; #1; if(!read_valid || read_data !== 32'd{((final.arrays a)[j]?.getD 0).toNat}) $fatal(1, \"array {a}[{j}] mismatch: %d\",read_data);\n"
    let regs := (circuit.machine.nodes.toList.flatMap Circuit.Node.registers).eraseDups
    for r in regs do
      tb := tb ++ s!"read_reg=1; read_id={r}; #1; if(!read_valid || read_data !== 32'd{(final.regs r).toNat}) $fatal(1,\"reg {r} mismatch\");\n"
  tb := tb ++ "$display(\"PASS cycles=%d\", cycles); $finish; end endmodule\n"
  IO.FS.writeFile (directory / "tb.sv") tb
  let finishedAt ← IO.monoMsNow
  let route := match HybridUnifiedPipeline.lower plan with | .compact _ => "compact" | .expanded _ => "expanded"
  let metrics := Lean.Json.mkObj [
    ("case",Lean.toJson name),("family",Lean.toJson ((fixture.map (·.family)).getD "regression")),
    ("variant",Lean.toJson ((fixture.map (·.variant)).getD "existing")),
    ("independent_oracle",Lean.toJson fixture.isSome),("size",Lean.toJson size),
    ("regression_reference",Lean.toJson "preindexed-children-precomputed-clock"),
    ("compute_cycles",Lean.toJson cycles),("states",Lean.toJson circuit.machine.nodes.size),
    ("holding_registers",Lean.toJson circuit.wires.size),("route",Lean.toJson route),
    ("fifo_banks",Lean.toJson circuit.machine.capacities.size),
    ("fifo_words",Lean.toJson (circuit.machine.capacities.foldl (fun n p => n+p.2) 0)),
    ("memory_banks",Lean.toJson circuit.memories.size),
    ("memory_words",Lean.toJson (circuit.memories.foldl (fun n p => n+p.2) 0)),
    ("rtl_bytes",Lean.toJson rtl.utf8ByteSize),
    ("generation_ms",Lean.toJson (generatedAt-startedAt)),
    ("lean_total_ms",Lean.toJson (finishedAt-startedAt)),
    ("phases",Lean.Json.mkObj (phases ++ [("regression_ms",Lean.toJson (finishedAt-generatedAt))]))]
  IO.FS.writeFile (directory / "metrics.json") (metrics.pretty ++ "\n")

def benchmarkKernels (f : BenchmarkFixture) : Except String (List Kernel) := do
  let supply := fun _ : Unit => (List.range f.size).map Int.ofNat
  let n := f.size
  match f.family with
  | "axpy" => return [HLSBenchmarks.axpyCode.kernel n 0 0 1 n supply]
  | "fir4" => return [HLSBenchmarks.firCode.kernel n 0 0 1 (n-3) supply]
  | "prefix" => return [HLSBenchmarks.prefixCode.kernel n 0 0 1 n supply]
  | "dot" => return [HLSBenchmarks.dotCode.kernel n 0 0 1 n supply]
  | "histogram" => return [HLSBenchmarks.histogramCode.kernel n 0 0 1 n supply]
  | "gather" => return [HLSBenchmarks.gatherCode.kernel n 0 0 1 n supply]
  | "gemm2" => return [HLSBenchmarks.gemmCode.kernel n 0 0 1 4 supply]
  | "stencil3" => return [HLSBenchmarks.stencilCode.kernel n 0 0 1 4 supply]
  | "replace-zero" => return [HLSBenchmarks.replaceZeroCode.kernel n 1 0 1 n supply]
  | "recurrence" => return [HLSBenchmarks.recurrenceCode.kernel n 0 0 1 n supply]
  | "fir-pipeline" => return [HLSBenchmarks.firCode.kernel n 0 0 1 (n-3) supply,
      HLSBenchmarks.replaceZeroCode.kernel n 1 0 1 (n-3) supply]
  | other => throw s!"unknown benchmark family {other}"

def checkBenchmarks : IO Unit := do
  let contents ← IO.FS.readFile "artifacts/benchmarks/fixtures.json"
  let fixtures ← IO.ofExcept (do
    let json ← Lean.Json.parse contents
    let cases ← (← json.getObjVal? "cases").getArr?
    cases.toList.mapM parseFixture)
  for f in fixtures do
    let kernels ← IO.ofExcept (benchmarkKernels f)
    check f.name (f.expected.map Prod.fst) kernels f.x f.y f.size 0 (some f)



def main : IO Unit := do
  check "producer-consumer" [2]
    [WordFrontendExamples.producer.kernel 4 0 0 1 4 (fun _ => [0,1,2,3]),
     WordFrontendExamples.consumer.kernel 4 1 0 1 3 (fun _ => [0,1,2,3])]
  let a := WordWorkloads.Global.producerA.kernel 4 0 0 1 3 (fun _ => [])
  let b := WordWorkloads.Global.producerB.kernel 4 0 0 1 3 (fun _ => [])
  let c := WordWorkloads.Global.consumerA.kernel 4 1 0 1 3 (fun _ => [0,1,2])
  let d := WordWorkloads.Global.consumerB.kernel 4 5 0 1 3 (fun _ => [0,1,2])
  let mark := WordWorkloads.Global.independent.kernel 4 0 0 1 1 (fun _ => [])
  let observe := WordWorkloads.Global.observing.kernel 4 0 0 1 1 (fun _ => [])
  check "interleaved" [2,6] [a,b,c,d]
  check "nonadjacent" [2,3] [a,mark,c]
  check "intervening-read" [2,3] [a,observe,c]
  check "public-output" [1,2,3] [a,mark,c]
  check "reverse-memory" [1] [WordFrontendExamples.generatedFilter.kernel 4 0 2 (-1) 3 (fun _ => [0,1,2,3])]
  check "arbitrary-initial-memory" [1]
    [WordFrontendExamples.generatedFilter.kernel 4 0 2 (-1) 3 (fun _ => [0,1,2,3])]
    (initialFill := 2779096485)

  check "dynamic-loop" [0] [WordFrontendExamples.loopCode.kernel 4 0 0 1 1 (fun _ => [])] 4294967295 3
  check "dynamic-zero" [0] [WordFrontendExamples.loopCode.kernel 4 0 0 1 1 (fun _ => [])] 7 0
  check "dynamic-failure" [0] [WordFrontendExamples.loopCode.kernel 4 0 0 1 1 (fun _ => [])] 7 5
  check "conditional-true" [0] [WordFrontendExamples.conditionalCode.kernel 4 0 0 1 1 (fun _ => [])] 9 1
  check "conditional-false" [0] [WordFrontendExamples.conditionalCode.kernel 4 0 0 1 1 (fun _ => [])] 9 0
  check "captured-old-value" [0,1] [WordFrontendExamples.capturedCode.kernel 4 0 0 1 1 (fun _ => [])]
  check "local-overflow" [0] [WordFrontendExamples.localCode.kernel 4 0 0 1 1 (fun _ => [])] 4294967295 3
  check "indirect-failure" [2] [WordFrontendExamples.indirectCode.kernel 4 0 0 1 1 (fun _ => [])]
  check "wrapped-index" [1] [WordFrontendExamples.producer.kernel 4 0 4294967296 1 2 (fun _ => [])]
  check "negative-index" [1] [WordFrontendExamples.producer.kernel 4 0 0 (-1) 2 (fun _ => [])]

  let ascending := fun _ => (List.range 64).map Int.ofNat
  let descending := fun _ => ((List.range 64).map Int.ofNat).reverse
  check "filter-three" [1] [WordWorkloads.Window.filterCode.kernel 64 0 0 1 3 ascending] 0 0 64
  check "dilated" [1] [WordWorkloads.Window.filterDilatedCode.kernel 64 0 0 1 3 ascending] 0 0 64
  check "dilated-reverse" [1] [WordWorkloads.Window.filterDilatedAltCode.kernel 64 0 0 1 3 descending] 0 0 64
  check "negative-step" [1] [WordWorkloads.Window.filterDilatedRevCode.kernel 64 0 2 (-1) 3 descending] 0 0 64
  check "negative-step-memory" [1] [WordWorkloads.Window.filterDilatedRevCode.kernel 64 0 2 (-1) 3 ascending] 0 0 64
  check "zero-count" [1] [WordFrontendExamples.producer.kernel 4 0 0 1 0 (fun _ => [])]

  checkBenchmarks
