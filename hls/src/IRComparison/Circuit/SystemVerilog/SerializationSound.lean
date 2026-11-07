import IRComparison.Circuit.SystemVerilog.ConcreteModule
import IRComparison.Circuit.SystemVerilog.ModuleSound

namespace IRComparison.Circuit.SystemVerilog
open Concrete

theorem Expr.literalReadback_assignment (e : Expr) (env : Environment) (width : Nat) :
    e.literalReadback.assignment env width = e.assignment env width := by
  simp only [Expr.assignment,Expr.literalReadback_type,Expr.literalReadback_eval]

theorem Destination.literalReadback_write (d : Destination) (env : Environment) (e : Expr) (s : Store) :
    d.literalReadback.write env e.literalReadback s = d.write env e s := by
  cases d <;> simp only [Destination.literalReadback,Destination.write,
    Expr.literalReadback_eval,Expr.literalReadback_assignment]

theorem Statement.literalReadback_eval (s : Statement) (env : Environment) (pending : Store) :
    s.literalReadback.eval env pending = s.eval env pending := by
  induction s generalizing env pending with
  | skip => rfl
  | assign d e => exact d.literalReadback_write env e pending
  | seq a b ha hb => simp only [Statement.literalReadback,Statement.eval,ha,hb]
  | branch c a b ha hb =>
    simp only [Statement.literalReadback,Statement.eval,Expr.literalReadback_eval,ha,hb]
  | forRange n count body ih =>
    simp only [Statement.literalReadback,Statement.eval,ih]


namespace Concrete
theorem printStatement_eval (s : Statement) (env : Environment) (pending : Store) :
    (parseStatement (printStatement s)).bind (fun parsed => parsed.eval env pending) =
      s.eval env pending := by
  rw [parse_printStatement]
  exact s.literalReadback_eval env pending

end Concrete

theorem environmentFor_readback (shape : StorageShape) (r : FiniteRuntime shape)
    (wires : Array Wire) (values : Array Int) (busy : Bool) (ports : RTL.Ports) :
    environmentFor shape r (wires.map wireReadback) values busy ports =
      environmentFor shape r wires values busy ports := by
  unfold environmentFor
  congr 1
  funext n
  cases n <;> simp [Array.getElem?_map,wireReadback,Option.map_map,Function.comp_def]

theorem appendWires_readback (base : Environment) (wires : List Wire) (values : Array Int) :
    appendWires base (wires.map wireReadback) values = appendWires base wires values := by
  induction wires generalizing values with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons,appendWires,wireReadback,Expr.literalReadback_assignment,ih]

theorem selected_readback (cases : List Statement) (fallback : Statement) (pc : Nat) :
    ((cases.map Statement.literalReadback)[pc]?).getD fallback.literalReadback =
      ((cases[pc]?).getD fallback).literalReadback := by
  simp only [List.getElem?_map]
  cases cases[pc]? <;> rfl

/-- Serialization preserves every clock action, including reset/config/start.
This is separate from the source-level theorem's prepared-start contract. -/
theorem moduleReadback_tick (code : ModuleCode) (shape : StorageShape)
    (ports : RTL.Ports) (r : RTL.InterfaceState shape) :
    (moduleReadback code).tick shape ports r = code.tick shape ports r := by
  unfold ModuleCode.tick
  simp only [moduleReadback,environmentFor_readback,Array.toList_map,appendWires_readback,selected_readback]
  cases h : code.controller.select ports r.busy <;>
    simp only [h,bind,Option.bind,Statement.literalReadback_eval]

theorem moduleReadback_run (code : ModuleCode) (shape : StorageShape)
    (cycles : Nat) (r : RTL.InterfaceState shape) :
    (moduleReadback code).run shape cycles r = code.run shape cycles r := by
  induction cycles generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [ModuleCode.run,ModuleCode.run,moduleReadback_tick]
    cases code.tick shape {} r with
    | none => rfl
    | some next => exact ih next

theorem moduleReadback_read (code : ModuleCode) (shape : StorageShape)
    (r : FiniteRuntime shape) (request : ReadRequest) :
    (moduleReadback code).read.eval (environmentFor shape r (moduleReadback code).wires #[]) request =
      code.read.eval (environmentFor shape r code.wires #[]) request := by
  simp only [moduleReadback,environmentFor_readback]

/-- Meaning preservation starts from the printed String. The independent
parser supplies every field of the module executed on the left-hand side. -/
theorem printModule_run (code : ModuleCode)
    (positive : ∀ d ∈ code.storage, 0 < d.width)
    (standard : code.controller = RTL.controller)
    (shape : StorageShape) (cycles : Nat) (r : RTL.InterfaceState shape) :
    (parseModule (printModule code)).bind (fun parsed => parsed.run shape cycles r) =
      code.run shape cycles r := by
  rw [parse_printModule code positive standard]
  exact moduleReadback_run code shape cycles r

@[simp] theorem physicalDeclaration_name (d : Declaration) :
    (physicalDeclaration d).name = d.name := by cases d <;> rfl
@[simp] theorem physicalDeclaration_width (d : Declaration) :
    (physicalDeclaration d).width = d.width := by cases d <;> rfl
@[simp] theorem physicalDeclaration_signed (d : Declaration) :
    (physicalDeclaration d).signed = d.signed := by cases d <;> rfl

theorem declaredType_readback (ds : List Declaration) (n : Name) :
    declaredType (ds.map physicalDeclaration) n = declaredType ds n := by
  simp only [declaredType,List.find?_map,Option.map_map,Function.comp_def,
    physicalDeclaration_name,physicalDeclaration_width,physicalDeclaration_signed]

theorem declaredCapacity_readback (ds : List Declaration) (n : Name) :
    declaredCapacity (ds.map physicalDeclaration) n = (declaredCapacity ds n).map (max 1) := by
  simp only [declaredCapacity,List.find?_map,Function.comp_def,physicalDeclaration_name]
  cases found : ds.find? (fun d => d.name == n) with
  | none => rfl
  | some d => cases d <;> rfl

theorem generated_standard (generated : generateModule a outputs = .ok code) :
    code.controller = RTL.controller := by
  obtain ⟨cases,emission,_,same⟩ := generateModule_components generated
  rw [same]
  rfl

def runText (text : String) (shape : StorageShape) (cycles : Nat) (r : RTL.InterfaceState shape) :
    Option (RTL.InterfaceState shape) :=
  (parseModule text).bind (fun parsed => parsed.run shape cycles r)

def readText (text : String) (shape : StorageShape) (r : FiniteRuntime shape) (request : ReadRequest) :
    Option ReadReply := do
  let parsed ← parseModule text
  parsed.read.eval (environmentFor shape r parsed.wires #[]) request

/-- Whole production-printer theorem, including declaration widths and
physical array extents. No parser success is assumed by the theorem. -/
theorem emit_text_correct (success : emit a outputs = .ok text) :
    ∃ code parsed,
      generateModule a outputs = .ok code ∧ code.StorageMatches a.storageShape ∧
      parseModule text = some parsed ∧
      (∀ n, declaredType parsed.storage n = declaredType code.storage n) ∧
      (∀ n, declaredCapacity parsed.storage n = (declaredCapacity code.storage n).map (max 1)) ∧
      (∀ ports state, parsed.tick a.storageShape ports state = code.tick a.storageShape ports state) ∧
      (∀ state request, parsed.read.eval (environmentFor a.storageShape state parsed.wires #[]) request =
        code.read.eval (environmentFor a.storageShape state code.wires #[]) request) := by
  obtain ⟨code,generated,printed⟩ := emit_module success
  obtain ⟨cases,emission,_,same⟩ := generateModule_components generated
  have matched : code.StorageMatches a.storageShape := by rw [same]; exact moduleCode_storage _ _ _ _
  refine ⟨code,moduleReadback code,generated,matched,?_,?_,?_,?_,?_⟩
  · rw [← printed]
    exact parse_printModule code matched.positive (generated_standard generated)
  · exact declaredType_readback code.storage
  · exact declaredCapacity_readback code.storage
  · exact fun ports state => moduleReadback_tick code _ ports state
  · exact fun state request => moduleReadback_read code _ state request

/-- Source-to-String execution and observation theorem. The start boundary,
source preconditions and failure behavior are exactly those of the existing
pipeline theorem. Execution here starts by parsing the emitted characters. -/
theorem emitted_text_pipeline_readout (p : HybridWord.Plan outputs sizes ks)
    (compiled : compile layout (HybridUnifiedPipeline.lower p) = .ok checked)
    (emitted : emit checked.artifact outputs = .ok text)
    (outputsSafe : ∀ id ∈ outputs, id < layoutLimit layout)
    (outputPorts : ∀ id ∈ outputs, checked.artifact.storageShape.hasMemory id)
    (prepared : FiniteRuntime checked.artifact.storageShape) (x y : BitVec 32)
    (sized : PipelineShapes.Layout sizes (RTL.restoreLengths checked.artifact prepared).inputSource.encode)
    (ready : p.Ready (HybridWord.encode x) (HybridWord.encode y)
      (RTL.restoreLengths checked.artifact prepared).inputSource.encode) :
    let a := checked.artifact
    let s := (RTL.restoreLengths a prepared).inputSource
    ∃ cycles result,
      runText text a.storageShape cycles ⟨RTL.beginInvocation a prepared x y,true⟩ = some result ∧
      result.core.done = true ∧ result.busy = false ∧
      (∀ final, HybridWord.source x y ks s = some final →
        result.core.error = false ∧ ∀ request,
          readText text a.storageShape result.core request = some (stateReadResult a outputs final.encode request)) ∧
      (HybridWord.source x y ks s = none → result.core.error = true) := by
  obtain ⟨code,cycles,result,generated,printed,matched,executed,finished,idle,observed,failed⟩ :=
    emitted_pipeline_readout p compiled emitted outputsSafe outputPorts prepared x y sized ready
  have parsed : parseModule text = some (moduleReadback code) := by
    rw [← printed]
    exact parse_printModule code matched.positive (generated_standard generated)
  refine ⟨cycles,result,?_,finished,idle,?_,failed⟩
  · simpa only [runText,parsed,Option.bind_some,moduleReadback_run] using executed
  · intro final source
    obtain ⟨noError,reads⟩ := observed final source
    refine ⟨noError,fun request => ?_⟩
    simpa only [readText,parsed,bind,Option.bind,moduleReadback_read] using reads request

end IRComparison.Circuit.SystemVerilog
