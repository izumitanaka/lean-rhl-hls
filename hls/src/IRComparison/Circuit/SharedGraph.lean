import IRComparison.Circuit.SharedSafety
import IRComparison.Circuit.Pipelining.StructuredBounds
import IRComparison.Circuit.Pipelining.Rolled

namespace IRComparison.Circuit.Shared
open Pipelining SystemVerilog

/-- Declaration-only skeleton. Expression dependencies are inventoried directly
from graph nodes; no expanded expression is stored in the metadata artifact. -/
def expressionInventory (p : Program) : List Circuit.Node :=
  p.reads.filterMap fun c => match c with
    | .reg k => some (.assign k (.lit 0) 0)
    | _ => none

def inventory : ClockNode Program → List Circuit.Node
  | .batch as next => as.flatMap fun a =>
      (a.node next).mapExpressions (fun _ => .lit 0) ::
      (match a with
      | .wire _ e | .assign _ e | .send _ e => expressionInventory e
      | .store _ j e => expressionInventory j ++ expressionInventory e
      | _ => [])
  | .branch e yes no => .branch (.lit 0) yes no :: expressionInventory e
  | .jump next => [.jump next]
  | .halt => [.halt]

def artifact (g : ClockGraph Program) (wires : Array Interval)
    (memories publicMemories : Array (Nat × Nat)) : Artifact :=
  ⟨⟨1,(g.nodes.toList.flatMap inventory ++ List.replicate g.nodes.size Circuit.Node.halt).toArray,g.capacities⟩,
    wires,memories,publicMemories⟩

def graphStatements (g : ClockGraph Program) : List (RTL.Statement Program) :=
  g.nodes.toList.map ClockNode.statement

def graphCases (a : Artifact) (g : ClockGraph Program) : List (RTL.Statement Prepared) :=
  (graphStatements g).map (RTL.Statement.mapExpressions (prepare a.storageShape.wireRange))

def checkGraph (a : Artifact) (g : ClockGraph Program) : Except String InvariantTable := do
  checkModuleArtifact a
  let _ ← checkStorage a
  unless g.capacities == a.machine.capacities do throw "structured capacities differ"
  unless g.nodes.size ≤ a.storageShape.states do throw "structured PC does not fit"
  unless 1 < g.nodes.size do throw "structured entry is absent"
  unless initialWidthsSafe a.wires.toList do throw "structured input widths do not fit"
  unless g.nodes.toList.all (fun n => decide (n.closed a.storageShape)) do throw "structured reference outside storage"
  unless g.nodes.toList.all (fun n => decide n.distinct) do throw "structured simultaneous bank writes"
  unless g.nodes.toList.all (fun n => decide (n.targets g.nodes.size)) do throw "structured successor outside graph"
  let table ← inferClockInvariant a g
  unless validClockInvariant a g table do throw "structured interval invariant failed"
  return table

def generateGraphModule (a : Artifact) (g : ClockGraph Program) (outputs : List Nat) : Except String ModuleCode := do
  let _ ← checkGraph a g
  NetEmission.generateModule a outputs (graphCases a g)

theorem checkGraph_sound (h : checkGraph a g = .ok table) : GraphChecks a g table := by
  cases hm : checkModuleArtifact a <;> cases hs : checkStorage a <;>
    simp [checkGraph,hm,hs,bind,Except.bind,pure,Except.pure] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i capacity size entry initial closed distinct targets
  cases hi : inferClockInvariant a g <;> simp [hi,bind,Except.bind,pure,Except.pure] at h
  split at h <;> try contradiction
  rename_i valid
  cases h
  refine ⟨by simpa using capacity,size,entry,initial,valid,?_,?_,?_⟩
  all_goals
    intro n hn
    obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hn
    subst n
    first | exact closed i hi | exact distinct i hi | exact targets i hi

theorem generateGraphModule_components (h : generateGraphModule a g outputs = .ok code) :
    ∃ table, GraphChecks a g table ∧ NetEmission.generateModule a outputs (graphCases a g) = .ok code := by
  cases hc : checkGraph a g <;> simp [generateGraphModule,hc,bind,Except.bind] at h
  exact ⟨_,checkGraph_sound hc,h⟩

end IRComparison.Circuit.Shared
