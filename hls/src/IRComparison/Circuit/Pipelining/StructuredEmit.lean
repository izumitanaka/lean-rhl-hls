import IRComparison.Circuit.Pipelining.StructuredBounds

namespace IRComparison.Circuit.Pipelining
open SystemVerilog

/-- A declaration inventory, not an executable replacement for the graph. -/
def ClockNode.inventory : ClockNode → List Node
  | .batch as next => as.map (fun a => a.node next)
  | .branch e yes no => [.branch e yes no]
  | .jump next => [.jump next]
  | .halt => [.halt]

def ClockGraph.artifact (g : ClockGraph) (wires : Array Interval)
    (memories publicMemories : Array (Nat × Nat)) : Artifact :=
  ⟨⟨1,(g.nodes.toList.flatMap ClockNode.inventory ++ List.replicate g.nodes.size Node.halt).toArray,g.capacities⟩,
    wires,memories,publicMemories⟩

def graphStatements (g : ClockGraph) : List RTL.Statement := g.nodes.toList.map ClockNode.statement

def graphCases (a : Artifact) (g : ClockGraph) :=
  (graphStatements g).map (RTL.Statement.mapExpressions (RTL.combinational a.storageShape.wireRange))

def generateGraph (a : Artifact) (g : ClockGraph) : Except String (List SystemVerilog.Statement × Emission) :=
  ((graphCases a g).mapM (statementCode a)).run {}

def checkGraph (a : Artifact) (g : ClockGraph) : Except String InvariantTable := do
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

def generateGraphModule (a : Artifact) (g : ClockGraph) (outputs : List Nat) : Except String ModuleCode := do
  let _ ← checkGraph a g
  let (cases,emission) ← generateGraph a g
  checkReadOutputs a outputs
  return moduleCode a outputs cases emission.text

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
    ∃ table, GraphChecks a g table ∧ ∃ codes emission, generateGraph a g = .ok (codes,emission) ∧
      code = moduleCode a outputs codes emission.text := by
  cases hc : checkGraph a g <;> simp [generateGraphModule,hc,bind,Except.bind] at h
  cases hg : generateGraph a g <;> simp [hg] at h
  cases hr : checkReadOutputs a outputs <;> simp [hr,pure,Except.pure] at h
  exact ⟨_,checkGraph_sound hc,_,_,rfl,h.symm⟩

theorem graphModule_text (h : generateGraphModule a g outputs = .ok code)
    (n : Nat) (r : RTL.InterfaceState a.storageShape) :
    (Concrete.parseModule code.text).bind (fun parsed => parsed.run a.storageShape n r) = code.run a.storageShape n r := by
  obtain ⟨_,_,codes,emission,_,rfl⟩ := generateGraphModule_components h
  exact printModule_run _ (moduleCode_storage _ _ _ _).positive rfl _ _ _

theorem ClockNode.references (n : ClockNode) (hc : n.closed shape) :
    StatementReferences shape (n.statement.mapExpressions (RTL.combinational wr)) := by
  cases n with
  | batch as next => exact lowerClock_references next as hc
  | branch e yes no => exact lowerNode_references wr (.branch e yes no) hc
  | jump next => exact lowerNode_references wr (.jump next) hc
  | halt => trivial

theorem ClockNode.ready (n : ClockNode) (hc : n.closed shape) :
    StatementReady shape old cap (n.statement.mapExpressions (RTL.combinational wr)) := by
  cases n with
  | batch as next => exact lowerClock_ready next as hc
  | branch e yes no => exact lowerNode_ready wr old cap (.branch e yes no) hc
  | jump next => exact lowerNode_ready wr old cap (.jump next) hc
  | halt => trivial

theorem ClockNode.frame (n : ClockNode) (hc : n.closed shape) (hd : n.distinct) :
    StatementFrame shape old cap (n.statement.mapExpressions (RTL.combinational wr)) old := by
  cases n with
  | batch as next => exact lowerClock_frame next as hc hd
  | branch e yes no => exact lowerNode_frame wr old cap (.branch e yes no) hc
  | jump next => exact lowerNode_frame wr old cap (.jump next) hc
  | halt => simp [ClockNode.statement,RTL.halt,RTL.Statement.mapExpressions,StatementFrame]

theorem graphStatements_references (hc : ∀ n ∈ g.nodes.toList, n.closed shape)
    (hm : body ∈ graphStatements g) :
    StatementReferences shape (body.mapExpressions (RTL.combinational wr)) := by
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hm
  exact n.references (hc n hn)

theorem graphStatements_ready (hc : ∀ n ∈ g.nodes.toList, n.closed shape)
    (hm : body ∈ graphStatements g) :
    StatementReady shape old cap (body.mapExpressions (RTL.combinational wr)) := by
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hm
  exact n.ready (hc n hn)

theorem graphStatements_frame (hc : ∀ n ∈ g.nodes.toList, n.closed shape)
    (hd : ∀ n ∈ g.nodes.toList, n.distinct) (hm : body ∈ graphStatements g) :
    StatementFrame shape old cap (body.mapExpressions (RTL.combinational wr)) old := by
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hm
  exact n.frame (hc n hn) (hd n hn)

end IRComparison.Circuit.Pipelining
