import IRComparison.Circuit.Pipelining.StructuredEmit
import IRComparison.Circuit.SystemVerilog.GenerationTotal
import IRComparison.Circuit.AllocationLayout
import IRComparison.Circuit.Pipelining.InitialWidths
import IRComparison.Circuit.Pipelining.Construction

namespace IRComparison.Circuit.Pipelining
open SystemVerilog.Generation

/-- Local emission obligations for simultaneous actions. The scheduling and
width-invariant checks remain separate obligations of circuit generation. -/
def ClockNode.EmitReady (a : Artifact) : ClockNode → Prop
  | .batch actions _ => ∀ action ∈ actions, NodeReady a (action.node 0)
  | .branch e yes no => NodeReady a (.branch e yes no)
  | .jump next => NodeReady a (.jump next)
  | .halt => True

instance (a : Artifact) (n : ClockNode) : Decidable (n.EmitReady a) := by
  cases n <;> unfold ClockNode.EmitReady <;> infer_instance

theorem action_guard_emitReady (action : Action) (h : NodeReady a (action.node 0)) :
    TestReady a ((ready action).mapExpressions (RTL.combinational a.storageShape.wireRange)) := by
  cases action <;> simp_all [NodeReady,Action.node,Node.inStorage,ready,
    RTL.Test.mapExpressions,TestReady,combinational_ready]
  all_goals exact combinational_ready (.lit 0) trivial

theorem action_writes_emitReady (action : Action) (h : NodeReady a (action.node 0)) :
    StatementReady a ((writes action).mapExpressions (RTL.combinational a.storageShape.wireRange)) := by
  cases action <;> simp_all [NodeReady,Action.node,Node.inStorage,writes,
    RTL.Statement.mapExpressions,RTL.Scalar.mapExpressions,RTL.MemoryRhs.mapExpressions,
    RTL.QueueRhs.mapExpressions,StatementReady,AssignmentReady,ScalarReady,
    combinational_ready,wordBounds_combinational,show a.storageShape.wires = a.wires from rfl]

theorem allReady_emitReady (actions : List Action)
    (h : ∀ action ∈ actions, NodeReady a (action.node 0)) :
    TestReady a ((allReady actions).mapExpressions (RTL.combinational a.storageShape.wireRange)) := by
  induction actions with
  | nil => exact combinational_ready (.lit 0) trivial
  | cons action actions ih =>
    exact ⟨action_guard_emitReady action (h action (by simp)),ih (fun b hb => h b (by simp [hb]))⟩

theorem allWrites_emitReady (actions : List Action)
    (h : ∀ action ∈ actions, NodeReady a (action.node 0)) :
    StatementReady a ((allWrites actions).mapExpressions (RTL.combinational a.storageShape.wireRange)) := by
  induction actions with
  | nil => trivial
  | cons action actions ih =>
    exact ⟨action_writes_emitReady action (h action (by simp)),ih (fun b hb => h b (by simp [hb]))⟩

theorem ClockNode.statement_emitReady (n : ClockNode) (h : n.EmitReady a) :
    StatementReady a (n.statement.mapExpressions (RTL.combinational a.storageShape.wireRange)) := by
  cases n with
  | batch actions next =>
    exact ⟨allReady_emitReady actions h,⟨allWrites_emitReady actions h,by trivial⟩,by trivial⟩
  | branch e yes no => exact lowerNode_ready (.branch e yes no) h
  | jump next => exact lowerNode_ready (.jump next) h
  | halt => trivial

/-- Success of the actual simultaneous-case emitter, without an emission-success
premise and without testing concrete input values. -/
theorem generateGraph_succeeds (h : ∀ n ∈ g.nodes.toList, n.EmitReady a) :
    ∃ cases emission, generateGraph a g = .ok (cases,emission) := by
  have each : ∀ s ∈ graphCases a g, Total (statementCode a s) := by
    intro s hs
    simp only [graphCases,graphStatements,List.map_map,List.mem_map,Function.comp_def] at hs
    obtain ⟨n,hn,rfl⟩ := hs
    exact statementCode_total _ (n.statement_emitReady (h n hn))
  obtain ⟨cases,emission,generated,_⟩ := total_mapM (graphCases a g) (statementCode a) each {}
  exact ⟨cases,emission,generated⟩

/-- Once circuit validation has succeeded, structurally ready cases and declared
public outputs cannot introduce a later emission failure. This is NOT a proof
that interval inference or circuit validation always succeeds. -/
theorem generateGraphModule_succeeds (validated : checkGraph a g = .ok table)
    (h : ∀ n ∈ g.nodes.toList, n.EmitReady a)
    (ports : ∀ n ∈ outputs, a.storageShape.hasMemory n) :
    ∃ code, generateGraphModule a g outputs = .ok code := by
  obtain ⟨cases,emission,generated⟩ := generateGraph_succeeds h
  exact ⟨SystemVerilog.moduleCode a outputs cases emission.text,by
    simp [generateGraphModule,validated,generated,checkReadOutputs_total ports,
      bind,Except.bind,pure,Except.pure]⟩

theorem ClockNode.EmitReady.closed {n : ClockNode} (h : n.EmitReady a) : n.closed a.storageShape := by
  cases n with
  | batch actions next => exact fun action member => (h action member).1
  | branch | jump => exact h.1
  | halt => trivial

theorem Action.node_storage (action : Action) (h : (action.node 0).inStorage shape)
    (target : targetPC < shape.states) : (action.node targetPC).inStorage shape := by
  cases action <;> simp_all [Action.node,Node.inStorage]

theorem ClockNode.inventory_storage (n : ClockNode) (h : n.closed shape)
    (targets : n.targets shape.states) : ∀ node ∈ n.inventory, node.inStorage shape := by
  cases n with
  | batch actions next =>
    intro node member
    obtain ⟨action,actionMember,rfl⟩ := List.mem_map.mp member
    exact Action.node_storage action (h action actionMember) targets
  | branch | jump => simpa only [ClockNode.inventory,List.mem_singleton,forall_eq] using h
  | halt => simp [ClockNode.inventory,Node.inStorage]

theorem ClockNode.targets_mono (n : ClockNode) (h : n.targets small) (le : small ≤ large) : n.targets large := by
  cases n <;> simp_all [ClockNode.targets] <;> omega

theorem ClockGraph.inventory_size (g : ClockGraph) (wires memories originals) :
    g.nodes.size ≤ (g.artifact wires memories originals).storageShape.states := by
  simp [ClockGraph.artifact,Artifact.storageShape]

theorem ClockGraph.inventory_closed (g : ClockGraph) (wires memories originals)
    (h : ∀ n ∈ g.nodes.toList, n.closed (g.artifact wires memories originals).storageShape)
    (targets : ∀ n ∈ g.nodes.toList, n.targets g.nodes.size) :
    let a := g.artifact wires memories originals
    ∀ n ∈ a.machine.nodes.toList, n.inStorage a.storageShape := by
  dsimp only
  intro n member
  simp only [ClockGraph.artifact,List.toList_toArray,List.mem_append,List.mem_flatMap] at member
  rcases member with ⟨node,member,inside⟩ | member
  · exact node.inventory_storage (h node member)
      (node.targets_mono (targets node member) (g.inventory_size wires memories originals)) n inside
  · have eq := (List.mem_replicate.mp member).2
    subst n
    trivial

/-- Remaining conditions for graph validation, separating construction facts
from interval inference. Successful validation itself is not a premise. -/
theorem checkGraph_succeeds (module : ModuleReady a) (checks : GraphChecks a g table)
    (inferred : inferClockInvariant a g = .ok table) : checkGraph a g = .ok table := by
  have storage : checkStorage a = .ok ⟨module.entry,module.closed⟩ := by
    unfold checkStorage
    split
    · split
      · rfl
      · exact False.elim (‹¬ (∀ node ∈ a.machine.nodes.toList, node.inStorage a.storageShape)› module.closed)
    · exact False.elim (‹¬ a.machine.entry < a.storageShape.states› module.entry)
  have closed : g.nodes.toList.all (fun n => decide (n.closed a.storageShape)) = true :=
    List.all_eq_true.mpr (fun n hn => decide_eq_true (checks.closed n hn))
  have distinct : g.nodes.toList.all (fun n => decide n.distinct) = true :=
    List.all_eq_true.mpr (fun n hn => decide_eq_true (checks.distinct n hn))
  have targets : g.nodes.toList.all (fun n => decide (n.targets g.nodes.size)) = true :=
    List.all_eq_true.mpr (fun n hn => decide_eq_true (checks.targets n hn))
  simp [checkGraph,checkModuleArtifact_total module,storage,checks.capacity,checks.size,
    checks.entry,checks.initial,closed,distinct,targets,inferred,checks.invariant,bind,Except.bind,pure,Except.pure]

end IRComparison.Circuit.Pipelining
