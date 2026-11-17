import IRComparison.Circuit.PipelineReferenceScope
import IRComparison.Circuit.PipelineWordRanges
import IRComparison.Circuit.ScheduleRanges
import IRComparison.Circuit.SystemVerilog.ReadPortSound

namespace IRComparison.Circuit.ReferenceScope
open SystemVerilog.Generation

variable {b : Build} {a : Artifact}

structure Inventory (b : Build) (a : Artifact) : Prop where
  wires : a.wires = b.wires
  memories : a.memories = b.memories
  queues : a.machine.capacities = b.queues
  unique : (a.memories.toList.map Prod.fst).Nodup

theorem Inventory.memory (h : Inventory b a) (declared : Memory b n) : a.storageShape.hasMemory n := by
  obtain ⟨size,member⟩ := declared
  apply Allocation.declared_live
  simpa only [h.memories] using member

theorem Inventory.queue (h : Inventory b a) (declared : Queue b q) :
    q < a.storageShape.queues ∧ QueueDeclared a q := by
  obtain ⟨size,member⟩ := declared
  have hm : (q,size) ∈ a.machine.capacities.toList := by simpa only [h.queues] using member
  refine ⟨Allocation.declared_bound hm,?_⟩
  rw [QueueDeclared,List.isSome_find?,List.any_eq_true]
  exact ⟨(q,size),hm,by simp⟩

theorem Inventory.copy (h : Inventory b a) (declared : Copy b dst src) :
    a.storageShape.hasMemory dst ∧ a.storageShape.hasMemory src ∧
      a.storageShape.memorySize dst = a.storageShape.memorySize src := by
  obtain ⟨size,hd,hs⟩ := declared
  refine ⟨h.memory ⟨size,hd⟩,h.memory ⟨size,hs⟩,?_⟩
  have hd' : (dst,size) ∈ a.memories.toList := by simpa only [h.memories] using hd
  have hs' : (src,size) ∈ a.memories.toList := by simpa only [h.memories] using hs
  change ((a.memories.toList.find? (fun p => p.1 == dst)).map Prod.snd).getD 0 =
    ((a.memories.toList.find? (fun p => p.1 == src)).map Prod.snd).getD 0
  rw [Allocation.find_declared h.unique hd',Allocation.find_declared h.unique hs']
  rfl

theorem Expression.storage (h : Expression b e) (inventory : Inventory b a)
    (registers : ∀ r ∈ e.registers, r < a.storageShape.registers) : e.inStorage a.storageShape := by
  induction e with
  | fail | lit => trivial
  | wire => simpa only [Expr.inStorage,Artifact.storageShape,inventory.wires] using h
  | reg r => exact registers r (by simp [Expr.registers])
  | memory m j ih => exact ⟨inventory.memory h.1,ih h.2 registers⟩
  | natIndex _ ih | wrap32 _ ih => exact ih h registers
  | bin _ _ _ ia ib | seq _ _ ia ib =>
    exact ⟨ia h.1 (fun r hr => registers r (List.mem_append_left _ hr)),
      ib h.2 (fun r hr => registers r (List.mem_append_right _ hr))⟩
  | select c x y ic ix iy =>
    exact ⟨ic h.1 (fun r hr => registers r (by simp [Expr.registers,hr])),
      ix h.2.1 (fun r hr => registers r (by simp [Expr.registers,hr])),
      iy h.2.2 (fun r hr => registers r (by simp [Expr.registers,hr]))⟩

theorem Expression.rangeScoped (h : Expression b e) : RangeScoped b.wires.size e := by
  induction e with
  | fail => exact .fail
  | lit => exact .lit
  | wire => exact .wire h
  | reg => exact .reg
  | memory => exact .memory
  | natIndex _ ih => exact (ih h).natIndex
  | wrap32 _ _ => exact .wrap32
  | bin _ _ _ ia ib => exact .bin (ia h.1) (ib h.2)
  | seq _ _ ia ib => exact .seq (ib h.2)
  | select _ _ _ ic ia ib => exact .select (ia h.2.1) (ib h.2.2)

theorem Inventory.word (h : Inventory b a) (scope : Expression b e)
    (word : WordRanges.Word (CommandWordRanges.wires b) e) :
    isWord (range a.storageShape.wireRange e) = true := by
  have same := scope.rangeScoped.frame_range
  change isWord (range (CommandWordRanges.wires b) e) = true at word
  rw [same] at word
  change isWord (range (fun n => b.wires.toList[n]?.getD zeroRange) e) = true at word
  change isWord (range (fun n => a.wires[n]?.getD zeroRange) e) = true
  simpa only [h.wires,Frame.get,Array.getElem?_toList] using word

theorem Operation.ready {next : Nat} (refs : Operation b action) (words : CommandWordRanges.ActionWords b action)
    (inventory : Inventory b a) (exit : next < a.machine.nodes.size)
    (registers : ∀ r ∈ (action.node next).registers, r < a.storageShape.registers) :
    NodeReady a (action.node next) := by
  cases action with
  | wire k e => exact ⟨⟨by simpa [Artifact.storageShape,inventory.wires] using refs.1,refs.2.storage inventory registers,exit⟩,trivial⟩
  | assign k e =>
    exact ⟨⟨registers k (by simp [Action.node,Node.registers]),
      refs.storage inventory (fun r hr => registers r (List.mem_cons_of_mem _ hr)),exit⟩,inventory.word refs words⟩
  | store m j e =>
    exact ⟨⟨inventory.memory refs.1,
      refs.2.1.storage inventory (fun r hr => registers r (List.mem_append_left _ hr)),
      refs.2.2.storage inventory (fun r hr => registers r (List.mem_append_right _ hr)),exit⟩,
      inventory.word refs.2.2 words⟩
  | send q e =>
    have queue := inventory.queue refs.1
    exact ⟨⟨queue.1,refs.2.storage inventory registers,exit⟩,queue.2,inventory.word refs.2 words⟩
  | receive q k =>
    have queue := inventory.queue refs.1
    exact ⟨⟨queue.1,by simpa [Artifact.storageShape,inventory.wires] using refs.2,exit⟩,queue.2⟩
  | clear q =>
    have queue := inventory.queue refs
    exact ⟨⟨queue.1,exit⟩,queue.2⟩
  | erase m => exact ⟨⟨inventory.memory refs,exit⟩,trivial⟩
  | snapshot dst src =>
    have copy := inventory.copy refs
    exact ⟨⟨copy.1,copy.2.1,Nat.le_of_eq copy.2.2.symm,exit⟩,copy.2.2⟩

/-- Every operation in the laid-out controller is emit-ready. Jump targets
come from structural layout; register declarations come from the node scan. -/
theorem Control.layout_ready {code : Schedule} {base next : Nat}
    (refs : Control b code) (words : CommandWordRanges.DataWords b code)
    (inventory : Inventory b a) (space : base + code.size ≤ a.machine.nodes.size)
    (exit : next < a.machine.nodes.size)
    (registers : ∀ n ∈ code.layout base next, ∀ r ∈ n.registers, r < a.storageShape.registers) :
    ∀ n ∈ code.layout base next, NodeReady a n := by
  induction code generalizing base next with
  | skip =>
    intro n member
    simp only [Schedule.layout,List.mem_singleton] at member
    subst n
    exact ⟨exit,trivial⟩
  | step action =>
    intro n member
    simp only [Schedule.layout,List.mem_singleton] at member
    subst n
    exact refs.ready words inventory exit (registers _ (by simp [Schedule.layout]))
  | seq left right il ir =>
    have positive := right.size_pos
    have leftSpace : base + left.size ≤ a.machine.nodes.size := by
      simp only [Schedule.size] at space; omega
    have middle : base + left.size < a.machine.nodes.size := by
      simp only [Schedule.size] at space; omega
    have first := il refs.1 words.1 leftSpace middle
      (fun n hn => registers n (List.mem_append_left _ hn))
    have second := ir refs.2 words.2 (by simpa only [Schedule.size,Nat.add_assoc] using space) exit
      (fun n hn => registers n (List.mem_append_right _ hn))
    intro n member
    exact (List.mem_append.mp member).elim (first n) (second n)
  | branch condition left right il ir =>
    have lp := left.size_pos
    have rp := right.size_pos
    have bounds : base+1 < a.machine.nodes.size ∧ base+1+left.size < a.machine.nodes.size := by
      simp only [Schedule.size] at space; omega
    have guard : NodeReady a (.branch condition (base+1) (base+1+left.size)) :=
      ⟨⟨refs.1.storage inventory (registers (.branch condition (base+1) (base+1+left.size)) (by simp [Schedule.layout])),bounds⟩,trivial⟩
    have first := il (base:=base+1) refs.2.1 words.1 (by simp only [Schedule.size] at space; omega) exit
      (fun n hn => registers n (by simp only [Schedule.layout,List.mem_cons,List.mem_append]; exact Or.inr (Or.inl hn)))
    have second := ir (base:=base+1+left.size) refs.2.2 words.2 (by simp only [Schedule.size] at space; omega) exit
      (fun n hn => registers n (by simp only [Schedule.layout,List.mem_cons,List.mem_append]; exact Or.inr (Or.inr hn)))
    intro n member
    rcases List.mem_cons.mp member with rfl | member
    · exact guard
    · exact (List.mem_append.mp member).elim (first n) (second n)
  | loop condition body ih =>
    have positive := body.size_pos
    have bodyStart : base+1 < a.machine.nodes.size := by simp only [Schedule.size] at space; omega
    have guard : NodeReady a (.branch condition (base+1) next) :=
      ⟨⟨refs.1.storage inventory (registers (.branch condition (base+1) next) (by simp [Schedule.layout])),bodyStart,exit⟩,trivial⟩
    have child := ih (base:=base+1) (next:=base) refs.2 words (by simp only [Schedule.size] at space; omega) (by omega)
      (fun n hn => registers n (List.mem_cons_of_mem _ hn))
    intro n member
    rcases List.mem_cons.mp member with rfl | member
    · exact guard
    · exact child n member

/-- Assembly adds a halt node; all declarations and branch destinations are
therefore sufficient for the actual whole-module emitter. -/
theorem Control.assemble_ready {code : Schedule}
    (refs : Control b code) (words : CommandWordRanges.DataWords b code)
    (inventory : Inventory b a) (assembled : a.machine = code.assemble b.queues) :
    ∀ n ∈ a.machine.nodes.toList, NodeReady a n := by
  have size : a.machine.nodes.size = 1 + code.size := by
    simp [assembled,Schedule.assemble,Schedule.layout_length,Nat.add_comm]
  have nodes : a.machine.nodes.toList = Node.halt :: code.layout 1 0 := by
    simp [assembled,Schedule.assemble]
  have ready := refs.layout_ready words inventory (base:=1) (next:=0) (by omega) (by omega)
    (fun n hn r hr => SystemVerilog.declared_register_bound a r
      (List.mem_flatMap.mpr ⟨n,by rw [nodes]; exact List.mem_cons_of_mem _ hn,hr⟩))
  intro n member
  rw [nodes] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨trivial,trivial⟩
  · exact ready n member

end IRComparison.Circuit.ReferenceScope

