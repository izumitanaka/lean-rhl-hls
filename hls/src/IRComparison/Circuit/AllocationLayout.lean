import IRComparison.Circuit.Allocation
import IRComparison.Circuit.SystemVerilog.GenerationTotal

namespace IRComparison.Circuit.Allocation

/-- Looking up a declared identifier returns its own capacity. -/
theorem find_declared {entries : List (Nat × Nat)}
    (unique : (entries.map Prod.fst).Nodup) (member : p ∈ entries) :
    entries.find? (fun q => q.1 == p.1) = some p := by
  induction entries with
  | nil => simp at member
  | cons e es ih =>
    simp only [List.map_cons,List.nodup_cons] at unique
    rcases List.mem_cons.mp member with rfl | member
    · simp
    · have different : e.1 ≠ p.1 := by
        intro eq
        exact unique.1 (eq ▸ List.mem_map.mpr ⟨p,member,rfl⟩)
      have neq : (e.1 == p.1) = false := beq_eq_false_iff_ne.mpr different
      simp only [List.find?,neq,ih unique.2 member]

theorem eraseDups_of_nodup {ids : List Nat} (unique : ids.Nodup) : ids.eraseDups = ids := by
  induction ids with
  | nil => rfl
  | cons a ids ih =>
    have h := List.nodup_cons.mp unique
    have filtered : ids.filter (fun b => !b == a) = ids := by
      apply List.filter_eq_self.mpr
      intro b hb
      have ne : b ≠ a := by intro eq; subst b; exact h.1 hb
      simp [ne]
    rw [List.eraseDups_cons,filtered,ih h.2]

theorem unique_length {entries : Array (Nat × Nat)}
    (unique : (entries.toList.map Prod.fst).Nodup) :
    (entries.toList.map Prod.fst).eraseDups.length = entries.size := by
  rw [eraseDups_of_nodup unique]
  simp

theorem declared_bound {entries : Array (Nat × Nat)} (member : p ∈ entries.toList) :
    p.1 < idBound (entries.toList.map Prod.fst) := by
  have h := layout_member_bound member
  simpa only [idBound,layoutLimit,List.foldl_map,Array.foldl_toList] using h

theorem declared_live {a : Artifact} (member : (n,size) ∈ a.memories.toList) :
    a.storageShape.hasMemory n := by
  refine ⟨declared_bound member,?_⟩
  change a.memories.any (fun p => p.1 == n) = true
  rw [← Array.any_toList,List.any_eq_true]
  exact ⟨(n,size),member,by simp⟩

/-- The interface check follows from preservation of the declaration table;
no circuit execution or successful validation is assumed. -/
theorem interface_of_extension (a : Artifact)
    (unique : (a.memories.toList.map Prod.fst).Nodup)
    (originalUnique : (a.originalMemories.toList.map Prod.fst).Nodup)
    (kept : a.originalMemories.toList.IsPrefix a.memories.toList) :
    SystemVerilog.InterfaceLayout a := by
  constructor
  · intro p hp
    have member := kept.subset hp
    refine ⟨?_,declared_bound member,?_⟩
    · rw [find_declared originalUnique hp]; rfl
    · rw [find_declared unique member]; simp
  · intro p hp
    refine ⟨declared_bound hp,?_⟩
    rw [find_declared unique hp]; rfl

/-- Properties of declarations that the emitter requires. The actual generated
control graph and its width invariant remain separate obligations. -/
structure MetadataReady (a : Artifact) : Prop where
  interface : SystemVerilog.InterfaceLayout a
  memories : (a.memories.toList.map Prod.fst).eraseDups.length = a.memories.size
  queues : (a.machine.capacities.toList.map Prod.fst).eraseDups.length = a.machine.capacities.size
  publicMemories : ∀ p ∈ a.originalMemories.toList, a.storageShape.hasMemory p.1

theorem scheduled_metadata (backend : CountedBackend) (layout : Array (Nat × Nat))
    (unique : (layout.toList.map Prod.fst).Nodup) (code : HybridUnifiedPipeline.Code)
    (machine : Machine)
    (capacities : machine.capacities = (scheduleWith backend.build layout code).build.queues) :
    MetadataReady ⟨machine,(scheduleWith backend.build layout code).build.wires,
      (scheduleWith backend.build layout code).build.memories,layout⟩ := by
  obtain ⟨valid,kept⟩ := schedule_allocated backend layout unique code
  refine ⟨interface_of_extension _ valid.memories.unique unique kept.memories,
    unique_length valid.memories.unique,?_,?_⟩
  · simpa only [capacities] using unique_length valid.queues.unique
  · intro p hp
    exact declared_live (kept.memories.subset hp)

theorem MetadataReady.ports (h : MetadataReady a) {outputs : List Nat}
    (outputsDeclared : ∀ n ∈ outputs, ∃ size, (n,size) ∈ a.originalMemories.toList) :
    ∀ n ∈ outputs, a.storageShape.hasMemory n := by
  intro n hn
  obtain ⟨size,member⟩ := outputsDeclared n hn
  exact h.publicMemories (n,size) member

/-- Supply the metadata part of the previous emitter-success theorem. -/
theorem MetadataReady.moduleReady (h : MetadataReady a)
    (entry : a.machine.entry < a.machine.nodes.size)
    (closed : ∀ n ∈ a.machine.nodes.toList, n.inStorage a.storageShape) :
    SystemVerilog.Generation.ModuleReady a :=
  ⟨h.interface,entry,h.memories,h.queues,closed⟩

end IRComparison.Circuit.Allocation
