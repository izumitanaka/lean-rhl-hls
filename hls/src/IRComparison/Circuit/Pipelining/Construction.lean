import IRComparison.Circuit.Pipelining.StructuredBounds
import IRComparison.Circuit.Pipelining.Rolled

/-! Structural facts produced by scheduling and assembly. These do not assume
that the resulting graph has passed the circuit validator. -/
namespace IRComparison.Circuit.Pipelining

def ClockTree.Safe : ClockTree → Prop
  | .block bs => ∀ actions ∈ bs, BundleSafe actions
  | .seq a b | .branch _ a b => a.Safe ∧ b.Safe
  | .loop _ body => body.Safe

theorem blockSchedule_safe (strategy : Array Action → Cycles) (actions : List Action) :
    (blockSchedule strategy actions).Safe := by
  intro batch member
  obtain ⟨ids,idsMember,rfl⟩ := List.mem_map.mp member
  exact of_decide_eq_true (List.all_eq_true.mp (compile_safe actions.toArray _) ids idsMember)

theorem scheduleStructure_safe (strategy : Array Action → Cycles) (s : Circuit.Schedule) :
    (scheduleStructure strategy s).Safe := by
  induction s with
  | skip | step => exact blockSchedule_safe _ _
  | seq a b ia ib =>
    simp only [scheduleStructure]
    split
    · exact blockSchedule_safe _ _
    · exact ⟨ia,ib⟩
  | branch e a b ia ib => exact ⟨ia,ib⟩
  | loop e body ih => exact ih

theorem overlapLoop_safe (e : Expr) (bs : Batches) (safe : (ClockTree.block bs).Safe) :
    (overlapLoop e bs).Safe := by
  unfold overlapLoop
  split
  · rename_i tail revPrefix hr
    split
    · rename_i head rest hp
      split
      · rename_i checks
        have shape : bs = (head::rest) ++ [tail] := by
          have hh := congrArg List.reverse hr
          simpa [hp] using hh
        have first : (ClockTree.block (head::rest)).Safe := by
          intro actions member
          exact safe actions (by rw [shape]; exact List.mem_append_left _ member)
        have last : (ClockTree.block [tail]).Safe := by
          intro actions member
          have eq := List.mem_singleton.mp member
          subst actions
          exact safe tail (by rw [shape]; simp)
        have steady : (ClockTree.block ((tail++head)::rest)).Safe := by
          intro actions member
          rcases List.mem_cons.mp member with rfl | member
          · exact checks.1
          · exact first actions (List.mem_cons_of_mem _ member)
        exact ⟨⟨first,steady,last⟩,by intro actions member; simp at member⟩
      · exact safe
    · exact safe
  · exact safe

theorem overlapLoops_safe (tree : ClockTree) (safe : tree.Safe) : (overlapLoops tree).Safe := by
  induction tree with
  | block => exact safe
  | seq a b ia ib | branch e a b ia ib => exact ⟨ia safe.1,ib safe.2⟩
  | loop e body ih =>
    cases body with
    | block bs => exact overlapLoop_safe e bs safe
    | seq | branch | loop => exact ih safe

theorem BundleSafe.banksDistinct (h : BundleSafe actions) : BanksDistinct actions := by
  apply h.imp
  intro a b compatible cell member other
  exact compatible.2 cell (List.mem_filter.mp member).1 (List.mem_filter.mp other).1

def ClockNode.Safe : ClockNode → Prop
  | .batch actions _ => BundleSafe actions
  | _ => True

theorem ClockNode.Safe.distinct {n : ClockNode} (h : n.Safe) : n.distinct := by
  cases n with
  | batch => exact h.banksDistinct
  | branch | jump | halt => trivial

variable {base next limit : Nat}

theorem blockLayout_safe (bs : Batches) (safe : ∀ actions ∈ bs, BundleSafe actions) :
    ∀ n ∈ clockBlockLayout base next bs, n.Safe := by
  induction bs generalizing base with
  | nil =>
    intro n member
    have eq : n = .jump next := by simpa [clockBlockLayout] using member
    subst n; trivial
  | cons actions rest ih =>
    intro n member
    rcases List.mem_cons.mp member with rfl | member
    · exact safe actions (by simp)
    · exact ih (fun b hb => safe b (by simp [hb])) n member

theorem ClockTree.layout_safe (tree : ClockTree) (safe : tree.Safe) :
    ∀ n ∈ tree.layout base next, n.Safe := by
  induction tree generalizing base next with
  | block bs => exact blockLayout_safe bs safe
  | seq a b ia ib =>
    intro n member
    rcases List.mem_append.mp member with member | member
    · exact ia safe.1 n member
    · exact ib safe.2 n member
  | branch e a b ia ib =>
    intro n member
    rcases List.mem_cons.mp member with rfl | member
    · trivial
    · rcases List.mem_append.mp member with member | member
      · exact ia safe.1 n member
      · exact ib safe.2 n member
  | loop e body ih =>
    intro n member
    rcases List.mem_cons.mp member with rfl | member
    · trivial
    · exact ih safe n member

theorem ClockTree.size_positive (tree : ClockTree) : 0 < tree.size := by
  induction tree <;> simp_all [ClockTree.size] <;> omega

theorem blockLayout_targets (bs : Batches) (space : base+bs.length+1 ≤ limit) (exit : next < limit) :
    ∀ n ∈ clockBlockLayout base next bs, n.targets limit := by
  induction bs generalizing base with
  | nil =>
    intro n member
    have eq : n = .jump next := by simpa [clockBlockLayout] using member
    subst n; exact exit
  | cons actions rest ih =>
    intro n member
    rcases List.mem_cons.mp member with rfl | member
    · change base+1 < limit; simp only [List.length_cons] at space; omega
    · exact ih (by simp only [List.length_cons] at space; omega) n member

theorem ClockTree.layout_targets (tree : ClockTree) (space : base+tree.size ≤ limit) (exit : next < limit) :
    ∀ n ∈ tree.layout base next, n.targets limit := by
  induction tree generalizing base next with
  | block bs => exact blockLayout_targets bs (by simpa [ClockTree.size,Nat.add_assoc] using space) exit
  | seq a b ia ib =>
    have positive := b.size_positive
    simp only [ClockTree.size] at space
    intro n member
    rcases List.mem_append.mp member with member | member
    · exact ia (by omega) (by omega) n member
    · exact ib (by omega) exit n member
  | branch e a b ia ib =>
    have posa := a.size_positive
    have posb := b.size_positive
    simp only [ClockTree.size] at space
    intro n member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨by omega,by omega⟩
    · rcases List.mem_append.mp member with member | member
      · exact ia (by omega) exit n member
      · exact ib (by omega) exit n member
  | loop e body ih =>
    have positive := body.size_positive
    simp only [ClockTree.size] at space
    intro n member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨by omega,exit⟩
    · exact ih (by omega) (by omega) n member

/-- Assembly never creates an absent successor, including back edges. -/
theorem ClockTree.assemble_targets (tree : ClockTree) (queues : Array (Nat × Nat)) :
    ∀ n ∈ (tree.assemble queues).nodes.toList, n.targets (tree.assemble queues).nodes.size := by
  intro n member
  simp only [ClockTree.assemble,List.toList_toArray,List.mem_cons] at member
  rcases member with rfl | member
  · trivial
  · apply tree.layout_targets (base := 1) (next := 0) _ _ n member
    · simp [ClockTree.assemble,tree.layout_length]; omega
    · simp [ClockTree.assemble]

/-- Scheduling safety survives assembly; interval transfer can use the same
ordered-clock fact as the semantic proof. -/
theorem ClockTree.assemble_safe (tree : ClockTree) (safe : tree.Safe) (queues : Array (Nat × Nat)) :
    ∀ n ∈ (tree.assemble queues).nodes.toList, n.Safe := by
  intro n member
  simp only [ClockTree.assemble,List.toList_toArray,List.mem_cons] at member
  rcases member with rfl | member
  · trivial
  · exact tree.layout_safe safe n member

/-- Every assembled clock inherits the scheduler's bank-write discipline. -/
theorem ClockTree.assemble_distinct (tree : ClockTree) (safe : tree.Safe) (queues : Array (Nat × Nat)) :
    ∀ n ∈ (tree.assemble queues).nodes.toList, n.distinct :=
  fun n member => (tree.assemble_safe safe queues n member).distinct

theorem ClockTree.assemble_entry (tree : ClockTree) (queues : Array (Nat × Nat)) :
    1 < (tree.assemble queues).nodes.size := by
  have positive := tree.size_positive
  simp [ClockTree.assemble,tree.layout_length]
  exact positive

end IRComparison.Circuit.Pipelining
