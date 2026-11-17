import IRComparison.Circuit.SystemVerilog.ReadPortSound

namespace IRComparison.Circuit.SystemVerilog

def declaredType (code : List Declaration) (name : Name) : Option IntegralType :=
  (code.find? (fun d => d.name == name)).map (fun d => ⟨d.width,d.signed⟩)

@[simp] theorem array_findSome_none (xs : Array α) : xs.findSome? (fun _ => (none : Option β)) = none := by
  simp

@[simp] theorem list_find_false (xs : List α) : xs.find? (fun _ => false) = none := by
  simp

theorem array_find_select (xs : Array α) (p : α → Bool) (f : α → β) :
    xs.findSome? (fun x => if p x then some (f x) else none) = (xs.find? p).map f := by
  rw [Array.find?_eq_findSome?_guard,Array.map_findSome?]
  congr 1
  funext x
  cases hp : p x <;> simp [hp,Option.guard]

theorem array_find_select_prop (xs : Array α) (p : α → Prop) [DecidablePred p] (f : α → β) :
    xs.findSome? (fun x => if p x then some (f x) else none) = (xs.find? (fun x => decide (p x))).map f := by
  simpa only [decide_eq_true_eq] using array_find_select xs (fun x => decide (p x)) f

/-- Every found storage declaration has exactly the width/signedness used
by the executable expression semantics. This compares lookup behavior and
therefore does not assume unique declarations or hide a new layout check. -/
theorem storageDeclarations_type (a : Artifact) (r : FiniteRuntime a.storageShape)
    (wires : Array Wire) (name : Name) (t : IntegralType)
    (found : declaredType (storageDeclarations a) name = some t) :
    t = (environment a r wires #[]).type name := by
  cases name <;>
    simp [declaredType,storageDeclarations,Declaration.name,Declaration.width,Declaration.signed,
      List.find?_append,List.find?_cons,Function.comp_def,Bool.beq_eq_decide_eq] at found
  all_goals try { subst t; rfl }
  case holding id =>
    obtain ⟨n,⟨rfl,inside,_⟩,rfl⟩ := found
    simp [environment,environmentFor,Artifact.storageShape,StorageShape.wireRange,Array.getElem?_eq_getElem inside]
  case register id =>
    obtain ⟨_,rfl⟩ := found
    rfl
  case memory id =>
    obtain ⟨entry,_,he⟩ := Array.exists_of_findSome?_eq_some found
    split at he <;> simp_all
    exact he.symm
  case queue id =>
    obtain ⟨entry,_,he⟩ := Array.exists_of_findSome?_eq_some found
    split at he <;> simp_all
    exact he.symm
  case length id =>
    have simplified : a.memories.findSome? (fun e => if e.1 = id then some (⟨bits e.2,false⟩ : IntegralType) else none) = some t := by
      apply Eq.trans ?_ found
      congr 1
      funext e
      by_cases eq : e.1 = id <;> simp [eq]
    clear found
    have found := simplified
    rw [array_find_select_prop a.memories (fun e => e.1 = id)] at found
    cases he : a.memories.find? (fun e => decide (e.1 = id)) with
    | none => simp [he] at found
    | some entry =>
      simp only [he,Option.map_some,Option.some.injEq] at found
      subst t
      simp [environment,environmentFor,Artifact.storageShape,Bool.beq_eq_decide_eq,he]
  case used id =>
    have simplified : a.machine.capacities.findSome? (fun e => if e.1 = id then some (⟨bits e.2,false⟩ : IntegralType) else none) = some t := by
      apply Eq.trans ?_ found
      congr 1
      funext e
      by_cases eq : e.1 = id <;> simp [eq]
    clear found
    have found := simplified
    rw [array_find_select_prop a.machine.capacities (fun e => e.1 = id)] at found
    cases he : a.machine.capacities.find? (fun e => decide (e.1 = id)) with
    | none => simp [he] at found
    | some entry =>
      simp only [he,Option.map_some,Option.some.injEq] at found
      subst t
      simp [environment,environmentFor,Artifact.storageShape,Machine.capacity,Bool.beq_eq_decide_eq,he]

/-- Logical capacity before SV's nonempty-range padding. -/
def declaredCapacity (code : List Declaration) (name : Name) : Option Nat := do
  let d ← code.find? (fun d => d.name == name)
  match d with
  | .bank _ _ capacity => some capacity
  | .scalar .. => none

theorem storageDeclarations_memory_capacity (a : Artifact) (id : Nat) :
    declaredCapacity (storageDeclarations a) (.memory id) =
      ((a.memories.toList.find? (fun p => p.1 == id)).map Prod.snd) := by
  simp [declaredCapacity,storageDeclarations,Declaration.name,List.find?_append,List.find?_cons,
    Function.comp_def,Bool.beq_eq_decide_eq]
  calc
    _ = ((a.memories.findSome? (fun e => if e.1 = id then
        some (Declaration.bank (Name.memory e.1) 32 e.2) else none)).bind
        (fun d => match d with | .bank _ _ capacity => some capacity | .scalar .. => none)) := by
      congr 2
      funext e
      by_cases h : e.1 = id <;> simp [h]
    _ = _ := by
      rw [array_find_select_prop a.memories (fun e => e.1 = id)]
      cases a.memories.find? (fun p => decide (p.1 = id)) <;> rfl

theorem storageDeclarations_queue_capacity (a : Artifact) (id : Nat) :
    declaredCapacity (storageDeclarations a) (.queue id) =
      ((a.machine.capacities.toList.find? (fun p => p.1 == id)).map Prod.snd) := by
  simp [declaredCapacity,storageDeclarations,Declaration.name,List.find?_append,List.find?_cons,
    Function.comp_def,Bool.beq_eq_decide_eq]
  calc
    _ = ((a.machine.capacities.findSome? (fun e => if e.1 = id then
        some (Declaration.bank (Name.queue e.1) 32 e.2) else none)).bind
        (fun d => match d with | .bank _ _ capacity => some capacity | .scalar .. => none)) := by
      congr 2
      funext e
      by_cases h : e.1 = id <;> simp [h]
    _ = _ := by
      rw [array_find_select_prop a.machine.capacities (fun e => e.1 = id)]
      cases a.machine.capacities.find? (fun p => decide (p.1 = id)) <;> rfl

theorem storageDeclarations_positive (a : Artifact) :
    ∀ d ∈ storageDeclarations a, 0 < d.width := by
  simp [storageDeclarations,Declaration.width,bits,signedWidth]
  intro d member
  rcases member with ⟨n,_,rfl⟩ | ⟨n,_,rfl⟩ | ⟨n,size,_,rfl|rfl⟩ | ⟨n,size,_,rfl|rfl⟩ <;> simp

end IRComparison.Circuit.SystemVerilog
