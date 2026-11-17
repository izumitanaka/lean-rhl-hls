import IRComparison.Circuit.SharedEmitSound

namespace IRComparison.Circuit.Shared.NetEmission
open SystemVerilog

/-- External reference bounds only. Local .wire references are resolved by
emission through the shared graph; they are not holding-register IDs. -/
def ExternalRefs (localNames : Bool) (shape : StorageShape) (e : RTL.Term) : Prop :=
  (match e with
    | .wire n => localNames = true ∨ n < shape.wires.size
    | .register n => n < shape.registers
    | .length n | .cell n _ => n < shape.memories
    | _ => True) ∧ ∀ child ∈ e.children, ExternalRefs localNames shape child
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ ‹_›

def selectedRuntime (r : Runtime) (refs : Option (Array Signal)) (signals : Array Int) : Runtime :=
  match refs with
  | none => r
  | some _ => LocalRTL.fullRuntime r signals

@[simp] theorem selectedRuntime_data (r : Runtime) (refs : Option (Array Signal)) (signals : Array Int) :
    (selectedRuntime r refs signals).data = r.data := by cases refs <;> rfl

theorem physical_from_refs (a : Artifact) (r : FiniteRuntime a.storageShape)
    (decls : Wires) (values : Array Int) (refs : Option (Array Signal)) (signals : Array Int) (e : RTL.Term)
    (closed : ExternalRefs refs.isSome a.storageShape e) :
    Physical a (selectedRuntime r.decode refs signals)
      ((environment a r decls #[]).withTemporaries values) refs e := by
  rw [Physical.eq_def,ExternalRefs.eq_def] at *
  refine ⟨?_,fun child member => physical_from_refs a r decls values refs signals child (closed.2 child member)⟩
  intro unresolved
  cases e with
  | wire n =>
    cases refs with
    | some rs => simp [resolved] at unresolved
    | none =>
      have hn : n < a.storageShape.wires.size := by simpa using closed.1
      exact physicalNode_finite a r decls values (.wire n) (by simp [ReferencesIn,RTL.Term.children,hn])
  | register n =>
    have h := physicalNode_finite a r decls values (.register n) (by simp [ReferencesIn,RTL.Term.children,closed.1])
    simpa [PhysicalNode] using h
  | length n =>
    have h := physicalNode_finite a r decls values (.length n) (by simp [ReferencesIn,RTL.Term.children,closed.1])
    simpa [PhysicalNode] using h
  | cell n j =>
    have h := physicalNode_finite a r decls values (.cell n (.literal 0)) (by simp [ReferencesIn,RTL.Term.children,closed.1])
    simpa [PhysicalNode] using h
  | literal | binary | wrap32 | nonnegative | resize | mux => trivial
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ member

def ValidityRefs (localNames : Bool) (shape : StorageShape) : RTL.Validity → Prop
  | .yes | .no => True
  | .and u v => ValidityRefs localNames shape u ∧ ValidityRefs localNames shape v
  | .address n j => ExternalRefs localNames shape j ∧ n < shape.memories
  | .mux c u v => ExternalRefs localNames shape c ∧ ValidityRefs localNames shape u ∧ ValidityRefs localNames shape v

theorem validityPhysical_from_refs (a : Artifact) (r : FiniteRuntime a.storageShape)
    (decls : Wires) (values : Array Int) (refs : Option (Array Signal)) (signals : Array Int) (v : RTL.Validity)
    (closed : ValidityRefs refs.isSome a.storageShape v) :
    PhysicalValidity a (selectedRuntime r.decode refs signals)
      ((environment a r decls #[]).withTemporaries values) refs v := by
  induction v with
  | yes | no => trivial
  | and u v ihu ihv => exact ⟨ihu closed.1,ihv closed.2⟩
  | address n j =>
    refine ⟨physical_from_refs a r decls values refs signals j closed.1,?_⟩
    have h := physicalNode_finite a r decls values (.length n) (by simp [ReferencesIn,RTL.Term.children,closed.2])
    simpa [PhysicalNode] using h
  | mux c u v ihu ihv => exact ⟨physical_from_refs a r decls values refs signals c closed.1,ihu closed.2.1,ihv closed.2.2⟩

def CodeReferences (shape : StorageShape) : LocalRTL.Code → Prop
  | .source e => ExternalRefs false shape e.value ∧ ValidityRefs false shape e.valid
  | .localNode e => ExternalRefs true shape e.value ∧ ValidityRefs true shape e.valid

theorem codePhysical_from_refs (a : Artifact) (r : FiniteRuntime a.storageShape)
    (decls : Wires) (values : Array Int) (c : LocalRTL.Code) (closed : CodeReferences a.storageShape c) :
    CodePhysical a r.decode ((environment a r decls #[]).withTemporaries values) c := by
  cases c with
  | source e =>
    exact ⟨physical_from_refs a r decls values none #[] e.value closed.1,
      validityPhysical_from_refs a r decls values none #[] e.valid closed.2⟩
  | localNode e =>
    intro refs signals
    exact ⟨physical_from_refs a r decls values (some refs) signals e.value closed.1,
      validityPhysical_from_refs a r decls values (some refs) signals e.valid closed.2⟩

end IRComparison.Circuit.Shared.NetEmission
