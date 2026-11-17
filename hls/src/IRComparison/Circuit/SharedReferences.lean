import IRComparison.Circuit.SharedRange
import IRComparison.Circuit.SharedStatementSound

namespace IRComparison.Circuit.Shared
open SystemVerilog

def Node.closed (shape : StorageShape) : Node → Prop
  | .input e => e.inStorage shape
  | .memory a _ => shape.hasMemory a
  | _ => True

instance (shape : StorageShape) (n : Node) : Decidable (n.closed shape) := by
  cases n <;> simp only [Node.closed] <;> infer_instance

instance : ExpressionStorage Program where
  closed shape p := ∀ n ∈ p.graph, n.closed shape

instance (shape : StorageShape) : ∀ p : Program, Decidable (ExpressionStorage.closed shape p) :=
  fun p => inferInstanceAs (Decidable (∀ n ∈ p.graph, n.closed shape))

theorem references_external (e : RTL.Term) (h : ReferencesIn shape e) :
    NetEmission.ExternalRefs false shape e := by
  rw [ReferencesIn.eq_def] at h
  rw [NetEmission.ExternalRefs.eq_def]
  refine ⟨?_,fun c hc => references_external c (h.2 c hc)⟩
  cases e <;> simpa using h.1
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ hc

theorem validity_external (e : RTL.Validity) (h : ValidityReferences shape e) :
    NetEmission.ValidityRefs false shape e := by
  induction e with
  | yes | no => trivial
  | and a b ia ib => exact ⟨ia h.1,ib h.2⟩
  | address a j => exact ⟨references_external j h.2,h.1⟩
  | mux c a b ia ib => exact ⟨references_external c h.1,ia h.2.1,ib h.2.2⟩

@[simp] theorem external_literal : NetEmission.ExternalRefs localNames s (.literal n) := by
  rw [NetEmission.ExternalRefs.eq_def]
  simp [RTL.Term.children]
@[simp] theorem external_wire : NetEmission.ExternalRefs localNames s (.wire n) ↔ localNames = true ∨ n < s.wires.size := by
  rw [NetEmission.ExternalRefs.eq_def]
  simp [RTL.Term.children]
@[simp] theorem external_register : NetEmission.ExternalRefs localNames s (.register n) ↔ n < s.registers := by
  rw [NetEmission.ExternalRefs.eq_def]
  simp [RTL.Term.children]
@[simp] theorem external_length : NetEmission.ExternalRefs localNames s (.length n) ↔ n < s.memories := by
  rw [NetEmission.ExternalRefs.eq_def]
  simp [RTL.Term.children]
@[simp] theorem external_cell : NetEmission.ExternalRefs localNames s (.cell n j) ↔ n < s.memories ∧ NetEmission.ExternalRefs localNames s j := by
  rw [NetEmission.ExternalRefs.eq_def]
  simp [RTL.Term.children]
@[simp] theorem external_binary : NetEmission.ExternalRefs localNames s (.binary op u v) ↔ NetEmission.ExternalRefs localNames s u ∧ NetEmission.ExternalRefs localNames s v := by
  rw [NetEmission.ExternalRefs.eq_def]
  simp [RTL.Term.children]
@[simp] theorem external_resize : NetEmission.ExternalRefs localNames s (.resize k v) ↔ NetEmission.ExternalRefs localNames s v := by
  rw [NetEmission.ExternalRefs.eq_def]
  simp [RTL.Term.children]
@[simp] theorem external_wrap32 : NetEmission.ExternalRefs localNames s (.wrap32 v) ↔ NetEmission.ExternalRefs localNames s v := by
  rw [NetEmission.ExternalRefs.eq_def]
  simp [RTL.Term.children]

@[simp] theorem external_nonnegative : NetEmission.ExternalRefs localNames s (.nonnegative v) ↔ NetEmission.ExternalRefs localNames s v := by
  rw [NetEmission.ExternalRefs.eq_def]
  simp [RTL.Term.children]
@[simp] theorem external_mux : NetEmission.ExternalRefs localNames s (.mux c u v) ↔ NetEmission.ExternalRefs localNames s c ∧ NetEmission.ExternalRefs localNames s u ∧ NetEmission.ExternalRefs localNames s v := by
  rw [NetEmission.ExternalRefs.eq_def]
  simp [RTL.Term.children,and_assoc]

theorem lower_references (n : Node) (h : n.closed shape) :
    NetEmission.CodeReferences shape (LocalRTL.lower wr rs n) := by
  cases n with
  | input e =>
    have hc := combinational_references wr e h
    exact ⟨references_external _ hc.1,validity_external _ hc.2⟩
  | memory a j =>
    simp [LocalRTL.lower,LocalRTL.raw,NetEmission.CodeReferences,
      NetEmission.ValidityRefs,RTL.Term.children,LocalRTL.valueRef,LocalRTL.validRef,h.1]
  | binary | wrap32 | natIndex | select | seq =>
    simp [LocalRTL.lower,LocalRTL.raw,NetEmission.CodeReferences,
      NetEmission.ValidityRefs,RTL.Term.children,LocalRTL.valueRef,LocalRTL.validRef]

theorem lowerGraph_references (g : Graph) (h : ∀ n ∈ g, n.closed shape) :
    ∀ c ∈ (LocalRTL.lowerGraph wr g).code, NetEmission.CodeReferences shape c := by
  induction g with
  | nil => simp [LocalRTL.lowerGraph]
  | cons n g ih =>
    intro c hc
    simp only [LocalRTL.lowerGraph,List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact lower_references n (h n (by simp))
    · exact ih (fun n hn => h n (by simp [hn])) c hc

theorem prepare_references (p : Program) (h : ExpressionStorage.closed shape p) :
    ExpressionSemantics.references shape (prepare wr p) :=
  lowerGraph_references p.graph h

@[simp] theorem zero_closed : ExpressionStorage.closed shape (ExpressionEvaluation.zero : Program) := by
  change ∀ n ∈ [Node.input (.lit 0)], n.closed shape
  simp [Node.closed,Expr.inStorage]

end IRComparison.Circuit.Shared
