import IRComparison.Circuit.SystemVerilog.TermSound

namespace IRComparison.Circuit.SystemVerilog

/-- Existing physical layout bounds, expressed for the emitter's terms.
This predicate is proof support; it is not another source-language filter. -/
def ReferencesIn (shape : StorageShape) (e : RTL.Term) : Prop :=
  (match e with
    | .wire n => n < shape.wires.size
    | .register n => n < shape.registers
    | .length n | .cell n _ => n < shape.memories
    | _ => True) ∧ ∀ child ∈ e.children, ReferencesIn shape child
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ ‹_›

theorem memorySize_shape (known : memorySize a n = .ok size) : a.storageShape.memorySize n = size := by
  unfold memorySize at known
  cases found : a.memories.toList.find? (fun p => p.1 == n) with
  | none => simp [found,throw] at known
  | some pair =>
    simp only [found] at known
    cases known
    simp only [Artifact.storageShape,found,Option.map_some,Option.getD_some]

theorem physicalNode_finite (a : Artifact) (r : FiniteRuntime a.storageShape)
    (declarations : Array Wire) (values : Array Int) (e : RTL.Term)
    (closed : ReferencesIn a.storageShape e) :
    PhysicalNode a r.decode ((environment a r declarations #[]).withTemporaries values) e := by
  let env := (environment a r declarations #[]).withTemporaries values
  rw [ReferencesIn.eq_def] at closed
  cases e with
  | wire n =>
    have hn : n < a.wires.size := closed.1
    have hnShape : n < a.storageShape.wires.size := hn
    have declared : a.wires[n]? = some a.wires[n] := Array.getElem?_eq_getElem hn
    have widthEq : signedWidth (a.storageShape.wireRange n) = signedWidth (a.wires[n]?.getD wordRange) := by
      simp [Artifact.storageShape,StorageShape.wireRange,declared]
    have stored : env.scalar (.holding n) = some (r.decode.wires n) := by
      simp [env,environment,environmentFor,Environment.withTemporaries,FiniteRuntime.decode,hnShape]
    refine SignedMeaning.reference env (.holding n) (by unfold signedWidth; omega) ?_ stored ?_
    · simp [env,Environment.withTemporaries,environment,environmentFor,widthEq]
    · rw [← widthEq]
      simp [FiniteRuntime.decode,show n < a.storageShape.wires.size from hn]
  | register n =>
    have hn : n < a.storageShape.registers := closed.1
    apply unsigned_reference_meaning (env:=env) (w:=32)
    · rfl
    · simp [env,Environment.withTemporaries,environment,environmentFor,FiniteRuntime.decode,hn]
    · simp only [FiniteRuntime.decode,hn,↓reduceDIte,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  | length n =>
    intro size known
    have hn : n < a.storageShape.memories := closed.1
    have capacity := memorySize_shape known
    have usedBound : (r.arrays ⟨n,hn⟩).used.val < 2^bits size := by
      have used : (r.arrays ⟨n,hn⟩).used.val < size+1 := by
        simpa only [capacity] using (r.arrays ⟨n,hn⟩).used.isLt
      have := bits_fits size
      omega
    have lengthMeaning := unsigned_reference_meaning (env:=env) (name:=.length n) (w:=bits size)
      (by simp [env,Environment.withTemporaries,environment,environmentFor,capacity])
      (n:=((r.arrays ⟨n,hn⟩).used.val : Int))
      (by simp [env,Environment.withTemporaries,environment,environmentFor,hn])
      (by simp only [BitVec.ofInt_natCast,BitVec.toNat_ofNat,Nat.mod_eq_of_lt usedBound])
    simpa only [FiniteRuntime.decode,hn,↓reduceDIte,WordBuffer.contents,Array.size_ofFn] using lengthMeaning
  | cell n j =>
    intro size known
    have hn : n < a.storageShape.memories := closed.1
    have capacity := memorySize_shape known
    have usedBound : (r.arrays ⟨n,hn⟩).used.val < 2^bits size := by
      have used : (r.arrays ⟨n,hn⟩).used.val < size+1 := by
        simpa only [capacity] using (r.arrays ⟨n,hn⟩).used.isLt
      have := bits_fits size
      omega
    have lengthMeaning := unsigned_reference_meaning (env:=env) (name:=.length n) (w:=bits size)
      (by simp [env,Environment.withTemporaries,environment,environmentFor,capacity])
      (n:=((r.arrays ⟨n,hn⟩).used.val : Int))
      (by simp [env,Environment.withTemporaries,environment,environmentFor,hn])
      (by simp only [BitVec.ofInt_natCast,BitVec.toNat_ofNat,Nat.mod_eq_of_lt usedBound])
    refine ⟨?_,rfl,?_⟩
    · simpa only [FiniteRuntime.decode,hn,↓reduceDIte,WordBuffer.contents,Array.size_ofFn] using lengthMeaning
    · intro k v fetched
      simp only [FiniteRuntime.decode,hn,↓reduceDIte,WordBuffer.contents] at fetched
      obtain ⟨live,element⟩ := Array.getElem?_eq_some_iff.mp fetched
      simp only [Array.size_ofFn] at live
      have inside : k < a.storageShape.memorySize n := by
        have used : (r.arrays ⟨n,hn⟩).used.val < a.storageShape.memorySize n+1 := (r.arrays ⟨n,hn⟩).used.isLt
        omega
      simp only [Array.getElem_ofFn] at element
      subst v
      constructor
      · simp [env,Environment.withTemporaries,environment,environmentFor,hn,inside]
      · simp
  | literal | binary | nonnegative | resize | mux => trivial

/-- Physical correspondence follows from finite-word storage and ordinary
reference bounds; no zero initialization or per-input equation oracle is used. -/
theorem physicalTree_finite (a : Artifact) (r : FiniteRuntime a.storageShape)
    (declarations : Array Wire) (values : Array Int) (e : RTL.Term)
    (closed : ReferencesIn a.storageShape e) :
    PhysicalTree a r.decode ((environment a r declarations #[]).withTemporaries values) e := by
  rw [PhysicalTree.eq_def]
  refine ⟨physicalNode_finite a r declarations values e closed,?_⟩
  intro child member
  rw [ReferencesIn.eq_def] at closed
  exact physicalTree_finite a r declarations values child (closed.2 child member)
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ member

/-- Whole-generator shared values now need only ordinary layout bounds and
successful concrete evaluation, rather than assumed physical expression meanings.
Deriving every generated reference bound from the existing storage certificate,
and proving evaluation totality, are subsequent composition obligations. -/
theorem generateCode_finite_values (a : Artifact) (r : FiniteRuntime a.storageShape)
    (generated : generateCode a = .ok (statements,emission))
    (evaluated : evaluateWires a r emission.text = some values)
    (closed : ∀ entry ∈ emission.cache.toList, ReferencesIn a.storageShape entry.1) :
    CacheMeaning ((environment a r emission.text #[]).withTemporaries values) r.decode emission :=
  generateCode_values_correct a r generated evaluated
    (fun entry member => physicalTree_finite a r emission.text values entry.1 (closed entry member))

end IRComparison.Circuit.SystemVerilog
