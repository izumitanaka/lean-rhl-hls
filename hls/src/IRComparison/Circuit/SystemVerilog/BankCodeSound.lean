import IRComparison.Circuit.SystemVerilog.BankUpdateSound

namespace IRComparison.Circuit.SystemVerilog

theorem require_success (success : require condition message before = .ok (result,after)) :
    condition = true ∧ after = before := by
  cases condition <;> simp only [require,Bool.false_eq_true,↓reduceIte] at success
  · cases success
  · exact ⟨rfl,(pure_success () success).2⟩

theorem wordValue_state (success : wordValue a e before = .ok (result,after)) : after = before :=
  (require_success success).2

theorem finite_memory_allocated {id : Nat} (a : Artifact) (r : FiniteRuntime a.storageShape) (final : Emission) (values : Array Int)
    (inside : id < a.storageShape.memories) (indexInside : j < (r.decode.data.arrays id).size) :
    (((environment a r final.text #[]).withTemporaries values).cell (.memory id) j).isSome = true := by
  have used : (r.arrays ⟨id,inside⟩).used.val < a.storageShape.memorySize id+1 := (r.arrays ⟨id,inside⟩).used.isLt
  have physical : j < a.storageShape.memorySize id := by
    simp only [FiniteRuntime.decode,inside,↓reduceDIte,WordBuffer.contents,Array.size_ofFn] at indexInside
    omega
  simp [environment,environmentFor,Environment.withTemporaries,inside,physical]

/-- The real array-write generator writes exactly the selected physical
word, using the old-state index and value. Other pending writes are retained. -/
theorem statementCode_store_correct {id : Nat} (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) (j v : RTL.Combinational)
    (inside : id < a.storageShape.memories)
    (closedJ : CombinationalReferences a.storageShape j) (closedV : CombinationalReferences a.storageShape v)
    (nonnegative : 0 ≤ j.value.eval r.decode)
    (indexInside : (j.value.eval r.decode).toNat < (r.decode.data.arrays id).size)
    (good : before.WellFormed)
    (success : statementCode a (.memory id (.set source j v)) before = .ok (code,after))
    (grows : after.Extends final)
    (meaning : CacheMeaning ((environment a r final.text #[]).withTemporaries values) r.decode final)
    (pending : Store) :
    code.eval ((environment a r final.text #[]).withTemporaries values) pending =
      some (pending.setCell (.memory id) (j.value.eval r.decode).toNat (BitVec.ofInt 32 (v.value.eval r.decode)).toNat) := by
  rw [statementCode] at success
  obtain ⟨size,s0,sized,rest0⟩ := bind_success _ _ success
  have same0 := (lift_success (memorySize a id) sized).2
  subst s0
  obtain ⟨ignored,s1,required1,rest1⟩ := bind_success _ _ rest0
  have same1 := (require_success required1).2
  subst s1
  obtain ⟨ignored,s2,checked,rest2⟩ := bind_success _ _ rest1
  have same := wordValue_state checked
  subst s2
  obtain ⟨js,s3,compiledJ,rest3⟩ := bind_success _ _ rest2
  obtain ⟨vs,compiledV,eq⟩ := return_success (expression a v)
    (fun vs => Statement.assign (.index (.memory id) (.reference js.name)) (.reference vs.name)) rest3
  subst code
  obtain ⟨middleGood,_,_⟩ := preserves_expression a j before good js s3 compiledJ
  obtain ⟨_,more,_⟩ := preserves_expression a v s3 middleGood vs after compiledV
  exact Statement.assign_index_signed
    (expression_correct a r final values j closedJ good compiledJ (more.trans grows) meaning).1 nonnegative
    (expression_correct a r final values v closedV middleGood compiledV grows meaning).1
    (finite_memory_allocated a r final values inside indexInside) pending

theorem statementCode_erase_correct {id : Nat} (a : Artifact)
    (success : statementCode a (.memory id .empty) before = .ok (code,after)) (env : Environment) (pending : Store) :
    code.eval env pending = some (pending.setScalar (.length id) 0) := by
  rw [statementCode] at success
  obtain ⟨size,s0,sized,rest0⟩ := bind_success _ _ success
  obtain ⟨rfl,_⟩ := pure_success _ rest0
  simpa using Statement.assign_signed (SignedMeaning.integer (env:=env) 0) (.length id) pending

theorem statementCode_clear_correct (a : Artifact)
    (success : statementCode a (.queue q .empty) before = .ok (code,after)) (env : Environment) (pending : Store) :
    code.eval env pending = some (pending.setScalar (.used q) 0) := by
  rw [statementCode] at success
  obtain ⟨ignored,s0,required,rest⟩ := bind_success _ _ success
  obtain ⟨rfl,_⟩ := pure_success _ rest
  simpa using Statement.assign_signed (SignedMeaning.integer (env:=env) 0) (.used q) pending

/-- Actual FIFO append code: the old used counter selects the cell and
increments once. The room premise is the existing generated branch guard. -/
theorem statementCode_send_correct (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) (v : RTL.Combinational)
    (inside : q < a.storageShape.queues) (room : (r.decode.queues q).length < a.machine.capacity q)
    (closed : CombinationalReferences a.storageShape v) (good : before.WellFormed)
    (success : statementCode a (.queue q (.append source v)) before = .ok (code,after))
    (grows : after.Extends final)
    (meaning : CacheMeaning ((environment a r final.text #[]).withTemporaries values) r.decode final)
    (pending : Store) :
    code.eval ((environment a r final.text #[]).withTemporaries values) pending =
      some ((pending.setCell (.queue q) (r.decode.queues q).length (BitVec.ofInt 32 (v.value.eval r.decode)).toNat).setScalar (.used q) ((r.decode.queues q).length+1)) := by
  rw [statementCode] at success
  obtain ⟨ignored,s0,required0,rest0⟩ := bind_success _ _ success
  have same0 := (require_success required0).2
  subst s0
  obtain ⟨ignored,s1,required1,rest1⟩ := bind_success _ _ rest0
  have same1 := (require_success required1).2
  subst s1
  obtain ⟨ignored,s2,checked,rest2⟩ := bind_success _ _ rest1
  have same := wordValue_state checked
  subst s2
  obtain ⟨signal,compiled,rfl⟩ := return_success (expression a v) _ rest2
  have data := (expression_correct a r final values v closed good compiled grows meaning).1
  obtain ⟨typed,stored,fits⟩ := finite_used a r final values inside
  have address := unsigned_reference_self typed stored fits
  have addressValue : (Value.ofInt ⟨bits (a.machine.capacity q),false⟩ (r.decode.queues q).length).integer =
      ((r.decode.queues q).length : Int) := by
    simp only [Value.integer,Value.ofInt,Bool.false_eq_true,↓reduceIte,BitVec.ofInt_natCast,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fits]
  have allocated : (((environment a r final.text #[]).withTemporaries values).cell (.queue q) (r.decode.queues q).length).isSome = true := by
    simp [environment,environmentFor,Environment.withTemporaries,inside,show (r.decode.queues q).length < a.storageShape.queueSize q from room]
  have writeCell := Statement.assign_index_value address addressValue allocated (data.assignment 32) pending
  have counter := counter_assignment typed (by unfold bits; omega) stored fits (op:=.add) (Or.inl rfl)
  have newFits : (r.decode.queues q).length+1 < 2^bits (a.machine.capacity q) := by have := bits_fits (a.machine.capacity q); omega
  rw [Statement.seq_eval,writeCell]
  simp only [Option.bind,Statement.eval,Destination.write,bind,pure]
  rw [typed,counter]
  simp only [Option.bind,beq_self_eq_true,↓reduceIte,← Int.natCast_add_one,BitVec.ofInt_natCast,BitVec.toNat_ofNat,Nat.mod_eq_of_lt newFits]

  rfl

/-- The actual receive-side shift and used-counter decrement. Unused tail
cells may retain arbitrary data; they are not part of the FIFO contents. -/
theorem statementCode_tail_correct (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) (inside : q < a.storageShape.queues)
    (nonempty : r.decode.queues q ≠ [])
    (success : statementCode a (.queue q (.tail source)) before = .ok (code,after)) (pending : Store) :
    let env := (environment a r final.text #[]).withTemporaries values
    code.eval env pending = some (({pending with cell := fun n j =>
        if n = (Name.queue q) ∧ j < a.machine.capacity q-1 then env.cell (.queue q) (j+1) else pending.cell n j}).setScalar (.used q) ((r.decode.queues q).length-1 : Nat)) := by
  rw [statementCode] at success
  obtain ⟨ignored,s0,required0,rest0⟩ := bind_success _ _ success
  obtain ⟨ignored,s1,required1,rest1⟩ := bind_success _ _ rest0
  obtain ⟨rfl,_⟩ := pure_success _ rest1
  let env := (environment a r final.text #[]).withTemporaries values
  let words : Nat → BitVec 32 := fun j => if h : j < a.storageShape.queueSize q then (r.queues ⟨q,inside⟩).cells ⟨j,h⟩ else 0
  have stored (i : Nat) (hi : i < a.machine.capacity q) : env.cell (.queue q) i = some ((words i).toNat : Int) := by
    simp [env,words,environment,environmentFor,Environment.withTemporaries,inside,
      show i < a.storageShape.queueSize q from hi]
  have shifted := fifo_shift_correct env pending (.queue q) (.shiftIndex q) (by simp) rfl words (a.machine.capacity q) stored
  have shiftedCells : (fun n j => if n = Name.queue q ∧ j < a.machine.capacity q-1 then some ((words (j+1)).toNat : Int) else pending.cell n j) =
      (fun n j => if n = Name.queue q ∧ j < a.machine.capacity q-1 then env.cell (.queue q) (j+1) else pending.cell n j) := by
    funext n j
    split
    · next selected => rw [stored (j+1) (by omega)]
    · rfl
  rw [shiftedCells] at shifted
  obtain ⟨typed,used,fits⟩ := finite_used a r final values inside
  have counter := counter_assignment typed (by unfold bits; omega) used fits (op:=.sub) (Or.inr rfl)
  have positive : 0 < (r.decode.queues q).length := List.length_pos_iff.mpr nonempty
  have newFits : (r.decode.queues q).length-1 < 2^bits (a.machine.capacity q) := by omega
  have minus : ((r.decode.queues q).length : Int)-1 = ((r.decode.queues q).length-1 : Nat) := by omega
  change _ = some _
  rw [Statement.seq_eval,shifted]
  simp only [Option.bind,Statement.eval,Destination.write,bind,pure]
  rw [typed,counter]
  simp only [show (Operator.sub == .add) = false from rfl,Bool.false_eq_true,↓reduceIte,minus,
    BitVec.ofInt_natCast,BitVec.toNat_ofNat,Nat.mod_eq_of_lt newFits]
  rfl

/-- Snapshot expansion copies the physical bank and its live length. The
successful size check supplies the equal-capacity fact used by the proof. -/
theorem statementCode_copy_correct {id source : Nat} (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) (inside : id < a.storageShape.memories)
    (sourceInside : source < a.storageShape.memories)
    (success : statementCode a (.memory id (.copy source)) before = .ok (code,after)) (pending : Store) :
    let env := (environment a r final.text #[]).withTemporaries values
    code.eval env pending = some (({pending with cell := fun n j =>
        if n = (Name.memory id) ∧ j < a.storageShape.memorySize id then env.cell (.memory source) j else pending.cell n j}).setScalar (.length id) (r.decode.data.arrays source).size) := by
  rw [statementCode] at success
  obtain ⟨size,s0,sized,rest0⟩ := bind_success _ _ success
  obtain ⟨sizeKnown,_⟩ := lift_success (memorySize a id) sized
  obtain ⟨sourceSize,s1,sourceSized,rest1⟩ := bind_success _ _ rest0
  obtain ⟨sourceKnown,_⟩ := lift_success (memorySize a source) sourceSized
  obtain ⟨ignored,s2,required,rest2⟩ := bind_success _ _ rest1
  have sameSize : size = sourceSize := by simpa using (require_success required).1
  obtain ⟨rfl,_⟩ := pure_success _ rest2
  have targetSize := memorySize_shape sizeKnown
  have sourceCapacity : a.storageShape.memorySize source = size := (memorySize_shape sourceKnown).trans sameSize.symm
  let env := (environment a r final.text #[]).withTemporaries values
  let words : Nat → BitVec 32 := fun j => if h : j < a.storageShape.memorySize source then (r.arrays ⟨source,sourceInside⟩).cells ⟨j,h⟩ else 0
  have stored (i : Nat) (hi : i < size) : env.cell (.memory source) i = some ((words i).toNat : Int) := by
    simp [env,words,environment,environmentFor,Environment.withTemporaries,sourceInside,
      show i < a.storageShape.memorySize source by omega]
  have allocated (i : Nat) (hi : i < size) : (env.cell (.memory id) i).isSome = true := by
    simp [env,environment,environmentFor,Environment.withTemporaries,inside,
      show i < a.storageShape.memorySize id by omega]
  have copied := snapshot_copy_correct env pending (.memory source) (.memory id) .loopIndex (by simp) (by simp)
    rfl rfl words size stored allocated
  have copiedCells : (fun n j => if n = Name.memory id ∧ j < size then some ((words j).toNat : Int) else pending.cell n j) =
      (fun n j => if n = Name.memory id ∧ j < a.storageShape.memorySize id then env.cell (.memory source) j else pending.cell n j) := by
    funext n j
    rw [targetSize]
    split
    · next selected => rw [stored j selected.2]
    · rfl
  rw [copiedCells] at copied
  have lengthStored : env.scalar (.length source) = some ((r.decode.data.arrays source).size : Int) := by
    simp [env,environment,environmentFor,Environment.withTemporaries,FiniteRuntime.decode,sourceInside,WordBuffer.contents]
  have lengthFits : (r.decode.data.arrays source).size < 2^bits size := by
    have used : (r.arrays ⟨source,sourceInside⟩).used.val < a.storageShape.memorySize source+1 := (r.arrays ⟨source,sourceInside⟩).used.isLt
    have bound := bits_fits size
    simp only [FiniteRuntime.decode,sourceInside,↓reduceDIte,WordBuffer.contents,Array.size_ofFn]
    omega
  have sourceType : env.type (.length source) = ⟨bits size,false⟩ := by
    change (⟨bits (a.storageShape.memorySize source),false⟩ : IntegralType) = _
    rw [sourceCapacity]
  have targetType : env.type (.length id) = ⟨bits size,false⟩ := by
    change (⟨bits (a.storageShape.memorySize id),false⟩ : IntegralType) = _
    rw [targetSize]
  have lengthCopy := unsigned_reference_assignment sourceType lengthStored lengthFits (bits size)
  change _ = some _
  rw [Statement.seq_eval,copied]
  simp only [Option.bind,Statement.eval,Destination.write,bind,pure]
  rw [targetType,lengthCopy]
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt lengthFits]
  rfl

end IRComparison.Circuit.SystemVerilog
