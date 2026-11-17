import IRComparison.Circuit.SystemVerilog.ExecutionSound

namespace IRComparison.Circuit.SystemVerilog

def Store.scalarBits (store : Store) (env : Environment) (name : Name) : Option (BitVec (env.type name).width) :=
  (store.scalar name).map (BitVec.ofInt (env.type name).width)

/-- Observable core-state correspondence. Signed registers are compared as
bit patterns; memory/FIFO cells are compared only inside their live prefix.
Unused physical padding and temporary combinational wires are not observed. -/
structure Store.Matches (store : Store) (env : Environment) (shape : StorageShape) (runtime : Runtime) : Prop where
  pc : store.scalarBits env .pc = some (BitVec.ofNat (env.type .pc).width runtime.pc)
  done : store.scalarBits env .done = some (BitVec.ofInt (env.type .done).width (if runtime.done then 1 else 0))
  error : store.scalarBits env .error = some (BitVec.ofInt (env.type .error).width (if runtime.error then 1 else 0))
  regs : ∀ n, n < shape.registers → store.scalarBits env (.register n) = some (BitVec.ofInt (env.type (.register n)).width (runtime.data.regs n))
  wires : ∀ n, n < shape.wires.size → store.scalarBits env (.holding n) = some (BitVec.ofInt (env.type (.holding n)).width (runtime.wires n))
  memoryLength : ∀ n, n < shape.memories → store.scalar (.length n) = some ((runtime.data.arrays n).size : Int)
  memoryCells : ∀ n, n < shape.memories → ∀ j (hj : j < (runtime.data.arrays n).size),
    store.cell (.memory n) j = some (BitVec.ofInt 32 ((runtime.data.arrays n)[j]'hj)).toNat
  queueLength : ∀ q, q < shape.queues → store.scalar (.used q) = some ((runtime.queues q).length : Int)
  queueCells : ∀ q, q < shape.queues → ∀ j (hj : j < (runtime.queues q).length),
    store.cell (.queue q) j = some (BitVec.ofInt 32 ((runtime.queues q)[j]'hj)).toNat

theorem finite_store_matches (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) :
    let env := (environment a r final.text #[]).withTemporaries values
    env.store.Matches env a.storageShape r.decode := by
  constructor
  · rfl
  · rfl
  · rfl
  · intro n hn; simp [Store.scalarBits,Environment.store,environment,environmentFor,Environment.withTemporaries,FiniteRuntime.decode,hn]
  · intro n hn; simp [Store.scalarBits,Environment.store,environment,environmentFor,Environment.withTemporaries,FiniteRuntime.decode,hn]
  · intro n hn; simp [Environment.store,environment,environmentFor,Environment.withTemporaries,FiniteRuntime.decode,hn,WordBuffer.contents]
  · intro n hn j hj
    have live : j < (r.arrays ⟨n,hn⟩).used.val := by
      simpa only [FiniteRuntime.decode,hn,↓reduceDIte,WordBuffer.contents,Array.size_ofFn] using hj
    have cap : j < a.storageShape.memorySize n := by
      have used : (r.arrays ⟨n,hn⟩).used.val < a.storageShape.memorySize n+1 := (r.arrays ⟨n,hn⟩).used.isLt
      omega
    simp [Environment.store,environment,environmentFor,Environment.withTemporaries,FiniteRuntime.decode,hn,cap,WordBuffer.contents]
  · intro q hq; simp [Environment.store,environment,environmentFor,Environment.withTemporaries,FiniteRuntime.decode,hq,WordBuffer.contents]
  · intro q hq j hj
    have live : j < (r.queues ⟨q,hq⟩).used.val := by
      simpa only [FiniteRuntime.decode,hq,↓reduceDIte,WordBuffer.contents,Array.length_toList,Array.size_ofFn] using hj
    have cap : j < a.storageShape.queueSize q := by
      have used : (r.queues ⟨q,hq⟩).used.val < a.storageShape.queueSize q+1 := (r.queues ⟨q,hq⟩).used.isLt
      omega
    simp [Environment.store,environment,environmentFor,Environment.withTemporaries,FiniteRuntime.decode,hq,cap,WordBuffer.contents]

theorem Store.Matches.writeRegister {pending : Store} {runtime : Runtime} (related : pending.Matches env shape runtime)
    (target : RTL.Register) (n : Int) (pcNonnegative : target = .pc → 0 ≤ n) :
    (pending.writeRegister env target n).Matches env shape (target.write runtime n) := by
  rcases related with ⟨pc,done,error,regs,wires,memoryLength,memoryCells,queueLength,queueCells⟩
  cases target <;> constructor <;>
    simp_all [Store.writeRegister,Store.scalarBits,Store.setScalar,RTL.Register.write,Runtime.setWire,State.set,
      BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq,-BitVec.toNat_ofInt]
  all_goals first
    | assumption
    | (intros k hk; split <;> simp_all [BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq,-BitVec.toNat_ofInt])
    | (rw [← BitVec.ofInt_natCast,Int.toNat_of_nonneg pcNonnegative])

  all_goals subst k; simp only [BitVec.setWidth_eq]

/-- Frame rule for replacing one logical array. Only its live prefix needs
to be represented, while all other banks and scalar registers retain their
previous observations. -/
theorem Store.Matches.setArray {pending writes : Store} {runtime : Runtime} {id : Nat}
    (related : pending.Matches env shape runtime) (data : Array Int)
    (scalars : ∀ name, writes.scalar name = if name = .length id then some (data.size : Int) else pending.scalar name)
    (otherCells : ∀ name j, name ≠ .memory id → writes.cell name j = pending.cell name j)
    (cells : ∀ j (hj : j < data.size), writes.cell (.memory id) j = some (BitVec.ofInt 32 (data[j]'hj)).toNat) :
    writes.Matches env shape (runtime.setArray id data) := by
  constructor
  · simpa [Store.scalarBits,scalars,Runtime.setArray] using related.pc
  · simpa [Store.scalarBits,scalars,Runtime.setArray] using related.done
  · simpa [Store.scalarBits,scalars,Runtime.setArray] using related.error
  · intro n hn; simpa [Store.scalarBits,scalars,Runtime.setArray] using related.regs n hn
  · intro n hn; simpa [Store.scalarBits,scalars,Runtime.setArray] using related.wires n hn
  · intro n hn
    by_cases same : n = id
    · subst n; simp [scalars,Runtime.setArray]
    · simpa [scalars,Runtime.setArray,same] using related.memoryLength n hn
  · intro n hn j hj
    by_cases same : n = id
    · subst n; simpa [Runtime.setArray] using cells j (by simpa [Runtime.setArray] using hj)
    · rw [otherCells (.memory n) j (by simpa)]
      simpa [Runtime.setArray,same] using related.memoryCells n hn j (by simpa [Runtime.setArray,same] using hj)
  · intro q hq; simpa [scalars,Runtime.setArray] using related.queueLength q hq
  · intro q hq j hj
    rw [otherCells (.queue q) j (by simp)]
    exact related.queueCells q hq j hj

theorem Store.Matches.setQueue {pending writes : Store} {runtime : Runtime}
    (related : pending.Matches env shape runtime) (data : List Int)
    (scalars : ∀ name, writes.scalar name = if name = .used q then some (data.length : Int) else pending.scalar name)
    (otherCells : ∀ name j, name ≠ .queue q → writes.cell name j = pending.cell name j)
    (cells : ∀ j (hj : j < data.length), writes.cell (.queue q) j = some (BitVec.ofInt 32 (data[j]'hj)).toNat) :
    writes.Matches env shape (runtime.setQueue q data) := by
  constructor
  · simpa [Store.scalarBits,scalars,Runtime.setQueue] using related.pc
  · simpa [Store.scalarBits,scalars,Runtime.setQueue] using related.done
  · simpa [Store.scalarBits,scalars,Runtime.setQueue] using related.error
  · intro n hn; simpa [Store.scalarBits,scalars,Runtime.setQueue] using related.regs n hn
  · intro n hn; simpa [Store.scalarBits,scalars,Runtime.setQueue] using related.wires n hn
  · intro n hn; simpa [scalars,Runtime.setQueue] using related.memoryLength n hn
  · intro n hn j hj
    rw [otherCells (.memory n) j (by simp)]
    exact related.memoryCells n hn j hj
  · intro n hn
    by_cases same : n = q
    · subst n; simp [scalars,Runtime.setQueue]
    · simpa [scalars,Runtime.setQueue,same] using related.queueLength n hn
  · intro n hn j hj
    by_cases same : n = q
    · subst n; simpa [Runtime.setQueue] using cells j (by simpa [Runtime.setQueue] using hj)
    · rw [otherCells (.queue n) j (by simpa)]
      simpa [Runtime.setQueue,same] using related.queueCells n hn j (by simpa [Runtime.setQueue,same] using hj)

theorem Store.Matches.erase {pending : Store} {runtime : Runtime} {id : Nat}
    (related : pending.Matches env shape runtime) :
    (pending.setScalar (.length id) 0).Matches env shape (runtime.setArray id #[]) := by
  apply related.setArray #[]
  · intro name; rfl
  · intros; rfl
  · intro j hj; simp at hj

theorem Store.Matches.clear {pending : Store} {runtime : Runtime}
    (related : pending.Matches env shape runtime) :
    (pending.setScalar (.used q) 0).Matches env shape (runtime.setQueue q []) := by
  apply related.setQueue []
  · intro name; rfl
  · intros; rfl
  · intro j hj; simp at hj

theorem Store.Matches.store {pending : Store} {runtime : Runtime} {id : Nat}
    (related : pending.Matches env shape runtime) (inside : id < shape.memories) (j : Nat) (v : Int) :
    (pending.setCell (.memory id) j (BitVec.ofInt 32 v).toNat).Matches env shape
      (runtime.setArray id ((runtime.data.arrays id).set! j v)) := by
  apply related.setArray
  · intro name
    by_cases selected : name = .length id
    · subst name; simpa [Store.setCell] using related.memoryLength id inside
    · simp [Store.setCell,selected]
  · intro name k other; simp [Store.setCell,other]
  · intro k hk
    by_cases same : k = j
    · subst k; simp [Store.setCell]
    · have live : k < (runtime.data.arrays id).size := by simpa using hk
      simp only [Array.set!_eq_setIfInBounds] at hk ⊢
      rw [Array.getElem_setIfInBounds_ne (a:=v) live (Ne.symm same)]
      simpa [Store.setCell,same] using related.memoryCells id inside k live

theorem Store.Matches.push {pending : Store} {runtime : Runtime}
    (related : pending.Matches env shape runtime) (inside : q < shape.queues) (v : Int) :
    ((pending.setCell (.queue q) (runtime.queues q).length (BitVec.ofInt 32 v).toNat).setScalar (.used q) ((runtime.queues q).length+1)).Matches
      env shape (runtime.setQueue q (runtime.queues q ++ [v])) := by
  apply related.setQueue
  · intro name; simp [Store.setScalar,Store.setCell]
  · intro name j other; simp [Store.setScalar,Store.setCell,other]
  · intro j hj
    by_cases last : j = (runtime.queues q).length
    · subst j; simp [Store.setScalar,Store.setCell]
    · have live : j < (runtime.queues q).length := by simp only [List.length_append,List.length_singleton] at hj; omega
      simpa [Store.setScalar,Store.setCell,last,List.getElem_append,live] using related.queueCells q inside j live

/-- Full-bank copy may change padding arbitrarily without changing the
logical array. Only the source's live cells are used in the correspondence. -/
theorem Store.Matches.copy {pending : Store} {runtime old : Runtime} {id source : Nat}
    (related : pending.Matches env shape runtime) (oldRelated : env.store.Matches env shape old)
    (sourceInside : source < shape.memories) (fits : (old.data.arrays source).size ≤ capacity) :
    (({pending with cell := fun name j =>
      if name = (Name.memory id) ∧ j < capacity then env.cell (.memory source) j else pending.cell name j}).setScalar
        (.length id) (old.data.arrays source).size).Matches env shape (runtime.setArray id (old.data.arrays source)) := by
  apply related.setArray
  · intro name; rfl
  · intro name j other; simp [Store.setScalar,other]
  · intro j hj
    simpa [Store.setScalar,show j < capacity by omega,Environment.store] using oldRelated.memoryCells source sourceInside j hj

theorem Store.Matches.shift {pending : Store} {runtime old : Runtime}
    (related : pending.Matches env shape runtime) (oldRelated : env.store.Matches env shape old)
    (inside : q < shape.queues) (fits : (old.queues q).length ≤ capacity) :
    (({pending with cell := fun name j =>
      if name = (Name.queue q) ∧ j < capacity-1 then env.cell (.queue q) (j+1) else pending.cell name j}).setScalar
        (.used q) ((old.queues q).length-1 : Nat)).Matches env shape (runtime.setQueue q (old.queues q).tail) := by
  apply related.setQueue
  · intro name; simp only [Store.setScalar,List.length_tail]
  · intro name j other; simp [Store.setScalar,other]
  · intro j hj
    have live : j+1 < (old.queues q).length := by simp only [List.length_tail] at hj; omega
    have physical : j < capacity-1 := by omega
    simpa [Store.setScalar,physical,List.getElem_tail,Environment.store] using oldRelated.queueCells q inside (j+1) live

end IRComparison.Circuit.SystemVerilog
