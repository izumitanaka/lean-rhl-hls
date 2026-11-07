import IRComparison.Circuit.SystemVerilog.StatementEval
import IRComparison.Circuit.RTL.BankLoops

namespace IRComparison.Circuit.SystemVerilog

/-- Concrete indexed RHS used by both snapshot copies and FIFO shifts.
The index is read from a correctly sized fixed loop counter. -/
theorem loop_cell_assignment (env : Environment) (name loopVar : Name)
    (distinct : name ≠ loopVar) (declared : env.type name = ⟨32,false⟩)
    (inside : iteration ≤ count) (value : BitVec 32)
    (stored : env.cell name iteration = some (value.toNat : Int)) :
    (Expr.index name (.reference loopVar)).assignment (env.loop loopVar count iteration) 32 = some value := by
  let loopEnv := env.loop loopVar count iteration
  have typed : loopEnv.type name = ⟨32,false⟩ := by simp [loopEnv,Environment.loop,distinct,declared]
  have counter : (Expr.reference loopVar).eval loopEnv none =
      some (Value.ofInt ⟨bits count,false⟩ iteration) := loop_reference_eval env loopVar inside
  have fits := loop_counter_fits inside
  change (Expr.index name (.reference loopVar)).assignment loopEnv 32 = _
  unfold Expr.assignment
  simp only [Expr.type,typed]
  rw [Expr.eval,counter]
  simp [Value.integer,Value.ofInt,Value.inContext,IntegralType.context,Expr.type,typed,
    fits,show loopEnv.cell name iteration = some (value.toNat : Int) from stored]
  rw [typed]
  have reduced : ((value.toNat : Int) % 4294967296) = value.toNat :=
    Int.emod_eq_of_lt (by omega) (by have h := value.isLt; change value.toNat < 4294967296 at h; omega)
  simp [show ¬(iteration : Int) < 0 by omega,reduced,BitVec.ofInt_natCast]

/-- A cell update template keeps every other pending cell unchanged. -/
theorem loop_copy_cell (env : Environment) (pending : Store) (source target loopVar : Name)
    (sourceDistinct : source ≠ loopVar) (targetDistinct : target ≠ loopVar)
    (sourceType : env.type source = ⟨32,false⟩) (targetType : env.type target = ⟨32,false⟩)
    (inside : iteration ≤ count) (value : BitVec 32)
    (stored : env.cell source iteration = some (value.toNat : Int))
    (allocated : (env.cell target iteration).isSome = true) :
    (Statement.assign (.index target (.reference loopVar)) (.index source (.reference loopVar))).eval
      (env.loop loopVar count iteration) pending = some (pending.setCell target iteration value.toNat) := by
  let loopEnv := env.loop loopVar count iteration
  have typed : loopEnv.type target = ⟨32,false⟩ := by simp [loopEnv,Environment.loop,targetDistinct,targetType]
  have counter : (Expr.reference loopVar).eval loopEnv none =
      some (Value.ofInt ⟨bits count,false⟩ iteration) := loop_reference_eval env loopVar inside
  have fits := loop_counter_fits inside
  change (Statement.assign (.index target (.reference loopVar)) (.index source (.reference loopVar))).eval loopEnv pending = _
  simp only [Statement.eval,Destination.write]
  rw [counter]
  obtain ⟨old,hold⟩ := Option.isSome_iff_exists.mp allocated
  have hold' : loopEnv.cell target iteration = some old := hold
  have rhs := loop_cell_assignment env source loopVar sourceDistinct sourceType inside value stored
  change (Expr.index source (.reference loopVar)).assignment loopEnv 32 = some value at rhs
  simp [Value.integer,Value.ofInt,fits,typed,hold',rhs]
  rw [typed]
  simp [rhs]

theorem Store.fold_cells (indices : List Nat) (target : Name) (values : Nat → Int) (pending : Store) :
    indices.foldl (fun p i => p.setCell target i (values i)) pending =
      {pending with cell := fun n j => if n = target then
        (indices.foldl (fun cells i => fun k => if k = i then some (values i) else cells k) (pending.cell n)) j
        else pending.cell n j} := by
  induction indices generalizing pending with
  | nil =>
    simp only [List.foldl_nil]
    simp
  | cons i rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    unfold Store.setCell
    congr 1
    funext n j
    by_cases selected : n = target <;> simp [selected]

/-- Fixed-range NBA template correctness, independently of unused cells.
The body premise is one generic iteration, not a fixed unrolling. -/
theorem forRange_cells (env : Environment) (loopVar target : Name) (count : Nat) (body : Statement)
    (values : Nat → Int)
    (bodyCorrect : ∀ i, i < count → ∀ pending,
      body.eval (env.loop loopVar count i) pending = some (pending.setCell target i (values i)))
    (pending : Store) :
    (Statement.forRange loopVar count body).eval env pending =
      some {pending with cell := fun n j =>
        if n = target then RTL.writeRange count (fun i => some (values i)) (pending.cell n) j else pending.cell n j} := by
  have fold (indices : List Nat) (valid : ∀ i ∈ indices, i < count) (writes : Store) :
      indices.foldlM (fun p i => body.eval (env.loop loopVar count i) p) writes =
        some (indices.foldl (fun p i => p.setCell target i (values i)) writes) := by
    induction indices generalizing writes with
    | nil => rfl
    | cons i rest ih =>
      simp only [List.foldlM_cons,List.foldl_cons,bodyCorrect i (valid i (by simp)),bind,Option.bind]
      exact ih (fun j hj => valid j (by simp [hj])) _
  rw [Statement.eval,fold _ (by simp)]
  rw [Store.fold_cells]
  rfl

/-- The snapshot-copy loop emitted by `statementCode`, at every capacity.
Physical padding is copied too; only live-prefix observations are later
used to connect this result to the source array semantics. -/
theorem snapshot_copy_correct (env : Environment) (pending : Store) (source target loopVar : Name)
    (sourceDistinct : source ≠ loopVar) (targetDistinct : target ≠ loopVar)
    (sourceType : env.type source = ⟨32,false⟩) (targetType : env.type target = ⟨32,false⟩)
    (values : Nat → BitVec 32) (count : Nat)
    (stored : ∀ i, i < count → env.cell source i = some ((values i).toNat : Int))
    (allocated : ∀ i, i < count → (env.cell target i).isSome = true) :
    (Statement.forRange loopVar count
      (.assign (.index target (.reference loopVar)) (.index source (.reference loopVar)))).eval env pending =
      some {pending with cell := fun n j =>
        if n = target ∧ j < count then some ((values j).toNat : Int) else pending.cell n j} := by
  rw [forRange_cells env loopVar target count _ (fun i => ((values i).toNat : Int))
    (fun i hi writes => loop_copy_cell env writes source target loopVar sourceDistinct targetDistinct
      sourceType targetType (by omega) (values i) (stored i hi) (allocated i hi))]
  congr 1
  congr 1
  funext n j
  rw [RTL.writeRange_correct]
  by_cases hn : n = target <;> by_cases hj : j < count <;> simp [hn,hj]

end IRComparison.Circuit.SystemVerilog
