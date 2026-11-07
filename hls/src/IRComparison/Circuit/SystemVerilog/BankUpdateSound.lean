import IRComparison.Circuit.SystemVerilog.ScalarSound
import IRComparison.Circuit.SystemVerilog.BankSound

namespace IRComparison.Circuit.SystemVerilog

theorem unsigned_reference_assignment {n : Nat} (typed : env.type name = ⟨w,false⟩)
    (stored : env.scalar name = some (n : Int)) (fits : n < 2^w) (k : Nat) :
    (Expr.reference name).assignment env k = some (BitVec.ofNat k n) := by
  unfold Expr.assignment
  simp only [Expr.type,typed,unsigned_reference_context typed stored fits,bind,Option.bind,
    Value.integer,Value.ofInt,Bool.false_eq_true,↓reduceIte,BitVec.ofInt_natCast,BitVec.toNat_ofNat]
  have bound : n < 2^(max w k) := Nat.lt_of_lt_of_le fits (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  simp [Nat.mod_eq_of_lt bound]

theorem unsigned_binary_eval {x y : Nat} (leftType : a.type env = ⟨wa,false⟩)
    (rightType : b.type env = ⟨v,s⟩) (leftLarger : wa ≤ w) (larger : v ≤ w)
    (comparison : op.comparison = false) (notAnd : op ≠ .and)
    (leftValue : a.eval env (some ⟨w,false⟩) = some (Value.ofInt ⟨w,false⟩ x))
    (rightValue : b.eval env (some ⟨w,false⟩) = some (Value.ofInt ⟨w,false⟩ y))
    (leftFits : x < 2^w) (rightFits : y < 2^w) (computed : arithmetic op x y = some result) :
    (Expr.binary op a b).eval env (some ⟨w,false⟩) = some (Value.ofInt ⟨w,false⟩ result) := by
  have notAndBool : (op == .and) = false := by simp [notAnd]
  rw [Expr.eval]
  simp only [Expr.type,comparison,notAndBool,Bool.false_or,Bool.false_eq_true,↓reduceIte,
    leftType,rightType,IntegralType.join,IntegralType.context,Nat.max_eq_right (Nat.max_le.mpr ⟨leftLarger,larger⟩),
    Bool.false_and,leftValue,rightValue,bind,Option.bind,Value.integer,Value.ofInt,
    BitVec.ofInt_natCast,BitVec.toNat_ofNat,Nat.mod_eq_of_lt leftFits,Nat.mod_eq_of_lt rightFits,computed]
  simp only [pure]
  rw [comparison,notAndBool,leftType,rightType]
  simp [Nat.max_eq_right (Nat.max_le.mpr ⟨leftLarger,larger⟩)]
  rw [Nat.max_eq_right (Nat.max_le.mpr ⟨leftLarger,larger⟩)]

/-- Increment/decrement templates operate at the declared counter width.
The caller's room/nonempty guard establishes that the result does not wrap. -/
theorem counter_assignment {n : Nat} (typed : env.type name = ⟨w,false⟩) (positive : 0 < w)
    (stored : env.scalar name = some (n : Int)) (fits : n < 2^w)
    (operation : op = .add ∨ op = .sub) :
    (Expr.binary op (.reference name) (.bit true)).assignment env w =
      some (BitVec.ofInt w (if op == .add then (n : Int)+1 else (n : Int)-1)) := by
  have unitFits : 1 < 2^w := Nat.one_lt_two_pow (by omega)
  have rhs : (Expr.bit true).eval env (some ⟨w,false⟩) = some (Value.ofInt ⟨w,false⟩ 1) := by
    simp [Expr.eval,Expr.type,IntegralType.context,Value.inContext,truth,Value.ofInt,Nat.max_eq_right (show 1 ≤ w by omega)]
    rw [Nat.max_eq_right (show 1 ≤ w by omega)]
  have lhs : (Expr.reference name).eval env (some ⟨w,false⟩) = some (Value.ofInt ⟨w,false⟩ n) := by
    simpa using unsigned_reference_context typed stored fits w
  have comparison : op.comparison = false := by rcases operation with rfl | rfl <;> rfl
  have notAnd : op ≠ .and := by rcases operation with rfl | rfl <;> decide
  have notAndBool : (op == .and) = false := by simp [notAnd]
  have computed : arithmetic op n 1 = some (if op == .add then (n : Int)+1 else (n : Int)-1) := by
    rcases operation with rfl | rfl <;> rfl
  have calculated := unsigned_binary_eval (a:=.reference name) (b:=.bit true) typed rfl (Nat.le_refl _)
    (show 1 ≤ w by omega) comparison notAnd lhs rhs fits unitFits computed
  unfold Expr.assignment
  simp only [Expr.type,comparison,notAndBool,Bool.false_or,Bool.false_eq_true,↓reduceIte,
    typed,IntegralType.join,Bool.false_and,Nat.max_eq_left (show 1 ≤ w by omega)]
  rw [calculated]
  simp only [bind,Option.bind,pure,Value.integer,Value.ofInt,Bool.false_eq_true,↓reduceIte,
    BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem unsigned_reference_self {n : Nat} (typed : env.type name = ⟨w,false⟩)
    (stored : env.scalar name = some (n : Int)) (fits : n < 2^w) :
    (Expr.reference name).eval env none = some (Value.ofInt ⟨w,false⟩ n) := by
  rw [Expr.eval_self,show (Expr.reference name).type env = ⟨w,false⟩ from typed]
  simpa using unsigned_reference_context typed stored fits w

theorem index_assignment {j : Nat} (address : jExpr.eval env none = some jv)
    (addressValue : jv.integer = (j : Int))
    (typed : env.type name = ⟨32,false⟩) (value : BitVec 32)
    (stored : env.cell name j = some (value.toNat : Int)) :
    (Expr.index name jExpr).assignment env 32 = some value := by
  unfold Expr.assignment
  simp only [Expr.type,typed,Expr.eval,address,bind,Option.bind,addressValue,
    show ¬(j : Int) < 0 by omega,↓reduceIte,Int.toNat_natCast,stored]
  simp only [IntegralType.context,Value.inContext,bind,Option.bind,pure,Value.ofInt,Value.integer,
    Nat.max_self,Bool.false_and,Bool.false_eq_true,↓reduceIte,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]

  rfl

theorem Statement.assign_index_value {j : Nat} {value : BitVec (env.type name).width} (address : jExpr.eval env none = some jv)
    (addressValue : jv.integer = (j : Int))
    (allocated : (env.cell name j).isSome = true)
    (rhs : valueExpr.assignment env (env.type name).width = some value) (pending : Store) :
    (Statement.assign (.index name jExpr) valueExpr).eval env pending =
      some (pending.setCell name j value.toNat) := by
  obtain ⟨old,stored⟩ := Option.isSome_iff_exists.mp allocated
  simp only [Statement.eval,Destination.write,address,bind,Option.bind,addressValue,
    show ¬(j : Int) < 0 by omega,↓reduceIte,Int.toNat_natCast,stored,rhs,pure]

theorem loop_successor_eval (env : Environment) (loopVar : Name) (inside : iteration < count) :
    (Expr.binary .add (.reference loopVar) (.integer 1)).eval (env.loop loopVar count iteration) none =
      some (Value.ofInt ⟨max (bits count) (bits 1+1),false⟩ (iteration+1)) := by
  let w := max (bits count) (bits 1+1)
  have typed : (env.loop loopVar count iteration).type loopVar = ⟨bits count,false⟩ := by simp [Environment.loop]
  have stored : (env.loop loopVar count iteration).scalar loopVar = some (iteration : Int) := by simp [Environment.loop]
  have fits : iteration < 2^bits count := Nat.lt_of_lt_of_le inside (Nat.le_of_lt (bits_fits count))
  have lhs : (Expr.reference loopVar).eval (env.loop loopVar count iteration) (some ⟨w,false⟩) =
      some (Value.ofInt ⟨w,false⟩ iteration) := by
    simpa only [Nat.max_eq_right (show bits count ≤ w from Nat.le_max_left _ _)] using unsigned_reference_context typed stored fits w
  have rhs : (Expr.integer 1).eval (env.loop loopVar count iteration) (some ⟨w,false⟩) =
      some (Value.ofInt ⟨w,false⟩ 1) := by
    simpa only [Nat.max_eq_right (show bits 1+1 ≤ w from Nat.le_max_right _ _)] using integer_unsigned_context (env:=env.loop loopVar count iteration) 1 w
  rw [Expr.eval_self]
  have resultType : (Expr.binary .add (.reference loopVar) (.integer 1)).type (env.loop loopVar count iteration) = ⟨w,false⟩ := by
    simp [Expr.type,typed,Operator.comparison,IntegralType.join,w]
  rw [resultType]
  exact unsigned_binary_eval typed rfl (Nat.le_max_left _ _) (Nat.le_max_right _ _) rfl (by decide) lhs rhs
    (Nat.lt_of_lt_of_le fits (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _)))
    (Nat.lt_of_lt_of_le (bits_fits 1) (Nat.pow_le_pow_right (by decide) (by dsimp [w]; omega))) rfl

/-- The in-place FIFO shift uses old cells for every RHS, even after a
lower-index cell has already acquired a pending nonblocking write. -/
theorem fifo_shift_correct (env : Environment) (pending : Store) (bank loopVar : Name)
    (distinct : bank ≠ loopVar) (typed : env.type bank = ⟨32,false⟩)
    (values : Nat → BitVec 32) (capacity : Nat)
    (stored : ∀ i, i < capacity → env.cell bank i = some ((values i).toNat : Int)) :
    (Statement.forRange loopVar (capacity-1)
      (.assign (.index bank (.reference loopVar))
        (.index bank (.binary .add (.reference loopVar) (.integer 1))))).eval env pending =
      some {pending with cell := fun n j =>
        if n = bank ∧ j < capacity-1 then some ((values (j+1)).toNat : Int) else pending.cell n j} := by
  have bodyCorrect (i : Nat) (hi : i < capacity-1) (writes : Store) :
      (Statement.assign (.index bank (.reference loopVar))
        (.index bank (.binary .add (.reference loopVar) (.integer 1)))).eval
          (env.loop loopVar (capacity-1) i) writes = some (writes.setCell bank i (values (i+1)).toNat) := by
    have localType : (env.loop loopVar (capacity-1) i).type bank = ⟨32,false⟩ := by simp [Environment.loop,distinct,typed]
    have successor := loop_successor_eval env loopVar hi
    have nextFits : i+1 < 2^(max (bits (capacity-1)) (bits 1+1)) := by
      have bound := bits_fits (capacity-1)
      have widen := Nat.pow_le_pow_right (n:=2) (by decide) (Nat.le_max_left (bits (capacity-1)) (bits 1+1))
      omega
    have nextValue : (Value.ofInt ⟨max (bits (capacity-1)) (bits 1+1),false⟩ ((i : Int)+1)).integer = ((i+1 : Nat) : Int) := by
      simp only [Value.integer,Value.ofInt,Bool.false_eq_true,↓reduceIte,← Int.natCast_add_one,
        BitVec.ofInt_natCast,BitVec.toNat_ofNat,Nat.mod_eq_of_lt nextFits]
    have rhs := index_assignment successor nextValue localType (values (i+1)) (stored (i+1) (by omega))
    have targetIndex := loop_reference_eval env loopVar (show i ≤ capacity-1 by omega)
    simp only [Statement.eval,Destination.write,targetIndex,bind,Option.bind,Value.integer,Value.ofInt,
      Bool.false_eq_true,↓reduceIte,BitVec.ofInt_natCast,loop_counter_fits (show i ≤ capacity-1 by omega),
      show ¬(i : Int) < 0 by omega,Int.toNat_natCast]
    have old : (env.loop loopVar (capacity-1) i).cell bank i = some ((values i).toNat : Int) := stored i (by omega)
    rw [old,localType]
    simp only [rhs,Option.bind,pure]

  rw [forRange_cells env loopVar bank (capacity-1) _ (fun i => ((values (i+1)).toNat : Int)) bodyCorrect]
  congr 1
  congr 1
  funext n j
  rw [RTL.writeRange_correct]
  by_cases hn : n = bank <;> by_cases hj : j < capacity-1 <;> simp [hn,hj]

end IRComparison.Circuit.SystemVerilog
