import IRComparison.Circuit.SystemVerilog.TotalSound

namespace IRComparison.Circuit.SystemVerilog

/-- One-bit predicates in the emitted code. Their type is needed when a
conditional propagates its unsigned context into the selected branch. -/
structure BooleanMeaning (env : Environment) (e : Expr) (b : Bool) : Prop where
  typed : e.type env = ⟨1,false⟩
  evaluated : e.eval env none = some (truth b)

theorem BooleanMeaning.bit (b : Bool) : BooleanMeaning env (.bit b) b := by
  refine ⟨rfl,?_⟩
  rw [Expr.eval]
  exact congrArg some (Value.inContext_self _)

theorem BooleanMeaning.and (left : BooleanMeaning env a p) (right : BooleanMeaning env b q) :
    BooleanMeaning env (.binary .and a b) (p && q) :=
  ⟨rfl,and_self left.evaluated (fun _ => right.evaluated)⟩

theorem SignedMeaning.boolean_comparison (left : SignedMeaning env a wa x) (right : SignedMeaning env b wb y)
    (comparison : op.comparison = true) (computed : arithmetic op x y = some (if result then 1 else 0)) :
    BooleanMeaning env (.binary op a b) result :=
  ⟨by simp [Expr.type,comparison],left.comparison right comparison computed⟩

theorem BooleanMeaning.select (condition : BooleanMeaning env c choice)
    (left : BooleanMeaning env a p) (right : BooleanMeaning env b q) :
    BooleanMeaning env (.select c a b) (if choice then p else q) := by
  have resultType : (Expr.select c a b).type env = ⟨1,false⟩ := by
    simp [Expr.type,left.typed,right.typed,IntegralType.join]
  refine ⟨resultType,?_⟩
  rw [Expr.eval]
  simp only [resultType,IntegralType.context_none,condition.evaluated,bind,Option.bind,truth_integer]
  have leftContext : a.eval env (some ⟨1,false⟩) = some (truth p) := by
    rw [← left.typed,← a.eval_self]
    exact left.evaluated
  have rightContext : b.eval env (some ⟨1,false⟩) = some (truth q) := by
    rw [← right.typed,← b.eval_self]
    exact right.evaluated
  cases choice <;> simpa using (show _ from by first | exact leftContext | exact rightContext)

theorem map_success (action : EmitM α) (f : α → β)
    (success : (f <$> action) before = .ok (result,after)) :
    ∃ raw, action before = .ok (raw,after) ∧ result = f raw := by
  rw [map_eq_pure_bind] at success
  obtain ⟨raw,middle,computed,returned⟩ := bind_success _ _ success
  obtain ⟨rfl,rfl⟩ := pure_success (f raw) returned
  exact ⟨raw,computed,rfl⟩

theorem return_success (action : EmitM α) (f : α → β)
    (success : (action >>= fun raw => pure (f raw)) before = .ok (result,after)) :
    ∃ raw, action before = .ok (raw,after) ∧ result = f raw :=
  map_success action f (by simpa only [map_eq_pure_bind] using success)

/-- Lookup in the final sharing table supplies the actual source value,
including when later output statements have added more declarations. -/
theorem termText_value (a : Artifact) (e : RTL.Term) (good : before.WellFormed)
    (success : termText a e before = .ok (signal,after)) (grows : after.Extends final)
    (meaning : CacheMeaning env runtime final) :
    SignedMeaning env (.reference signal.name) signal.width (e.eval runtime) := by
  have member := (termText_builds a e before good signal after success).2.2.2
  exact meaning (e,signal) (extends_cache_member grows member)

theorem finite_length_meaning (a : Artifact) (r : FiniteRuntime a.storageShape)
    (declarations : Array Wire) (values : Array Int) (inside : n < a.storageShape.memories)
    (known : memorySize a n = .ok size) :
    SignedMeaning ((environment a r declarations #[]).withTemporaries values)
      (.unsigned (.reference (.length n))) (bits size+1) ((r.decode.data.arrays n).size : Int) :=
  physicalNode_finite a r declarations values (.length n) (by simpa using inside) size known

/-- The generated two-sided address predicate has exactly the RTL validity
meaning. Negative indices remain invalid; conversion to Nat does not erase
that check. -/
theorem address_meaning {lengthValue : Nat} (input : SignedMeaning env e w j)
    (length : SignedMeaning env lenExpr lw (lengthValue : Int)) :
    BooleanMeaning env (.binary .and (.binary .ge e (.integer 0)) (.binary .lt e lenExpr))
      (decide (0 ≤ j ∧ j.toNat < lengthValue)) := by
  have zero := SignedMeaning.integer (env:=env) 0
  have lower := input.boolean_comparison zero (op:=.ge) rfl (result:=decide (0 ≤ j)) (by simp [arithmetic])
  have upper := input.boolean_comparison length (op:=.lt) rfl (result:=decide (j < (lengthValue:Int))) (by simp [arithmetic])
  have h := lower.and upper
  have eq : (decide (0 ≤ j) && decide (j < (lengthValue:Int))) = decide (0 ≤ j ∧ j.toNat < lengthValue) := by
    by_cases nonnegative : 0 ≤ j
    · have equivalent : j < (lengthValue:Int) ↔ j.toNat < lengthValue := by omega
      simp only [nonnegative,decide_true,Bool.true_and,true_and,equivalent]
    · simp [nonnegative]
  simpa only [eq] using h


/-- The actual validity-expression generator, including conditional validity,
is connected to RTL.Validity.eval using the final shared netlist values. -/
theorem validityText_correct (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) (v : RTL.Validity)
    (closed : ValidityReferences a.storageShape v) (good : before.WellFormed)
    (success : validityText a v before = .ok (expr,after)) (grows : after.Extends final)
    (meaning : CacheMeaning ((environment a r final.text #[]).withTemporaries values) r.decode final) :
    BooleanMeaning ((environment a r final.text #[]).withTemporaries values) expr (v.eval r.decode) := by
  induction v generalizing before after expr with
  | yes =>
    obtain ⟨rfl,_⟩ := pure_success (Expr.bit true) success
    exact BooleanMeaning.bit true
  | no =>
    obtain ⟨rfl,_⟩ := pure_success (Expr.bit false) success
    exact BooleanMeaning.bit false
  | and u v ihU ihV =>
    rw [validityText] at success
    obtain ⟨left,middle,first,remaining⟩ := bind_success _ _ success
    obtain ⟨right,last,rfl⟩ := map_success _ _ remaining
    obtain ⟨middleGood,_,_⟩ := preserves_validityText a u before good left middle first
    obtain ⟨_,more,_⟩ := preserves_validityText a v middle middleGood right after last
    exact (ihU closed.1 good first (more.trans grows)).and (ihV closed.2 middleGood last grows)
  | address n j =>
    rw [validityText] at success
    obtain ⟨size,middle,found,remaining⟩ := bind_success _ _ success
    obtain ⟨known,rfl⟩ := lift_success (memorySize a n) found
    obtain ⟨signal,compiled,rfl⟩ := return_success (termText a j)
      (fun js => Expr.binary .and (.binary .ge (.reference js.name) (.integer 0))
        (.binary .lt (.reference js.name) (.unsigned (.reference (.length n))))) remaining
    have input := termText_value a j good compiled grows meaning
    have length := finite_length_meaning a r final.text values closed.1 known
    exact address_meaning input length
  | mux c u v ihU ihV =>
    rw [validityText] at success
    obtain ⟨condition,middle,first,remaining⟩ := bind_success _ _ success
    obtain ⟨left,last,second,remaining⟩ := bind_success _ _ remaining
    obtain ⟨right,third,rfl⟩ := map_success _ _ remaining
    obtain ⟨middleGood,_,_⟩ := preserves_termText a c before good condition middle first
    obtain ⟨lastGood,more,_⟩ := preserves_validityText a u middle middleGood left last second
    obtain ⟨_,latest,_⟩ := preserves_validityText a v last lastGood right after third
    have conditionValue := termText_value a c good first (more.trans (latest.trans grows)) meaning
    have predicate := conditionValue.boolean_comparison (SignedMeaning.integer 0) (op:=.ne) rfl
      (result:=c.eval r.decode != 0) (by simp [arithmetic])
    exact predicate.select (ihU closed.2.1 middleGood second (latest.trans grows)) (ihV closed.2.2 lastGood third grows)

/-- Values and their validity are both those of the original combinational
RTL expression. Validity is not replaced by a successful default value. -/
theorem expression_correct (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) (e : RTL.Combinational)
    (closed : CombinationalReferences a.storageShape e) (good : before.WellFormed)
    (success : expression a e before = .ok (signal,after)) (grows : after.Extends final)
    (meaning : CacheMeaning ((environment a r final.text #[]).withTemporaries values) r.decode final) :
    SignedMeaning ((environment a r final.text #[]).withTemporaries values)
      (.reference signal.name) signal.width (e.value.eval r.decode) ∧
    BooleanMeaning ((environment a r final.text #[]).withTemporaries values) signal.valid (e.valid.eval r.decode) := by
  rw [expression] at success
  obtain ⟨data,middle,first,remaining⟩ := bind_success _ _ success
  obtain ⟨valid,last,rfl⟩ := return_success (validityText a e.valid) (fun v => {data with valid := v}) remaining
  obtain ⟨middleGood,_,_⟩ := preserves_termText a e.value before good data middle first
  obtain ⟨_,more,_⟩ := preserves_validityText a e.valid middle middleGood valid after last
  exact ⟨termText_value a e.value (signal:=data) good first (more.trans grows) meaning,
    validityText_correct a r final values e.valid closed.2 middleGood last grows meaning⟩


theorem BooleanMeaning.and_lazy (left : BooleanMeaning env a p)
    (right : p = true → BooleanMeaning env b q) : BooleanMeaning env (.binary .and a b) (p && q) :=
  ⟨rfl,and_self left.evaluated (fun h => (right h).evaluated)⟩

theorem unsigned_reference_context {n : Nat} (typed : env.type name = ⟨w,false⟩)
    (stored : env.scalar name = some (n : Int)) (fits : n < 2^w) (k : Nat) :
    (Expr.reference name).eval env (some ⟨k,false⟩) =
      some (Value.ofInt ⟨max w k,false⟩ n) := by
  rw [Expr.eval]
  simp only [Expr.type,typed,IntegralType.context,stored,bind,Option.bind,Value.inContext,Value.ofInt,
    Bool.false_and,↓reduceIte]
  rw [typed]
  simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt fits]

theorem integer_unsigned_context (n k : Nat) :
    (Expr.integer n).eval env (some ⟨k,false⟩) = some (Value.ofInt ⟨max (bits n+1) k,false⟩ n) := by
  have fits : n < 2^(bits n+1) := Nat.lt_of_lt_of_le (bits_fits n) (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Expr.eval]
  simp [Expr.type,IntegralType.context,Value.inContext,Value.ofInt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fits]

/-- Unsigned context for length/capacity comparisons. The nonnegative
integer literal keeps its value when joined with an unsigned bank counter. -/
theorem unsigned_comparison {x y : Nat} (leftType : a.type env = ⟨wa,sa⟩) (rightType : b.type env = ⟨wb,sb⟩)
    (unsigned : (sa && sb) = false) (comparison : op.comparison = true)
    (leftValue : a.eval env (some ⟨max wa wb,false⟩) = some (Value.ofInt ⟨max wa wb,false⟩ x))
    (rightValue : b.eval env (some ⟨max wa wb,false⟩) = some (Value.ofInt ⟨max wa wb,false⟩ y))
    (leftFits : x < 2^(max wa wb)) (rightFits : y < 2^(max wa wb))
    (computed : arithmetic op x y = some (if result then 1 else 0)) :
    BooleanMeaning env (.binary op a b) result := by
  have notAnd : (op == .and) = false := by cases op <;> simp_all [Operator.comparison]
  refine ⟨by simp [Expr.type,comparison],?_⟩
  rw [Expr.eval]
  simp only [Expr.type,comparison,notAnd,Bool.true_or,Bool.false_eq_true,↓reduceIte,IntegralType.context_none,
    leftType,rightType,IntegralType.join,unsigned,leftValue,rightValue,bind,Option.bind]
  simp only [Value.integer,Value.ofInt,Bool.false_eq_true,↓reduceIte,BitVec.ofInt_natCast,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt leftFits,Nat.mod_eq_of_lt rightFits,computed,bind,Option.bind]
  cases result <;> rfl

theorem count_lt_integer {n : Nat} (typed : env.type name = ⟨w,false⟩)
    (stored : env.scalar name = some (n : Int)) (fits : n < 2^w) (limit : Nat) :
    BooleanMeaning env (.binary .lt (.reference name) (.integer limit)) (decide (n < limit)) := by
  apply unsigned_comparison (a:=.reference name) (b:=.integer limit) (op:=.lt) (x:=n) (y:=limit) typed rfl rfl rfl
  · simpa only [Nat.max_eq_right (Nat.le_max_left w (bits limit+1))] using
      unsigned_reference_context typed stored fits (max w (bits limit+1))
  · simpa only [Nat.max_eq_right (Nat.le_max_right w (bits limit+1))] using
      integer_unsigned_context (env:=env) limit (max w (bits limit+1))
  · exact Nat.lt_of_lt_of_le fits (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  · exact Nat.lt_of_lt_of_le (bits_fits limit) (Nat.pow_le_pow_right (by decide) (by omega))
  · simp only [arithmetic,Int.ofNat_lt,decide_eq_true_eq]

theorem integer_lt_count {n : Nat} (typed : env.type name = ⟨w,false⟩)
    (stored : env.scalar name = some (n : Int)) (fits : n < 2^w) (limit : Nat) :
    BooleanMeaning env (.binary .lt (.integer limit) (.reference name)) (decide (limit < n)) := by
  apply unsigned_comparison (a:=.integer limit) (b:=.reference name) (op:=.lt) (x:=limit) (y:=n) rfl typed rfl rfl
  · simpa only [Nat.max_eq_right (Nat.le_max_left (bits limit+1) w)] using
      integer_unsigned_context (env:=env) limit (max (bits limit+1) w)
  · simpa only [Nat.max_eq_right (Nat.le_max_right (bits limit+1) w)] using
      unsigned_reference_context typed stored fits (max (bits limit+1) w)
  · exact Nat.lt_of_lt_of_le (bits_fits limit) (Nat.pow_le_pow_right (by decide) (by omega))
  · exact Nat.lt_of_lt_of_le fits (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  · simp only [arithmetic,Int.ofNat_lt,decide_eq_true_eq]

end IRComparison.Circuit.SystemVerilog
