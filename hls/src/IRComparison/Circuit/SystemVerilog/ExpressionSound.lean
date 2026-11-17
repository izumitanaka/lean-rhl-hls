import IRComparison.Circuit.SystemVerilog.Arithmetic

namespace IRComparison.Circuit.SystemVerilog

theorem signed_widen (v : BitVec w) (positive : 0 < w) (larger : w ≤ k) :
    (BitVec.ofInt k v.toInt).toInt = v.toInt := by
  have lo := BitVec.le_toInt v
  have hi := BitVec.toInt_lt (x:=v)
  have pn : 2^(w-1) ≤ 2^(k-1) := Nat.pow_le_pow_right (by decide) (by omega)
  have pi : ((2^(w-1) : Nat) : Int) ≤ ((2^(k-1) : Nat) : Int) := by omega
  simp only [Int.natCast_pow] at pi
  change (2:Int)^(w-1) ≤ (2:Int)^(k-1) at pi
  exact BitVec.toInt_ofInt_eq_self (by omega) (by omega) (by omega)

theorem signed_reference_eval (env : Environment) (name : Name)
    (declared : env.type name = ⟨w,true⟩) (stored : env.scalar name = some v)
    (fits : (BitVec.ofInt w v).toInt = v) (contextWidth : Nat) :
    (Expr.reference name).eval env (some ⟨contextWidth,true⟩) =
      some (Value.ofInt ⟨max w contextWidth,true⟩ v) := by
  have width : (env.type name).width = w := congrArg IntegralType.width declared
  simp_all [Expr.eval,Expr.type,IntegralType.context,Value.inContext,Value.ofInt,BitVec.toInt_ofInt]
  rw [declared]

theorem signed_reference_self (env : Environment) (name : Name)
    (declared : env.type name = ⟨w,true⟩) (stored : env.scalar name = some v)
    (fits : (BitVec.ofInt w v).toInt = v) :
    (Expr.reference name).eval env none = some (Value.ofInt ⟨w,true⟩ v) := by
  have width : (env.type name).width = w := congrArg IntegralType.width declared
  simp_all [Expr.eval,Expr.type,IntegralType.context,Value.inContext,Value.ofInt,BitVec.toInt_ofInt]
  rw [declared]

theorem cast_reference_eval (env : Environment) (name : Name)
    (declared : env.type name = ⟨w,true⟩) (stored : env.scalar name = some v)
    (fits : (BitVec.ofInt w v).toInt = v) (positive : 0 < w)
    (castWidth contextWidth : Nat) (castPositive : 0 < castWidth) :
    (Expr.cast castWidth (.reference name) castPositive).eval env (some ⟨contextWidth,true⟩) =
      some (Value.ofInt ⟨max castWidth contextWidth,true⟩ (BitVec.ofInt castWidth v).toInt) := by
  have extended : (BitVec.ofInt (max w castWidth) v).toInt = v := by
    have h := signed_widen (BitVec.ofInt w v) positive (Nat.le_max_left w castWidth)
    simpa only [fits] using h
  rw [Expr.eval]
  simp only [Expr.type,declared,IntegralType.context]
  rw [signed_reference_eval env name declared stored fits castWidth]
  simp [Value.integer,Value.inContext,Value.ofInt,extended]

theorem literal_eval (positive : 0 < w) (fits : (BitVec.ofInt w v).toInt = v) (contextWidth : Nat) :
    (Expr.literal w v positive).eval env (some ⟨contextWidth,true⟩) =
      some (Value.ofInt ⟨max w contextWidth,true⟩ v) := by
  simp [Expr.eval,Expr.type,IntegralType.context,Value.inContext,Value.ofInt,fits]

/-- The decimal digits printed for a signed literal encode exactly the
original bit pattern, including negative integers and truncation. -/
theorem literal_printed_bits (w : Nat) (n : Int) :
    Value.ofInt ⟨w,true⟩ (BitVec.ofInt w n).toNat = Value.ofInt ⟨w,true⟩ n := by
  simp only [Value.ofInt,BitVec.ofInt_natCast,BitVec.ofNat_toNat]
  simp

/-- A native arithmetic expression whose operands have already been widened.
The result remains a bitvector; `arithmetic_working_width` establishes when
its signed interpretation equals the mathematical operation. -/
theorem binary_eval (env : Environment) (left right : Expr)
    (leftType : left.type env = ⟨w,true⟩) (rightType : right.type env = ⟨w,true⟩)
    (notComparison : op.comparison = false) (notAnd : op ≠ .and)
    (leftValue : left.eval env (some ⟨w,true⟩) = some (Value.ofInt ⟨w,true⟩ a))
    (rightValue : right.eval env (some ⟨w,true⟩) = some (Value.ofInt ⟨w,true⟩ b))
    (leftFits : (BitVec.ofInt w a).toInt = a) (rightFits : (BitVec.ofInt w b).toInt = b) :
    (Expr.binary op left right).eval env (some ⟨w,true⟩) =
      (arithmetic op a b).map (Value.ofInt ⟨w,true⟩) := by
  have notAndBool : (op == .and) = false := by simp [notAnd]
  rw [Expr.eval]
  simp only [Expr.type,notComparison,notAndBool,Bool.false_or,Bool.false_eq_true,ite_false,
    leftType,rightType,IntegralType.join,IntegralType.context,Nat.max_self,Bool.true_and,
    leftValue,rightValue,bind,Option.bind,Value.integer,Value.ofInt,ite_true,leftFits,rightFits]
  cases hresult : arithmetic op a b <;> simp_all [IntegralType.join,IntegralType.context]
  cases op <;> simp_all [Operator.comparison, IntegralType.join, IntegralType.context]
  all_goals
    rw [leftType,rightType]
    change Value.ofInt ⟨max (max w w) w,true⟩ _ = _
    rw [Nat.max_self, Nat.max_self]

theorem widened_binary_eval (env : Environment) (left right : Name)
    (a : BitVec wa) (b : BitVec wb) (leftPositive : 0 < wa) (rightPositive : 0 < wb)
    (leftType : env.type left = ⟨wa,true⟩) (rightType : env.type right = ⟨wb,true⟩)
    (leftStored : env.scalar left = some a.toInt) (rightStored : env.scalar right = some b.toInt)
    (notComparison : op.comparison = false) (notAnd : op ≠ .and) :
    let w := wa+wb+2
    (Expr.binary op (.cast w (.reference left) (by omega)) (.cast w (.reference right) (by omega))).eval env
      (some ⟨w,true⟩) = (arithmetic op a.toInt b.toInt).map (Value.ofInt ⟨w,true⟩) := by
  let w := wa+wb+2
  have leftFits := signed_widen a leftPositive (show wa ≤ w by omega)
  have rightFits := signed_widen b rightPositive (show wb ≤ w by omega)
  apply binary_eval env _ _ (by rfl) (by rfl) notComparison notAnd
  · simpa [w,leftFits] using cast_reference_eval env left leftType leftStored
      (by simp) leftPositive w w (by omega)
  · simpa [w,rightFits] using cast_reference_eval env right rightType rightStored
      (by simp) rightPositive w w (by omega)
  · exact leftFits
  · exact rightFits

/-- The exact widening pattern used by the emitter implements mathematical
native arithmetic without overflowing before the explicit destination resize.
This holds for every operand bit pattern, not only the regression inputs. -/
theorem widened_binary_correct (env : Environment) (left right : Name)
    (a : BitVec wa) (b : BitVec wb) (leftPositive : 0 < wa) (rightPositive : 0 < wb)
    (leftType : env.type left = ⟨wa,true⟩) (rightType : env.type right = ⟨wb,true⟩)
    (leftStored : env.scalar left = some a.toInt) (rightStored : env.scalar right = some b.toInt)
    (notComparison : op.comparison = false) (notAnd : op ≠ .and) :
    let w := wa+wb+2
    ((Expr.binary op (.cast w (.reference left) (by omega)) (.cast w (.reference right) (by omega))).eval env
      (some ⟨w,true⟩)).map Value.integer = arithmetic op a.toInt b.toInt := by
  dsimp only
  rw [widened_binary_eval env left right a b leftPositive rightPositive leftType rightType leftStored rightStored notComparison notAnd]
  cases result : arithmetic op a.toInt b.toInt with
  | none => rfl
  | some value =>
    simp only [Option.map_some]
    exact congrArg some (arithmetic_working_width a b result)

@[simp] theorem IntegralType.context_none (t : IntegralType) : t.context none = t := rfl
@[simp] theorem IntegralType.context_self (t : IntegralType) : t.context (some t) = t := by
  cases t
  simp [context]

theorem Expr.eval_self (e : Expr) : e.eval env none = e.eval env (some (e.type env)) := by
  rw [Expr.eval.eq_def,Expr.eval.eq_def]
  simp only [IntegralType.context_none,IntegralType.context_self]

/-- Compositional contract for a signed expression: the value survives every
signed width context, not just the declaration immediately receiving it. -/
structure SignedMeaning (env : Environment) (e : Expr) (width : Nat) (value : Int) : Prop where
  positive : 0 < width
  typed : e.type env = ⟨width,true⟩
  fits : (BitVec.ofInt width value).toInt = value
  contexts : ∀ contextWidth, e.eval env (some ⟨contextWidth,true⟩) =
    some (Value.ofInt ⟨max width contextWidth,true⟩ value)

variable {env : Environment} {e : Expr} {width : Nat} {value : Int}

theorem SignedMeaning.extended (h : SignedMeaning env e width value) (k : Nat) :
    (BitVec.ofInt (max width k) value).toInt = value := by
  simpa only [h.fits] using signed_widen (BitVec.ofInt width value) h.positive (Nat.le_max_left width k)

theorem SignedMeaning.self (h : SignedMeaning env e width value) :
    e.eval env none = some (Value.ofInt ⟨width,true⟩ value) := by
  rw [e.eval_self,h.typed]
  simpa using h.contexts width

/-- Destination truncation happens after evaluating the mathematical signed
value; the destination itself may be unsigned. -/
theorem SignedMeaning.assignment (h : SignedMeaning env e width value) (destinationWidth : Nat) :
    e.assignment env destinationWidth = some (BitVec.ofInt destinationWidth value) := by
  unfold Expr.assignment
  rw [h.typed]
  rw [h.contexts destinationWidth]
  simp [Value.integer,Value.ofInt,h.extended destinationWidth]

theorem SignedMeaning.reference (env : Environment) (name : Name) (positive : 0 < width)
    (typed : env.type name = ⟨width,true⟩) (stored : env.scalar name = some value)
    (fits : (BitVec.ofInt width value).toInt = value) :
    SignedMeaning env (.reference name) width value :=
  ⟨positive,typed,fits,fun k => signed_reference_eval env name typed stored fits k⟩

theorem SignedMeaning.literal (positive : 0 < width)
    (fits : (BitVec.ofInt width value).toInt = value) :
    SignedMeaning env (.literal width value positive) width value :=
  ⟨positive,rfl,fits,fun k => literal_eval positive fits k⟩

theorem SignedMeaning.cast (h : SignedMeaning env e width value) (positive : 0 < newWidth) :
    SignedMeaning env (.cast newWidth e positive) newWidth (BitVec.ofInt newWidth value).toInt := by
  refine ⟨positive,rfl,by simp,?_⟩
  intro k
  rw [Expr.eval]
  simp only [Expr.type,h.typed,IntegralType.context]
  rw [h.contexts newWidth]
  simp [Value.integer,Value.ofInt,Value.inContext,h.extended newWidth]

theorem SignedMeaning.binary (left : SignedMeaning env a width x) (right : SignedMeaning env b width y)
    (notComparison : op.comparison = false) (notAnd : op ≠ .and)
    (computed : arithmetic op x y = some value) (fits : (BitVec.ofInt width value).toInt = value) :
    SignedMeaning env (.binary op a b) width value := by
  have notAndBool : (op == .and) = false := by simp [notAnd]
  have resultType : (Expr.binary op a b).type env = ⟨width,true⟩ := by
    simp [Expr.type,left.typed,right.typed,notComparison,notAnd,IntegralType.join]
  refine ⟨left.positive,resultType,fits,?_⟩
  intro k
  rw [Expr.eval]
  simp only [resultType,IntegralType.context,notAndBool,notComparison,Bool.false_eq_true,↓reduceIte]
  rw [left.contexts,right.contexts]
  simp [Value.integer,Value.ofInt,left.extended (max width k),right.extended (max width k),computed]


theorem SignedMeaning.integer (n : Nat) :
    SignedMeaning env (.integer n) (bits n+1) (n : Int) := by
  have fits : (BitVec.ofInt (bits n+1) (n : Int)).toInt = n := by
    exact ofInt_signed_preserves (by omega) (by simpa using bits_fits n)
  refine ⟨by omega,rfl,fits,?_⟩
  intro k
  simpa only [Expr.eval,Expr.type] using (literal_eval (env:=env) (by omega : 0 < bits n+1) fits k)

@[simp] theorem truth_integer (b : Bool) : (truth b).integer = if b then 1 else 0 := by
  cases b <;> decide

/-- Comparisons determine operand widths independently of the outer context. -/
theorem SignedMeaning.comparison (left : SignedMeaning env a wa x) (right : SignedMeaning env b wb y)
    (comparison : op.comparison = true) (computed : arithmetic op x y = some (if result then 1 else 0)) :
    (Expr.binary op a b).eval env none = some (truth result) := by
  have notAnd : (op == .and) = false := by cases op <;> simp_all [Operator.comparison]
  rw [Expr.eval]
  simp only [Expr.type,comparison,notAnd,Bool.true_or,↓reduceIte,IntegralType.context_none,
    left.typed,right.typed,IntegralType.join,Bool.true_and]
  rw [left.contexts,right.contexts]
  simp [Value.integer,Value.ofInt,left.extended (max wa wb),right.extended (max wa wb),computed,
    Value.inContext,truth]
  cases result <;> rfl

theorem and_self (left : a.eval env none = some (truth p))
    (right : p = true → b.eval env none = some (truth q)) :
    (Expr.binary .and a b).eval env none = some (truth (p && q)) := by
  rw [Expr.eval]
  simp only [Expr.type,Operator.comparison,BEq.rfl,Bool.false_or,↓reduceIte,
    IntegralType.context_none,left,bind,Option.bind,truth_integer]
  cases p <;> simp [right,truth,Value.inContext,Value.ofInt]
  cases q <;> decide

/-- Only the selected branch must evaluate. This is essential for the
zero-divisor guard in the emitted division expression. -/
theorem SignedMeaning.select_true (condition : c.eval env none = some v) (taken : v.integer ≠ 0)
    (left : SignedMeaning env a wa x) (rightType : b.type env = ⟨wb,true⟩) :
    SignedMeaning env (.select c a b) (max wa wb) x := by
  have resultType : (Expr.select c a b).type env = ⟨max wa wb,true⟩ := by
    simp [Expr.type,left.typed,rightType,IntegralType.join]
  refine ⟨by have := left.positive; omega,resultType,left.extended wb,?_⟩
  intro k
  have branch : (v.integer != 0) = true := by simp [taken]
  rw [Expr.eval]
  simp only [resultType,IntegralType.context,condition,bind,Option.bind,branch,↓reduceIte]
  rw [left.contexts]
  rw [show max wa (max (max wa wb) k) = max (max wa wb) k by omega]

theorem SignedMeaning.select_false (condition : c.eval env none = some v) (taken : v.integer = 0)
    (leftType : a.type env = ⟨wa,true⟩) (right : SignedMeaning env b wb y) :
    SignedMeaning env (.select c a b) (max wa wb) y := by
  have resultType : (Expr.select c a b).type env = ⟨max wa wb,true⟩ := by
    simp [Expr.type,leftType,right.typed,IntegralType.join]
  refine ⟨by have := right.positive; omega,resultType,?_,?_⟩
  · simpa [Nat.max_comm] using right.extended wa
  · intro k
    rw [Expr.eval]
    simp only [resultType,IntegralType.context,condition,bind,Option.bind,taken,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
    rw [right.contexts]
    rw [show max wb (max (max wa wb) k) = max (max wa wb) k by omega]

/-- Native arithmetic with unequal natural widths; the signed join is the
same one that the concrete evaluator propagates into both operands. -/
theorem SignedMeaning.binary_join (left : SignedMeaning env a wa x) (right : SignedMeaning env b wb y)
    (notComparison : op.comparison = false) (notAnd : op ≠ .and)
    (computed : arithmetic op x y = some value)
    (fits : (BitVec.ofInt (max wa wb) value).toInt = value) :
    SignedMeaning env (.binary op a b) (max wa wb) value := by
  have notAndBool : (op == .and) = false := by simp [notAnd]
  have resultType : (Expr.binary op a b).type env = ⟨max wa wb,true⟩ := by
    simp [Expr.type,left.typed,right.typed,notComparison,notAnd,IntegralType.join]
  refine ⟨by have := left.positive; omega,resultType,fits,?_⟩
  intro k
  rw [Expr.eval]
  simp only [resultType,IntegralType.context,notAndBool,notComparison,Bool.false_eq_true,↓reduceIte]
  rw [left.contexts,right.contexts]
  simp [Value.integer,Value.ofInt,left.extended (max (max wa wb) k),
    right.extended (max (max wa wb) k),computed]


theorem SignedMeaning.select_bool (condition : c.eval env none = some (truth choice))
    (leftType : a.type env = ⟨wa,true⟩) (rightType : b.type env = ⟨wb,true⟩)
    (left : choice = true → SignedMeaning env a wa x)
    (right : choice = false → SignedMeaning env b wb y) :
    SignedMeaning env (.select c a b) (max wa wb) (if choice then x else y) := by
  cases choice with
  | true => exact select_true condition (by decide) (left rfl) rightType
  | false => exact select_false condition (by decide) leftType (right rfl)


theorem Value.inContext_self (v : Value) : v.inContext v.type = v := by
  obtain ⟨⟨width,signed⟩,b⟩ := v
  cases signed <;> simp [Value.inContext,Value.ofInt]

/-- `$signed({1'b0, e})` exposes the unsigned bit pattern as a nonnegative
signed value, with the extra bit preventing a change of sign. -/
theorem unsigned_meaning (typed : e.type env = ⟨w,signed⟩)
    (evaluated : e.eval env none = some (Value.ofInt ⟨w,signed⟩ n)) :
    SignedMeaning env (.unsigned e) (w+1) ((BitVec.ofInt w n).toNat : Int) := by
  have fits : (BitVec.ofInt (w+1) ((BitVec.ofInt w n).toNat : Int)).toInt = (BitVec.ofInt w n).toNat :=
    ofInt_signed_preserves (by omega) (by simpa only [Int.natAbs_natCast,Nat.add_sub_cancel] using (BitVec.ofInt w n).isLt)
  refine ⟨by omega,by simp [Expr.type,typed],fits,?_⟩
  intro k
  have resultType : (Expr.unsigned e).type env = ⟨w+1,true⟩ := by simp [Expr.type,typed]
  rw [Expr.eval]
  simp only [resultType,IntegralType.context,evaluated,bind,Option.bind,
    Value.ofInt,Value.inContext,Bool.true_and,↓reduceIte]
  rw [resultType]
  change some (Value.ofInt ⟨max (w+1) k,true⟩ (BitVec.ofInt (w+1) ((BitVec.ofInt w n).toNat : Int)).toInt) = _
  rw [fits]
  rfl

theorem unsigned_reference_meaning (typed : env.type name = ⟨w,false⟩)
    (stored : env.scalar name = some n)
    (fits : ((BitVec.ofInt w n).toNat : Int) = n) :
    SignedMeaning env (.unsigned (.reference name)) (w+1) n := by
  have evaluation : (Expr.reference name).eval env none = some (Value.ofInt ⟨w,false⟩ n) := by
    rw [Expr.eval]
    simp only [Expr.type,typed,IntegralType.context_none,stored,bind,Option.bind]
    exact congrArg some (Value.inContext_self _)
  simpa only [fits] using unsigned_meaning (e:=.reference name) typed evaluation

theorem unsigned_index_meaning (typed : env.type name = ⟨w,false⟩)
    (address : SignedMeaning env jExpr jw j) (nonnegative : 0 ≤ j)
    (stored : env.cell name j.toNat = some n)
    (fits : ((BitVec.ofInt w n).toNat : Int) = n) :
    SignedMeaning env (.unsigned (.index name jExpr)) (w+1) n := by
  have evaluation : (Expr.index name jExpr).eval env none = some (Value.ofInt ⟨w,false⟩ n) := by
    rw [Expr.eval]
    simp only [Expr.type,typed,IntegralType.context_none,address.self,bind,Option.bind,
      Value.integer,Value.ofInt,↓reduceIte,address.fits,show ¬ j < 0 by omega,stored]
    rw [typed]
    exact congrArg some (Value.inContext_self _)
  simpa only [fits] using unsigned_meaning (e:=.index name jExpr) typed evaluation


theorem SignedMeaning.nonnegative (input : SignedMeaning env e w x) :
    SignedMeaning env (.select (.binary .lt e (.integer 0)) (.integer 0) e)
      (max 2 w) (x.toNat : Int) := by
  have zero := SignedMeaning.integer (env:=env) 0
  change SignedMeaning env (.integer 0) 2 0 at zero
  have test := input.comparison zero (op:=.lt) rfl (result:=decide (x < 0)) (by simp [arithmetic])
  have h := SignedMeaning.select_bool test zero.typed input.typed (fun _ => zero) (fun _ => input)
  have valueEq : (if decide (x < 0) then (0 : Int) else x) = x.toNat := by
    split <;> rename_i h <;> simp_all <;> omega
  simpa only [valueEq] using h

end IRComparison.Circuit.SystemVerilog
