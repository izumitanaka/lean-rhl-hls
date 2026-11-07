import IRComparison.Frontend.NativeWindowExpr

namespace IRComparison.AffineAddress

structure Linear where
  coefficient : Int
  offset : Int
  deriving Repr, DecidableEq

def Linear.eval (e : Linear) (i : Int) := e.coefficient*i+e.offset

def Valid (guards : List Linear) (i : Int) : Prop := ∀ g ∈ guards, 0 ≤ g.eval i

theorem valid_append : Valid (a++b) i ↔ Valid a i ∧ Valid b i := by
  simp [Valid,List.mem_append,or_imp,forall_and]

structure View (expression : Expr) where
  linear : Linear
  guards : List Linear
  correct : ∀ i x y s ls, Valid guards i → expression.eval i x y s ls = some (linear.eval i)

def parse : (expression : Expr) → Option (View expression)
  | .lit n => some ⟨⟨0,n⟩,[],by intros; simp [Expr.eval,Linear.eval]⟩
  | .index => some ⟨⟨1,0⟩,[],by intros; simp [Expr.eval,Linear.eval]⟩
  | .natIndex e => do
    let a ← parse e
    return ⟨a.linear,a.linear::a.guards,by
      intro i x y s ls h
      have hg : Valid a.guards i := by intro g hm; exact h g (by simp [hm])
      have hn : 0 ≤ a.linear.eval i := h _ (by simp)
      simp [Expr.eval,a.correct i x y s ls hg,Int.toNat_of_nonneg hn]; omega⟩
  | .add a b => do
    let aa ← parse a
    let bb ← parse b
    return ⟨⟨aa.linear.coefficient+bb.linear.coefficient,aa.linear.offset+bb.linear.offset⟩,
      aa.guards++bb.guards,by
        intro i x y s ls h
        obtain ⟨ha,hb⟩ := valid_append.mp h
        simp [Expr.eval,aa.correct i x y s ls ha,bb.correct i x y s ls hb,Linear.eval,Int.add_mul,Int.add_assoc,Int.add_comm,Int.add_left_comm]⟩
  | .sub a b => do
    let aa ← parse a
    let bb ← parse b
    return ⟨⟨aa.linear.coefficient-bb.linear.coefficient,aa.linear.offset-bb.linear.offset⟩,
      aa.guards++bb.guards,by
        intro i x y s ls h
        obtain ⟨ha,hb⟩ := valid_append.mp h
        simp [Expr.eval,aa.correct i x y s ls ha,bb.correct i x y s ls hb,Linear.eval,Int.sub_mul]
        omega⟩
  | .mul (.lit k) b => do
    let bb ← parse b
    return ⟨⟨k*bb.linear.coefficient,k*bb.linear.offset⟩,bb.guards,by
      intro i x y s ls h
      simp [Expr.eval,bb.correct i x y s ls h,Linear.eval,Int.mul_add,Int.mul_assoc]⟩
  | .mul a (.lit k) => do
    let aa ← parse a
    return ⟨⟨aa.linear.coefficient*k,aa.linear.offset*k⟩,aa.guards,by
      intro i x y s ls h
      simp [Expr.eval,aa.correct i x y s ls h,Linear.eval,Int.add_mul,Int.mul_add,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]⟩
  | .div a (.lit k) => do
    if positive : 0 < k then
      let aa ← parse a
      let upper : Linear := ⟨-aa.linear.coefficient,k-1-aa.linear.offset⟩
      return ⟨⟨0,0⟩,aa.linear::upper::aa.guards,by
        intro i x y s ls h
        have ha : Valid aa.guards i := by intro g hg; exact h g (by simp [hg])
        have lo := h aa.linear (by simp)
        have hi := h upper (by simp)
        have bound : aa.linear.eval i < k := by
          simp only [upper, Linear.eval, Int.neg_mul] at hi lo ⊢
          omega
        simp only [Expr.eval, aa.correct i x y s ls ha]
        simpa only [bind, Option.bind, pure, Pure.pure, Linear.eval, Int.zero_mul, Int.zero_add] using
          congrArg some (Int.ediv_eq_zero_of_lt lo bound)⟩
    else none
  | _ => none

/-- Endpoint bounds imply bounds at every iteration, for either stride sign. -/
theorem linear_between (a d : Int) (n k : Nat) (hk : k ≤ n) :
    min a (a+(n:Int)*d) ≤ a+(k:Int)*d ∧ a+(k:Int)*d ≤ max a (a+(n:Int)*d) := by
  by_cases hd : 0 ≤ d
  · have h₁ : 0 ≤ (k:Int)*d := Int.mul_nonneg (by omega) hd
    have h₂ : (k:Int)*d ≤ (n:Int)*d := Int.mul_le_mul_of_nonneg_right (by omega) hd
    constructor <;> omega
  · have h₁ : (k:Int)*d ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
    have h₂ : (n:Int)*d ≤ (k:Int)*d := Int.mul_le_mul_of_nonpos_right (by omega) (by omega)
    constructor <;> omega

def endpoints (g : Linear) (start stride : Int) (count : Nat) : Bool :=
  count == 0 || (0 ≤ g.eval start && 0 ≤ g.eval (start+(Int.ofNat (count-1))*stride))

theorem endpoints_sound (h : endpoints g start stride count = true) (hk : k < count) :
    0 ≤ g.eval (start+(k:Int)*stride) := by
  simp only [endpoints,Bool.or_eq_true,beq_iff_eq,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with hz | ⟨h₀,hn⟩
  · omega
  · have bounds := linear_between (g.eval start) (g.coefficient*stride) (count-1) k (by omega)
    have expand (j : Nat) : g.eval (start+(j:Int)*stride) = g.eval start+(j:Int)*(g.coefficient*stride) := by
      simp [Linear.eval,Int.mul_add,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.add_assoc,Int.add_comm,Int.add_left_comm]
    have hn' : 0 ≤ g.eval start+((count-1:Nat):Int)*(g.coefficient*stride) := by
      rw [← expand (count-1)]
      exact hn
    rw [expand]
    omega

def checkGuards (guards : List Linear) (start stride : Int) (count : Nat) : Bool :=
  guards.all (fun g => endpoints g start stride count)

theorem checkGuards_sound (h : checkGuards guards start stride count = true) (hk : k < count) :
    Valid guards (start+(k:Int)*stride) := by
  intro g hg
  exact endpoints_sound ((List.all_eq_true.mp h) g hg) hk

end IRComparison.AffineAddress
