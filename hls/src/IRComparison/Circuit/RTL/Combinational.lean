import IRComparison.Circuit.RTL.CombinationalSyntax
import IRComparison.Circuit.RTL.Semantics

namespace IRComparison.Circuit.RTL

def Term.eval (r : Runtime) : Term → Int
  | .literal n => n
  | .wire n => r.wires n
  | .register n => r.data.regs n
  | .length a => (r.data.arrays a).size
  | .cell a j => ((r.data.arrays a)[(j.eval r).toNat]?).getD 0
  | .binary op a b => hardwareBin op (a.eval r) (b.eval r)
  | .nonnegative a => (a.eval r).toNat
  | .resize w a => (BitVec.ofInt w (a.eval r)).toInt
  | .mux c a b => if c.eval r != 0 then a.eval r else b.eval r

def Validity.eval (r : Runtime) : Validity → Bool
  | .yes => true
  | .no => false
  | .and a b => a.eval r && b.eval r
  | .address a j => decide (0 ≤ j.eval r ∧ (j.eval r).toNat < (r.data.arrays a).size)
  | .mux c a b => if c.eval r != 0 then a.eval r else b.eval r

@[simp] theorem Validity.both_eval (a b : Validity) (r : Runtime) :
    (both a b).eval r = (a.eval r && b.eval r) := by
  cases a <;> cases b <;> simp [both, eval]

@[simp] theorem Validity.choose_eval (c : Term) (a b : Validity) (r : Runtime) :
    (choose c a b).eval r = (if c.eval r != 0 then a.eval r else b.eval r) := by
  cases a <;> cases b <;> simp [choose, eval]

def Combinational.eval (p : Combinational) (r : Runtime) : Option Int :=
  if p.valid.eval r then some (p.value.eval r) else none

theorem Combinational.resize_eval (p : Combinational) :
    (Combinational.mk (.resize w p.value) p.valid p.bounds).eval r =
      (p.eval r).map (fun n => (BitVec.ofInt w n).toInt) := by
  simp only [eval,Term.eval]
  split <;> rfl

theorem Combinational.success {p : Combinational} (h : p.eval r = some v) : p.valid.eval r = true ∧ p.value.eval r = v := by
  unfold eval at h
  split at h
  · exact ⟨by assumption,Option.some.inj h⟩
  · cases h

theorem Combinational.failure {p : Combinational} (h : p.eval r = none) : p.valid.eval r = false := by
  unfold eval at h
  split at h
  · cases h
  · exact Bool.eq_false_iff.mpr (by assumption)

theorem combinational_correct (wr : Nat → Interval) (e : Circuit.Expr) (r : Runtime) :
    (combinational wr e).eval r = e.bitEval wr r.data r.wires := by
  induction e with
  | fail | lit | wire | reg => rfl
  | memory a j ih =>
    cases hj : j.bitEval wr r.data r.wires with
    | none =>
      have hh := Combinational.failure (ih.trans hj)
      simp [combinational,Combinational.eval,Validity.eval,hh,Circuit.Expr.bitEval,hj]
    | some index =>
      obtain ⟨defined,value⟩ := Combinational.success (ih.trans hj)
      by_cases negative : index < 0
      · simp [combinational,Combinational.eval,Validity.eval,defined,value,Term.eval,Circuit.Expr.bitEval,hj,arrayInput,negative,show ¬0 ≤ index from by omega]
      · by_cases inside : index.toNat < (r.data.arrays a).size
        · simp [combinational,Combinational.eval,Validity.eval,defined,Term.eval,value,Circuit.Expr.bitEval,hj,arrayInput,negative,inside,show 0 ≤ index from by omega]
        · simp [combinational,Combinational.eval,Validity.eval,defined,Term.eval,value,Circuit.Expr.bitEval,hj,arrayInput,negative,inside]
  | natIndex a ih =>
    cases ha : a.bitEval wr r.data r.wires with
    | none =>
      have hh := Combinational.failure (ih.trans ha)
      simp [combinational,Combinational.eval,hh,Circuit.Expr.bitEval,ha]
    | some v =>
      obtain ⟨defined,value⟩ := Combinational.success (ih.trans ha)
      simp [combinational,Combinational.eval,defined,Term.eval,value,Circuit.Expr.bitEval,ha]
  | bin op a b ihA ihB =>
    cases ha : a.bitEval wr r.data r.wires with
    | none =>
      have hh := Combinational.failure (ihA.trans ha)
      simp [combinational,Combinational.eval,Validity.eval,hh,Circuit.Expr.bitEval,ha]
    | some x =>
      obtain ⟨da,va⟩ := Combinational.success (ihA.trans ha)
      cases hb : b.bitEval wr r.data r.wires with
      | none =>
        have hh := Combinational.failure (ihB.trans hb)
        simp [combinational,Combinational.eval,Validity.eval,da,hh,Circuit.Expr.bitEval,ha,hb]
      | some y =>
        obtain ⟨db,vb⟩ := Combinational.success (ihB.trans hb)
        simp [combinational,Combinational.eval,Validity.eval,da,db,Term.eval,va,vb,Circuit.Expr.bitEval,ha,hb]
  | seq a b ihA ihB =>
    cases ha : a.bitEval wr r.data r.wires with
    | none =>
      have hh := Combinational.failure (ihA.trans ha)
      simp [combinational,Combinational.eval,hh,Circuit.Expr.bitEval,ha]
    | some x =>
      obtain ⟨da,va⟩ := Combinational.success (ihA.trans ha)
      cases hb : b.bitEval wr r.data r.wires with
      | none =>
        have hh := Combinational.failure (ihB.trans hb)
        simp [combinational,Combinational.eval,da,hh,Circuit.Expr.bitEval,ha,hb]
      | some y =>
        obtain ⟨db,vb⟩ := Combinational.success (ihB.trans hb)
        simp [combinational,Combinational.eval,da,db,Term.eval,vb,Circuit.Expr.bitEval,ha,hb]
  | select c a b ihC ihA ihB =>
    cases hc : c.bitEval wr r.data r.wires with
    | none =>
      have hh := Combinational.failure (ihC.trans hc)
      simp [combinational,Combinational.eval,Validity.eval,hh,Circuit.Expr.bitEval,hc]
    | some cv =>
      obtain ⟨dc,vc⟩ := Combinational.success (ihC.trans hc)
      by_cases yes : cv ≠ 0
      · cases ha : a.bitEval wr r.data r.wires with
        | none =>
          have hh := Combinational.failure (ihA.trans ha)
          simp [combinational,Combinational.eval,Validity.eval,dc,vc,hh,Circuit.Expr.bitEval,hc,yes,ha]
        | some av =>
          obtain ⟨da,va⟩ := Combinational.success (ihA.trans ha)
          simp [combinational,Combinational.eval,Validity.eval,dc,vc,da,Term.eval,va,Circuit.Expr.bitEval,hc,yes,ha]
      · have zero : cv = 0 := by omega
        cases hb : b.bitEval wr r.data r.wires with
        | none =>
          have hh := Combinational.failure (ihB.trans hb)
          simp [combinational,Combinational.eval,Validity.eval,dc,vc,hh,Circuit.Expr.bitEval,hc,zero,hb]
        | some bv =>
          obtain ⟨db,vb⟩ := Combinational.success (ihB.trans hb)
          simp [combinational,Combinational.eval,Validity.eval,dc,vc,db,Term.eval,vb,Circuit.Expr.bitEval,hc,zero,hb]

end IRComparison.Circuit.RTL
