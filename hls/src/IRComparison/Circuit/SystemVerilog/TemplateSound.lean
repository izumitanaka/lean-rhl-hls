import IRComparison.Circuit.SystemVerilog.DivisionSound
import IRComparison.Circuit.RTL.Combinational

namespace IRComparison.Circuit.SystemVerilog

/-- A concrete expression assigned to a generated signed net. Its natural
width can differ from the destination (comparisons and small constants do). -/
structure AssignedMeaning (env : Environment) (e : Expr) (width : Nat) (value : Int) : Prop where
  assignment : e.assignment env width = some (BitVec.ofInt width value)
  fits : (BitVec.ofInt width value).toInt = value

variable {value : Int} {signal : Signal}

theorem SignedMeaning.assigned (h : SignedMeaning env e naturalWidth value)
    (fits : (BitVec.ofInt width value).toInt = value) : AssignedMeaning env e width value :=
  ⟨h.assignment width,fits⟩

theorem widen_meaning (h : SignedMeaning env (.reference signal.name) signal.width value)
    (larger : signal.width ≤ width) (positive : 0 < width) :
    SignedMeaning env (widen signal width positive) width value := by
  have preserved : (BitVec.ofInt width value).toInt = value := by
    simpa [Nat.max_eq_right larger] using h.extended width
  simpa only [widen,preserved] using h.cast positive

/-- All emitted arithmetic templates, including the concrete corrected
division tree, preserve the source operation on arbitrary signed operands. -/
theorem termTemplate_binary (a : Artifact) (op : Bin) (u v : RTL.Term) (us vs : Signal)
    (left : SignedMeaning env (.reference us.name) us.width x)
    (right : SignedMeaning env (.reference vs.name) vs.width y)
    (compiled : termTemplate a (.binary op u v) [us,vs] = .ok (rhs,width)) :
    AssignedMeaning env rhs width (hardwareBin op x y) := by
  let w := us.width+vs.width+2
  have wl := widen_meaning left (show us.width ≤ w by omega) (show 0 < w by omega)
  have wr := widen_meaning right (show vs.width ≤ w by omega) (show 0 < w by omega)
  have fits (operation : Operator) (z : Int) (computed : arithmetic operation x y = some z) :
      (BitVec.ofInt w z).toInt = z := by
    have hh := arithmetic_working_width (BitVec.ofInt us.width x) (BitVec.ofInt vs.width y)
      (op:=operation) (v:=z)
    simpa only [left.fits,right.fits] using hh (by simpa only [left.fits,right.fits] using computed)
  cases op with
  | add =>
    simp only [termTemplate] at compiled
    cases compiled
    exact (wl.binary wr (op:=.add) rfl (by decide) rfl (fits .add _ rfl)).assigned (fits .add _ rfl)
  | sub =>
    simp only [termTemplate] at compiled
    cases compiled
    exact (wl.binary wr (op:=.sub) rfl (by decide) rfl (fits .sub _ rfl)).assigned (fits .sub _ rfl)
  | mul =>
    simp only [termTemplate] at compiled
    cases compiled
    exact (wl.binary wr (op:=.mul) rfl (by decide) rfl (fits .mul _ rfl)).assigned (fits .mul _ rfl)
  | div =>
    simp only [termTemplate] at compiled
    cases compiled
    have divMeaning := division_meaning (BitVec.ofInt us.width x) (BitVec.ofInt vs.width y)
      (by simpa only [left.fits] using wl) (by simpa only [right.fits] using wr)
    simp only [left.fits,right.fits,← verilogDivision_correct] at divMeaning
    exact divMeaning.assigned divMeaning.fits
  | lt =>
    simp only [termTemplate] at compiled
    cases compiled
    have cmp := wl.comparison wr (op:=.lt) rfl (result:=decide (x < y)) (by simp [arithmetic])
    have one := SignedMeaning.integer (env:=env) 1
    have zero := SignedMeaning.integer (env:=env) 0
    change SignedMeaning env (.integer 1) 2 1 at one
    change SignedMeaning env (.integer 0) 2 0 at zero
    have h := SignedMeaning.select_bool cmp one.typed zero.typed (fun _ => one) (fun _ => zero)
    simp only [Nat.max_self,decide_eq_true_eq] at h
    apply h.assigned
    exact fits .lt _ (by simp [arithmetic,hardwareBin,Bin.eval])

theorem termTemplate_literal (a : Artifact) (n : Int)
    (compiled : termTemplate a (.literal n) [] = .ok (rhs,width)) :
    AssignedMeaning env rhs width n := by
  simp only [termTemplate] at compiled
  cases compiled
  have fits : (BitVec.ofInt (bits n.natAbs+2) n).toInt = n := by
    apply ofInt_signed_preserves (by omega)
    have := bits_fits n.natAbs
    simpa only [show bits n.natAbs+2-1 = bits n.natAbs+1 by omega,Nat.pow_succ] using
      (show n.natAbs < 2^bits n.natAbs*2 by omega)
  exact (SignedMeaning.literal (env:=env) (by omega) fits).assigned fits

theorem termTemplate_resize (a : Artifact) (v : RTL.Term) (signal : Signal)
    (input : SignedMeaning env (.reference signal.name) signal.width x)
    (compiled : termTemplate a (.resize k v) [signal] = .ok (rhs,width)) :
    AssignedMeaning env rhs width (BitVec.ofInt k x).toInt := by
  simp only [termTemplate] at compiled
  split at compiled
  · cases compiled
    exact (input.cast ‹0 < k›).assigned (by simp)
  · cases compiled

theorem termTemplate_nonnegative (a : Artifact) (v : RTL.Term) (signal : Signal)
    (input : SignedMeaning env (.reference signal.name) signal.width x)
    (compiled : termTemplate a (.nonnegative v) [signal] = .ok (rhs,width)) :
    AssignedMeaning env rhs width (x.toNat : Int) := by
  simp only [termTemplate] at compiled
  cases compiled
  have h := input.nonnegative
  apply h.assigned
  by_cases negative : x < 0
  · simp [Int.toNat_of_nonpos (by omega : x ≤ 0)]
  · simpa [Int.toNat_of_nonneg (by omega : 0 ≤ x)] using input.fits

theorem termTemplate_mux (a : Artifact) (c u v : RTL.Term) (cs us vs : Signal)
    (condition : SignedMeaning env (.reference cs.name) cs.width z)
    (left : SignedMeaning env (.reference us.name) us.width x)
    (right : SignedMeaning env (.reference vs.name) vs.width y)
    (compiled : termTemplate a (.mux c u v) [cs,us,vs] = .ok (rhs,width)) :
    AssignedMeaning env rhs width (if z != 0 then x else y) := by
  simp only [termTemplate] at compiled
  cases compiled
  have wl := widen_meaning left (Nat.le_max_left _ _) (show 0 < max us.width vs.width by have := us.positive; omega)
  have wr := widen_meaning right (Nat.le_max_right _ _) (show 0 < max us.width vs.width by have := vs.positive; omega)
  have test := condition.comparison (SignedMeaning.integer (env:=env) 0) (op:=.ne) rfl
    (result:= z != 0) (by simp [arithmetic])
  have h := SignedMeaning.select_bool test wl.typed wr.typed (fun _ => wl) (fun _ => wr)
  simp only [Nat.max_self] at h
  exact h.assigned h.fits


/-- Array contents are only needed below the live length. Unused physical
cells may contain arbitrary words, and are never inspected by this proof. -/
theorem termTemplate_cell (a : Artifact) (id size : Nat) (j : RTL.Term) (signal : Signal)
    (values : Array Int) (input : SignedMeaning env (.reference signal.name) signal.width x)
    (known : memorySize a id = .ok size)
    (length : SignedMeaning env (.unsigned (.reference (.length id))) (bits size+1) (values.size : Int))
    (memoryType : env.type (.memory id) = ⟨32,false⟩)
    (cells : ∀ k v, values[k]? = some v → env.cell (.memory id) k = some v ∧
      ((BitVec.ofInt 32 v).toNat : Int) = v)
    (compiled : termTemplate a (.cell id j) [signal] = .ok (rhs,width)) :
    AssignedMeaning env rhs width (values[x.toNat]?.getD 0) := by
  simp only [termTemplate,known,bind,Except.bind,pure,Except.pure] at compiled
  cases compiled
  have address := input.nonnegative
  have test := address.comparison length (op:=.lt) rfl
    (result:=decide (x.toNat < values.size)) (by simp only [arithmetic,Int.ofNat_lt,decide_eq_true_eq])
  have zero := SignedMeaning.integer (env:=env) 0
  change SignedMeaning env (.integer 0) 2 0 at zero
  have readType : (Expr.unsigned (.index (.memory id)
      (.select (.binary .lt (.reference signal.name) (.integer 0)) (.integer 0) (.reference signal.name)))).type env = ⟨33,true⟩ := by
    simp [Expr.type,memoryType]
  by_cases inside : x.toNat < values.size
  · have fetched : values[x.toNat]? = some values[x.toNat] := by simp [inside]
    obtain ⟨stored,fits⟩ := cells _ _ fetched
    have read := unsigned_index_meaning memoryType address (by omega) (by simpa only [Int.toNat_natCast] using stored) fits
    have h := SignedMeaning.select_true test (by simp [inside]) read zero.typed
    simp only [show max 33 2 = 33 by decide] at h
    simpa only [fetched,Option.getD_some] using h.assigned h.fits
  · have h := SignedMeaning.select_false test (by simp [inside]) readType zero
    simp only [show max 33 2 = 33 by decide] at h
    simpa [Array.getElem?_eq_none (by omega : values.size ≤ x.toNat)] using h.assigned h.fits


/-- Correspondence required only for physical reads used by this node.
This is a proof premise about the existing storage environment, not a
runtime checker or a restriction added to source syntax. -/
def PhysicalNode (a : Artifact) (r : Runtime) (env : Environment) : RTL.Term → Prop
  | .wire n => SignedMeaning env (.reference (.holding n))
      (signedWidth (a.wires[n]?.getD wordRange)) (r.wires n)
  | .register n => SignedMeaning env (.unsigned (.reference (.register n))) 33 (r.data.regs n)
  | .length n => ∀ size, memorySize a n = .ok size →
      SignedMeaning env (.unsigned (.reference (.length n))) (bits size+1) ((r.data.arrays n).size : Int)
  | .cell n _ => ∀ size, memorySize a n = .ok size →
      SignedMeaning env (.unsigned (.reference (.length n))) (bits size+1) ((r.data.arrays n).size : Int) ∧
      env.type (.memory n) = ⟨32,false⟩ ∧
      ∀ j v, (r.data.arrays n)[j]? = some v → env.cell (.memory n) j = some v ∧
        ((BitVec.ofInt 32 v).toNat : Int) = v
  | _ => True

/-- Pointwise correspondence retaining the order and length of two lists. -/
inductive Paired (relation : α → β → Prop) : List α → List β → Prop where
  | nil : Paired relation [] []
  | cons : relation a b → Paired relation as bs → Paired relation (a::as) (b::bs)

/-- One-node preservation for every term constructor of the actual emitter. -/
theorem termTemplate_correct (a : Artifact) (r : Runtime) (e : RTL.Term)
    (physical : PhysicalNode a r env e)
    (inputs : Paired (fun child signal =>
      SignedMeaning env (.reference signal.name) signal.width (child.eval r)) e.children args)
    (compiled : termTemplate a e args = .ok (rhs,width)) :
    AssignedMeaning env rhs width (e.eval r) := by
  cases e with
  | literal n =>
    cases inputs
    exact termTemplate_literal a n compiled
  | wire n =>
    cases inputs
    simp only [termTemplate] at compiled
    split at compiled
    · change Except.ok (_,_) = Except.ok (rhs,width) at compiled
      cases compiled
      exact physical.assigned physical.fits
    · simp [Functor.map,Except.map,throw] at compiled
  | register n =>
    cases inputs
    cases compiled
    exact physical.assigned physical.fits
  | length n =>
    cases inputs
    simp only [termTemplate] at compiled
    cases known : memorySize a n with
    | error why => simp [known,Functor.map,Except.map] at compiled
    | ok size =>
      simp [known,Functor.map,Except.map] at compiled
      rcases compiled with ⟨rfl,rfl⟩
      exact (physical size known).assigned (physical size known).fits
  | cell n j =>
    cases inputs with
    | cons h tail =>
      cases tail
      rename_i signal
      cases known : memorySize a n with
      | error why => simp [termTemplate,known,Functor.map,Except.map] at compiled
      | ok size =>
        obtain ⟨length,typed,cells⟩ := physical size known
        exact termTemplate_cell a n size j signal (r.data.arrays n) h known length typed cells compiled
  | resize k v =>
    cases inputs with
    | cons h tail =>
      cases tail
      exact termTemplate_resize a v _ h compiled
  | nonnegative v =>
    cases inputs with
    | cons h tail =>
      cases tail
      exact termTemplate_nonnegative a v _ h compiled
  | binary op u v =>
    cases inputs with
    | cons hu tail =>
      cases tail with
      | cons hv tail =>
        cases tail
        exact termTemplate_binary a op u v _ _ hu hv compiled
  | mux c u v =>
    cases inputs with
    | cons hc tail =>
      cases tail with
      | cons hu tail =>
        cases tail with
        | cons hv tail =>
          cases tail
          exact termTemplate_mux a c u v _ _ _ hc hu hv compiled

end IRComparison.Circuit.SystemVerilog
