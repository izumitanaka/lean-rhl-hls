import IRComparison.Memory.CompactSequence
import IRComparison.Memory.SymbolicWindowSchedule
import IRComparison.Memory.WindowFIFO

namespace IRComparison.CompactRouting
open AffineAddress CompactSequence

theorem entries_get (n count : Nat) (h : n < count) (first step : Int) :
    (PaperCore.IndexSequence.entries first step count)[n]? = some (first+(n:Int)*step) := by
  induction n generalizing count first with
  | zero => cases count <;> simp_all [PaperCore.IndexSequence.entries]
  | succ n ih =>
    cases count with
    | zero => omega
    | succ count =>
      rw [PaperCore.IndexSequence.entries,List.getElem?_cons_succ,ih count (by omega)]
      congr 1 <;> simp [Nat.add_sub_add_right,Int.natCast_add,Int.add_mul,Int.add_assoc,Int.add_comm,Int.add_left_comm]

theorem entries_drop (n count : Nat) (h : n ≤ count) (first step : Int) :
    (PaperCore.IndexSequence.entries first step count).drop n =
      PaperCore.IndexSequence.entries (first+(n:Int)*step) step (count-n) := by
  induction n generalizing count first with
  | zero => simp
  | succ n ih =>
    cases count with
    | zero => omega
    | succ count =>
      rw [PaperCore.IndexSequence.entries,List.drop_succ_cons,ih count (by omega)]
      congr 1 <;> simp [Nat.add_sub_add_right,Int.natCast_add,Int.add_mul,Int.add_assoc,Int.add_comm,Int.add_left_comm]

@[simp] theorem literal_eval (v i : Int) : (Linear.mk 0 v).eval i = v := by simp [Linear.eval]

def plus (a b : Linear) : Linear := ⟨a.coefficient+b.coefficient,a.offset+b.offset⟩
def minus (a b : Linear) : Linear := ⟨a.coefficient-b.coefficient,a.offset-b.offset⟩
def scale (k : Int) (a : Linear) : Linear := ⟨k*a.coefficient,k*a.offset⟩
@[simp] theorem plus_eval : (plus a b).eval i = a.eval i+b.eval i := by
  simp [plus,Linear.eval,Int.add_mul,Int.add_assoc,Int.add_comm,Int.add_left_comm]
@[simp] theorem minus_eval : (minus a b).eval i = a.eval i-b.eval i := by
  simp [minus,Linear.eval,Int.sub_mul,Int.sub_eq_add_neg,Int.add_mul,Int.neg_mul,Int.neg_add,Int.add_assoc,Int.add_comm,Int.add_left_comm]
@[simp] theorem scale_eval : (scale k a).eval i = k*a.eval i := by simp [scale,Linear.eval,Int.mul_add,Int.mul_assoc]

structure Sequence where
  first : Linear
  step : Int
  count : Linear
  deriving Repr, DecidableEq

def Sequence.at (s : Sequence) (i : Int) : Seq := ⟨s.first.eval i,s.step,(s.count.eval i).toNat⟩

def advance (s : Sequence) (discard : Linear) : Sequence :=
  let consumed := plus discard ⟨0,1⟩
  ⟨plus s.first (scale s.step consumed),s.step,minus s.count consumed⟩

inductive Load where
  | saved (slot : Nat)
  | take (discard : Linear)
  deriving Repr, DecidableEq

def instantiate (i : Int) : List Load → List WindowFIFO.Load :=
  List.map (fun l => match l with | .saved n => .saved n | .take n => .take (n.eval i).toNat)

structure Route (source : List SymbolicWindowSchedule.Load) (before : Sequence) where
  code : List Load
  after : Sequence
  guards : List Linear
  correct : ∀ i, Valid guards i → ∀ input old q,
    CommunicationIR.Corresponds input (before.at i).entries q →
    (WindowFIFO.execute input old (instantiate i code) q).map Prod.fst = SymbolicWindowSchedule.execute input i old source ∧
    ∀ vs tail, WindowFIFO.execute input old (instantiate i code) q = some (vs,tail) →
      CommunicationIR.Corresponds input (after.at i).entries tail

def limit (before : Sequence) (discard : Linear) : Linear :=
  minus (minus before.count discard) ⟨0,1⟩

theorem take_valid (before : Sequence) (discard address : Linear)
    (same : plus before.first (scale before.step discard) = address)
    (nonneg : 0 ≤ discard.eval i) (bound : 0 ≤ (limit before discard).eval i)
    (hq : CommunicationIR.Corresponds input (before.at i).entries q) :
    ∃ v, q[(discard.eval i).toNat]? = some v ∧ input (address.eval i) = some v ∧
      CommunicationIR.Corresponds input ((advance before discard).at i).entries
        (q.drop ((discard.eval i).toNat+1)) := by
  have bound' : 0 ≤ before.count.eval i - discard.eval i - 1 := by
    simpa only [limit,minus_eval,literal_eval] using bound
  have hc : (discard.eval i).toNat < (before.at i).count := by
    change (discard.eval i).toNat < (before.count.eval i).toNat
    omega
  have addressEq : (before.at i).first + ((discard.eval i).toNat:Int)*(before.at i).step = address.eval i := by
    have h := congrArg (fun a : Linear => a.eval i) same
    simp only [plus_eval,scale_eval] at h
    simpa only [Sequence.at,Int.toNat_of_nonneg nonneg,Int.mul_comm] using h
  have found : (before.at i).entries[(discard.eval i).toNat]? = some (address.eval i) := by
    rw [Seq.entries,entries_get _ _ hc,addressEq]
  obtain ⟨v,hv,hi,rest⟩ := WindowFIFO.Corresponds.at_drop hq found
  refine ⟨v,hv,hi,?_⟩
  have tailEq : ((advance before discard).at i).entries =
      (before.at i).entries.drop ((discard.eval i).toNat+1) := by
    rw [Seq.entries,Seq.entries,entries_drop _ _ (by omega)]
    have firstEq : ((advance before discard).at i).first =
        (before.at i).first + (((discard.eval i).toNat+1:Nat):Int) * (before.at i).step := by
      change (plus before.first (scale before.step (plus discard ⟨0,1⟩))).eval i =
        before.first.eval i + (((discard.eval i).toNat+1:Nat):Int)*before.step
      simp only [plus_eval,scale_eval]
      rw [Int.natCast_add,Int.natCast_one,Int.toNat_of_nonneg nonneg]
      simp only [Linear.eval,Int.zero_mul,Int.zero_add]
      rw [Int.mul_comm before.step]
    have countEq : ((advance before discard).at i).count =
        (before.at i).count - ((discard.eval i).toNat+1) := by
      change ((minus before.count (plus discard ⟨0,1⟩)).eval i).toNat =
        (before.count.eval i).toNat - ((discard.eval i).toNat+1)
      simp only [minus_eval,plus_eval,literal_eval]
      change (before.count.eval i - (discard.eval i + 1)).toNat = _
      omega
    rw [firstEq,countEq]
    rfl
  rw [tailEq]
  exact rest

def saved (tail : Route rest before) (slot : Nat) : Route (.saved slot::rest) before where
  code := .saved slot::tail.code
  after := tail.after
  guards := tail.guards
  correct := by
    intro i valid input old q hq
    obtain ⟨same,suffix⟩ := tail.correct i valid input old q hq
    cases hv : old[slot]? with
    | none => simp [instantiate,WindowFIFO.execute,WindowFIFO.Load.eval,SymbolicWindowSchedule.execute,SymbolicWindowSchedule.Load.eval,hv]
    | some v =>
      cases ht : WindowFIFO.execute input old (instantiate i tail.code) q with
      | none =>
        simp only [instantiate,List.map_cons] at ht same ⊢
        simp [WindowFIFO.execute,WindowFIFO.Load.eval,SymbolicWindowSchedule.execute,SymbolicWindowSchedule.Load.eval,hv,← same,ht]
      | some pair =>
        obtain ⟨vs,qs⟩ := pair
        constructor
        · simp only [instantiate,List.map_cons] at ht same ⊢
          simp [WindowFIFO.execute,WindowFIFO.Load.eval,SymbolicWindowSchedule.execute,SymbolicWindowSchedule.Load.eval,hv,← same,ht]
        · intro out qs' h
          simp only [instantiate,List.map_cons] at ht h
          simp [WindowFIFO.execute,WindowFIFO.Load.eval,hv,ht] at h
          obtain ⟨rfl,rfl⟩ := h
          exact suffix vs qs ht

def take (discard address : Linear) (same : plus before.first (scale before.step discard) = address)
    (tail : Route rest (advance before discard)) : Route (.memory address::rest) before where
  code := .take discard::tail.code
  after := tail.after
  guards := discard::limit before discard::tail.guards
  correct := by
    intro i valid input old q hq
    have nonneg := valid discard (by simp)
    have bound := valid (limit before discard) (by simp)
    have htvalid : Valid tail.guards i := fun g hg => valid g (by simp [hg])
    obtain ⟨v,hv,hi,rest⟩ := take_valid before discard address same nonneg bound hq
    obtain ⟨eq,suffix⟩ := tail.correct i htvalid input old (q.drop ((discard.eval i).toNat+1)) rest
    cases ht : WindowFIFO.execute input old (instantiate i tail.code) (q.drop ((discard.eval i).toNat+1)) with
    | none =>
      simp only [instantiate,List.map_cons] at ht eq ⊢
      simp [WindowFIFO.execute,WindowFIFO.Load.eval,SymbolicWindowSchedule.execute,SymbolicWindowSchedule.Load.eval,hv,hi,← eq,ht]
    | some pair =>
      obtain ⟨vs,qs⟩ := pair
      constructor
      · simp only [instantiate,List.map_cons] at ht eq ⊢
        simp [WindowFIFO.execute,WindowFIFO.Load.eval,SymbolicWindowSchedule.execute,SymbolicWindowSchedule.Load.eval,hv,hi,← eq,ht]
      · intro out qs' h
        simp only [instantiate,List.map_cons] at ht h
        simp [WindowFIFO.execute,WindowFIFO.Load.eval,hv,ht] at h
        obtain ⟨rfl,rfl⟩ := h
        exact suffix vs qs ht

/-- Integer division only proposes an affine discard count. Exact address
    equality and nonnegative/count guards independently validate it. -/
def compile : (source : List SymbolicWindowSchedule.Load) → (before : Sequence) → Option (Route source before)
  | [],before => some ⟨[],before,[],by intro i h input old q hq; exact ⟨rfl,by intro vs qs eq; cases eq; exact hq⟩⟩
  | .saved n::rest,before => do return saved (← compile rest before) n
  | .memory address::rest,before => do
    let delta := minus address before.first
    let discard : Linear := ⟨delta.coefficient / before.step,delta.offset / before.step⟩
    if same : plus before.first (scale before.step discard) = address then
      return take discard address same (← compile rest (advance before discard))
    else none

def shiftLinear (a : Linear) (delta : Int) : Linear := ⟨a.coefficient,a.offset+a.coefficient*delta⟩
theorem shiftLinear_eval : (shiftLinear a delta).eval i = a.eval (i+delta) := by
  simp [shiftLinear,Linear.eval,Int.mul_add,Int.add_assoc,Int.add_comm,Int.add_left_comm]
def shift (s : Sequence) (delta : Int) : Sequence := ⟨shiftLinear s.first delta,s.step,shiftLinear s.count delta⟩
theorem shift_at : (shift s delta).at i = s.at (i+delta) := by
  simp only [shift,Sequence.at,shiftLinear_eval]

end IRComparison.CompactRouting
