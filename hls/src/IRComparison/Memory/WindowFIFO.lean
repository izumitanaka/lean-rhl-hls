import IRComparison.Frontend.NativeWindowPlan

namespace IRComparison.WindowFIFO
open WindowSchedule CommunicationIR

inductive Load where
  | memory (address : Int)
  | saved (slot : Nat)
  | take (discard : Nat)
  deriving Repr, DecidableEq

/-- Discard and take are destructive. There is no FIFO peek. -/
def Load.eval (input : Input) (old queue : List Int) : Load → Option (Int × List Int)
  | .memory a => return (← input a,queue)
  | .saved n => return (← old[n]?,queue)
  | .take n => do return (← queue[n]?,queue.drop (n+1))

def execute (input : Input) (old : List Int) : List Load → List Int → Option (List Int × List Int)
  | [],q => some ([],q)
  | l::ls,q => do
      let (v,rest) ← l.eval input old q
      let (vs,tail) ← execute input old ls rest
      return (v::vs,tail)

theorem Corresponds.at_drop (h : Corresponds input indices queue) (found : indices[n]? = some key) :
    ∃ v, queue[n]? = some v ∧ input key = some v ∧
      Corresponds input (indices.drop (n+1)) (queue.drop (n+1)) := by
  induction h generalizing n with
  | nil => simp at found
  | cons hi ht ih =>
    cases n with
    | zero => simp at found; subst key; exact ⟨_,rfl,hi,ht⟩
    | succ n => simpa using ih (by simpa using found)

/-- A route consumes a prefix, permits explicit discard, and preserves the
    unconsumed suffix for downstream stages. -/
inductive Routes : List WindowSchedule.Load → List Int → List Load → List Int → Prop where
  | nil : Routes [] producer [] producer
  | saved : Routes rest producer code tail → Routes (.saved j::rest) producer (.saved j::code) tail
  | take : producer[n]? = some key → Routes rest (producer.drop (n+1)) code tail →
      Routes (.memory key::rest) producer (.take n::code) tail

structure Route (loads : List WindowSchedule.Load) (producer : List Int) where
  code : List Load
  remaining : List Int
  correct : Routes loads producer code remaining

def route : (loads : List WindowSchedule.Load) → (producer : List Int) → Option (Route loads producer)
  | [],producer => some ⟨[],producer,.nil⟩
  | .saved j::rest,producer => do
      let next ← route rest producer
      return ⟨.saved j::next.code,next.remaining,.saved next.correct⟩
  | .memory key::rest,producer => do
      let position ← slot key producer
      let next ← route rest (producer.drop (position.val+1))
      return ⟨.take position.val::next.code,next.remaining,.take position.property next.correct⟩

/-- The equality covers failure too. On successful loads the suffix relation
    is preserved; no contract demands consuming an entire producer channel. -/
theorem Routes.correct {loads : List WindowSchedule.Load} (route : Routes loads indices code remaining)
    (hq : Corresponds input indices q) (old : List Int) :
    (execute input old code q).map Prod.fst = WindowSchedule.execute input old loads ∧
    ∀ vs tail, execute input old code q = some (vs,tail) → Corresponds input remaining tail := by
  induction route generalizing q with
  | nil => exact ⟨rfl,by intros; simp_all [execute]⟩
  | @saved rest producer code tail j route ih =>
    obtain ⟨eq,suffix⟩ := ih hq
    cases hj : old[j]? with
    | none => simp [execute,Load.eval,WindowSchedule.execute,WindowSchedule.Load.eval,hj]
    | some v =>
      cases he : execute input old code q with
      | none => simp [execute,Load.eval,WindowSchedule.execute,WindowSchedule.Load.eval,hj,← eq,he]
      | some pair =>
        obtain ⟨vs,qs⟩ := pair
        constructor
        · simp [execute,Load.eval,WindowSchedule.execute,WindowSchedule.Load.eval,hj,← eq,he]
        · intro out rest h
          simp [execute,Load.eval,hj,he] at h
          obtain ⟨rfl,rfl⟩ := h
          exact suffix vs qs he
  | @take producer n key rest code tail found route ih =>
    obtain ⟨v,hv,hi,hrest⟩ := Corresponds.at_drop hq found
    obtain ⟨eq,suffix⟩ := ih hrest
    cases he : execute input old code (q.drop (n+1)) with
    | none => simp [execute,Load.eval,WindowSchedule.execute,WindowSchedule.Load.eval,hv,hi,← eq,he]
    | some pair =>
      obtain ⟨vs,qs⟩ := pair
      constructor
      · simp [execute,Load.eval,WindowSchedule.execute,WindowSchedule.Load.eval,hv,hi,← eq,he]
      · intro out rest h
        simp [execute,Load.eval,hv,he] at h
        obtain ⟨rfl,rfl⟩ := h
        exact suffix vs qs he

end IRComparison.WindowFIFO
