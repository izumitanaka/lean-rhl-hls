import IRComparison.Hybrid.ChannelBuffers

namespace IRComparison.ChannelWindow
open HybridIR AffineAddress

/-- A placement plan reuses the existing memory/copy/FIFO load operations.
It is lowered to ordinary ChannelCmd, not a new source or circuit operation. -/
inductive Load where
  | memory (address : Linear)
  | saved (slot : Nat)
  | take (discard : Linear)
  deriving Repr, DecidableEq

def Load.at (i : Int) : Load → WindowFIFO.Load
  | .memory a => .memory (a.eval i)
  | .saved n => .saved n
  | .take n => .take (n.eval i).toNat

def linear (index : Value) (a : Linear) : Value :=
  .add (.mul (.lit a.coefficient) index) (.lit a.offset)

theorem linear_correct (he : index.eval i x y ls [] = some j) :
    (linear index a).eval i x y ls [] = some (a.eval j) := by
  simp [linear,Value.eval,he,Linear.eval]

def Load.code (array channel buffer width padding : Nat) (index : Value) : Load → ChannelCmd
  | .memory a => .hold buffer (.memory array (linear index a))
  | .saved n => .hold buffer (.pure (.local (if n < width then n else width+padding)))
  | .take n => ChannelBuffers.take channel buffer (linear index n)

@[simp] theorem queue_self (s : ChannelState) : s.setQueue a (s.queues a) = s := by
  cases s; simp only [ChannelState.setQueue]; congr; funext k; split <;> simp_all
@[simp] theorem queue_queue (s : ChannelState) : (s.setQueue a p).setQueue a q = s.setQueue a q := by
  simp only [ChannelState.setQueue]; congr; funext k; split <;> simp_all
@[simp] theorem queue_buffer (s : ChannelState) :
    (s.setBuffer b v).setQueue a q = (s.setQueue a q).setBuffer b v := rfl

theorem Load.correct (l : Load) (size : old.length = width) (extraSize : extra.length = padding)
    (hi : index.eval outer x y (old++extra) [] = some i) :
    (l.code array channel buffer width padding index).eval outer x y s (old++extra) =
      ((l.at i).eval (arrayInput (s.data.arrays array)) old (s.queues channel)).map
        (fun (v,q) => (s.setQueue channel q).setBuffer buffer v) := by
  cases l with
  | memory a =>
    simp only [Load.code,ChannelCmd.eval,ReadCode.eval,linear_correct hi,bind,Option.bind]
    simp only [Load.at,WindowFIFO.Load.eval,arrayInput]
    cases h : (if a.eval i < 0 then none else (s.data.arrays array)[(a.eval i).toNat]?) <;> simp [h]
  | saved n =>
    have he : (Value.local (if n < width then n else width+padding)).eval outer x y (old++extra) [] = old[n]? := by
      by_cases hn : n < width
      · simp [Value.eval,hn,List.getElem?_append_left (by omega : n < old.length)]
      · simp only [Value.eval,hn,ite_false]
        rw [List.getElem?_eq_none (by simp [size,extraSize]),List.getElem?_eq_none (by omega : old.length ≤ n)]
    simp only [Load.code,ChannelCmd.eval,ReadCode.eval,he,Load.at,WindowFIFO.Load.eval]
    cases old[n]? <;> simp [Option.map]
  | take n =>
    simp only [Load.code,Load.at,WindowFIFO.Load.eval,ChannelBuffers.take_correct (linear_correct hi)]
    cases (s.queues channel)[(n.eval i).toNat]? <;> rfl

def put (s : ChannelState) (base : Nat) : List Int → ChannelState
  | [] => s
  | v::vs => put (s.setBuffer base v) (base+1) vs

@[simp] theorem put_data (values : List Int) : (put s base values).data = s.data := by
  induction values generalizing s base <;> simp_all [put,ChannelState.setBuffer]
@[simp] theorem put_queues (values : List Int) : (put s base values).queues = s.queues := by
  induction values generalizing s base <;> simp_all [put,ChannelState.setBuffer]
@[simp] theorem put_queue (values : List Int) :
    (put s base values).setQueue a q = put (s.setQueue a q) base values := by
  induction values generalizing s base <;> simp_all [put]

def loads (array channel base width padding : Nat) (index : Value) : List Load → ChannelCmd
  | [] => .skip
  | l::ls => .seq (l.code array channel base width padding index) (loads array channel (base+1) width padding index ls)

theorem loads_correct (items : List Load) (size : old.length = width) (extraSize : extra.length = padding)
    (hi : index.eval outer x y (old++extra) [] = some i) :
    (loads array channel base width padding index items).eval outer x y s (old++extra) =
      (WindowFIFO.execute (arrayInput (s.data.arrays array)) old (items.map (Load.at i)) (s.queues channel)).map
        (fun (vs,q) => put (s.setQueue channel q) base vs) := by
  induction items generalizing s base with
  | nil => simp [loads,ChannelCmd.eval,WindowFIFO.execute,put]
  | cons l ls ih =>
    simp only [loads,ChannelCmd.eval,Load.correct l size extraSize hi,List.map_cons,WindowFIFO.execute]
    cases hl : (l.at i).eval (arrayInput (s.data.arrays array)) old (s.queues channel) with
    | none => rfl
    | some pair =>
      obtain ⟨v,q⟩ := pair
      simp only [Option.map_some,bind,Option.bind]
      rw [ih]
      simp only [ChannelState.setBuffer,ChannelState.setQueue,ite_true]
      cases WindowFIFO.execute (arrayInput (s.data.arrays array)) old (ls.map (Load.at i)) q with
      | none => rfl
      | some pair =>
        obtain ⟨vs,tail⟩ := pair
        simp only [bind,Option.bind,pure,Option.map_some,put]
        congr 2
        congr 1
        funext k
        split <;> simp_all

/-- Only the named cells change; private buffers outside this window survive. -/
theorem put_other (values : List Int) (outside : slot < base ∨ base+values.length ≤ slot) :
    (put s base values).buffers slot = s.buffers slot := by
  induction values generalizing base s with
  | nil => rfl
  | cons v vs ih =>
    have ne : slot ≠ base := by simp only [List.length_cons] at outside; omega
    rw [put,ih (by simp only [List.length_cons] at outside; omega)]
    simp [ChannelState.setBuffer,ne]

theorem put_at (values : List Int) (hk : k < values.length) :
    (put s base values).buffers (base+k) = values[k]? := by
  induction values generalizing base s k with
  | nil => simp at hk
  | cons v vs ih =>
    cases k with
    | zero =>
      simp only [Nat.add_zero,put]
      rw [put_other vs (Or.inl (by omega : base < base+1))]
      simp [ChannelState.setBuffer]
    | succ k => simpa [put,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (s:=s.setBuffer base v) (base:=base+1) (k:=k) (by simpa using hk)

def Held (s : ChannelState) (base : Nat) (values : List Int) : Prop :=
  ∀ k, k < values.length → s.buffers (base+k) = values[k]?

theorem put_held (values : List Int) : Held (put s base values) base values :=
  fun _ h => put_at values h

theorem held_read (h : Held s base values) :
    ((List.range values.length).map (base+·)).mapM s.buffers = some values := by
  induction values generalizing base with
  | nil => rfl
  | cons v vs ih =>
    have first := h 0 (by simp)
    simp only [Nat.add_zero,List.getElem?_cons_zero] at first
    have tail : Held s (base+1) vs := by
      intro k hk
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h (k+1) (by simp; omega)
    simp only [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,List.mapM_cons,Nat.add_zero,first,Option.bind_some]
    have next := ih tail
    simp only [List.mapM_map,Function.comp_def] at next ⊢
    simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] at next ⊢
    rw [next]
    rfl

theorem capture_held (h : Held s base values) :
    (ChannelBuffers.capture ((List.range values.length).map (base+·)) c).eval i x y s ls =
      c.eval i x y s (values++ls) := by
  rw [ChannelBuffers.capture_correct,held_read h]
  rfl

theorem execute_length (items : List WindowFIFO.Load)
    (h : WindowFIFO.execute input old items q = some (vs,tail)) : vs.length = items.length := by
  induction items generalizing q vs with
  | nil => simpa [WindowFIFO.execute] using congrArg (Option.map (fun p => p.1.length)) h.symm
  | cons l ls ih =>
    simp only [WindowFIFO.execute] at h
    cases he : l.eval input old q with
    | none => simp [he] at h
    | some pair =>
      obtain ⟨v,next⟩ := pair
      cases ht : WindowFIFO.execute input old ls next with
      | none => simp [he,ht] at h
      | some pair =>
        obtain ⟨vals,last⟩ := pair
        simp only [he,ht,bind,Option.bind,pure,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        simp [ih ht]

end IRComparison.ChannelWindow
