import IRComparison.Hybrid.HybridSource
import IRComparison.Core.Relational

/-! Named communication inside the mixed IR body. This is the target-side
extension; `MemoryCmd` and its source semantics are unchanged. Buffers are
private state, distinct from observable source registers. -/
namespace IRComparison.HybridIR

structure ChannelState where
  data : State
  queues : Nat → List Int
  buffers : Nat → Option Int

def ChannelState.setQueue (s : ChannelState) (a : Nat) (q : List Int) : ChannelState :=
  {s with queues := fun k => if k = a then q else s.queues k}
def ChannelState.setBuffer (s : ChannelState) (b : Nat) (v : Int) : ChannelState :=
  {s with buffers := fun k => if k = b then some v else s.buffers k}

def ChannelState.receive (s : ChannelState) (a b : Nat) : Option ChannelState :=
  match s.queues a with
  | [] => none
  | v::rest => some ((s.setQueue a rest).setBuffer b v)

def ChannelState.send (s : ChannelState) (a : Nat) (v : Int) : ChannelState :=
  s.setQueue a (s.queues a ++ [v])

inductive ChannelCmd where
  | skip
  | letValue (value : ReadCode) (body : ChannelCmd)
  | letBuffer (buffer : Nat) (body : ChannelCmd)
  | assign (reg : Nat) (value : ReadCode)
  | store (array : Nat) (address value : ReadCode)
  | hold (buffer : Nat) (value : ReadCode)
  | receive (channel buffer : Nat)
  | send (channel : Nat) (value : ReadCode)
  | seq (first second : ChannelCmd)
  | branch (condition : ReadCode) (yes no : ChannelCmd)
  | repeat (count : Nat) (body : ChannelCmd)
  | forRange (count : ReadCode) (body : ChannelCmd)
  deriving Repr, DecidableEq

def ChannelCmd.eval (i x y : Int) : ChannelCmd → ChannelState → List Int → Option ChannelState
  | .skip,s,_ => some s
  | .letValue e b,s,ls => do b.eval i x y s ((← e.eval i x y s.data ls [])::ls)
  | .letBuffer b c,s,ls => do c.eval i x y s ((← s.buffers b)::ls)
  | .assign r e,s,ls => do return {s with data := s.data.set r (← e.eval i x y s.data ls [])}
  | .store a j e,s,ls => do return {s with data := ← s.data.write a (← j.eval i x y s.data ls []) (← e.eval i x y s.data ls [])}
  | .hold b e,s,ls => do return s.setBuffer b (← e.eval i x y s.data ls [])
  | .receive a b,s,_ => s.receive a b
  | .send a e,s,ls => do return s.send a (← e.eval i x y s.data ls [])
  | .seq a b,s,ls => do b.eval i x y (← a.eval i x y s ls) ls
  | .branch e a b,s,ls => do
      if (← e.eval i x y s.data ls []) != 0 then a.eval i x y s ls else b.eval i x y s ls
  | .repeat n b,s,ls => (List.range n).foldlM (fun t _ => b.eval i x y t ls) s
  | .forRange e b,s,ls => do
      let n ← e.eval i x y s.data ls []
      (List.range n.toNat).foldlM (fun t k => b.eval i x y t (Int.ofNat k::ls)) s

/-- Copy is a derived operation, preserving a failed read of an undefined
private buffer. It never consults or peeks into a FIFO. -/
def ChannelCmd.copy (dst src : Nat) : ChannelCmd :=
  .letBuffer src (.hold dst (.pure (.local 0)))

def ChannelCmd.ofMemory : MemoryCmd → ChannelCmd
  | .skip => .skip
  | .assign r e => .assign r e
  | .store a j e => .store a j e
  | .letValue e b => .letValue e (ofMemory b)
  | .seq a b => .seq (ofMemory a) (ofMemory b)
  | .branch e a b => .branch e (ofMemory a) (ofMemory b)
  | .repeat n b => .repeat n (ofMemory b)
  | .forRange e b => .forRange e (ofMemory b)

private theorem fold_memory {f : State → α → Option State}
    {g : ChannelState → α → Option ChannelState}
    (h : ∀ s a, g s a = (f s.data a).map (fun t => {s with data := t}))
    (as : List α) (s : ChannelState) :
    as.foldlM g s = (as.foldlM f s.data).map (fun t => {s with data := t}) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldlM_cons,List.foldlM_cons,h]
    cases f s.data a <;> simp_all

/-- Memory retention remains available for every source body, including
nested control, without introducing a restriction on source programs. -/
theorem ChannelCmd.ofMemory_correct (c : MemoryCmd) (s : ChannelState) :
    (ChannelCmd.ofMemory c).eval i x y s ls = (c.eval i x y s.data ls).map (fun t => {s with data := t}) := by
  induction c generalizing s ls with
  | skip => rfl
  | assign r e =>
    simp only [ofMemory,eval,MemoryCmd.eval]
    cases e.eval i x y s.data ls [] <;> rfl
  | store a j e =>
    simp only [ofMemory,eval,MemoryCmd.eval]
    cases j.eval i x y s.data ls [] with
    | none => rfl
    | some k =>
      cases e.eval i x y s.data ls [] with
      | none => rfl
      | some v => simp only [bind,Option.bind]; cases s.data.write a k v <;> rfl
  | letValue e b ih =>
    simp only [ofMemory,eval,MemoryCmd.eval]
    cases e.eval i x y s.data ls [] <;> simp_all
  | seq a b ia ib =>
    simp only [ofMemory,eval,MemoryCmd.eval,ia]
    cases a.eval i x y s.data ls <;> simp_all
  | branch e a b ia ib =>
    simp only [ofMemory,eval,MemoryCmd.eval]
    cases e.eval i x y s.data ls [] with
    | none => rfl
    | some v => simp only [bind,Option.bind]; split <;> simp_all
  | «repeat» n b ih =>
    exact fold_memory (f:=fun t (_:Nat) => b.eval i x y t ls) (fun s _ => ih (s:=s) (ls:=ls)) (List.range n) s
  | forRange e b ih =>
    simp only [ofMemory,eval,MemoryCmd.eval]
    cases e.eval i x y s.data ls [] with
    | none => rfl
    | some n => exact fold_memory (fun s (k:Nat) => ih (s:=s) (ls:=(k:Int)::ls)) _ s

/-- Independent channels really are framed by primitive communication. -/
theorem ChannelState.receive_other {s t : ChannelState} (h : s.receive a b = some t) (ne : c ≠ a) :
    t.queues c = s.queues c := by
  unfold receive at h
  cases hq : s.queues a <;> simp only [hq] at h
  · cases h
  · cases h; simp [setBuffer,setQueue,ne]

theorem ChannelState.send_other (s : ChannelState) (ne : c ≠ a) : (s.send a v).queues c = s.queues c := by
  simp [send,setQueue,ne]

end IRComparison.HybridIR
