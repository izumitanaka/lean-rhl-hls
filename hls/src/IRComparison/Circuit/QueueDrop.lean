import IRComparison.Circuit.Counter

namespace IRComparison.Circuit

/-- Sequential destructive reads: a missing token fails immediately. -/
def dropPrefix : Nat → List α → Option (List α)
  | 0,q => some q
  | _+1,[] => none
  | n+1,_::q => dropPrefix n q

def receiveHead : List α → Option (α × List α)
  | [] => none
  | x::xs => some (x,xs)

theorem drop_receive (n : Nat) (q : List α) :
    (dropPrefix n q).bind receiveHead = (q[n]?).map (fun v => (v,q.drop (n+1))) := by
  induction n generalizing q with
  | zero => cases q <;> rfl
  | succ n ih => cases q with
    | nil => simp [dropPrefix]
    | cons x xs => simpa [dropPrefix] using ih xs

def dropOne (s : State × List Int) : Option (State × List Int) :=
  match s.2 with
  | [] => none
  | _::xs => some (s.1,xs)

theorem drop_fold (first count : Nat) (s : State) (q : List Int) :
    (List.range' first count).foldlM (fun s _ => dropOne s) (s,q) =
      (dropPrefix count q).map (fun rest => (s,rest)) := by
  induction count generalizing first q with
  | zero => rfl
  | succ n ih =>
    cases q with
    | nil => simp [List.range'_succ,dropOne,dropPrefix]
    | cons x xs => simpa [List.range'_succ,dropOne,dropPrefix] using ih (first+1) xs

def Payload.setQueue (p : Payload) (q : Nat) (vs : List Int) : Payload :=
  { p with queues := fun k => if k = q then vs else p.queues k }

theorem receive_eval (he : p.queues qi = v::vs) :
    (Action.receive qi slot).eval cap p = some ((p.setQueue qi vs).setWire slot v) := by
  simp [Action.eval,Action.node,execute,Payload.at,he,Runtime.setWire,Runtime.setQueue,
    Payload.setWire,Payload.setQueue,Runtime.payload]

theorem receive_empty (he : p.queues qi = []) : (Action.receive qi slot).eval cap p = none := by
  simp [Action.eval,Action.node,execute,Payload.at,he]

/-- The low-level discard loop performs exactly the destructive receives
represented by `dropPrefix`; it never reads a token nondestructively. -/
theorem discard_loop (qi countSlot counter scratch : Nat) (hsc : scratch ≠ counter)
    (hsn : scratch ≠ countSlot) (hcn : counter ≠ countSlot) (count : Nat) (p : Payload)
    (hn : p.wires countSlot = (count : Int)) (hk : p.wires counter = 0) :
    ∃ result,
      (Schedule.loop (.bin .lt (.wire counter) (.wire countSlot))
        (.seq (.step (.receive qi scratch)) (.step (.wire counter (.bin .add (.wire counter) (.lit 1)))))).Eval cap p result ∧
      result.map (observe qi) = (dropPrefix count (p.queues qi)).map (fun rest => (p.data,rest)) := by
  let P := fun q : Payload => q.wires countSlot = (count : Int)
  have hinc : ∀ q v, P q → P (q.setWire counter v) := by
    intro q v hq
    simpa [P,Payload.setWire,Ne.symm hcn] using hq
  have hb : ∀ (j : Nat) q, P q → q.wires counter = (j:Int) →
      ∃ result, (Schedule.step (.receive qi scratch)).Eval cap q result ∧
        result.map (observe qi) = dropOne (observe qi q) ∧ LoopResult P counter j result := by
    intro j q hq hk
    cases he : q.queues qi with
    | nil =>
      refine ⟨none,?_,by simp [dropOne,observe,he],?_⟩
      · rw [← receive_empty (slot:=scratch) he]; exact .step
      · intro t ht; cases ht
    | cons v vs =>
      let t := (q.setQueue qi vs).setWire scratch v
      refine ⟨some t,?_,?_,?_⟩
      · rw [← receive_eval (slot:=scratch) he]; exact .step
      · simp [dropOne,observe,he,t,Payload.setWire,Payload.setQueue]
      · intro u hu; cases hu
        constructor
        · simpa [P,t,Payload.setWire,Payload.setQueue,Ne.symm hsn] using hq
        · simpa [t,Payload.setWire,Payload.setQueue,Ne.symm hsc] using hk
  obtain ⟨r,hr,ho,_⟩ := counter_iterations (output:=qi) (P:=P) (stop:=count)
    (limit:=.wire countSlot) (counter:=counter) (f:=fun _ => dropOne)
    (fun _ h => congrArg some h) hinc hb count 0 (by omega) p hn hk
  exact ⟨r,hr,by simpa only [observe,drop_fold] using ho⟩

end IRComparison.Circuit
