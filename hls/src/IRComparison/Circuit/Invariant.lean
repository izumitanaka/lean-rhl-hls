import IRComparison.Circuit.Width

namespace IRComparison.Circuit

abbrev Frame := List Interval
def zeroRange : Interval := ⟨0,0⟩
def Frame.get (f : Frame) (n : Nat) := f[n]?.getD zeroRange
def Frame.contains (f : Frame) (w : Nat → Int) : Prop := ∀ n, (f.get n).Contains (w n)

def Frame.within : Frame → Frame → Bool
  | [],[] => true
  | a::as,b::bs => decide (b.lo ≤ a.lo ∧ a.hi ≤ b.hi) && Frame.within as bs
  | _,_ => false

theorem Frame.within_sound {a b : Frame} {w : Nat → Int}
    (h : a.within b = true) (ha : a.contains w) : b.contains w := by
  induction a generalizing b w with
  | nil => cases b with
    | nil => exact ha
    | cons => cases h
  | cons x xs ih => cases b with
    | nil => cases h
    | cons y ys =>
      have hh : (y.lo ≤ x.lo ∧ x.hi ≤ y.hi) ∧ Frame.within xs ys = true := by simpa [within] using h
      intro n
      cases n with
      | zero => have h0 := ha 0; change x.Contains (w 0) at h0; change y.Contains (w 0); unfold Interval.Contains at *; omega
      | succ n =>
        exact ih hh.2 (fun k => ha (k+1)) n

def Frame.empty (f : Frame) : Bool := f.any fun r => r.hi < r.lo

theorem Frame.not_empty {f : Frame} {w : Nat → Int} (h : f.contains w) : f.empty = false := by
  induction f generalizing w with
  | nil => rfl
  | cons r rs ih =>
    have h0 := h 0
    change r.lo ≤ w 0 ∧ w 0 ≤ r.hi at h0
    have hr : ¬ r.hi < r.lo := by omega
    simpa [empty,hr] using ih (fun n => h (n+1))

def Frame.merge : Frame → Frame → Frame
  | a::as,b::bs => union a b :: Frame.merge as bs
  | [],bs => bs
  | as,[] => as

/-- Threshold widening uses both the counter bound and its predecessor, so
the invariant at the loop increment retains k<count rather than k≤count. -/
def Frame.widen : Frame → Frame → Frame → Frame
  | top::tops,old::olds,new::news =>
      let lower := if new.lo < old.lo then min top.lo new.lo else old.lo
      let upper := if old.hi < new.hi then
        if new.hi ≤ top.hi-1 then max new.hi (top.hi-1) else max new.hi top.hi
        else old.hi
      ⟨lower,upper⟩ :: widen tops olds news
  | _,_,news => news

def Frame.refine (f : Frame) (condition : Expr) (yes : Bool) : Frame :=
  match condition with
  | .bin .lt (.wire k) rhs =>
      let old := f.get k
      let r := range f.get rhs
      f.set k (if yes then ⟨old.lo,min old.hi (r.hi-1)⟩ else ⟨max old.lo r.lo,old.hi⟩)
  | _ => f

theorem Frame.set_same {f : Frame} (hf : f.contains w) (h : r.Contains (w k)) :
    Frame.contains (f.set k r) w := by
  by_cases hk : k < f.length
  · intro n
    by_cases hn : k = n
    · subst n; simpa [Frame.get,List.getElem?_set_self hk] using h
    · simpa [Frame.get,List.getElem?_set_ne hn] using hf n
  · simpa [List.set_eq_of_length_le (by omega : f.length ≤ k)] using hf

theorem Frame.set_value {f : Frame} (hf : f.contains w) (hk : k < f.length) (h : r.Contains v) :
    Frame.contains (f.set k r) (fun n => if n = k then v else w n) := by
  intro n
  by_cases hn : n = k
  · subst n; simpa [Frame.get,List.getElem?_set_self hk] using h
  · simpa [Frame.get,List.getElem?_set_ne (Ne.symm hn),hn] using hf n

theorem Frame.refine_sound (f : Frame) (hb : InputsBound s w f.get)
    (he : e.eval s w = some v) (hv : (v != 0) = yes) : (f.refine e yes).contains w := by
  unfold refine
  split
  · rename_i k rhs
    apply Frame.set_same hb.wires
    have hold := hb.wires k
    simp only [Expr.eval] at he
    cases hr : rhs.eval s w with
    | none => simp [hr] at he
    | some z =>
      have hz := range_correct rhs hb hr
      simp only [hr,bind,Option.bind,Bin.eval] at he
      have he' : (if w k < z then (1:Int) else 0) = v := Option.some.inj he
      cases yes <;> simp only [Bool.false_eq_true,↓reduceIte,Interval.Contains] at *
      · have hge : z ≤ w k := by split at he' <;> simp_all <;> omega
        omega
      · have hlt : w k < z := by split at he' <;> simp_all <;> omega
        omega
  · exact hb.wires

def isWord (r : Interval) : Bool := 0 ≤ r.lo && r.hi ≤ 4294967295

def transfer (f : Frame) (n : Node) : Except String (List (Nat × Frame)) := do
  if f.empty then return []
  match n with
  | .halt => return []
  | .branch c yes no => return [(yes,f.refine c true),(no,f.refine c false)]
  | .wire k e next =>
      if k < f.length then return [(next,f.set k (range f.get e))]
      else throw s!"undeclared holding register {k}"
  | .receive _ k next =>
      if k < f.length then return [(next,f.set k wordRange)]
      else throw s!"undeclared receive register {k}"
  | .assign _ e next | .store _ _ e next | .send _ e next =>
      if isWord (range f.get e) then return [(next,f)]
      else throw "non-BV32 value written to a data register, array, or FIFO"
  | .jump next | .snapshot _ _ next | .erase _ next | .clear _ next => return [(next,f)]

def initialFrame (a : Artifact) : Frame :=
  (List.range a.wires.size).map fun n => if n < 2 then wordRange else zeroRange

abbrev InvariantTable := Array (Option Frame)

def validEdge (table : InvariantTable) (edge : Nat × Frame) : Bool :=
  edge.2.empty || match table[edge.1]?.join with
    | none => false
    | some target => edge.2.within target

def validNode (a : Artifact) (table : InvariantTable) (pc : Nat) : Bool :=
  match table[pc]?.join with
  | none => true
  | some frame =>
    frame.length == a.wires.size && (frame.empty || frame.within a.wires.toList) &&
    match a.machine.nodes[pc]? with
    | none => false
    | some n => match transfer frame n with
      | .error _ => false
      | .ok edges => edges.all (validEdge table)

def validInvariant (a : Artifact) (table : InvariantTable) : Bool :=
  table.size == a.machine.nodes.size &&
  (match table[a.machine.entry]?.join with
   | none => false
   | some entry => (initialFrame a).within entry) &&
  (List.range a.machine.nodes.size).all (validNode a table)

/-- The heuristic only proposes a table; all entries and edges are checked. -/
def checkInvariant (a : Artifact) (table : InvariantTable) : Except String Unit :=
  if validInvariant a table then .ok () else .error "holding-register invariant is not inductive or exceeds declared ranges"

def inferInvariant (a : Artifact) : Except String InvariantTable := do
  let mut table : InvariantTable := (Array.replicate a.machine.nodes.size none).set! a.machine.entry (some (initialFrame a))
  let mut work := [a.machine.entry]
  let mut fuel := 32 * (a.machine.nodes.size+1) * (a.wires.size+1)
  while !work.isEmpty do
    if fuel = 0 then throw "interval analysis did not converge within its work budget"
    fuel := fuel-1
    let pc := work.head!
    work := work.tail
    let some frame := table[pc]?.join | throw "invalid worklist entry"
    let successors ← transfer frame a.machine.nodes[pc]!
    for (next,f) in successors do
      unless f.empty do
        if next ≥ table.size then throw "invalid control edge"
        match table[next]?.join with
        | none =>
            table := table.set! next (some f)
            work := next::work
        | some old =>
            unless f.within old do
              let joined := old.merge f
              let widened := Frame.widen a.wires.toList old joined
              table := table.set! next (some widened)
              work := next::work
  checkInvariant a table
  return table

end IRComparison.Circuit
