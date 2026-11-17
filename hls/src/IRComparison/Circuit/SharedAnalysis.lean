import IRComparison.Circuit.SharedExpr
import IRComparison.Circuit.Pipelining.Actions

namespace IRComparison.Circuit.Shared

def bound (ranges : Array Interval) (ref : Nat) := ranges[ref]?.getD wordRange

def Node.range (wr : Nat → Interval) (rs : Array Interval) : Node → Interval
  | .input e => Circuit.range wr e
  | .memory .. | .wrap32 _ => wordRange
  | .binary op a b => binRange op (bound rs a) (bound rs b)
  | .natIndex a => ⟨max 0 (bound rs a).lo,max 0 (bound rs a).hi⟩
  | .select _ a b => union (bound rs a) (bound rs b)
  | .seq _ b => bound rs b

/-- Range transfer runs once per shared node, without tree expansion. -/
def ranges (wr : Nat → Interval) : Graph → Array Interval
  | [] => #[]
  | n::g => let rs := ranges wr g; rs.push (n.range wr rs)

@[simp] theorem ranges_size (g : Graph) : (ranges wr g).size = g.length := by
  induction g with
  | nil => rfl
  | cons n g ih => simp [ranges,ih]

def Bounded (cache : Cache) (rs : Array Interval) : Prop :=
  ∀ n v, get cache n = some v → (bound rs n).Contains v

theorem Node.range_correct (node : Node) (hb : InputsBound s w wr)
    (hc : Bounded cache rs) (he : node.eval s w cache = some v) :
    (node.range wr rs).Contains v := by
  cases node with
  | input e => exact Circuit.range_correct e hb he
  | memory a j =>
    cases hj : get cache j with
    | none => simp [Node.eval,hj] at he
    | some index =>
      simp only [Node.eval,hj] at he
      exact hb.memory a index v he
  | binary op a b =>
    cases ha : get cache a <;> cases hb' : get cache b <;> simp [Node.eval,ha,hb'] at he
    rename_i av bv
    subst v
    exact binRange_correct op (hc a av ha) (hc b bv hb')
  | wrap32 a =>
    cases ha : get cache a with
    | none => simp [Node.eval,ha] at he
    | some av =>
      simp [Node.eval,ha] at he
      subst v
      have lo := Int.emod_nonneg av (by decide : (4294967296 : Int) ≠ 0)
      have hi := Int.emod_lt_of_pos av (by decide : (0 : Int) < 4294967296)
      simp only [Node.range,wordRange,Interval.Contains]
      omega
  | natIndex a =>
    cases ha : get cache a with
    | none => simp [Node.eval,ha] at he
    | some av =>
      simp [Node.eval,ha] at he
      subst v
      have h := hc a av ha
      simp only [Node.range,Interval.Contains] at *
      omega
  | select c a b =>
    cases ht : get cache c with
    | none => simp [Node.eval,ht] at he
    | some cv =>
      simp only [Node.eval,ht,bind,Option.bind] at he
      split at he
      · have h := hc a v he
        simp only [Node.range,union,Interval.Contains] at *
        omega
      · have h := hc b v he
        simp only [Node.range,union,Interval.Contains] at *
        omega
  | seq a b =>
    cases ha : get cache a with
    | none => simp [Node.eval,ha] at he
    | some av =>
      simp only [Node.eval,ha,Option.bind_some] at he
      exact hc b v he

theorem Bounded.push {value : Option Int} (h : Bounded cache rs) (same : cache.size = rs.size)
    (valid : ∀ v, value = some v → r.Contains v) : Bounded (cache.push value) (rs.push r) := by
  intro n v hv
  unfold get at hv
  unfold bound
  rw [Array.getElem?_push] at hv ⊢
  by_cases hn : n = cache.size
  · simp only [hn] at hv
    simpa [← same,hn] using valid v hv
  · simp only [hn,if_false] at hv
    simpa [← same,hn] using h n v hv

theorem ranges_correct (g : Graph) (hb : InputsBound s w wr) :
    Bounded (values s w g) (ranges wr g) := by
  induction g with
  | nil => intro n v h; simp [values,get] at h
  | cons n g ih =>
    exact ih.push (by simp) (fun _ he => n.range_correct hb ih he)

def Program.range (p : Program) (wr : Nat → Interval) := bound (ranges wr p.graph) p.result

theorem Program.range_correct (p : Program) (hb : InputsBound s w wr)
    (he : p.eval s w = some v) : (p.range wr).Contains v :=
  ranges_correct p.graph hb p.result v he

/-- Direct external dependencies only. Internal references have already been
analysed at their defining nodes; they do not recursively copy dependency lists.
This is conservative (includes unselected branches and unused caller leaves). -/
def Node.reads : Node → List Pipelining.Cell
  | .input e => Pipelining.reads e
  | .memory a _ => [.array a]
  | _ => []

def references (g : Graph) : List Pipelining.Cell := g.flatMap Node.reads

theorem Node.agrees (n : Node) (p q : Payload)
    (h : Pipelining.Agrees n.reads p q) :
    n.eval p.data p.wires cache = n.eval q.data q.wires cache := by
  cases n with
  | input e => exact Pipelining.expr_agrees e p q h
  | memory a j =>
    have ha : p.data.arrays a = q.data.arrays a := by
      have hh := h (.array a) (by simp [Node.reads])
      simpa [Pipelining.get] using hh
    simp [Node.eval,ha]
  | binary | wrap32 | natIndex | select | seq => rfl

theorem values_agree (g : Graph) (p q : Payload)
    (h : Pipelining.Agrees (references g) p q) :
    values p.data p.wires g = values q.data q.wires g := by
  induction g with
  | nil => rfl
  | cons n g ih =>
    have hs : Pipelining.Agrees (n.reads ++ references g) p q := h
    have hh := Pipelining.agrees_append hs
    simp only [values,ih hh.2,n.agrees p q hh.1]

def Program.reads (p : Program) : List Pipelining.Cell := references p.graph

theorem Program.agrees (program : Program) (p q : Payload)
    (h : Pipelining.Agrees program.reads p q) :
    program.eval p.data p.wires = program.eval q.data q.wires := by
  unfold Program.eval
  rw [values_agree program.graph p q h]

end IRComparison.Circuit.Shared
