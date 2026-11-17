import IRComparison.Circuit.CommandFrame

namespace IRComparison.Circuit

/-- The compiler only stores captured values in fresh holding registers. -/
structure Context (bound : Nat) (i : Expr) (ls : List Expr) (p : Payload)
    (iv xv yv : Int) (lvs : List Int) : Prop where
  inputs : 2 ≤ bound
  indexScope : Static bound i
  localsScope : ∀ e ∈ ls, Static bound e
  index : i.eval p.data p.wires = some iv
  left : p.wires 0 = xv
  right : p.wires 1 = yv
  locals : Matches p.data p.wires ls lvs

theorem Context.weaken (h : Context n i ls p iv xv yv lvs) (hn : n ≤ k) :
    Context k i ls p iv xv yv lvs :=
  ⟨Nat.le_trans h.inputs hn,h.indexScope.mono hn,fun e he => (h.localsScope e he).mono hn,
    h.index,h.left,h.right,h.locals⟩

theorem lookup_static (h : ∀ e ∈ ls, Static n e) : Static n (lookup ls k) := by
  unfold lookup
  cases he : ls[k]? with
  | none => exact .fail
  | some e => exact h e (List.mem_of_getElem? he)

theorem Context.preserve (h : Context n i ls p iv xv yv lvs) (hw : SameBelow n p.wires q.wires) :
    Context n i ls q iv xv yv lvs := by
  refine ⟨h.inputs,h.indexScope,h.localsScope,?_,?_,?_,?_⟩
  · exact (h.indexScope.stable hw).symm.trans h.index
  · exact (hw 0 (by have := h.inputs; omega)).symm.trans h.left
  · exact (hw 1 (by have := h.inputs; omega)).symm.trans h.right
  · intro k
    exact ((lookup_static h.localsScope).stable hw).symm.trans (h.locals k)

def Payload.setWire (p : Payload) (slot : Nat) (v : Int) : Payload :=
  { p with wires := fun k => if k = slot then v else p.wires k }

theorem Payload.setWire_below (p : Payload) : SameBelow n p.wires (p.setWire n v).wires := by
  intro k hk; simp [setWire,show k ≠ n from by omega]

theorem Context.bind (h : Context n i ls p iv xv yv lvs) :
    Context (n+1) i (.wire n::ls) (p.setWire n v) iv xv yv (v::lvs) := by
  have hp := h.preserve (p.setWire_below (v:=v))
  refine ⟨by have := h.inputs; omega,h.indexScope.mono (by omega),?_,hp.index,hp.left,hp.right,?_⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact .wire (by omega)
    · exact (h.localsScope e he).mono (by omega)
  · exact matches_cons hp.locals (by simp [Expr.eval,Payload.setWire])

theorem Context.read (h : Context n i ls p iv xv yv lvs) (e : HybridIR.ReadCode) :
    (read i (.wire 0) (.wire 1) ls [] e).eval p.data p.wires = e.eval iv xv yv p.data lvs [] :=
  read_correct e h.index (congrArg some h.left) (congrArg some h.right) h.locals matches_nil

/-- The same command semantics with a finite send capacity. The source-to-RTL
connection must additionally discharge that the chosen capacity never adds a
failure; it may not silently assume an infinite FIFO. -/
def bounded (capacity : Nat) (i x y : Int) : HybridIR.Cmd → State → List Int → List Int → Option (State × List Int)
  | .skip,s,q,_ => some (s,q)
  | .letValue e b,s,q,ls => do bounded capacity i x y b s q ((← e.eval i x y s ls [])::ls)
  | .assign r e,s,q,ls => do return (s.set r (← e.eval i x y s ls []),q)
  | .store a j e,s,q,ls => do return (← s.write a (← j.eval i x y s ls []) (← e.eval i x y s ls []),q)
  | .send e,s,q,ls => do
      let v ← e.eval i x y s ls []
      if q.length < capacity then some (s,q++[v]) else none
  | .seq a b,s,q,ls => do
      let (t,qs) ← bounded capacity i x y a s q ls
      bounded capacity i x y b t qs ls
  | .branch e a b,s,q,ls => do
      if (← e.eval i x y s ls []) != 0 then bounded capacity i x y a s q ls else bounded capacity i x y b s q ls
  | .repeat n b,s,q,ls => (List.range n).foldlM (fun (t,qs) _ => bounded capacity i x y b t qs ls) (s,q)
  | .forRange e b,s,q,ls => do
      let n ← e.eval i x y s ls []
      (List.range n.toNat).foldlM (fun (t,qs) k => bounded capacity i x y b t qs (Int.ofNat k::ls)) (s,q)

def observe (output : Nat) (p : Payload) : State × List Int := (p.data,p.queues output)

end IRComparison.Circuit
