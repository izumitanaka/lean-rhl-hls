import IRComparison.Circuit.Counter
import IRComparison.Hybrid.ChannelBody

/-! Lower named communication in a body to existing circuit actions. Private
buffer cells use a value wire plus a definedness wire, so reading an undefined
buffer is an error, not an arbitrary uninitialized value. -/
namespace IRComparison.Circuit.ChannelLower
open HybridIR

structure Buffers where
  base : Nat
  count : Nat
  deriving Repr

def Buffers.stop (b : Buffers) := b.base + 2*b.count
def Buffers.value (b : Buffers) (slot : Nat) := b.base+2*slot
def Buffers.valid (b : Buffers) (slot : Nat) := b.base+2*slot+1

def Buffers.read (b : Buffers) (slot : Nat) : Expr :=
  if slot < b.count then .select (.wire (b.valid slot)) (.wire (b.value slot)) .fail else .fail

def Buffers.view (b : Buffers) (p : Payload) : ChannelState :=
  ⟨p.data,p.queues,fun slot => if slot < b.count && p.wires (b.valid slot) != 0 then some (p.wires (b.value slot)) else none⟩

def bufferCount : ChannelCmd → Nat
  | .letBuffer b c => max (b+1) (bufferCount c)
  | .hold b _ | .receive _ b => b+1
  | .letValue _ c | .repeat _ c | .forRange _ c => bufferCount c
  | .seq a b | .branch _ a b => max (bufferCount a) (bufferCount b)
  | _ => 0

/-- Captured locals use fresh wires outside the private buffer bank. -/
def lower (buffers : Buffers) (i : Expr) (locals : List Expr) : ChannelCmd → Builder Schedule
  | .skip => pure .skip
  | .assign r e => pure (.step (.assign r (read i (.wire 0) (.wire 1) locals [] e)))
  | .store a j e => pure (.step (.store a (read i (.wire 0) (.wire 1) locals [] j) (read i (.wire 0) (.wire 1) locals [] e)))
  | .send q e => pure (.step (.send q (read i (.wire 0) (.wire 1) locals [] e)))
  | .hold b e => pure (.seq (.step (.wire (buffers.value b) (read i (.wire 0) (.wire 1) locals [] e)))
      (.step (.wire (buffers.valid b) (.lit 1))))
  | .receive q b => pure (.seq (.step (.receive q (buffers.value b))) (.step (.wire (buffers.valid b) (.lit 1))))
  | .letBuffer b c => do
      let v ← fresh
      return .seq (.step (.wire v (buffers.read b))) (← lower buffers i (.wire v::locals) c)
  | .letValue e c => do
      let expr := read i (.wire 0) (.wire 1) locals [] e
      let v ← freshFor expr
      return .seq (.step (.wire v expr)) (← lower buffers i (.wire v::locals) c)
  | .seq a b => do
      let first ← lower buffers i locals a
      return .seq first (← lower buffers i locals b)
  | .branch e a b => do
      let yes ← lower buffers i locals a
      let no ← lower buffers i locals b
      return .branch (read i (.wire 0) (.wire 1) locals [] e) yes no
  | .repeat n c => do
      let k ← fresh ⟨0,n⟩
      return counterLoop k (.lit n) (← lower buffers i locals c)
  | .forRange e c => do
      let expr := Expr.natIndex (read i (.wire 0) (.wire 1) locals [] e)
      let n ← freshFor expr
      let k ← fresh (← bounds expr)
      let body ← lower buffers i (.wire k::locals) c
      return .seq (.step (.wire n expr)) (counterLoop k (.wire n) body)

/-- Capacity-aware target interpretation. Connection to unbounded logical
queues additionally requires a sufficient-capacity proof, as in the old path. -/
def bounded (cap : Nat → Nat) (i x y : Int) : ChannelCmd → ChannelState → List Int → Option ChannelState
  | .skip,s,_ => some s
  | .assign r e,s,ls => do return {s with data := s.data.set r (← e.eval i x y s.data ls [])}
  | .store a j e,s,ls => do return {s with data := ← s.data.write a (← j.eval i x y s.data ls []) (← e.eval i x y s.data ls [])}
  | .send q e,s,ls => do
      let v ← e.eval i x y s.data ls []
      if (s.queues q).length < cap q then return s.send q v else none
  | .hold b e,s,ls => do return s.setBuffer b (← e.eval i x y s.data ls [])
  | .receive q b,s,_ => s.receive q b
  | .letBuffer b c,s,ls => do bounded cap i x y c s ((← s.buffers b)::ls)
  | .letValue e c,s,ls => do bounded cap i x y c s ((← e.eval i x y s.data ls [])::ls)
  | .seq a b,s,ls => do bounded cap i x y b (← bounded cap i x y a s ls) ls
  | .branch e a b,s,ls => do
      if (← e.eval i x y s.data ls []) != 0 then bounded cap i x y a s ls else bounded cap i x y b s ls
  | .repeat n c,s,ls => (List.range n).foldlM (fun t _ => bounded cap i x y c t ls) s
  | .forRange e c,s,ls => do
      let n ← e.eval i x y s.data ls []
      (List.range n.toNat).foldlM (fun t (k:Nat) => bounded cap i x y c t ((k:Int)::ls)) s

theorem Buffers.read_correct (b : Buffers) (p : Payload) :
    (b.read slot).eval p.data p.wires = (b.view p).buffers slot := by
  by_cases hs : slot < b.count <;> by_cases hv : p.wires (b.valid slot) = 0 <;>
    simp [read,view,Expr.eval,hs,hv]

theorem Buffers.view_fresh (b : Buffers) (p : Payload) (fresh : b.stop ≤ slot) :
    b.view (p.setWire slot v) = b.view p := by
  unfold view
  congr 1
  funext k
  by_cases hk : k < b.count
  · have hv : b.value k < slot := by dsimp [value,stop] at *; omega
    have hb : b.valid k < slot := by dsimp [valid,stop] at *; omega
    simp [Payload.setWire,hk,show b.value k ≠ slot from by omega,show b.valid k ≠ slot from by omega]
  · simp [hk]

theorem Buffers.view_set (b : Buffers) (p : Payload) (slot : Nat) (hs : slot < b.count) :
    b.view ((p.setWire (b.value slot) v).setWire (b.valid slot) 1) = (b.view p).setBuffer slot v := by
  unfold view ChannelState.setBuffer
  congr 1
  funext k
  by_cases hk : k = slot
  · subst k
    simp [Payload.setWire,hs,value,valid]
  · have vv : b.value k ≠ b.value slot := by dsimp [value]; omega
    have vb : b.value k ≠ b.valid slot := by dsimp [value,valid]; omega
    have bv : b.valid k ≠ b.value slot := by dsimp [value,valid]; omega
    have bb : b.valid k ≠ b.valid slot := by dsimp [valid]; omega
    simp [Payload.setWire,hk,vv,vb,bv,bb]

end IRComparison.Circuit.ChannelLower
