import IRComparison.Circuit.StorageShape

namespace IRComparison.Circuit

/-- Only bounded indices and fixed-width words are stored. The finite-domain
functions denote parallel banks, not dynamically growing maps. -/
structure FiniteRuntime (s : StorageShape) where
  pc : BitVec (bits (s.states-1))
  regs : Fin s.registers → BitVec 32
  arrays : (a : Fin s.memories) → WordBuffer (s.memorySize a.val)
  wires : (n : Fin s.wires.size) → BitVec (signedWidth (s.wireRange n.val))
  queues : (q : Fin s.queues) → WordBuffer (s.queueSize q.val)
  done : Bool
  error : Bool

def FiniteRuntime.decode (r : FiniteRuntime s) : Runtime where
  pc := r.pc.toNat
  data := ⟨fun n => if h : n < s.registers then (r.regs ⟨n,h⟩).toNat else 0,
    fun a => if h : a < s.memories then (r.arrays ⟨a,h⟩).contents else #[]⟩
  wires := fun n => if h : n < s.wires.size then (r.wires ⟨n,h⟩).toInt else 0
  queues := fun q => if h : q < s.queues then (r.queues ⟨q,h⟩).contents.toList else []
  done := r.done
  error := r.error

def FiniteRuntime.pack (s : StorageShape) (r : Runtime) : FiniteRuntime s where
  pc := BitVec.ofNat (bits (s.states-1)) r.pc
  regs := fun n => BitVec.ofInt 32 (r.data.regs n.val)
  arrays := fun a => WordBuffer.pack (s.memorySize a.val) (if s.memoryLive a.val then r.data.arrays a.val else #[])
  wires := fun n => BitVec.ofInt (signedWidth (s.wireRange n.val)) (r.wires n.val)
  queues := fun q => WordBuffer.pack (s.queueSize q.val) (r.queues q.val).toArray
  done := r.done
  error := r.error

/-- Arbitrary unused bank contents are allowed at the invocation boundary.
The function is proof/test support, not an extra reset or initialization pass. -/
def FiniteRuntime.withUnused (r : FiniteRuntime s)
    (memory : (a : Fin s.memories) → Fin (s.memorySize a.val) → BitVec 32)
    (queue : (q : Fin s.queues) → Fin (s.queueSize q.val) → BitVec 32) : FiniteRuntime s :=
  { r with arrays := fun a => (r.arrays a).withUnused (memory a),
           queues := fun q => (r.queues q).withUnused (queue q) }

theorem FiniteRuntime.withUnused_decode (r : FiniteRuntime s) (memory queue) :
    (r.withUnused memory queue).decode = r.decode := by
  simp only [decode,withUnused,WordBuffer.withUnused_contents]

structure StorageBound (s : StorageShape) (r : Runtime) : Prop where
  pc : r.pc < s.states
  data : DataWords r.data
  memories : ∀ a, s.hasMemory a → (r.data.arrays a).size ≤ s.memorySize a
  wires : ∀ n, n < s.wires.size → (s.wireRange n).Contains (r.wires n)
  queues : ∀ q, q < s.queues → (r.queues q).length ≤ s.queueSize q
  queueWords : ∀ q v, v ∈ r.queues q → wordRange.Contains v

theorem FiniteRuntime.pack_correct (h : StorageBound s r) :
    StorageAgreement s (FiniteRuntime.pack s r).decode r := by
  constructor
  · change (BitVec.ofNat (bits (s.states-1)) r.pc).toNat = r.pc
    have hb := bits_fits (s.states-1)
    have hp := h.pc
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  · intro n hn
    simp only [decode,pack,hn,↓reduceDIte]
    exact word_roundtrip (h.data.regs n)
  · intro a ha
    simp only [decode,pack,ha.1,ha.2,↓reduceDIte,↓reduceIte]
    exact WordBuffer.pack_correct _ _ (h.memories a ha) (h.data.arrays a)
  · intro n hn
    simp only [decode,pack,hn,↓reduceDIte]
    exact signedWidth_preserves (h.wires n hn)
  · intro q hq
    simp only [decode,pack,hq,↓reduceDIte]
    have hw : ∀ (n : Nat) (v : Int), (r.queues q).toArray[n]? = some v → wordRange.Contains v := by
      intro n v hv
      exact h.queueWords q v (List.mem_of_getElem? (by simpa using hv))
    rw [WordBuffer.pack_correct _ _ (by simpa using h.queues q hq) hw]
  · rfl
  · rfl

/-- This executable finite transition reuses the already verified node
arithmetic; decoding is local to the combinational calculation. Only the
fixed-width banks above are retained between cycles. -/
def FiniteRuntime.tick (m : Machine) (s : StorageShape) (r : FiniteRuntime s) : FiniteRuntime s :=
  pack s (m.bitTick s.wireRange r.decode)

def FiniteRuntime.run (m : Machine) (s : StorageShape) : Nat → FiniteRuntime s → FiniteRuntime s
  | 0,r => r
  | n+1,r => run m s n (tick m s r)

end IRComparison.Circuit
