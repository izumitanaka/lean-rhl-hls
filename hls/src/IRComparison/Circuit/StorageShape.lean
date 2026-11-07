import IRComparison.Circuit.FiniteBuffer

namespace IRComparison.Circuit

/-- Compile-time bounds on every bank. Sparse identifiers may leave unused
positions; no run-time allocation is possible in this representation. -/
structure StorageShape where
  registers : Nat
  memories : Nat
  queues : Nat
  memorySize : Nat → Nat
  memoryLive : Nat → Bool
  queueSize : Nat → Nat
  wires : Array Interval
  states : Nat

def StorageShape.wireRange (s : StorageShape) (n : Nat) := s.wires[n]?.getD zeroRange

def StorageShape.hasMemory (s : StorageShape) (a : Nat) : Prop := a < s.memories ∧ s.memoryLive a = true

instance (s : StorageShape) (a : Nat) : Decidable (s.hasMemory a) := inferInstanceAs (Decidable (_ ∧ _))

def Expr.inStorage (s : StorageShape) : Expr → Prop
  | .fail | .lit _ => True
  | .wire n => n < s.wires.size
  | .reg n => n < s.registers
  | .memory a j => s.hasMemory a ∧ j.inStorage s
  | .bin _ a b => a.inStorage s ∧ b.inStorage s
  | .natIndex a => a.inStorage s
  | .select c a b => c.inStorage s ∧ a.inStorage s ∧ b.inStorage s
  | .seq a b => a.inStorage s ∧ b.inStorage s

def Node.inStorage (s : StorageShape) : Node → Prop
  | .halt => True
  | .jump n => n < s.states
  | .wire k v n => k < s.wires.size ∧ v.inStorage s ∧ n < s.states
  | .assign k v n => k < s.registers ∧ v.inStorage s ∧ n < s.states
  | .store a j v n => s.hasMemory a ∧ j.inStorage s ∧ v.inStorage s ∧ n < s.states
  | .branch c yes no => c.inStorage s ∧ yes < s.states ∧ no < s.states
  | .snapshot a b n => s.hasMemory a ∧ s.hasMemory b ∧ s.memorySize b ≤ s.memorySize a ∧ n < s.states
  | .erase a n => s.hasMemory a ∧ n < s.states
  | .clear q n => q < s.queues ∧ n < s.states
  | .send q v n => q < s.queues ∧ v.inStorage s ∧ n < s.states
  | .receive q k n => q < s.queues ∧ k < s.wires.size ∧ n < s.states

structure StorageAgreement (s : StorageShape) (r t : Runtime) : Prop where
  pc : r.pc = t.pc
  regs : ∀ n, n < s.registers → r.data.regs n = t.data.regs n
  arrays : ∀ a, s.hasMemory a → r.data.arrays a = t.data.arrays a
  wires : ∀ n, n < s.wires.size → r.wires n = t.wires n
  queues : ∀ q, q < s.queues → r.queues q = t.queues q
  done : r.done = t.done
  error : r.error = t.error

theorem StorageAgreement.refl (s : StorageShape) (r : Runtime) : StorageAgreement s r r :=
  ⟨rfl,by intros; rfl,by intros; rfl,by intros; rfl,by intros; rfl,rfl,rfl⟩

theorem StorageAgreement.symm (h : StorageAgreement s r t) : StorageAgreement s t r :=
  ⟨h.pc.symm,fun n hn => (h.regs n hn).symm,fun n hn => (h.arrays n hn).symm,
    fun n hn => (h.wires n hn).symm,fun n hn => (h.queues n hn).symm,h.done.symm,h.error.symm⟩

theorem StorageAgreement.trans (h : StorageAgreement s r t) (g : StorageAgreement s t u) : StorageAgreement s r u :=
  ⟨h.pc.trans g.pc,fun n hn => (h.regs n hn).trans (g.regs n hn),
    fun n hn => (h.arrays n hn).trans (g.arrays n hn),fun n hn => (h.wires n hn).trans (g.wires n hn),
    fun n hn => (h.queues n hn).trans (g.queues n hn),h.done.trans g.done,h.error.trans g.error⟩

theorem Expr.storage_congr (e : Expr) (closed : e.inStorage s) (h : StorageAgreement s r t) :
    e.eval r.data r.wires = e.eval t.data t.wires := by
  induction e with
  | fail | lit => rfl
  | wire n => exact congrArg some (h.wires n closed)
  | reg n => exact congrArg some (h.regs n closed)
  | memory a j ih => simp only [Expr.eval,ih closed.2,h.arrays a closed.1]
  | natIndex e ih => simp only [Expr.eval,ih closed]
  | bin op a b ihA ihB => simp only [Expr.eval,ihA closed.1,ihB closed.2]
  | select c a b ihC ihA ihB => simp only [Expr.eval,ihC closed.1,ihA closed.2.1,ihB closed.2.2]
  | seq a b ihA ihB => simp only [Expr.eval,ihA closed.1,ihB closed.2]

end IRComparison.Circuit
