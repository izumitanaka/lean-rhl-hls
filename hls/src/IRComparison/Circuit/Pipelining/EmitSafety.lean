import IRComparison.Circuit.Pipelining.Emit

namespace IRComparison.Circuit.Pipelining
open SystemVerilog

theorem ready_references (a : Action) (hc : (a.node 0).inStorage shape) :
    TestReferences shape ((ready a).mapExpressions (RTL.combinational wr)) := by
  cases a <;> simp_all [Action.node,Node.inStorage,StorageShape.hasMemory,ready,
    RTL.Test.mapExpressions,TestReferences]
  all_goals exact combinational_references wr (.lit 0) trivial

theorem writes_references (a : Action) (hc : (a.node 0).inStorage shape) :
    StatementReferences shape ((writes a).mapExpressions (RTL.combinational wr)) := by
  cases a <;> simp_all [Action.node,Node.inStorage,writes,RTL.Statement.mapExpressions,
    RTL.Scalar.mapExpressions,RTL.MemoryRhs.mapExpressions,RTL.QueueRhs.mapExpressions,
    StatementReferences,ScalarReferences]

theorem allReady_references (as : List Action) (hc : ∀ a ∈ as, (a.node 0).inStorage shape) :
    TestReferences shape ((allReady as).mapExpressions (RTL.combinational wr)) := by
  induction as with
  | nil => simp [allReady,RTL.Test.mapExpressions,TestReferences,RTL.combinational,CombinationalReferences,ValidityReferences]
  | cons a as ih => exact ⟨ready_references a (hc a (by simp)),ih (fun a ha => hc a (by simp [ha]))⟩

theorem allWrites_references (as : List Action) (hc : ∀ a ∈ as, (a.node 0).inStorage shape) :
    StatementReferences shape ((allWrites as).mapExpressions (RTL.combinational wr)) := by
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨writes_references a (hc a (by simp)),ih (fun a ha => hc a (by simp [ha]))⟩

theorem lowerClock_references (next : Nat) (as : List Action)
    (hc : ∀ a ∈ as, (a.node 0).inStorage shape) :
    StatementReferences shape ((lowerClock next as).mapExpressions (RTL.combinational wr)) :=
  ⟨allReady_references as hc,⟨allWrites_references as hc,trivial⟩,⟨trivial,trivial⟩⟩

theorem ready_ready (a : Action) (hc : (a.node 0).inStorage shape) :
    TestReady shape old cap ((ready a).mapExpressions (RTL.combinational wr)) := by
  cases a <;> simp_all [Action.node,Node.inStorage,StorageShape.hasMemory,ready,
    RTL.Test.mapExpressions,TestReady]

theorem writes_ready (a : Action) (hc : (a.node 0).inStorage shape)
    (hr : ((ready a).mapExpressions (RTL.combinational wr)).evalWith RTL.Combinational.eval cap old = true) :
    StatementReady shape old cap ((writes a).mapExpressions (RTL.combinational wr)) := by
  cases a <;> simp_all [Action.node,Node.inStorage,StorageShape.hasMemory,ready,writes,
    RTL.Statement.mapExpressions,RTL.Test.mapExpressions,RTL.Scalar.mapExpressions,
    RTL.MemoryRhs.mapExpressions,RTL.QueueRhs.mapExpressions,StatementReady,ScalarReady]
  all_goals simp_all [RTL.Test.evalWith]
  rename_i bank j v
  cases flag : (RTL.combinational wr j).valid.eval old <;> simp_all [RTL.Combinational.eval]

theorem allReady_ready (as : List Action) (hc : ∀ a ∈ as, (a.node 0).inStorage shape) :
    TestReady shape old cap ((allReady as).mapExpressions (RTL.combinational wr)) := by
  induction as with
  | nil => trivial
  | cons a as ih => exact ⟨ready_ready a (hc a (by simp)),fun _ => ih (fun a ha => hc a (by simp [ha]))⟩

theorem allWrites_ready (as : List Action) (hc : ∀ a ∈ as, (a.node 0).inStorage shape)
    (hr : ((allReady as).mapExpressions (RTL.combinational wr)).evalWith RTL.Combinational.eval cap old = true) :
    StatementReady shape old cap ((allWrites as).mapExpressions (RTL.combinational wr)) := by
  induction as with
  | nil => trivial
  | cons a as ih =>
    have hh : ((ready a).mapExpressions (RTL.combinational wr)).evalWith RTL.Combinational.eval cap old = true ∧
        ((allReady as).mapExpressions (RTL.combinational wr)).evalWith RTL.Combinational.eval cap old = true := by
      simpa [allReady,RTL.Test.mapExpressions,RTL.Test.evalWith] using hr
    exact ⟨writes_ready a (hc a (by simp)) hh.1,ih (fun a ha => hc a (by simp [ha])) hh.2⟩

theorem lowerClock_ready (next : Nat) (as : List Action)
    (hc : ∀ a ∈ as, (a.node 0).inStorage shape) :
    StatementReady shape old cap ((lowerClock next as).mapExpressions (RTL.combinational wr)) :=
  ⟨allReady_ready as hc,fun hr => ⟨allWrites_ready as hc hr,trivial⟩,fun _ => ⟨trivial,trivial⟩⟩

theorem mapped_statement_bound (s : RTL.Statement) (h : InputsBound old.data old.wires wr) :
    (s.mapExpressions (RTL.combinational wr)).evalWith RTL.Combinational.eval cap old pending =
      s.evalWith oldRead cap old pending := by
  rw [RTL.map_statement_correct,statement_bound s h]

def BanksUnchanged (as : List Action) (old pending : Circuit.Runtime) : Prop :=
  ∀ c ∈ as.flatMap bankWrites, get pending.payload c = get old.payload c

theorem writes_frame (a : Action) (hc : (a.node 0).inStorage shape)
    (banks : BanksUnchanged [a] old pending) :
    StatementFrame shape old cap ((writes a).mapExpressions (RTL.combinational wr)) pending := by
  cases a <;> simp_all [Action.node,Node.inStorage,writes,RTL.Statement.mapExpressions,
    RTL.Scalar.mapExpressions,RTL.MemoryRhs.mapExpressions,RTL.QueueRhs.mapExpressions,
    StatementFrame,BanksUnchanged,bankWrites,actionWrites,get,Circuit.Runtime.payload]

theorem writes_bank_preserved (a : Action) (c : Cell)
    (bank : (match c with | .array _ | .queue _ => true | _ => false) = true)
    (hn : c ∉ bankWrites a) :
    get (((writes a).mapExpressions (RTL.combinational wr)).evalWith
      RTL.Combinational.eval cap old pending).payload c = get pending.payload c := by
  cases c <;> simp only [Bool.false_eq_true] at bank <;> try contradiction
  all_goals cases a <;> simp_all [bankWrites,actionWrites,writes,RTL.Statement.mapExpressions,
    RTL.Scalar.mapExpressions,RTL.MemoryRhs.mapExpressions,RTL.QueueRhs.mapExpressions,
    RTL.Statement.evalWith,RTL.Register.write,Circuit.Runtime.payload,get,
    Circuit.Runtime.setArray,Circuit.Runtime.setQueue,Circuit.Runtime.setWire,State.set]

theorem banks_after (a : Action) (as : List Action)
    (hn : ∀ b ∈ as, Apart (bankWrites a) (bankWrites b))
    (hb : BanksUnchanged (a::as) old pending) :
    BanksUnchanged as old (((writes a).mapExpressions (RTL.combinational wr)).evalWith
      RTL.Combinational.eval cap old pending) := by
  intro c hc
  obtain ⟨b,hm,hc'⟩ := List.mem_flatMap.mp hc
  rw [writes_bank_preserved a c (List.mem_filter.mp hc').2 (fun ca => hn b hm c ca hc')]
  exact hb c (by simp [hc])

theorem allWrites_frame (as : List Action) (hc : ∀ a ∈ as, (a.node 0).inStorage shape)
    (hn : BanksDistinct as) (hb : BanksUnchanged as old pending) :
    StatementFrame shape old cap ((allWrites as).mapExpressions (RTL.combinational wr)) pending := by
  induction as generalizing pending with
  | nil => trivial
  | cons a as ih =>
    have hn' : (∀ b ∈ as, Apart (bankWrites a) (bankWrites b)) ∧ BanksDistinct as := by
      simpa [BanksDistinct] using hn
    refine ⟨writes_frame a (hc a (by simp)) (fun c hc => hb c (by simpa using List.mem_append_left (as.flatMap bankWrites) (by simpa using hc))),?_⟩
    exact ih (fun a ha => hc a (by simp [ha])) hn'.2 (banks_after a as hn'.1 hb)

theorem lowerClock_frame (next : Nat) (as : List Action)
    (hc : ∀ a ∈ as, (a.node 0).inStorage shape) (hn : BanksDistinct as) :
    StatementFrame shape old cap ((lowerClock next as).mapExpressions (RTL.combinational wr)) old := by
  change if _ then _ else _
  split
  · exact ⟨allWrites_frame as hc hn (fun _ _ => rfl),by
      simp [RTL.advance,RTL.Statement.mapExpressions,RTL.Scalar.mapExpressions,StatementFrame,RTL.Scalar.evalWith]⟩
  · simp [RTL.fault,RTL.Statement.mapExpressions,RTL.Scalar.mapExpressions,StatementFrame]

end IRComparison.Circuit.Pipelining
