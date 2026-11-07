import IRComparison.Circuit.FiniteStorage

namespace IRComparison.Circuit

theorem Expr.bitEval_storage_congr (e : Expr) (closed : e.inStorage s) (h : StorageAgreement s r t) :
    e.bitEval wr r.data r.wires = e.bitEval wr t.data t.wires := by
  induction e with
  | fail | lit => rfl
  | wire n => simp only [Expr.bitEval,h.wires n closed]
  | reg n => simp only [Expr.bitEval,h.regs n closed]
  | memory a j ih => simp only [Expr.bitEval,ih closed.2,h.arrays a closed.1]
  | natIndex e ih => simp only [Expr.bitEval,ih closed]
  | bin op a b ihA ihB => simp only [Expr.bitEval,ihA closed.1,ihB closed.2]
  | select c a b ihC ihA ihB => simp only [Expr.bitEval,ihC closed.1,ihA closed.2.1,ihB closed.2.2]
  | seq a b ihA ihB => simp only [Expr.bitEval,ihA closed.1,ihB closed.2]

theorem StorageAgreement.setPC (h : StorageAgreement s r t) :
    StorageAgreement s {r with pc := n} {t with pc := n} := {h with pc := rfl}

theorem StorageAgreement.stop (h : StorageAgreement s r t) :
    StorageAgreement s {r with done := true} {t with done := true} := {h with done := rfl}

theorem StorageAgreement.fault (h : StorageAgreement s r t) :
    StorageAgreement s {r with done := true,error := true} {t with done := true,error := true} :=
  {h with done := rfl,error := rfl}

theorem StorageAgreement.setWire (h : StorageAgreement s r t) :
    StorageAgreement s (r.setWire slot v) (t.setWire slot v) := by
  refine {h with wires := ?_}
  intro n hn
  simp only [Runtime.setWire]
  split
  · rfl
  · exact h.wires n hn

theorem StorageAgreement.setReg (h : StorageAgreement s r t) :
    StorageAgreement s {r with data := r.data.set slot v} {t with data := t.data.set slot v} := by
  refine {h with regs := ?_}
  intro n hn
  simp only [State.set]
  split
  · rfl
  · exact h.regs n hn

theorem StorageAgreement.setArray (h : StorageAgreement s r t) :
    StorageAgreement s (r.setArray a vs) (t.setArray a vs) := by
  refine {h with arrays := ?_}
  intro n hn
  simp only [Runtime.setArray]
  split
  · rfl
  · exact h.arrays n hn

theorem StorageAgreement.setQueue (h : StorageAgreement s r t) :
    StorageAgreement s (r.setQueue a vs) (t.setQueue a vs) := by
  refine {h with queues := ?_}
  intro n hn
  simp only [Runtime.setQueue]
  split
  · rfl
  · exact h.queues n hn

theorem StorageAgreement.write (h : StorageAgreement s r t) (ha : s.hasMemory a) :
    Option.Rel (StorageAgreement s)
      ((r.data.write a j v).map fun d => {r with data := d})
      ((t.data.write a j v).map fun d => {t with data := d}) := by
  unfold State.write
  rw [h.arrays a ha]
  split
  · exact .none
  · split
    · exact .some h.setArray
    · exact .none

theorem bitExecute_storage_congr (node : Node) (closed : node.inStorage s) (h : StorageAgreement s r t) :
    Option.Rel (StorageAgreement s) (bitExecute wr cap node r) (bitExecute wr cap node t) := by
  cases node with
  | halt => exact .some h.stop
  | jump n => exact .some h.setPC
  | wire k e n =>
    simp only [bitExecute,e.bitEval_storage_congr closed.2.1 h]
    cases e.bitEval wr t.data t.wires with
    | none => exact .none
    | some => exact .some h.setWire.setPC
  | assign k e n =>
    simp only [bitExecute,e.bitEval_storage_congr closed.2.1 h]
    cases e.bitEval wr t.data t.wires with
    | none => exact .none
    | some => exact .some h.setReg.setPC
  | store a j e n =>
    simp only [bitExecute,j.bitEval_storage_congr closed.2.1 h,e.bitEval_storage_congr closed.2.2.1 h]
    cases j.bitEval wr t.data t.wires with
    | none => exact .none
    | some index =>
      cases e.bitEval wr t.data t.wires with
      | none => exact .none
      | some value =>
        have hw := h.write (j:=index) (v:=value) closed.1
        simp only [bind,Option.bind]
        cases hr : r.data.write a index value <;> cases ht : t.data.write a index value <;> simp only [hr,ht,Option.map_some,Option.map_none] at hw
        · exact .none
        · cases hw
        · cases hw
        · exact .some (Option.rel_some_some.mp hw).setPC
  | branch e yes no =>
    simp only [bitExecute,e.bitEval_storage_congr closed.1 h]
    cases e.bitEval wr t.data t.wires with
    | none => exact .none
    | some => exact .some h.setPC
  | snapshot a b n =>
    simp only [bitExecute,h.arrays b closed.2.1]
    exact .some h.setArray.setPC
  | erase a n => exact .some h.setArray.setPC
  | clear q n => exact .some h.setQueue.setPC
  | send q e n =>
    simp only [bitExecute,e.bitEval_storage_congr closed.2.1 h,h.queues q closed.1]
    cases e.bitEval wr t.data t.wires with
    | none => exact .none
    | some value =>
      simp only [bind,Option.bind]
      split
      · exact .some h.setQueue.setPC
      · exact .none
  | receive q k n =>
    simp only [bitExecute,h.queues q closed.1]
    cases t.queues q with
    | nil => exact .none
    | cons => exact .some h.setQueue.setWire.setPC

theorem bitTick_storage_congr {m : Machine} (closed : ∀ node ∈ m.nodes.toList, node.inStorage s)
    (h : StorageAgreement s r t) : StorageAgreement s (m.bitTick wr r) (m.bitTick wr t) := by
  simp only [Machine.bitTick,h.done,h.pc]
  split
  · exact h
  · cases hn : m.nodes[t.pc]? with
    | none => exact h.fault.setPC
    | some node =>
      have hc := closed node (by simpa using Array.mem_of_getElem? hn)
      have he := bitExecute_storage_congr (wr:=wr) (cap:=m.capacity) node hc h
      simp only [Option.bind]
      cases hr : bitExecute wr m.capacity node r <;> cases ht : bitExecute wr m.capacity node t <;> simp only [hr,ht] at he
      · exact h.fault.setPC
      · cases he
      · cases he
      · exact Option.rel_some_some.mp he

end IRComparison.Circuit
