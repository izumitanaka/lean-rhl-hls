import IRComparison.Circuit.TransferSound

namespace IRComparison.Circuit

def TableBound (table : InvariantTable) (r : Runtime) : Prop :=
  r.done = true ∨ ∃ f, table[r.pc]?.join = some f ∧ RuntimeBound f r

theorem validInvariant_size (h : validInvariant a table = true) : table.size = a.machine.nodes.size := by
  simp only [validInvariant,Bool.and_eq_true,beq_iff_eq] at h
  exact h.1.1

theorem validInvariant_node (h : validInvariant a table = true) (hp : pc < a.machine.nodes.size) :
    validNode a table pc = true := by
  simp only [validInvariant,Bool.and_eq_true,List.all_eq_true] at h
  exact h.2 pc (List.mem_range.mpr hp)

theorem tick_table_bound (h : validInvariant a table = true) (hr : TableBound table r) :
    TableBound table (a.machine.tick r) := by
  by_cases hd : r.done = true
  · rw [halt_stable _ _ hd]; exact hr
  · rcases hr with done | ⟨f,hf,hb⟩
    · contradiction
    have hp : r.pc < table.size := by
      by_cases hn : r.pc < table.size
      · exact hn
      have hn' := Array.getElem?_eq_none (xs:=table) (by omega : table.size ≤ r.pc)
      simp [hn'] at hf
    have hn := validInvariant_node h (by rw [← validInvariant_size h]; exact hp)
    simp only [validNode,hf] at hn
    have he := Frame.not_empty hb.wires
    cases hc : a.machine.nodes[r.pc]? with
    | none => simp [hc] at hn
    | some instruction =>
      cases ht : transfer f instruction with
      | error _ => simp [hc,ht] at hn
      | ok edges =>
        have hall : edges.all (validEdge table) = true := by
          simp only [hc,ht,Bool.and_eq_true] at hn
          exact hn.2
        cases hs : execute a.machine.capacity instruction r with
        | none => exact Or.inl (by simp [Machine.tick,hd,hc,hs])
        | some t =>
          have hstep : a.machine.tick r = t := by simp [Machine.tick,hd,hc,hs]
          rw [hstep]
          rcases transfer_sound instruction hb ht hs with done | ⟨g,hg,hbg⟩
          · exact Or.inl done
          · have hedge := (List.all_eq_true.mp hall) (t.pc,g) hg
            have notEmpty := Frame.not_empty hbg.wires
            simp only [validEdge,notEmpty,Bool.false_or] at hedge
            cases htarget : table[t.pc]?.join with
            | none => simp [htarget] at hedge
            | some target =>
              simp only [htarget] at hedge
              exact Or.inr ⟨target,htarget,hbg.within hedge⟩

theorem run_table_bound (h : validInvariant a table = true) (hr : TableBound table r) (n : Nat) :
    TableBound table (a.machine.run n r) := by
  induction n generalizing r with
  | zero => exact hr
  | succ n ih => exact ih (tick_table_bound h hr)

theorem table_global_bound (h : validInvariant a table = true) (hr : TableBound table r)
    (hd : r.done = false) : InputsBound r.data r.wires (fun n => a.wires[n]?.getD zeroRange) := by
  rcases hr with done | ⟨f,hf,hb⟩
  · simp [hd] at done
  have hp : r.pc < table.size := by
    by_cases hn : r.pc < table.size
    · exact hn
    have hn' := Array.getElem?_eq_none (xs:=table) (by omega : table.size ≤ r.pc)
    simp [hn'] at hf
  have hn := validInvariant_node h (by rw [← validInvariant_size h]; exact hp)
  simp only [validNode,hf,Bool.and_eq_true,Frame.not_empty hb.wires,Bool.false_or] at hn
  have hw := hb.within hn.1.2
  have eqf : Frame.get a.wires.toList = (fun n => a.wires[n]?.getD zeroRange) := by
    funext n
    simp [Frame.get]
  have hi := hw.inputs
  rw [eqf] at hi
  exact hi

theorem initial_frame_bound (a : Artifact) (hsize : 2 ≤ a.wires.size) (s : HybridWord.State)
    (x y : HybridWord.Word) : RuntimeBound (initialFrame a) (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)) := by
  refine ⟨DataWords.encoded s,?_,by intros; simp_all [Machine.start]⟩
  intro n
  simp only [initialFrame,Frame.get,List.getElem?_map,Machine.start]
  by_cases hn : n < a.wires.size
  · rw [List.getElem?_range (by exact hn)]
    simp only [Option.map_some,Option.getD_some]
    by_cases h0 : n = 0
    · subst n; exact word_encoded x
    · by_cases h1 : n = 1
      · subst n; exact word_encoded y
      · have h2 : ¬ n < 2 := by omega
        simp [h0,h1,h2,zeroRange,Interval.Contains]
  · have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp [hn,h0,h1,zeroRange,Interval.Contains]

theorem initial_table_bound (h : validInvariant a table = true) (hsize : 2 ≤ a.wires.size)
    (s : HybridWord.State) (x y : HybridWord.Word) :
    TableBound table (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y)) := by
  have he : (match table[a.machine.entry]?.join with
    | none => false
    | some entry => (initialFrame a).within entry) = true := by
      simp only [validInvariant,Bool.and_eq_true] at h
      exact h.1.2
  cases ht : table[a.machine.entry]?.join with
  | none => simp [ht] at he
  | some f =>
      simp only [ht] at he
      exact Or.inr ⟨f,ht,(initial_frame_bound a hsize s x y).within he⟩

/-- An accepted table establishes the width premises at every live cycle,
for arbitrary BV32 initial data and input parameters, not just test vectors. -/
theorem reachable_widths (h : validInvariant a table = true) (hsize : 2 ≤ a.wires.size)
    (s : HybridWord.State) (x y : HybridWord.Word) (cycles : Nat)
    (live : (a.machine.run cycles (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y))).done = false) :
    InputsBound
      (a.machine.run cycles (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y))).data
      (a.machine.run cycles (a.machine.start s.encode (HybridWord.encode x) (HybridWord.encode y))).wires
      (fun n => a.wires[n]?.getD zeroRange) :=
  table_global_bound h (run_table_bound h (initial_table_bound h hsize s x y) cycles) live

end IRComparison.Circuit
