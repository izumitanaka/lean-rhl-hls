import IRComparison

open IRComparison

-- A True postcondition cannot justify an inserted empty receive.
example : ¬ Relational.Insertion (fun (_ : Unit) (_ : BufferRules.Buffer) => True)
    BufferRules.receive (fun _ _ => True) := by
  intro h
  obtain ⟨out,run,_⟩ := Relational.insertion_succeeds h (s := ()) (t := (0,[])) trivial
  simp [BufferRules.receive] at run

-- Nor can it justify an undefined buffer copy.
example : ¬ Relational.Insertion (fun (_ : Unit) (_ : Unit) => True)
    (fun _ => (none : Option Int)) (fun _ _ => True) := by
  intro h
  obtain ⟨out,run,_⟩ := Relational.insertion_succeeds h (s := ()) (t := ()) trivial
  contradiction

-- An arbitrary relation, a stride of two, and unequal intermediate states:
-- the general loop rule does not require identical source/target stores.
example (n : Nat) : Relational.Translation (fun s t : Int => s = t+10)
    (Relational.iterate (fun _ (s : Int) => some (s+2)) n 0)
    (Relational.iterate (fun _ (t : Int) => some (t+2)) n 0)
    (fun s t => s = t+10) := by
  apply Relational.for_rule (P := fun _ s t => s = t+10)
  intro k s t h
  exact .some (by omega)

-- Retained-memory prefetch binds a value without consuming an unrelated
-- FIFO or changing the memory. The statement holds for any index and queue.
example (j : Int) (q : List Int) :
    Relational.Insertion
      (fun (xs : Array Int) (t : Array Int × List Int) =>
        t = (xs,q) ∧ ∃ v, arrayInput xs j = some v)
      (fun t => (arrayInput t.1 j).map (fun v => (t,v)))
      (fun xs out => out.1 = (xs,q) ∧ arrayInput xs j = some out.2) := by
  apply Relational.consequence
    (BufferRules.insertMemory_rule (fun xs => arrayInput xs j)
      (fun t : Array Int × List Int => arrayInput t.1 j) (fun xs t => t = (xs,q)))
  · intro xs t h
    obtain ⟨rfl,defined⟩ := h
    exact ⟨rfl,rfl,defined⟩
  · intro _ _ h
    exact h

-- A branch that may not execute its read cannot justify an unconditional
-- out-of-bounds prefetch, even with a True postcondition.
example : ¬ Relational.Insertion (fun (_ : Unit) (_ : Unit) => True)
    (fun _ => (arrayInput #[(7 : Int)] 1).map (fun v => ((),v)))
    (fun _ _ => True) := by
  intro h
  obtain ⟨out,run,_⟩ := Relational.insertion_succeeds h (s := ()) (t := ()) trivial
  simp [arrayInput] at run

-- Explicit discards consume; repeated reads cannot recover past values.
example : BufferRules.take 2 (0,[10,11,12,13]) = some (12,[13]) := rfl
example : BufferRules.take 1 (12,[13]) = none := rfl

-- Queued values cannot remain related after the corresponding memory
-- element has been overwritten. Tr-WriteMem requires freshness for this reason.
example : ¬ CommunicationIR.Corresponds (fun _ => some 11) [0] [10] := by
  intro h
  cases h with
  | cons eq rest => contradiction

#print axioms Relational.insertRight
#print axioms BufferRules.insertMemory_rule
#print axioms BufferRules.take_rule
#print axioms StreamState.directSend_rule
#print axioms HybridAlternatives.branch
#print axioms Circuit.Pipelining.scheduleStructure_rule
