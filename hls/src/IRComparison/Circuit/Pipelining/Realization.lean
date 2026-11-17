import IRComparison.Circuit.Pipelining.BatchBounds
import IRComparison.Circuit.Pipelining.RTLProgram

namespace IRComparison.Circuit.Pipelining

def initialWidthFrame (n : Nat) : Frame := (List.range n).map (fun k => if k < 2 then wordRange else zeroRange)

def initialWidthsSafe (f : Frame) : Bool := 2 ≤ f.length && (initialWidthFrame f.length).within f

def bankWrites {α : Type} (a : Action α) : List Cell := (actionWrites a).filter (fun c => match c with
  | .array _ | .queue _ => true
  | _ => false)

def BanksDistinct {α : Type} (as : List (Action α)) : Prop := as.Pairwise (fun a b => Apart (bankWrites a) (bankWrites b))

instance {α : Type} (as : List (Action α)) : Decidable (BanksDistinct as) :=
  inferInstanceAs (Decidable (as.Pairwise _))

def batchStatements : Nat → Batches → List RTL.Statement
  | _,[] => [RTL.halt]
  | pc,as :: rest => lowerClock (pc+1) as :: batchStatements (pc+1) rest

def batchProgram (bs : Batches) (capacities : Array (Nat × Nat)) : RTL.Program :=
  ⟨0,(batchStatements 0 bs).toArray,capacities⟩

theorem batch_fragment_finishes (p : RTL.Program) (bs : Batches)
    (hw : batchWidthsSafe f bs = true)
    (pc : Nat) (fits : ProgramFits p pc (batchStatements pc bs))
    (s : Payload) (bound : WidthBound f s) :
    (p.run f.get (bs.length+1) (s.at pc)).result =
      some ((runBatches p.capacity bs s).map Payload.data) := by
  induction bs generalizing pc s with
  | nil =>
    have hh := fits.head
    simp [RTL.Program.run,RTL.Program.tick,Payload.at,hh,RTL.halt,RTL.Statement.eval,
      RTL.Register.write,RTL.Scalar.eval,Circuit.Runtime.result,runBatches]
  | cons as rest ih =>
    have hw' : as.all (actionWidthSafe f) = true ∧ batchWidthsSafe f rest = true := by
      simpa [batchWidthsSafe] using hw
    have first := rtl_tick_bundle p s bound fits.head
    change (p.run f.get (rest.length+1) (p.tick f.get (s.at pc))).result = _
    rw [first]
    cases he : clock p.capacity as s with
    | none =>
      rw [rtl_run_done p _ _ rfl]
      simp [Circuit.Runtime.result,runBatches,he]
    | some t =>
      simp only [runBatches,he,Option.bind_some]
      exact ih hw'.2 (pc+1) fits.tail t
        (batch_width_preserved as (List.all_eq_true.mp hw'.1) bound he)

theorem batchProgram_correct (bs : Batches) (hw : batchWidthsSafe f bs = true)
    (s : Payload) (bound : WidthBound f s) :
    ((batchProgram bs capacities).run f.get (bs.length+1) (s.at 0)).result =
      some ((runBatches (capacityOf capacities) bs s).map Payload.data) := by
  apply batch_fragment_finishes _ bs hw 0 _ s bound
  intro k hk; simp [batchProgram]

def allocatedBatches (code : Array Action) (cycles : Cycles) (candidate : Array Nat) : Batches :=
  let bs := batches code cycles
  renamed (chooseAllocation bs candidate).mapping bs

theorem allocatedProgram_correct (code : Array Action) (cycles : Cycles) (candidate : Array Nat)
    (hw : batchWidthsSafe f (allocatedBatches code cycles candidate) = true)
    (s : HybridWord.State) (x y : HybridWord.Word) (bound : WidthBound f (wordPayload s x y)) :
    ((batchProgram (allocatedBatches code cycles candidate) capacities).run f.get
      ((allocatedBatches code cycles candidate).length+1) ((wordPayload s x y).at 0)).result =
      some ((runCycles (capacityOf capacities) code cycles (wordPayload s x y)).map Payload.data) := by
  rw [batchProgram_correct _ hw _ bound]
  simp only [allocatedBatches,allocated_word_correct,runBatches_eq]

/-- The actual reusable-register RTL interpreter is connected to the ordinary
Lean source, not merely to a separate hand-written example specification. -/
theorem pipelineWord_rtl_correct (k : HybridWord.Kernel) (b : Build) (hb : 2 ≤ b.wires.size)
    (ii : Nat) (selected : (pipelineWord k b ii).1 = .scheduled code plan)
    (candidate : Array Nat) (hw : batchWidthsSafe f (allocatedBatches code plan.cycles candidate) = true)
    (s : HybridWord.State) (x y : HybridWord.Word) (bound : WidthBound f (wordPayload s x y)) :
    ((batchProgram (allocatedBatches code plan.cycles candidate) capacities).run f.get
      ((allocatedBatches code plan.cycles candidate).length+1) ((wordPayload s x y).at 0)).result =
      some ((k.source x y s).map HybridWord.State.encode) := by
  rw [allocatedProgram_correct code plan.cycles candidate hw s x y bound]
  obtain ⟨result,he,ho⟩ := pipelineWord_correct k b hb ii s x y (cap := capacityOf capacities)
  rw [selected] at he
  change runCycles _ _ _ _ = result at he
  rw [he,ho]

end IRComparison.Circuit.Pipelining
