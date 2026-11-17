import IRComparison.Circuit.Pipelining.RTL
import IRComparison.Circuit.Pipelining.Bounds

namespace IRComparison.Circuit.Pipelining

def statements (code : Array Action) : Nat → Cycles → List RTL.Statement
  | _,[] => [RTL.halt]
  | pc,ids :: rest => lowerClock (pc+1) (ids.map (actionAt code)) :: statements code (pc+1) rest

def lowerProgram (code : Array Action) (cycles : Cycles) (capacities : Array (Nat × Nat)) : RTL.Program :=
  ⟨0,(statements code 0 cycles).toArray,capacities⟩

def ProgramFits (p : RTL.Program) (base : Nat) (ss : List RTL.Statement) : Prop :=
  ∀ k, k < ss.length → p.cases[base+k]? = ss[k]?

theorem ProgramFits.head (h : ProgramFits p base (s :: ss)) : p.cases[base]? = some s := by
  simpa using h 0 (by simp)

theorem ProgramFits.tail (h : ProgramFits p base (s :: ss)) : ProgramFits p (base+1) ss := by
  intro k hk
  simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h (k+1) (by simpa using Nat.succ_lt_succ hk)

theorem lowerProgram_fits : ProgramFits (lowerProgram code cycles capacities) 0 (statements code 0 cycles) := by
  intro k hk
  simp [lowerProgram]

theorem rtl_run_done (p : RTL.Program) (n : Nat) (r : Circuit.Runtime) (hd : r.done = true) :
    p.run wr n r = r := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [RTL.Program.run,RTL.Program.tick,hd] using ih

theorem rtl_tick_bundle (p : RTL.Program) (s : Payload) (bound : WidthBound f s)
    (hc : p.cases[pc]? = some (lowerClock (pc+1) as)) :
    p.tick f.get (s.at pc) = match clock p.capacity as s with
      | none => {s.at pc with done := true,error := true}
      | some t => t.at (pc+1) := by
  simp only [RTL.Program.tick,Payload.at,Bool.false_eq_true,ite_false,hc,Option.getD_some]
  have hb : InputsBound (s.at pc).data (s.at pc).wires f.get := bound.inputs
  have h := lowerClock_bit_correct (cap := p.capacity) (pc+1) as (s.at pc) hb
  simpa only [Payload.at,Circuit.Runtime.payload,withPayload] using h

theorem rtl_fragment_finishes (p : RTL.Program) (code : Array Action) (cycles : Cycles)
    (hs : safe code cycles = true) (hw : widthsSafe f code cycles = true)
    (pc : Nat) (fits : ProgramFits p pc (statements code pc cycles))
    (s : Payload) (bound : WidthBound f s) :
    (p.run f.get (cycles.length+1) (s.at pc)).result =
      some ((runCycles p.capacity code cycles s).map Payload.data) := by
  induction cycles generalizing pc s with
  | nil =>
    have hh := fits.head
    simp [RTL.Program.run,RTL.Program.tick,Payload.at,hh,RTL.halt,RTL.Statement.eval,
      RTL.Register.write,RTL.Scalar.eval,Circuit.Runtime.result,runCycles]
  | cons ids rest ih =>
    have hs' : safe code rest = true := by
      have hh : BundleSafe (ids.map (actionAt code)) ∧ safe code rest = true := by simpa [safe] using hs
      exact hh.2
    have hw' : widthsSafe f code rest = true := by
      have hh : (ids.all (fun id => actionWidthSafe f (actionAt code id)) = true) ∧ widthsSafe f code rest = true := by
        simpa [widthsSafe] using hw
      exact hh.2
    have first := rtl_tick_bundle p s bound fits.head
    change (p.run f.get (rest.length+1) (p.tick f.get (s.at pc))).result = _
    rw [first]
    cases he : clock p.capacity (ids.map (actionAt code)) s with
    | none =>
      rw [rtl_run_done p _ _ rfl]
      simp [Circuit.Runtime.result,runCycles,he]
    | some t =>
      simp only [runCycles,he,Option.bind_some]
      exact ih hs' hw' (pc+1) fits.tail t (clock_bound_head hs hw bound he)

theorem lowerProgram_correct (code : Array Action) (cycles : Cycles)
    (hs : safe code cycles = true) (hw : widthsSafe f code cycles = true)
    (s : Payload) (bound : WidthBound f s) :
    ((lowerProgram code cycles capacities).run f.get (cycles.length+1) (s.at 0)).result =
      some ((runCycles (capacityOf capacities) code cycles s).map Payload.data) :=
  rtl_fragment_finishes _ code cycles hs hw 0 lowerProgram_fits s bound

theorem sequential_safe (code : Array Action) : safe code (sequential code) = true := by
  simp [safe,sequential,BundleSafe,List.all_map,Function.comp_def]

theorem compile_safe (code : Array Action) (candidate : Cycles) :
    safe code (compile code candidate).cycles = true := by
  unfold compile
  split
  · have h : valid code candidate = true := by assumption
    simpa [valid] using (show safe code candidate = true ∧ _ from by simpa [valid] using h).1
  · exact sequential_safe code

theorem compiled_rtl_correct (code : Array Action) (candidate : Cycles)
    (hw : widthsSafe f code (compile code candidate).cycles = true)
    (s : Payload) (bound : WidthBound f s) :
    ((lowerProgram code (compile code candidate).cycles capacities).run f.get
      ((compile code candidate).cycles.length+1) (s.at 0)).result =
      some ((sourceEval (capacityOf capacities) code s).map Payload.data) := by
  rw [lowerProgram_correct code _ (compile_safe code candidate) hw s bound,compile_correct]

end IRComparison.Circuit.Pipelining
