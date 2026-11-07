import IRComparison.Core.StateLowering
import IRComparison.Core.SnapshotControlIR

namespace IRComparison.ControlIR

/-- A sequential controller before datapath and memory-timing lowering.
    An expression is still an abstract transaction, not a one-cycle circuit. -/
inductive Instr where
  | snapshots (code : SnapshotIR.Code)
  | assign (reg : Nat) (value : Expr)
  | store (array : Nat) (address value : Expr)
  | capture (value : Expr)
  | release
  | test (condition : Expr) (yes no : List Instr)
  | repeat (count : Nat) (body : List Instr)
  | forRange (count : Expr) (body : List Instr)
  | rangeStep (index remaining : Nat) (body : List Instr)
  deriving Repr

inductive Config where
  | running (pending : List Instr) (state : State) (locals : List Int)
  | inSnapshots (pending : List Instr) (locals : List Int) (snapshot : SnapshotControlIR.Config)
  | stopped (result : Option State)

/-- Explicit next-control-state transition. Local capture and release are
    private; no source-visible register is used as scratch storage. -/
def step (i x y : Int) : Config → Config
  | .inSnapshots _ _ (.stopped none) => .stopped none
  | .inSnapshots rest ls (.stopped (some s)) => .running rest s ls
  | .inSnapshots rest ls c@(.running ..) => .inSnapshots rest ls (SnapshotControlIR.step i x y c)
  | .inSnapshots rest ls c@(.iterating ..) => .inSnapshots rest ls (SnapshotControlIR.step i x y c)
  | .inSnapshots rest ls c@(.returning ..) => .inSnapshots rest ls (SnapshotControlIR.step i x y c)
  | .running (.snapshots code :: rest) s ls => .inSnapshots rest ls (.running code [s] ls [])
  | .stopped r => .stopped r
  | .running [] s _ => .stopped (some s)
  | .running (.assign r e :: rest) s ls =>
      match e.eval i x y s ls with
      | none => .stopped none
      | some v => .running rest (s.set r v) ls
  | .running (.store a j e :: rest) s ls =>
      match (do s.write a (← j.eval i x y s ls) (← e.eval i x y s ls)) with
      | none => .stopped none
      | some t => .running rest t ls
  | .running (.capture e :: rest) s ls =>
      match e.eval i x y s ls with
      | none => .stopped none
      | some v => .running rest s (v :: ls)
  | .running (.release :: rest) s ls =>
      match ls with
      | [] => .stopped none
      | _ :: tail => .running rest s tail
  | .running (.test e a b :: rest) s ls =>
      match e.eval i x y s ls with
      | none => .stopped none
      | some v => .running ((if v != 0 then a else b) ++ rest) s ls
  | .running (.forRange e body :: rest) s ls =>
      match e.eval i x y s ls with
      | none => .stopped none
      | some n => .running (.rangeStep 0 n.toNat body :: rest) s ls
  | .running (.rangeStep _ 0 _ :: rest) s ls => .running rest s ls
  | .running (.rangeStep k (n+1) body :: rest) s ls =>
      .running (.capture (.lit (Int.ofNat k)) :: body ++ .release :: .rangeStep (k+1) n body :: rest) s ls
  | .running (.repeat 0 _ :: rest) s ls => .running rest s ls
  | .running (.repeat (n+1) body :: rest) s ls =>
      .running (body ++ .repeat n body :: rest) s ls

/-- Compilation preserves counted loops rather than statically unrolling them. -/
def lower : Imperative.Cmd → List Instr
  | .skip => []
  | .assign r e => [.assign r e]
  | .store a j e => [.store a j e]
  | .letValue e b => .capture e :: (lower b ++ [.release])
  | .seq a b => lower a ++ lower b
  | .branch e a b => [.test e (lower a) (lower b)]
  | .repeat n b => [.repeat n (lower b)]
  | .forRange e b => [.forRange e (lower b)]

def resume (result : Option State) (rest : List Instr) (locals : List Int) : Config :=
  match result with
  | none => .stopped none
  | some s => .running rest s locals

/-- A finite execution in the actual transition system. -/
inductive Reaches (i x y : Int) : Config → Config → Prop where
  | refl (a) : Reaches i x y a a
  | next {a b} : Reaches i x y (step i x y a) b → Reaches i x y a b

theorem Reaches.trans (h : Reaches i x y a b) (g : Reaches i x y b c) : Reaches i x y a c := by
  induction h with
  | refl => exact g
  | next _ ih => exact .next (ih g)

theorem lift_snapshots (rest : List Instr) (locals : List Int)
    (h : SnapshotControlIR.Reaches i x y a b) :
    Reaches i x y (.inSnapshots rest locals a) (.inSnapshots rest locals b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih =>
    cases a with
    | running => exact .next ih
    | iterating => exact .next ih
    | returning => exact .next ih
    | stopped r => simpa only [SnapshotControlIR.step] using ih

theorem snapshots_correct (code : SnapshotIR.Code) (i x y : Int) (s : State)
    (ls : List Int) (rest : List Instr) :
    Reaches i x y (.running (.snapshots code :: rest) s ls)
      (resume (code.eval i x y [s] ls) rest ls) := by
  apply Reaches.next
  have h := SnapshotControlIR.lower_correct code i x y [s] ls []
  apply (lift_snapshots rest ls (h.trans (.next (.refl _)))).trans
  cases code.eval i x y [s] ls <;> exact .next (.refl _)

theorem repeat_succ (n : Nat) (b : Imperative.Cmd) (i x y : Int) (s : State) (ls : List Int) :
    (Imperative.Cmd.repeat (n+1) b).eval i x y s ls =
      (b.eval i x y s ls).bind (fun t => (Imperative.Cmd.repeat n b).eval i x y t ls) := by
  simp [Imperative.Cmd.eval, List.range_succ_eq_map, List.foldlM_map, List.foldlM_cons]

theorem range_correct (b : Imperative.Cmd) (i x y : Int)
    (bodyCorrect : ∀ s ls rest, Reaches i x y (.running (lower b ++ rest) s ls)
      (resume (b.eval i x y s ls) rest ls))
    (n k : Nat) (s : State) (ls : List Int) (rest : List Instr) :
    Reaches i x y (.running (.rangeStep k n (lower b) :: rest) s ls)
      (resume ((List.range' k n).foldlM (fun t j => b.eval i x y t (Int.ofNat j :: ls)) s) rest ls) := by
  induction n generalizing k s with
  | zero => exact .next (.refl _)
  | succ n ih =>
      apply Reaches.next
      apply Reaches.next
      simp only [step, Expr.eval, List.range', List.foldlM_cons]
      apply (bodyCorrect s (Int.ofNat k :: ls) (.release :: .rangeStep (k+1) n (lower b) :: rest)).trans
      cases hb : b.eval i x y s (Int.ofNat k :: ls) <;> simp only [hb, resume, bind, Option.bind]
      · exact .refl _
      · exact .next (ih (k+1) _)

/-- Every body executes to its semantic result and restores its local scope,
    for any following code. Failure halts instead of executing that code. -/
theorem lower_correct (b : Imperative.Cmd) (i x y : Int) (s : State)
    (ls : List Int) (rest : List Instr) :
    Reaches i x y (.running (lower b ++ rest) s ls)
      (resume (b.eval i x y s ls) rest ls) := by
  induction b generalizing s ls rest with
  | skip => exact .refl _
  | assign r e =>
      apply Reaches.next
      cases h : e.eval i x y s ls <;> simp [lower, step, Imperative.Cmd.eval, h, resume]
      all_goals exact .refl _
  | store a j e =>
      apply Reaches.next
      change Reaches i x y (resume (do s.write a (← j.eval i x y s ls) (← e.eval i x y s ls)) rest ls)
        (resume (do s.write a (← j.eval i x y s ls) (← e.eval i x y s ls)) rest ls)
      exact .refl _
  | letValue e b ih =>
      apply Reaches.next
      cases he : e.eval i x y s ls with
      | none => simpa [lower, step, he, Imperative.Cmd.eval, resume] using (Reaches.refl (i := i) (x := x) (y := y) (.stopped none))
      | some v =>
        simp only [lower, List.cons_append, List.append_assoc, List.singleton_append, step, he]
        simp only [Imperative.Cmd.eval, he, Option.bind_some]
        have first := ih s (v :: ls) (.release :: rest)
        apply first.trans
        cases hb : b.eval i x y s (v :: ls) <;> simp [hb, resume]
        · exact .refl _
        · exact .next (.refl _)
  | seq a b iha ihb =>
      simp only [lower, List.append_assoc, Imperative.Cmd.eval]
      apply (iha s ls (lower b ++ rest)).trans
      cases ha : a.eval i x y s ls <;> simp [ha, resume]
      · exact .refl _
      · exact ihb _ ls rest
  | branch e a b iha ihb =>
      apply Reaches.next
      cases he : e.eval i x y s ls with
      | none => simpa [lower, step, he, Imperative.Cmd.eval, resume] using (Reaches.refl (i := i) (x := x) (y := y) (.stopped none))
      | some v =>
        simp only [lower, List.singleton_append, step, he, Imperative.Cmd.eval, Option.bind_some]
        by_cases hz : v = 0
        · simpa [hz] using ihb s ls rest
        · simpa [hz] using iha s ls rest
  | «repeat» n b ih =>
      induction n generalizing s with
      | zero => exact .next (.refl _)
      | succ n ihn =>
          apply Reaches.next
          simp only [lower, List.singleton_append, step, repeat_succ]
          apply (ih s ls (.repeat n (lower b) :: rest)).trans
          cases hb : b.eval i x y s ls <;> simp [hb, resume]
          · exact .refl _
          · exact ihn _

  | forRange e b ih =>
      apply Reaches.next
      cases he : e.eval i x y s ls with
      | none => simpa [lower, step, Imperative.Cmd.eval,he,resume] using
          (Reaches.refl (i := i) (x := x) (y := y) (.stopped none))
      | some n =>
          simpa only [lower, List.singleton_append, step, Imperative.Cmd.eval, he, bind, Option.bind,
            List.range_eq_range'] using range_correct b i x y ih n.toNat 0 s ls rest

/-- Executable bounded simulation. Reaching the bound is distinguishable from
    failed execution: it returns a still-running configuration. -/
def run (i x y : Int) : Nat → Config → Config
  | 0, c => c
  | n+1, c => run i x y n (step i x y c)

theorem Reaches.finite (h : Reaches i x y a b) : ∃ n, run i x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem lower_finishes (b : Imperative.Cmd) (i x y : Int) (s : State) (ls : List Int) :
    ∃ n, run i x y n (.running (lower b) s ls) = .stopped (b.eval i x y s ls) := by
  have first := lower_correct b i x y s ls []
  simp only [List.append_nil] at first
  apply Reaches.finite
  apply first.trans
  cases h : b.eval i x y s ls <;> simp [resume]
  · exact .refl _
  · exact .next (.refl _)

theorem run_add (i x y : Int) (n m : Nat) (c : Config) :
    run i x y (n+m) c = run i x y m (run i x y n c) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih => simpa [run, Nat.succ_add] using ih (step i x y c)

@[simp] theorem run_stopped (i x y : Int) (n : Nat) (r : Option State) :
    run i x y n (.stopped r) = .stopped r := by
  induction n <;> simp_all [run, step]

/-- A simulation cannot terminate with a different result at another bound. -/
theorem result_unique (ha : run i x y n c = .stopped a)
    (hb : run i x y m c = .stopped b) : a = b := by
  have both : run i x y (n+m) c = .stopped a := by rw [run_add, ha, run_stopped]
  have other : run i x y (n+m) c = .stopped b := by rw [Nat.add_comm, run_add, hb, run_stopped]
  rw [both] at other
  exact Config.stopped.inj other

theorem lower_result_correct (b : Imperative.Cmd) (i x y : Int) (s : State) (ls : List Int)
    (h : run i x y fuel (.running (lower b) s ls) = .stopped result) :
    result = b.eval i x y s ls := by
  obtain ⟨n,hn⟩ := lower_finishes b i x y s ls
  exact result_unique h hn

/-- General state-version allocation, with explicit private snapshot storage. -/
def lowerVersions (b : Functional.Term) : List Instr := [.snapshots (SnapshotIR.lower b)]

theorem snapshots_finishes (code : SnapshotIR.Code) (i x y : Int) (s : State) (ls : List Int) :
    ∃ n, run i x y n (.running [.snapshots code] s ls) = .stopped (code.eval i x y [s] ls) := by
  apply Reaches.finite
  apply (snapshots_correct code i x y s ls []).trans
  cases code.eval i x y [s] ls <;> simp [resume]
  · exact .refl _
  · exact .next (.refl _)

theorem lowerVersions_finishes (b : Functional.Term) (i x y : Int) (s : State) (ls : List Int) :
    ∃ n, run i x y n (.running (lowerVersions b) s ls) = .stopped (b.eval i x y [s] ls) := by
  simpa only [SnapshotIR.lower_correct] using snapshots_finishes (SnapshotIR.lower b) i x y s ls

/-- The functional route uses the proved single-state allocation pass. -/
def lowerFunctional (b : Functional.Term) : Option (List Instr) := (StateLowering.lower b).map lower

theorem lowerFunctional_finishes (b : Functional.Term) (code : List Instr)
    (h : lowerFunctional b = some code) (i x y : Int) (s : State) (ls : List Int) :
    ∃ n, run i x y n (.running code s ls) = .stopped (b.eval i x y [s] ls) := by
  cases hb : StateLowering.lower b <;> simp [lowerFunctional,hb] at h
  subst code
  rw [← StateLowering.lower_correct b _ hb i x y s [] ls]
  exact lower_finishes _ i x y s ls

end IRComparison.ControlIR
