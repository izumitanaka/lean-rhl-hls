import IRComparison.Core.Frontend

namespace IRComparison.NativeLoop

/-- Actual Lean do/for syntax, not an evaluation function for an AST.
    The body is an arbitrary native Lean function. -/
def run (body : Int → σ → Option σ) (start stride : Int) (count : Nat)
    (initial : σ) : Option σ := do
  let mut state := initial
  for k in List.range count do
    state ← body (start + (k : Int) * stride) state
  return state

/-- Independent recursion used to state the general bridge. -/
def steps (body : Int → σ → Option σ) (stride : Int) : Nat → Int → σ → Option σ
  | 0, _, s => some s
  | n+1, i, s => do steps body stride n (i + stride) (← body i s)

theorem forIn_option (xs : List α) (body : α → σ → Option σ) (initial : σ) :
    forIn xs initial (fun a s => do return ForInStep.yield (← body a s)) =
      xs.foldlM (fun s a => body a s) initial := by
  induction xs generalizing initial with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.forIn_cons, List.foldlM_cons]
      cases h : body a initial with
      | none => rfl
      | some t => exact ih t

theorem run_eq_fold (body : Int → σ → Option σ) (start stride : Int)
    (count : Nat) (initial : σ) :
    run body start stride count initial =
      (List.range count).foldlM (fun s (k : Nat) => body (start + (k : Int) * stride) s) initial := by
  simpa [run] using forIn_option (List.range count)
    (fun k s => body (start + (k : Int) * stride) s) initial

theorem fold_eq_steps (body : Int → σ → Option σ) (start stride : Int)
    (count : Nat) (initial : σ) :
    (List.range count).foldlM (fun s (k : Nat) => body (start + (k : Int) * stride) s) initial =
      steps body stride count start initial := by
  induction count generalizing start initial with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ_eq_map]
      simp only [List.foldlM_cons, List.foldlM_map, steps]
      simp only [Int.natCast_zero, Int.zero_mul, Int.add_zero]
      have indexEq (k : Nat) : start + ((k+1 : Nat) : Int) * stride =
          start + stride + (k : Int) * stride := by
        simp [Int.natCast_add, Int.add_mul, Int.add_assoc, Int.add_comm, Int.add_left_comm]
      simpa only [indexEq] using congrArg (fun f => (body start initial).bind f)
        (funext fun s => ih (start + stride) s)

theorem run_eq_steps (body : Int → σ → Option σ) (start stride : Int)
    (count : Nat) (initial : σ) :
    run body start stride count initial = steps body stride count start initial := by
  rw [run_eq_fold, fold_eq_steps]

theorem steps_eq_iterate (body : Int → State → Option State) (start stride : Int)
    (count : Nat) (initial : State) :
    steps body stride count start initial = Source.iterate body stride count start initial := by
  induction count generalizing start initial with
  | zero => rfl
  | succ n ih => simp [steps, Source.iterate, ih]

/-- The native loop is related to the imperative meaning for every native body,
    not by checking particular loop sizes or particular source functions. -/
theorem run_eq_iterate (body : Int → State → Option State) (start stride : Int)
    (count : Nat) (initial : State) :
    run body start stride count initial = Source.iterate body stride count start initial := by
  rw [run_eq_steps, steps_eq_iterate]

/-- A native scalar-returning loop need not use the IR State type. -/
theorem run_congr (f g : Int → σ → Option σ) (h : ∀ i s, f i s = g i s)
    (start stride : Int) (count : Nat) (initial : σ) :
    run f start stride count initial = run g start stride count initial := by
  have eq : f = g := funext fun i => funext (h i)
  rw [eq]

/-- Read/compute structure expressed using Lean's native Option monad. -/
def readBody (input : Input) (step : Step σ) (leftOffset rightOffset : Int)
    (i : Int) (s : σ) : Option σ := do
  let x ← input (i + leftOffset)
  let y ← input (i + rightOffset)
  step i x y s

theorem steps_readBody (input : Input) (step : Step σ) (start stride : Int)
    (count : Nat) (leftOffset rightOffset : Int) (initial : σ) :
    steps (readBody input step leftOffset rightOffset) stride count start initial =
      readLoop input step stride leftOffset rightOffset count start initial := by
  induction count generalizing start initial with
  | zero => rfl
  | succ n ih => simp [steps, readBody, readLoop, ih, Option.bind_assoc]

theorem run_readBody (input : Input) (step : Step σ) (start stride : Int)
    (count : Nat) (leftOffset rightOffset : Int) (initial : σ) :
    run (readBody input step leftOffset rightOffset) start stride count initial =
      readLoop input step stride leftOffset rightOffset count start initial := by
  rw [run_eq_steps, steps_readBody]

/-- Generic connection from an actual native body to the imperative path.
    The body correspondence remains an explicit obligation of the frontend. -/
theorem imperative_correct (native : Step State) (body : Imperative.Cmd)
    (body_correct : ∀ i x y s, body.eval i x y s = native i x y s)
    (input : Input) (start stride : Int) (count : Nat) (l r : Int) (initial : State) :
    (Imperative.transform (.loop start stride count l r body)).eval input initial =
      run (readBody input native l r) start stride count initial := by
  rw [Imperative.transform_correct, run_readBody]
  have heq : (fun i x y => body.eval i x y) = native :=
    funext fun i => funext fun x => funext fun y => funext (body_correct i x y)
  simp [Imperative.Program.eval, heq]

/-- Direct functional path: no imperative IR or lowerProgram occurs here. -/
theorem functional_correct (native : Step State) (body : Functional.Term)
    (body_correct : ∀ i x y s, body.eval i x y [s] = native i x y s)
    (input : Input) (start stride : Int) (count : Nat) (l r : Int) (initial : State) :
    (Functional.transform (.loop start stride count l r body)).eval input initial =
      run (readBody input native l r) start stride count initial := by
  rw [Functional.transform_correct, run_readBody]
  simp [Functional.Program.eval, body_correct]

end IRComparison.NativeLoop
