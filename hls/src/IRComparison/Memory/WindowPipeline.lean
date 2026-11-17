import IRComparison.Memory.FunctionalWindowPlan

namespace IRComparison.WindowPipeline
open CommunicationIR

/-- A region boundary materializes the input stream from an initialized array.
    This is a sequential boundary operation, not elimination of the preceding
    producer's output memory. Internal blocks use only destructive FIFO reads. -/
structure Stage where
  array : Nat
  size : Nat
  producer : List Int
  fifo : Bool
  code : List WindowTransport.Block
  source : Int → Int → State → Option State
  correct : ∀ s, (s.arrays array).size = size → ∀ x y values,
    (fifo = true → Corresponds (arrayInput (s.arrays array)) producer values) →
    (WindowTransport.eval (arrayInput (s.arrays array)) x y code [] s values).map Prod.fst = source x y s

  window : Option (WindowView.View array size source) := none

/-- Rebase a certified region on its named Lean source without changing code. -/
def Stage.rebase (p : Stage) (source : Int → Int → State → Option State)
    (same : ∀ x y s, p.source x y s = source x y s) : Stage where
  array := p.array
  size := p.size
  producer := p.producer
  fifo := p.fifo
  code := p.code
  source := source
  correct := fun s hs x y values hc => (p.correct s hs x y values hc).trans (same x y s)
  window := p.window.map (fun v => v.rebase same)

/-- The emitted indices are logical metadata, not transmitted tags. -/
def Stage.queue (p : Stage) (s : State) : Option (List Int) :=
  if p.fifo then emit (arrayInput (s.arrays p.array)) p.producer else some []

def Stage.eval (p : Stage) (x y : Int) (s : State) : Option State := do
  let values ← p.queue s
  (WindowTransport.eval (arrayInput (s.arrays p.array)) x y p.code [] s values).map Prod.fst

def Stage.Ready (p : Stage) (s : State) : Prop :=
  (s.arrays p.array).size = p.size ∧
  (p.fifo = true → ∀ j ∈ p.producer, 0 ≤ j ∧ j < (p.size:Int))

theorem Stage.queue_ready (p : Stage) (s : State) (ready : p.Ready s) :
    ∃ values, p.queue s = some values ∧
      (p.fifo = true → Corresponds (arrayInput (s.arrays p.array)) p.producer values) := by
  by_cases hf : p.fifo = true
  · have coverage : WindowCoverage.Covered (arrayInput (s.arrays p.array)) p.size :=
      ready.1 ▸ WindowCoverage.array_covered (s.arrays p.array)
    obtain ⟨values,h⟩ := WindowCoverage.emit_exists coverage (ready.2 hf)
    exact ⟨values,by simp [queue,hf,h],fun _ => emit_correct h⟩
  · exact ⟨[],by simp [queue,hf],fun h => False.elim (hf h)⟩

theorem Stage.eval_correct (p : Stage) (s : State) (ready : p.Ready s) (x y : Int) :
    p.eval x y s = p.source x y s := by
  obtain ⟨values,hq,hc⟩ := p.queue_ready s ready
  simp only [Stage.eval,hq,bind,Option.bind]
  exact p.correct s ready.1 x y values hc

theorem Stage.finishes (p : Stage) (s : State) (ready : p.Ready s) (x y : Int) :
    ∃ values steps remaining, p.queue s = some values ∧
      WindowControl.run (arrayInput (s.arrays p.array)) x y steps
        (.start (WindowControl.lower p.code) [] s values) = .stopped (p.source x y s) remaining := by
  obtain ⟨values,hq,hc⟩ := p.queue_ready s ready
  obtain ⟨steps,errorQueue,h⟩ := WindowControl.lower_finishes
    (input:=arrayInput (s.arrays p.array)) (x:=x) (y:=y) p.code [] s values
  have same := p.correct s ready.1 x y values hc
  cases he : WindowTransport.eval (arrayInput (s.arrays p.array)) x y p.code [] s values with
  | none =>
    simp only [he,Option.map_none] at same
    exact ⟨values,steps,errorQueue,hq,by simpa [he,WindowControl.resultEnd,← same] using h⟩
  | some pair =>
    obtain ⟨t,tail⟩ := pair
    simp only [he,Option.map_some] at same
    exact ⟨values,steps,tail,hq,by simpa [he,WindowControl.resultEnd,← same] using h⟩

def imperative (p : WindowTransport.Selected size array body stride count start producer) : Stage where
  array := array
  size := size
  producer := producer
  fifo := p.isFIFO
  code := p.code
  source := fun x y s => Source.iterate (fun j => body.eval j x y) stride count start s
  correct := by
    intro s hs x y values hc
    rw [p.code_correct]
    apply p.correct s hs x y values
    cases p with
    | memory => trivial
    | fifo => exact hc rfl

  window := match p with
    | .memory .memory => none
    | .memory (.buffered b) | .fifo _ b _ => some ⟨b.imperative,by
        intro s hs x y
        exact b.imperative_correct _ hs s rfl .nil x y⟩

def functional (p : FunctionalWindowPlan.Artifact size array body stride count start producer) : Stage where
  array := array
  size := size
  producer := producer
  fifo := p.isFIFO
  code := p.code
  source := fun x y s => Source.iterate (fun j t => body.eval j x y [t]) stride count start s
  correct := fun s hs x y values hc => p.sound s x y values hs hc
  window := p.window

/-- A sequence may select a different input array at each stage. Outputs are
    memory at these boundaries; no claim of concurrent producer fusion. -/
def eval (x y : Int) : List Stage → State → Option State
  | [],s => some s
  | p::ps,s => do eval x y ps (← p.eval x y s)

def source (x y : Int) : List Stage → State → Option State
  | [],s => some s
  | p::ps,s => do source x y ps (← p.source x y s)

/-- Only reached regions need an initialized input. Failure does not require
    assumptions about unreachable later regions. -/
def Ready (x y : Int) : List Stage → State → Prop
  | [],_ => True
  | p::ps,s => p.Ready s ∧ ∀ t, p.source x y s = some t → Ready x y ps t

theorem eval_correct (stages : List Stage) (s : State) (ready : Ready x y stages s) :
    eval x y stages s = source x y stages s := by
  induction stages generalizing s with
  | nil => rfl
  | cons p ps ih =>
    simp only [eval,source,p.eval_correct s ready.1 x y]
    cases h : p.source x y s with
    | none => rfl
    | some t => exact ih t (ready.2 t h)

end IRComparison.WindowPipeline
