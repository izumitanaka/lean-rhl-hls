import IRComparison.Memory.FunctionalSymbolicBody
import IRComparison.Memory.SymbolicWindowLoop

namespace IRComparison.FunctionalSymbolicLoop
open AffineAddress SymbolicWindowSchedule

def allocate (c : FunctionalSymbolicBody.Compiled array depth coefficient offsets source)
    (before after : Imperative.Cmd) (hbefore : StateLowering.lower source = some before)
    (hafter : StateLowering.lower c.code = some after) :
    SymbolicWindowBody.Compiled array depth coefficient offsets before where
  code := after
  guards := c.guards
  frame := by
    intro i x y s ls out h
    have same := StateLowering.lower_correct source before hbefore i x y s [] ls
    exact c.frame i x y s [] ls out (same.symm.trans h)
  correct := by
    intro i valid data values locals s x y frozen held len
    rw [StateLowering.lower_correct c.code after hafter i x y s [] (locals++values)]
    rw [c.correct i valid data values locals s [] x y frozen held len]
    exact (StateLowering.lower_correct source before hbefore i x y s [] locals).symm

structure Artifact (size array : Nat) (source : Functional.Term) (start stride : Int) (count : Nat) where
  original : Imperative.Cmd
  originalCorrect : StateLowering.lower source = some original
  plan : SymbolicWindowLoop.Plan size array original start stride count

def compile (size array : Nat) (source : Functional.Term) (start stride : Int) (count : Nat) :
    Option (Artifact size array source start stride count) := do
  match originalEq : StateLowering.lower source with
  | none => none
  | some original => do
    let accessed ← FunctionalSymbolicBody.accesses array source
    let first ← accessed.head?
    let offsets := accessed.map Linear.offset
    let buffered := SymbolicWindowLoop.reuse offsets (first.coefficient*stride) count
    let window ← (if buffered then (PaperCore.WindowAnalysis.bounds offsets).map
      (fun (low,high) => WindowSchedule.interval (first.coefficient*stride < 0) low high)
      else some offsets)
    let body ← FunctionalSymbolicBody.compile array 0 first.coefficient window source
    match allocation : StateLowering.lower body.code with
    | none => none
    | some allocated =>
      if safe : checkGuards (body.guards++coverageGuards size first.coefficient window) start stride count = true then
        some ⟨original,originalEq,⟨first.coefficient,window,buffered,
          allocate body original allocated originalEq allocation,safe⟩⟩
      else none

theorem Artifact.correct (a : Artifact size array source start stride count) (s : State)
    (sized : (s.arrays array).size = size) :
    a.plan.code.eval (arrayInput (s.arrays array)) x y s =
      Source.iterate (fun i t => source.eval i x y [t]) stride count start s := by
  rw [a.plan.correct s sized]
  exact Source.iterate_congr _ _
    (fun i t => StateLowering.lower_correct source a.original a.originalCorrect i x y t [] []) stride count start s

structure Selection (size array : Nat) (source : Functional.Term) (start stride : Int) (count : Nat) where
  code : SymbolicWindowLoop.Code
  optimized : Bool
  correct : ∀ s, (s.arrays array).size = size → ∀ x y,
    code.eval (arrayInput (s.arrays array)) x y s =
      Source.iterate (fun i t => source.eval i x y [t]) stride count start s

def select (size array : Nat) (source : Functional.Term) (before : Imperative.Cmd)
    (allocation : StateLowering.lower source = some before) (start stride : Int) (count : Nat) :
    Selection size array source start stride count :=
  match compile size array source start stride count with
  | some p => ⟨p.plan.code,true,fun s hs x y => p.correct s hs⟩
  | none => ⟨SymbolicWindowLoop.direct before start stride count,false,by
    intro s hs x y
    rw [SymbolicWindowLoop.direct_correct]
    exact Source.iterate_congr _ _ (fun i t => StateLowering.lower_correct source before allocation i x y t [] []) stride count start s⟩

end IRComparison.FunctionalSymbolicLoop
