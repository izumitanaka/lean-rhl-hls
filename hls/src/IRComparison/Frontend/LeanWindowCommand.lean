import IRComparison.Frontend.LeanControlCommand
import IRComparison.Memory.WindowPipeline
import IRComparison.Memory.SymbolicWindowControl
import IRComparison.Memory.CompactTransport
import IRComparison.Memory.CompactFIFOControl
import IRComparison.Memory.CompactStage
import IRComparison.Memory.UnifiedPipeline

namespace IRComparison
open Lean Elab Command

/-- Ordinary Lean array-reading body -> min/max window -> FIFO/memory choice.
    Each body IR is analyzed and rewritten directly. Functional allocation
    follows window substitution; geometry and FIFO routing are shared. -/
elab "hls_window " source:ident " as " target:ident : command => do
  elabCommand (← `(hls_control $source as $target))
  let base := target.getId
  let fbody := mkIdent (.str base "functionalBody")
  let normalized := mkIdent (.str base "functionalAllocatedBody")
  let normProof := mkIdent (.str base "functionalAllocatedBody_correct")
  let fp := mkIdent (.str base "functionalBody_correct")
  elabCommand (← `(def $normalized : Imperative.Cmd := (StateLowering.lower $fbody).get (by decide)))
  elabCommand (← `(theorem $normProof (i x y : Int) (s : State) : ($normalized).eval i x y s [] = $source i x y s := by
    have h := StateLowering.lower_correct $fbody $normalized (by rfl) i x y s [] []
    exact h.trans ($fp i x y s)))
  for (suffix,body,proof) in [
      ("imperative",mkIdent (.str base "imperativeBody"),mkIdent (.str base "imperativeBody_correct")),
      ("functional",fbody,fp)] do
    let compact := mkIdent (.str base (suffix ++ "CompactWindow"))
    let compactCorrect := mkIdent (.str base (suffix ++ "CompactWindow_correct"))
    let compactFinishes := mkIdent (.str base (suffix ++ "CompactWindow_finishes"))
    if suffix == "imperative" then
      elabCommand (← `(def $compact (size array : Nat) (start stride : Int) (count : Nat) :=
        SymbolicWindowLoop.select size array $body start stride count))
    else
      elabCommand (← `(def $compact (size array : Nat) (start stride : Int) (count : Nat) :=
        FunctionalSymbolicLoop.select size array $body $normalized (by rfl) start stride count))
    let compactEq ← if suffix == "imperative" then
      `(by
        rw [SymbolicWindowLoop.Selected.correct]
        exact Source.iterate_congr _ _ (fun j t => $proof j x y t) stride count start s
        exact sized)
      else
      `(by
        rw [FunctionalSymbolicLoop.Selection.correct _ s sized x y]
        exact Source.iterate_congr _ _ (fun j t => $proof j x y t) stride count start s)
    elabCommand (← `(theorem $compactCorrect (size array : Nat) (start stride : Int) (count : Nat)
        (s : State) (sized : (s.arrays array).size = size) (x y : Int) :
        ($compact size array start stride count).code.eval (arrayInput (s.arrays array)) x y s =
          Source.iterate (fun j => $source j x y) stride count start s := $compactEq))
    elabCommand (← `(theorem $compactFinishes (size array : Nat) (start stride : Int) (count : Nat)
        (s : State) (sized : (s.arrays array).size = size) (x y : Int) :
        ∃ steps, SymbolicWindowControl.run ($compact size array start stride count).code
          (arrayInput (s.arrays array)) x y steps (.start s) =
          .stopped (Source.iterate (fun j => $source j x y) stride count start s) := by
      have h := (SymbolicWindowControl.correct (input:=arrayInput (s.arrays array))
        (x:=x) (y:=y) ($compact size array start stride count).code s).finite
      simpa only [($compactCorrect size array start stride count s sized x y)] using h))
    let compactStage := mkIdent (.str base (suffix ++ "CompactStage"))
    let compactWrap := mkIdent (if suffix == "imperative" then ``CompactStage.imperative else ``CompactStage.functional)
    elabCommand (← `(def $compactStage (size array : Nat) (start stride : Int) (count : Nat) : CompactStage.Stage :=
      ($compactWrap ($compact size array start stride count)).rebase
        (fun x y s => Source.iterate (fun j => $source j x y) stride count start s)
        (by intro x y s; exact Source.iterate_congr _ _ (fun j t => $proof j x y t) stride count start s)))
    let transport := mkIdent (.str base (suffix ++ "CompactTransport"))
    let transportCorrect := mkIdent (.str base (suffix ++ "CompactTransport_correct"))
    elabCommand (← `(def $transport (size array : Nat) (start stride : Int) (count : Nat) (supplier : CompactSequence.Seq) :=
      CompactTransport.select ($compact size array start stride count).code supplier))
    elabCommand (← `(theorem $transportCorrect (size array : Nat) (start stride : Int) (count : Nat)
        (supplier : CompactSequence.Seq) (s : State) (sized : (s.arrays array).size = size)
        (x y : Int) (queue : List Int)
        (hq : CommunicationIR.Corresponds (arrayInput (s.arrays array)) supplier.entries queue) :
        ($transport size array start stride count supplier).eval (arrayInput (s.arrays array)) x y s queue =
          Source.iterate (fun j => $source j x y) stride count start s := by
      rw [CompactTransport.Selected.correct _ hq]
      exact $compactCorrect size array start stride count s sized x y))
    let generated := mkIdent (.str base (suffix ++ "Window"))
    let correct := mkIdent (.str base (suffix ++ "Window_correct"))
    let finishes := mkIdent (.str base (suffix ++ "Window_finishes"))
    let finishLemma := mkIdent (if suffix == "imperative" then ``WindowControl.selected_finishes else ``FunctionalWindowPlan.Artifact.finishes)
    if suffix == "imperative" then
      elabCommand (← `(def $generated (size array : Nat) (start stride : Int) (count : Nat) (producer : List Int) :=
        WindowTransport.compile size array $body stride count start producer))
    else
      elabCommand (← `(def $generated (size array : Nat) (start stride : Int) (count : Nat) (producer : List Int) :=
        FunctionalWindowPlan.compile $fbody $normalized (by rfl) size array start stride count producer))
    let stage := mkIdent (.str base (suffix ++ "Stage"))
    let wrap := mkIdent (if suffix == "imperative" then ``WindowPipeline.imperative else ``WindowPipeline.functional)
    elabCommand (← `(def $stage (size array : Nat) (start stride : Int) (count : Nat) (producer : List Int) : WindowPipeline.Stage :=
      ($wrap ($generated size array start stride count producer)).rebase
        (fun x y s => Source.iterate (fun j => $source j x y) stride count start s)
        (by intro x y s; exact Source.iterate_congr _ _ (fun j t => $proof j x y t) stride count start s)))
    elabCommand (← `(theorem $correct (size array : Nat) (start stride : Int) (count : Nat) (producer : List Int)
        (s : State) (sized : (s.arrays array).size = size) (x y : Int) (values : List Int)
        (contract : ($generated size array start stride count producer).Contract (s.arrays array) values) :
        ($generated size array start stride count producer).eval (s.arrays array) x y s values =
          Source.iterate (fun j => $source j x y) stride count start s := by
      rw [($generated size array start stride count producer).correct s sized x y values contract]
      exact Source.iterate_congr _ _ (fun j t => $proof j x y t) stride count start s))
    elabCommand (← `(theorem $finishes (size array : Nat) (start stride : Int) (count : Nat) (producer : List Int)
        (s : State) (sized : (s.arrays array).size = size) (x y : Int) (values : List Int)
        (contract : ($generated size array start stride count producer).Contract (s.arrays array) values) :
        ∃ steps remaining, WindowControl.run (arrayInput (s.arrays array)) x y steps
          (.start (WindowControl.lower ($generated size array start stride count producer).code) [] s values) =
          .stopped (Source.iterate (fun j => $source j x y) stride count start s) remaining := by
      obtain ⟨steps,remaining,h⟩ :=  $finishLemma ($generated size array start stride count producer) s sized x y values contract
      have same := Source.iterate_congr _ _ (fun j t => $proof j x y t) stride count start s
      refine ⟨steps,remaining,?_⟩
      rw [← same]
      exact h))

    let kernel := mkIdent (.str base (suffix ++ "Kernel"))
    elabCommand (← `(def $kernel (size array : Nat) (start stride : Int) (count : Nat)
        (supplier : Unit → List Int) : UnifiedPipeline.Kernel :=
      ⟨$compactStage size array start stride count,
       (fun _ => $stage size array start stride count (supplier ())),by intros; rfl⟩))

  let imp := mkIdent (.str base "imperativeWindow")
  let funWindow := mkIdent (.str base "functionalWindow")
  let impCorrect := mkIdent (.str base "imperativeWindow_correct")
  let funCorrect := mkIdent (.str base "functionalWindow_correct")
  let agree := mkIdent (.str base "windows_agree")
  elabCommand (← `(theorem $agree (size array : Nat) (start stride : Int) (count : Nat) (producer : List Int)
      (s : State) (sized : (s.arrays array).size = size) (x y : Int) (values : List Int)
      (hi : ($imp size array start stride count producer).Contract (s.arrays array) values)
      (hf : ($funWindow size array start stride count producer).Contract (s.arrays array) values) :
      ($imp size array start stride count producer).eval (s.arrays array) x y s values =
        ($funWindow size array start stride count producer).eval (s.arrays array) x y s values := by
    rw [($impCorrect size array start stride count producer s sized x y values hi),
      ($funCorrect size array start stride count producer s sized x y values hf)]))

end IRComparison
