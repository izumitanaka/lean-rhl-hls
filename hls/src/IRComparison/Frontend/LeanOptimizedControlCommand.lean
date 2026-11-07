import IRComparison.Frontend.LeanControlCommand
import IRComparison.Core.ProgramControlIR

namespace IRComparison
open Lean Elab Command

/-- Ordinary Lean body -> both optimized loop programs -> explicit controllers.
    Loop parameters and immutable input remain arguments of the generated code
    and theorems, rather than being specialized to a benchmark instance. -/
elab "hls_optimized_control " source:ident " as " target:ident : command => do
  elabCommand (← `(hls_control $source as $target))
  let base := target.getId
  let ip := mkIdent (.str base "imperative")
  let fp := mkIdent (.str base "functional")
  let ips := mkIdent (.str base "imperative_correct")
  let fps := mkIdent (.str base "functional_correct")
  let fb := mkIdent (.str base "functionalBody")
  let fbc := mkIdent (.str base "functionalControl")
  let fbl := mkIdent (.str base "functionalControl_lowered")
  let ic := mkIdent (.str base "imperativeOptimizedControl")
  let fc := mkIdent (.str base "functionalOptimizedControl")
  let fl := mkIdent (.str base "functionalOptimizedControl_lowered")
  let ih := mkIdent (.str base "imperativeOptimizedControl_correct")
  let fh := mkIdent (.str base "functionalOptimizedControl_correct")
  elabCommand (← `(def $ic (start stride : Int) (count : Nat) (left right : Int) :
      List ProgramControlIR.Instr := ProgramControlIR.lower ($ip start stride count left right)))
  elabCommand (← `(def $fc (start stride : Int) (count : Nat) (left right : Int) :
      List ProgramControlIR.Instr :=
        ProgramControlIR.optimizedLoopCode start stride count left right $fbc))
  elabCommand (← `(theorem $fl (start stride : Int) (count : Nat) (left right : Int) :
      ProgramControlIR.lowerFunctional ($fp start stride count left right) =
        some ($fc start stride count left right) := by
    exact ProgramControlIR.lowerFunctional_optimizedLoop $fb $fbc $fbl start stride count left right))
  elabCommand (← `(theorem $ih (start stride : Int) (count : Nat) (left right : Int)
      (input : Input) (s : State) :
      ∃ fuel, ProgramControlIR.run input fuel
        (.running ($ic start stride count left right) s ProgramControlIR.initial) =
        .stopped (BodyBackends.runSource $source start stride count left right input s) := by
    have h := ProgramControlIR.lower_finishes ($ip start stride count left right) input s ProgramControlIR.initial
    have hs : ($ip start stride count left right).eval input s =
        BodyBackends.runSource $source start stride count left right input s :=
      $ips start stride count left right input s
    rw [hs] at h
    exact h))
  elabCommand (← `(theorem $fh (start stride : Int) (count : Nat) (left right : Int)
      (input : Input) (s : State) :
      ∃ fuel, ProgramControlIR.run input fuel
        (.running ($fc start stride count left right) s ProgramControlIR.initial) =
        .stopped (BodyBackends.runSource $source start stride count left right input s) := by
    have h := ProgramControlIR.lowerFunctional_finishes ($fp start stride count left right)
      ($fc start stride count left right) ($fl start stride count left right) input s ProgramControlIR.initial
    have hs : ($fp start stride count left right).eval input s =
        BodyBackends.runSource $source start stride count left right input s :=
      $fps start stride count left right input s
    rw [hs] at h
    exact h))
  for (suffix,code,correct) in [("imperative",ic,ih),("functional",fc,fh)] do
    let name := mkIdent (.str base (suffix ++ "OptimizedControl_result_correct"))
    elabCommand (← `(theorem $name (start stride : Int) (count : Nat) (left right : Int)
        (input : Input) (s : State) (fuel : Nat) (result : Option State)
        (h : ProgramControlIR.run input fuel
          (.running ($code start stride count left right) s ProgramControlIR.initial) = .stopped result) :
        result = BodyBackends.runSource $source start stride count left right input s := by
      obtain ⟨n,hn⟩ := $correct start stride count left right input s
      exact ProgramControlIR.result_unique h hn))

end IRComparison
