import IRComparison.Frontend.LeanVersionEntry
import IRComparison.Frontend.LeanCertificate
import IRComparison.Core.ControlIR
import IRComparison.Core.ProgramControlBody

namespace IRComparison
open Lean Elab Command

/-- Version-aware entry. The functional representation preserves source state
    identities; the proved imperative allocation makes private copies explicit. -/
elab "hls_snapshots " source:ident " as " target:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
  let some r := LeanVersionEntry.compile (← getEnv) name
    | throwErrorAt source "version-aware compilation failed; no unproved output was generated"
  let full := (← getCurrNamespace) ++ target.getId
  let fName := .str full "functional"
  let fpName := .str full "functional_correct"
  liftCoreM <| addAndCompile (.defnDecl {
    name := fName, levelParams := [], type := .const ``Functional.Term [],
    value := LeanBodyQuotation.functionalQuote r.emitted, hints := .abbrev, safety := .safe })
  liftCoreM <| addDecl (.thmDecl {
    name := fpName,levelParams := [],
    type := LeanCertificate.expression (LeanNamedBody.specification name
      (LeanBodyQuotation.functionalEval (LeanBodyQuotation.functionalCode r.emitted)
        (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 0))),
    value := LeanCertificate.expression r.proof })
  let f := mkIdent fName
  let fp := mkIdent fpName
  let i := mkIdent (.str target.getId "imperative")
  let ip := mkIdent (.str target.getId "imperative_correct")
  elabCommand (← `(def $i : SnapshotIR.Code := SnapshotIR.lower $f))
  elabCommand (← `(theorem $ip (i x y : Int) (s : State) :
      ($i).eval i x y [s] [] = $source i x y s := by
    exact (SnapshotIR.lower_correct $f i x y [s] []).trans ($fp i x y s)))

  let ic := mkIdent (.str target.getId "imperativeControl")
  let fc := mkIdent (.str target.getId "functionalControl")
  let icp := mkIdent (.str target.getId "imperativeControl_correct")
  let fcp := mkIdent (.str target.getId "functionalControl_correct")
  elabCommand (← `(def $ic : List ControlIR.Instr := [.snapshots $i]))
  elabCommand (← `(def $fc : List ControlIR.Instr := ControlIR.lowerVersions $f))
  elabCommand (← `(theorem $icp (i x y : Int) (s : State) :
      ∃ n, ControlIR.run i x y n (.running $ic s []) = .stopped ($source i x y s) := by
    have h := ControlIR.snapshots_finishes $i i x y s []
    have hp := $ip i x y s
    rw [hp] at h
    exact h))
  elabCommand (← `(theorem $fcp (i x y : Int) (s : State) :
      ∃ n, ControlIR.run i x y n (.running $fc s []) = .stopped ($source i x y s) := by
    have h := ControlIR.lowerVersions_finishes $f i x y s []
    have hp : ($f).eval i x y [s] [] = $source i x y s := $fp i x y s
    rw [hp] at h
    exact h))

  for (suffix,body,bodyCorrect) in [("imperative",ic,icp),("functional",fc,fcp)] do
    let output := mkIdent (.str target.getId (suffix ++ "OptimizedControl"))
    let correct := mkIdent (.str target.getId (suffix ++ "OptimizedControl_correct"))
    elabCommand (← `(def $output (start stride : Int) (count : Nat) (left right : Int) :
        List ProgramControlIR.Instr := ProgramControlIR.optimizedLoopCode start stride count left right $body))
    elabCommand (← `(theorem $correct (start stride : Int) (count : Nat) (left right : Int)
        (input : Input) (s : State) :
        ∃ fuel, ProgramControlIR.run input fuel
          (.running ($output start stride count left right) s ProgramControlIR.initial) =
          .stopped (BodyBackends.runSource $source start stride count left right input s) := by
      exact ProgramControlIR.optimizedBody_finishes $body $source $bodyCorrect start stride count left right input s))

end IRComparison
