import PaperCore.Insertion

namespace NativeRHL
open PaperCore

theorem exec_deterministic {Op Action M : Type} {meaning : Op → Int → Int → Int}
    {action : Action → State M → State M → Prop}
    {code : Stmt Op Action} {s t u : State M}
    (det : ∀ cmd s t u, action cmd s t → action cmd s u → t = u)
    (first : Exec meaning action code s t) (second : Exec meaning action code s u) : t = u := by
  induction first generalizing u with
  | action h => cases second with | action h' => exact det _ _ _ _ h h'
  | assign value => cases second with | assign value' =>
      have same := Option.some.inj (value.symm.trans value'); subst_vars; rfl
  | seq first last ihFirst ihLast =>
    cases second with
    | seq first' last' =>
      have same := ihFirst first'; subst_vars; exact ihLast last'
  | ifTrue value nonzero body ih =>
    cases second with
    | ifTrue value' nonzero' body' => exact ih body'
    | ifFalse value' body' => have same := Option.some.inj (value.symm.trans value'); contradiction
  | ifFalse value body ih =>
    cases second with
    | ifFalse value' body' => exact ih body'
    | ifTrue value' nonzero' body' => have same := Option.some.inj (value.symm.trans value'); subst_vars; contradiction
  | kernel body ih => cases second with | kernel body' => exact ih body'
  | forExit value =>
    cases second with
    | forExit value' => rfl
    | forLoop value' nonzero' body' counter' rest' =>
      have same := Option.some.inj (value.symm.trans value'); subst_vars; contradiction
  | forLoop value nonzero body counter rest ihBody ihRest =>
    cases second with
    | forExit value' =>
      have same := Option.some.inj (value.symm.trans value'); contradiction
    | forLoop value' nonzero' body' counter' rest' =>
      have same := Option.some.inj (value.symm.trans value'); subst_vars
      have states := ihBody body'; subst_vars
      have counters := Option.some.inj (counter.symm.trans counter'); subst_vars
      exact ihRest rest'

theorem target_deterministic {Op : Type} {meaning : Op → Int → Int → Int}
    {code : Target Op} {s t u : State Streams} (first : TargetExec meaning code s t)
    (second : TargetExec meaning code s u) : t = u :=
  exec_deterministic (action := StreamStep) (fun _ _ _ _ h h' => streamStep_deterministic h h') first second
/-- Every terminating loop reaches its explicit target endpoint. -/
theorem target_loop_counter {Op : Type} {meaning : Op → Int → Int → Int}
    {code : Target Op} {s out : State Streams} (run : TargetExec meaning code s out) :
    ∀ counter expr stop step body, code = .loop counter expr stop step body →
      out.regs.lookup counter = some stop := by
  induction run <;> intro counter expr stop step body eq <;> cases eq
  · simp [State.setReg]
  · rename_i ihBody ihRest
    exact ihRest _ _ _ _ _ rfl

end NativeRHL
