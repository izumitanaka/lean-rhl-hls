import PaperCore.WindowTrim
import PaperCore.WindowShifts

namespace PaperCore.WindowStrideShifts
open WindowLoads WindowShifts

inductive Steps (meaning : Op → Int → Int → Int) : Nat → List Var → State Streams → State Streams → Prop where
  | zero : Steps meaning 0 buffers s s
  | succ : WindowShifts.Steps meaning buffers s mid → Steps meaning n buffers.dropLast mid out →
      Steps meaning (n+1) buffers s out

def join (left right : Option (Target Op)) : Option (Target Op) :=
  match left,right with
  | none,b => b
  | a,none => a
  | some a,some b => some (.seq a b)

theorem join_exec : OptionalExec meaning (join left right) state out ↔
    ∃ mid, OptionalExec meaning left state mid ∧ OptionalExec meaning right mid out := by
  cases left with
  | none => simp [join,OptionalExec]
  | some a =>
    cases right with
    | none => simp [join,OptionalExec]
    | some b =>
      constructor
      · intro run; cases run with
        | seq first second => exact ⟨_,first,second⟩
      · rintro ⟨mid,first,second⟩; exact .seq first second

/-- Repeated statically emitted shifts shrink the live prefix each time.
    Only the final surviving prefix is used by the next iteration. -/
def code : Nat → List Var → Option (Target Op)
  | 0,_ => none
  | n+1,buffers => join (WindowShifts.code buffers) (code n buffers.dropLast)

theorem code_exec : OptionalExec meaning (code n buffers) state out ↔ Steps meaning n buffers state out := by
  induction n generalizing buffers state out with
  | zero =>
    constructor
    · intro same; change state = out at same; subst out; exact .zero
    · intro run; cases run; rfl
  | succ n ih =>
    constructor
    · intro run
      obtain ⟨mid,first,rest⟩ := join_exec.mp run
      exact .succ (WindowShifts.code_exec.mp first) (ih.mp rest)
    · intro run
      cases run with
      | succ first rest => exact join_exec.mpr ⟨_,WindowShifts.code_exec.mpr first,ih.mpr rest⟩

theorem shift_exists (count : Nat) (buffers : List Var)
    (corr : Corresponds ordinary arrays source target indices)
    (fresh : ∀ b ∈ buffers, ¬ ordinary b) (distinct : buffers.Nodup)
    (held : Held source.memory target.regs array first buffers) :
    ∃ out, Steps meaning count buffers target out ∧ Corresponds ordinary arrays source out indices ∧
      Held source.memory out.regs array (first+(count:Int)) (trim count buffers) := by
  induction count generalizing buffers first target with
  | zero => exact ⟨target,.zero,corr,by simpa [trim] using held⟩
  | succ n ih =>
    obtain ⟨mid,one,after,heldAfter⟩ := WindowShifts.shift_exists buffers corr fresh distinct held
    have sub := List.dropLast_sublist buffers
    obtain ⟨out,rest,final,heldFinal⟩ := ih buffers.dropLast after
      (fun b hb => fresh b (sub.subset hb)) (sub.nodup distinct) heldAfter
    refine ⟨out,.succ one rest,final,?_⟩
    simpa [trim,Int.natCast_add,Int.add_assoc,Int.add_comm,Int.add_left_comm] using heldFinal

theorem Steps.deterministic (first : Steps meaning n buffers state left)
    (second : Steps meaning n buffers state right) : left = right := by
  induction first generalizing right with
  | zero => cases second; rfl
  | succ first rest ih =>
    cases second with
    | succ otherFirst otherRest =>
      have same := first.deterministic otherFirst
      subst_vars
      exact ih otherRest

def append (body : Target Op) (count : Nat) (buffers : List Var) : Target Op :=
  match code count buffers with
  | none => body
  | some suffix => .seq body suffix

theorem append_exec {Op : Type} {meaning : Op → Int → Int → Int} {body : Target Op} :
    TargetExec meaning (append body count buffers) state out ↔
      ∃ mid, TargetExec meaning body state mid ∧ Steps meaning count buffers mid out := by
  cases hc : code (Op := Op) count buffers with
  | none =>
    constructor
    · intro run; exact ⟨out,by simpa [append,hc] using run,code_exec.mp (by simp [hc,OptionalExec])⟩
    · rintro ⟨mid,run,later⟩
      have same := code_exec.mpr later
      simp [hc,OptionalExec] at same
      subst out
      simpa [append,hc] using run
  | some suffix =>
    constructor
    · intro run
      simp only [append,hc] at run
      cases run with
      | seq first later => exact ⟨_,first,code_exec.mp (by simpa [hc,OptionalExec] using later)⟩
    · rintro ⟨mid,run,later⟩
      have suffixRun := code_exec.mpr later
      simp only [hc,OptionalExec] at suffixRun
      simpa [append,hc] using Exec.seq run suffixRun

#print axioms shift_exists
#print axioms append_exec
end PaperCore.WindowStrideShifts
