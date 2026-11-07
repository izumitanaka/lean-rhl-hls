import PaperCore.WindowLoads
import PaperCore.Move

namespace PaperCore.WindowLoads

theorem Held.congr_regs (held : Held heap regs array first buffers)
    (same : ∀ b ∈ buffers, other.lookup b = regs.lookup b) : Held heap other array first buffers := by
  induction buffers generalizing first with
  | nil => trivial
  | cons b rest ih =>
    obtain ⟨value,cell,reg,tail⟩ := held
    exact ⟨value,cell,(same b (by simp)).trans reg,
      ih tail (fun v hv => same v (List.mem_cons_of_mem _ hv))⟩

theorem Held.set_other (held : Held heap regs array first buffers) (other : dest ∉ buffers) :
    Held heap (put regs dest value) array first buffers := by
  apply held.congr_regs
  intro b member
  apply lookup_put_other
  intro same
  subst b
  exact other member

end PaperCore.WindowLoads

namespace PaperCore.WindowShifts
open WindowLoads

/-- Static, left-to-right register copies; each source is still untouched
    when it is read. The last slot is replenished separately. -/
inductive Steps (meaning : Op → Int → Int → Int) : List Var → State Streams → State Streams → Prop where
  | nil : Steps meaning [] s s
  | single : Steps meaning [b] s s
  | cons : TargetExec meaning (.assign b (.var c)) s mid →
      Steps meaning (c :: rest) mid out → Steps meaning (b :: c :: rest) s out

def code : List Var → Option (Target Op)
  | [] | [_] => none
  | b :: c :: rest =>
    match code (c :: rest) with
    | none => some (.assign b (.var c))
    | some tail => some (.seq (.assign b (.var c)) tail)

/-- An absent suffix means no command is emitted, not a new skip syntax. -/
def OptionalExec (meaning : Op → Int → Int → Int) (code : Option (Target Op))
    (state out : State Streams) : Prop :=
  match code with
  | none => state = out
  | some body => TargetExec meaning body state out

theorem code_exec {Op : Type} {meaning : Op → Int → Int → Int} : OptionalExec meaning (code buffers) state out ↔ Steps meaning buffers state out := by
  induction buffers generalizing state out with
  | nil =>
    constructor
    · intro h; change state = out at h; subst out; exact .nil
    · intro h; cases h; rfl
  | cons b rest ih =>
    cases rest with
    | nil =>
      constructor
      · intro h; change state = out at h; subst out; exact .single
      · intro h; cases h; rfl
    | cons c tail =>
      cases hc : code (Op := Op) (c :: tail) with
      | none =>
        constructor
        · intro run
          have actual : TargetExec meaning (.assign b (.var c)) state out := by simpa [code,hc,OptionalExec] using run
          exact .cons actual (ih.mp (by simp [hc,OptionalExec]))
        · intro run
          cases run with
          | cons first later =>
            have same := ih.mpr later
            simp [hc,OptionalExec] at same
            subst out
            simpa [code,hc,OptionalExec] using first
      | some suffix =>
        constructor
        · intro run
          have actual : TargetExec meaning (.seq (.assign b (.var c)) suffix) state out := by simpa [code,hc,OptionalExec] using run
          cases actual with
          | seq first later => exact .cons first (ih.mp (by simpa [hc,OptionalExec] using later))
        · intro run
          cases run with
          | cons first later =>
            have last := ih.mpr later
            simp only [hc,OptionalExec] at last
            simpa [code,hc,OptionalExec] using Exec.seq first last

theorem Steps.frame (run : Steps meaning buffers state out) (other : x ∉ buffers) :
    out.regs.lookup x = state.regs.lookup x := by
  induction run with
  | nil => rfl
  | single => rfl
  | @cons b c s mid rest out first later ih =>
    have facts : x ≠ b ∧ x ∉ c :: rest := by simpa using other
    have after := ih facts.2
    cases first
    exact after.trans (lookup_put_other _ _ _ _ facts.1)

theorem shift_exists (buffers : List Var)
    (corr : Corresponds ordinary arrays source target indices)
    (fresh : ∀ b ∈ buffers, ¬ ordinary b)
    (distinct : buffers.Nodup)
    (held : Held source.memory target.regs array first buffers) :
    ∃ out, Steps meaning buffers target out ∧ Corresponds ordinary arrays source out indices ∧
      Held source.memory out.regs array (first+1) buffers.dropLast := by
  induction buffers generalizing first target with
  | nil => exact ⟨target,.nil,corr,True.intro⟩
  | cons b rest ih =>
    cases rest with
    | nil => exact ⟨target,.single,corr,True.intro⟩
    | cons c rest =>
      obtain ⟨old,oldCell,oldReg,heldTail⟩ := held
      obtain ⟨value,cell,reg,heldRest⟩ := heldTail
      have distinctTail := (List.nodup_cons.mp distinct).2
      have notTail := (List.nodup_cons.mp distinct).1
      have midHeld : Held source.memory (target.setReg b value).regs array (first+1) (c :: rest) :=
        Held.set_other ⟨value,cell,reg,heldRest⟩ notTail
      obtain ⟨out,later,after,heldOut⟩ := ih (corr.setBuffer (fresh b (by simp)) value)
        (fun v hv => fresh v (List.mem_cons_of_mem _ hv)) distinctTail midHeld
      have read : TargetExec meaning (.assign b (.var c)) target (target.setReg b value) := .assign reg
      have heldB : out.regs.lookup b = some value := by
        rw [later.frame notTail]
        exact lookup_put_same ..
      refine ⟨out,.cons read later,after,?_⟩
      exact ⟨value,cell,heldB,heldOut⟩

def append (body : Target Op) (buffers : List Var) : Target Op :=
  match code buffers with
  | none => body
  | some suffix => .seq body suffix

theorem append_exec {Op : Type} {meaning : Op → Int → Int → Int} {body : Target Op} :
    TargetExec meaning (append body buffers) state out ↔
      ∃ mid, TargetExec meaning body state mid ∧ Steps meaning buffers mid out := by
  cases hc : code (Op := Op) buffers with
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

theorem Steps.deterministic (first : Steps meaning buffers state left)
    (second : Steps meaning buffers state right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | single => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons otherHead otherTail =>
      have same := assign_unique head otherHead
      subst_vars
      exact ih otherTail

#print axioms code_exec
#print axioms shift_exists
end PaperCore.WindowShifts
