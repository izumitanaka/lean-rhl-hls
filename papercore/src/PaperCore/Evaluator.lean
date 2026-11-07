import PaperCore.Semantics

namespace PaperCore

def memoryRun (meaning : Op → Int → Int → Int) : MemoryAction Op → State Heap → Option (State Heap)
  | .read x a e,s => do
    let i ← e.eval meaning s.regs
    return s.setReg x (← s.memory.lookup (a,i))
  | .write a e x,s => do
    let i ← e.eval meaning s.regs
    let v ← s.regs.lookup x
    return {s with memory := put s.memory (a,i) v}

def streamRun : StreamAction → State Streams → Option (State Streams)
  | .read x a,s => do
    let v :: tail ← s.memory.lookup a | none
    return {regs := put s.regs x v, memory := put s.memory a tail}
  | .write a x,s => do
    let values ← s.memory.lookup a
    let v ← s.regs.lookup x
    return {s with memory := put s.memory a (values ++ [v])}

/-- Fuel limits only the observer. None can mean exhaustion or undefined
    data; no claim of divergence is inferred from it. -/
def run (meaning : Op → Int → Int → Int) (action : Action → State M → Option (State M)) :
    Nat → Stmt Op Action → State M → Option (State M)
  | 0,_,_ => none
  | fuel+1,code,s => match code with
    | .action cmd => action cmd s
    | .assign x e => do return s.setReg x (← e.eval meaning s.regs)
    | .seq a b => do run meaning action fuel b (← run meaning action fuel a s)
    | .branch x yes no => do
      let v ← s.regs.lookup x
      run meaning action fuel (if v = 0 then no else yes) s
    | .loop x e stop step body => do
      let k ← e.eval meaning s.regs
      if k = stop then return s.setReg x stop else
        let mid ← run meaning action fuel body (s.setReg x k)
        let next ← mid.regs.lookup x
        run meaning action fuel (.loop x (.num (next+step)) stop step body) mid
    | .kernel body => run meaning action fuel body s

theorem memoryRun_sound (meaning : Op → Int → Int → Int)
    (h : memoryRun meaning cmd s = some t) : MemoryStep meaning cmd s t := by
  cases cmd with
  | read x a e =>
    cases hi : e.eval meaning s.regs with
    | none => simp [memoryRun,hi] at h
    | some i =>
      cases hv : s.memory.lookup (a,i) with
      | none => simp [memoryRun,hi,hv] at h
      | some v =>
        simp [memoryRun,hi,hv] at h
        subst t
        exact .read hi hv
  | write a e x =>
    cases hi : e.eval meaning s.regs with
    | none => simp [memoryRun,hi] at h
    | some i =>
      cases hv : s.regs.lookup x with
      | none => simp [memoryRun,hi,hv] at h
      | some v =>
        simp [memoryRun,hi,hv] at h
        subst t
        exact .write hi hv

theorem streamRun_sound (h : streamRun cmd s = some t) : StreamStep cmd s t := by
  cases cmd with
  | read x a =>
    cases hq : s.memory.lookup a with
    | none => simp [streamRun,hq] at h
    | some values =>
      cases values with
      | nil => simp [streamRun,hq] at h
      | cons v tail =>
        simp [streamRun,hq] at h
        subst t
        exact .read hq
  | write a x =>
    cases hq : s.memory.lookup a with
    | none => simp [streamRun,hq] at h
    | some values =>
      cases hv : s.regs.lookup x with
      | none => simp [streamRun,hq,hv] at h
      | some v =>
        simp [streamRun,hq,hv] at h
        subst t
        exact .write hq hv

theorem run_sound (meaning : Op → Int → Int → Int)
    (action : Action → State M → Option (State M))
    (relation : Action → State M → State M → Prop)
    (action_sound : ∀ cmd s t, action cmd s = some t → relation cmd s t)
    (h : run meaning action fuel code s = some t) : Exec meaning relation code s t := by
  induction fuel generalizing code s t with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases code with
    | action cmd => exact .action (action_sound cmd s t h)
    | assign x e =>
      cases he : e.eval meaning s.regs with
      | none => simp [run,he] at h
      | some v =>
        simp [run,he] at h
        subst t
        exact .assign he
    | seq a b =>
      cases ha : run meaning action fuel a s with
      | none => simp [run,ha] at h
      | some mid =>
        simp [run,ha] at h
        exact .seq (ih ha) (ih h)
    | branch x yes no =>
      cases hx : s.regs.lookup x with
      | none => simp [run,hx] at h
      | some v =>
        by_cases hz : v = 0
        · subst v
          exact .ifFalse hx (ih (by simpa [run,hx] using h))
        · exact .ifTrue hx hz (ih (by simpa [run,hx,hz] using h))
    | kernel body => exact .kernel (ih h)
    | loop x e stop step body =>
      cases he : e.eval meaning s.regs with
      | none => simp [run,he] at h
      | some k =>
        by_cases hk : k = stop
        · subst k
          simp [run,he] at h
          subst t
          exact .forExit he
        · cases hb : run meaning action fuel body (s.setReg x k) with
          | none => simp [run,he,hk,hb] at h
          | some mid =>
            cases hx : mid.regs.lookup x with
            | none => simp [run,he,hk,hb,hx] at h
            | some next =>
              simp [run,he,hk,hb,hx] at h
              exact .forLoop he hk (ih hb) hx (ih h)

#print axioms run_sound
#print axioms memoryRun_sound
#print axioms streamRun_sound
end PaperCore
