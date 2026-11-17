import IRComparison.Memory.StreamProducer

namespace IRComparison.StreamConsumer
open StreamState

def erase (array : Nat) (s : State) : State :=
  {s with arrays := fun a => if a = array then #[] else s.arrays a}

theorem erase_agree (s : State) : Agree array s (erase array s) :=
  ⟨rfl,by intro a h; simp [erase,h]⟩

theorem Agree.erase_eq (h : Agree array s t) : erase array s = erase array t := by
  cases s; cases t
  simp only [erase,State.mk.injEq]
  refine ⟨h.regs,funext fun a => ?_⟩
  by_cases ha : a = array
  · simp [ha]
  · simpa [ha] using h.arrays a ha

theorem erase_set (s : State) : erase array (s.set r v) = (erase array s).set r v := rfl

theorem erase_write (s : State) (different : a ≠ array) :
    (s.write a j v).map (erase array) = (erase array s).write a j v := by
  unfold State.write
  simp only [erase,different,↓reduceIte]
  split
  · rfl
  · split
    · simp only [Option.map_some,erase,Option.some.injEq,State.mk.injEq,true_and]
      funext b
      by_cases hb : b = array <;> by_cases ha : b = a <;> simp_all
    · rfl

structure Checked (array : Nat) (body : Imperative.Cmd) : Type where
  correct : ∀ i x y s ls, (body.eval i x y s ls).map (erase array) = body.eval i x y (erase array s) ls

/-- Read/write exclusion is checked after window substitution. This check
    never removes a remaining memory access by assumption. -/
def check (array : Nat) : (body : Imperative.Cmd) → Option (Checked array body)
  | .skip => some ⟨by intros; rfl⟩
  | .assign r e =>
    if safe : avoids array e = true then some ⟨by
      intro i x y s ls
      simp only [Imperative.Cmd.eval,← expr_correct e safe (erase_agree s)]
      cases he : e.eval i x y s ls <;> rfl⟩ else none
  | .store a j e =>
    if different : a ≠ array then
      if safeJ : avoids array j = true then
        if safeE : avoids array e = true then some ⟨by
          intro i x y s ls
          simp only [Imperative.Cmd.eval,← expr_correct j safeJ (erase_agree s),← expr_correct e safeE (erase_agree s)]
          cases hj : j.eval i x y s ls with
          | none => rfl
          | some index =>
            cases he : e.eval i x y s ls with
            | none => rfl
            | some v => exact erase_write s different⟩ else none
      else none
    else none
  | .letValue e b =>
    if safe : avoids array e = true then do
      let cb ← check array b
      return ⟨by
        intro i x y s ls
        simp only [Imperative.Cmd.eval,← expr_correct e safe (erase_agree s)]
        cases he : e.eval i x y s ls with
        | none => rfl
        | some v => exact cb.correct i x y s (v::ls)⟩
    else none
  | .seq a b => do
    let ca ← check array a
    let cb ← check array b
    return ⟨by
      intro i x y s ls
      simp only [Imperative.Cmd.eval,← ca.correct i x y s ls]
      cases ha : a.eval i x y s ls with
      | none => rfl
      | some t => exact cb.correct i x y t ls⟩
  | .branch e a b =>
    if safe : avoids array e = true then do
      let ca ← check array a
      let cb ← check array b
      return ⟨by
        intro i x y s ls
        simp only [Imperative.Cmd.eval,← expr_correct e safe (erase_agree s)]
        cases he : e.eval i x y s ls with
        | none => rfl
        | some v =>
          simp only [bind,Option.bind]
          split
          · exact ca.correct i x y s ls
          · exact cb.correct i x y s ls⟩
    else none
  | .repeat .. | .forRange .. => none

/-- No memory load remains on the selected input channel. -/
def loadsClosed : List WindowFIFO.Load → Bool
  | [] => true
  | .memory _::_ => false
  | _::ls => loadsClosed ls

theorem loads_independent (ls : List WindowFIFO.Load) (closed : loadsClosed ls = true) :
    WindowFIFO.execute input old ls q = WindowFIFO.execute other old ls q := by
  induction ls generalizing q with
  | nil => rfl
  | cons l ls ih =>
    cases l with
    | memory => simp [loadsClosed] at closed
    | saved j =>
      simp only [WindowFIFO.execute,WindowFIFO.Load.eval]
      cases hj : old[j]? with
      | none => rfl
      | some v => simp only [bind,Option.bind,ih closed]
    | take n =>
      simp only [WindowFIFO.execute,WindowFIFO.Load.eval]
      cases hj : q[n]? with
      | none => rfl
      | some v => simp only [bind,Option.bind,ih closed]

inductive Closed (array : Nat) : List WindowTransport.Block → Type where
  | nil : Closed array []
  | cons : loadsClosed b.loads = true → Checked array b.body → Closed array rest → Closed array (b::rest)

def checkBlocks (array : Nat) : (blocks : List WindowTransport.Block) → Option (Closed array blocks)
  | [] => some .nil
  | b::rest => do
    if h : loadsClosed b.loads = true then
      let body ← check array b.body
      let tail ← checkBlocks array rest
      return .cons h body tail
    else none

theorem Closed.correct (h : Closed array blocks) :
    (WindowTransport.eval input x y blocks old s q).map (fun p => (erase array p.1,p.2)) =
      WindowTransport.eval other x y blocks old (erase array s) q := by
  induction h generalizing old s q with
  | nil => rfl
  | @cons rest b loads body tail ih =>
    simp only [WindowTransport.eval,← loads_independent b.loads loads (input:=input) (other:=other)]
    cases hl : WindowFIFO.execute input old b.loads q with
    | none => rfl
    | some pair =>
      obtain ⟨vs,qs⟩ := pair
      simp only [bind,Option.bind,← body.correct b.index x y s vs]
      cases hb : b.body.eval b.index x y s vs with
      | none => rfl
      | some t => exact ih

end IRComparison.StreamConsumer
