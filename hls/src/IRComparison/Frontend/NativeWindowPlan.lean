import IRComparison.Frontend.NativeWindowBody

namespace IRComparison.NativeWindowPlan
open WindowSchedule
variable {source : Imperative.Cmd}

structure Block where
  index : Int
  loads : List Load
  body : Imperative.Cmd

structure FBlock where
  index : Int
  loads : List Load
  body : Functional.Term

def evalI (input : Input) (x y : Int) : List Block → List Int → State → Option State
  | [],_,s => some s
  | b::rest,old,s => do
      let values ← execute input old b.loads
      evalI input x y rest values (← b.body.eval b.index x y s values)

def evalF (input : Input) (x y : Int) : List FBlock → List Int → State → Option State
  | [],_,s => some s
  | b::rest,old,s => do
      let values ← execute input old b.loads
      evalF input x y rest values (← b.body.eval b.index x y [s] values)

inductive Plan (size array : Nat) (source : Imperative.Cmd) (stride : Int) : Nat → Int → List Int → Type where
  | nil : Plan size array source stride 0 i old
  | step (keys : List Int) (bounds : ∀ j ∈ keys, 0 ≤ j ∧ j < (size:Int))
      (body : NativeWindowBody.Compiled i array 0 keys source)
      (next : Plan size array source stride n (i+stride) keys) : Plan size array source stride (n+1) i old

def Plan.imperative : Plan size array source stride n i old → List Block
  | .nil => []
  | .step keys _ b next => ⟨i,loads old keys,b.code⟩ :: next.imperative

def Plan.functional : Plan size array source stride n i old → List FBlock
  | .nil => []
  | .step keys _ b next => ⟨i,loads old keys,lowerBody b.code⟩ :: next.functional

theorem Plan.imperative_correct (p : Plan size array source stride n i old)
    (data : Array Int) (sized : data.size = size) (s : State) (frozen : s.arrays array = data)
    (held : Matches (arrayInput data) old values) (x y : Int) :
    evalI (arrayInput data) x y p.imperative values s =
      Source.iterate (fun j => source.eval j x y) stride n i s := by
  induction p generalizing values s with
  | nil => rfl
  | @step i n old keys bounds body next ih =>
    have coverage : WindowCoverage.Covered (arrayInput data) size := sized ▸ WindowCoverage.array_covered data
    obtain ⟨vs,hvs⟩ := WindowCoverage.emit_exists coverage bounds
    have heldNext := emit_matches hvs
    simp only [Plan.imperative,evalI,loads_correct held,hvs,bind,Option.bind,Source.iterate]
    rw [show body.code.eval i x y s vs = source.eval i x y s [] from
      body.correct data vs [] s x y frozen heldNext rfl]
    cases hb : source.eval i x y s [] with
    | none => rfl
    | some t => exact ih t ((body.frame _ _ _ _ _ hb).trans frozen) heldNext

theorem Plan.functional_correct (p : Plan size array source stride n i old)
    (data : Array Int) (sized : data.size = size) (s : State) (frozen : s.arrays array = data)
    (held : Matches (arrayInput data) old values) (x y : Int) :
    evalF (arrayInput data) x y p.functional values s =
      Source.iterate (fun j => source.eval j x y) stride n i s := by
  induction p generalizing values s with
  | nil => rfl
  | @step i n old keys bounds body next ih =>
    have coverage : WindowCoverage.Covered (arrayInput data) size := sized ▸ WindowCoverage.array_covered data
    obtain ⟨vs,hvs⟩ := WindowCoverage.emit_exists coverage bounds
    have heldNext := emit_matches hvs
    simp only [Plan.functional,evalF,loads_correct held,hvs,bind,Option.bind,Source.iterate,lowerBody_correct]
    rw [show body.code.eval i x y s vs = source.eval i x y s [] from
      body.correct data vs [] s x y frozen heldNext rfl]
    cases hb : source.eval i x y s [] with
    | none => rfl
    | some t => exact ih t ((body.frame _ _ _ _ _ hb).trans frozen) heldNext

/-- Analysis specializes a finite loop's static addresses, not its data or
    branch outcomes. The generated block schedule currently expands trips. -/
def prepareWith (contiguous : Bool) (size array : Nat) (source : Imperative.Cmd) (stride : Int) :
    (count : Nat) → (index : Int) → (old : List Int) → Option (Plan size array source stride count index old)
  | 0,_,_ => some .nil
  | n+1,i,old => do
      let accessed ← NativeWindowBody.accesses i array source
      let (lo,hi) ← PaperCore.WindowAnalysis.bounds accessed
      let future ← NativeWindowBody.accesses (i+stride) array source
      let backwards := match accessed.head?,future.head? with
        | some a,some b => b < a
        | _,_ => false
      let keys := if contiguous then interval backwards lo hi else accessed
      if bounds : ∀ j ∈ keys, 0 ≤ j ∧ j < (size:Int) then
        let body ← NativeWindowBody.compile i array 0 keys source
        let next ← prepareWith contiguous size array source stride n (i+stride) keys
        return .step keys bounds body next
      else none


abbrev prepare := prepareWith true

/-- Reuse is decided before coverage, buffering or FIFO selection. Unknown
    accesses are optimization misses rather than alternate FIFO guesses. -/
def needsReuse (array : Nat) (body : Imperative.Cmd) (stride : Int) : Nat → Int → List Int → Option Bool
  | 0,_,_ => some false
  | n+1,i,seen => do
      let accessed ← NativeWindowBody.accesses i array body
      if accessed.any (fun j => seen.contains j) || accessed.eraseDups.length != accessed.length then
        return true
      else needsReuse array body stride n (i+stride) (seen++accessed)

def Plan.reads (p : Plan size array source stride n i old) : List Int :=
  p.imperative.flatMap (fun b => WindowSchedule.reads b.loads)

def Plan.reuses (p : Plan size array source stride n i old) : Bool :=
  p.imperative.any (fun b => b.loads.any fun l => match l with | .saved _ => true | _ => false)

inductive Result (size array : Nat) (source : Imperative.Cmd) (stride : Int) (count : Nat) (index : Int) where
  | memory
  | buffered (plan : Plan size array source stride count index [])

def compile (size array : Nat) (source : Imperative.Cmd) (stride : Int) (count : Nat) (index : Int) :=
  match needsReuse array source stride count index [] with
  | some true => match prepare size array source stride count index [] with
    | none => Result.memory (size:=size) (array:=array) (source:=source) (stride:=stride) (count:=count) (index:=index)
    | some p => Result.buffered p
  | _ => Result.memory

def Result.evalI (data : Array Int) (x y : Int) (s : State) : Result size array source stride count index → Option State
  | .memory => Source.iterate (fun j => source.eval j x y) stride count index s
  | .buffered p => NativeWindowPlan.evalI (arrayInput data) x y p.imperative [] s

def Result.evalF (data : Array Int) (x y : Int) (s : State) : Result size array source stride count index → Option State
  | .memory => Source.iterate (fun j => source.eval j x y) stride count index s
  | .buffered p => NativeWindowPlan.evalF (arrayInput data) x y p.functional [] s

theorem Result.correct (r : Result size array source stride count index)
    (s : State) (sized : (s.arrays array).size = size) (x y : Int) :
    r.evalI (s.arrays array) x y s = Source.iterate (fun j => source.eval j x y) stride count index s ∧
    r.evalF (s.arrays array) x y s = Source.iterate (fun j => source.eval j x y) stride count index s := by
  cases r with
  | memory => exact ⟨rfl,rfl⟩
  | buffered p => exact ⟨p.imperative_correct _ sized s rfl .nil x y,p.functional_correct _ sized s rfl .nil x y⟩

end IRComparison.NativeWindowPlan
