import IRComparison.Memory.FunctionalWindowBody
import IRComparison.Memory.WindowView
import IRComparison.Memory.WindowControl

namespace IRComparison.FunctionalWindowPlan
open WindowSchedule
variable {source : Functional.Term}

inductive Plan (size array : Nat) (source : Functional.Term) (stride : Int) : Nat → Int → List Int → Type where
  | nil : Plan size array source stride 0 i old
  | step (keys : List Int) (bounds : ∀ j ∈ keys, 0 ≤ j ∧ j < (size:Int))
      (body : FunctionalWindowBody.Compiled i array 0 keys source)
      (allocated : Imperative.Cmd) (allocation : StateLowering.lower body.code = some allocated)
      (next : Plan size array source stride n (i+stride) keys) : Plan size array source stride (n+1) i old

def Plan.functional : Plan size array source stride n i old → List NativeWindowPlan.FBlock
  | .nil => []
  | .step keys _ b _ _ next => ⟨i,loads old keys,b.code⟩ :: next.functional

def Plan.allocated : Plan size array source stride n i old → List NativeWindowPlan.Block
  | .nil => []
  | .step keys _ _ b _ next => ⟨i,loads old keys,b⟩ :: next.allocated

theorem Plan.functional_correct (p : Plan size array source stride n i old)
    (data : Array Int) (sized : data.size = size) (s : State) (frozen : s.arrays array = data)
    (held : Matches (arrayInput data) old values) (x y : Int) :
    NativeWindowPlan.evalF (arrayInput data) x y p.functional values s =
      Source.iterate (fun j t => source.eval j x y [t]) stride n i s := by
  induction p generalizing values s with
  | nil => rfl
  | @step i n old keys bounds body allocated allocation next ih =>
    have coverage : WindowCoverage.Covered (arrayInput data) size := sized ▸ WindowCoverage.array_covered data
    obtain ⟨vs,hvs⟩ := WindowCoverage.emit_exists coverage bounds
    have heldNext := emit_matches hvs
    simp only [Plan.functional,NativeWindowPlan.evalF,loads_correct held,hvs,bind,Option.bind,Source.iterate]
    rw [show body.code.eval i x y [s] vs = source.eval i x y [s] [] from
      body.correct data vs [] s [] x y frozen heldNext rfl]
    cases hb : source.eval i x y [s] [] with
    | none => rfl
    | some t => exact ih t ((body.frame _ _ _ _ _ _ hb).trans frozen) heldNext

theorem Plan.allocated_correct (p : Plan size array source stride n i old) (input : Input) (x y : Int)
    (values : List Int) (s : State) :
    NativeWindowPlan.evalI input x y p.allocated values s = NativeWindowPlan.evalF input x y p.functional values s := by
  induction p generalizing values s with
  | nil => rfl
  | @step i n old keys bounds body allocated allocation next ih =>
    simp only [Plan.allocated,Plan.functional,NativeWindowPlan.evalI,NativeWindowPlan.evalF]
    cases hv : execute input values (loads old keys) with
    | none => rfl
    | some vs =>
      simp only [bind,Option.bind]
      rw [StateLowering.lower_correct body.code allocated allocation i x y s [] vs]
      cases hb : body.code.eval i x y [s] vs with
      | none => rfl
      | some t => exact ih vs t

def prepare (contiguous : Bool) (size array : Nat) (source : Functional.Term) (stride : Int) :
    (count : Nat) → (index : Int) → (old : List Int) → Option (Plan size array source stride count index old)
  | 0,_,_ => some .nil
  | n+1,i,old => do
      let accessed ← FunctionalWindowBody.accesses i array source
      let (lo,hi) ← PaperCore.WindowAnalysis.bounds accessed
      let future ← FunctionalWindowBody.accesses (i+stride) array source
      let backwards := match accessed.head?,future.head? with
        | some a,some b => b < a
        | _,_ => false
      let keys := if contiguous then interval backwards lo hi else accessed
      if bounds : ∀ j ∈ keys, 0 ≤ j ∧ j < (size:Int) then
        let body ← FunctionalWindowBody.compile i array 0 keys source
        match allocated : StateLowering.lower body.code with
        | none => none
        | some code =>
          let next ← prepare contiguous size array source stride n (i+stride) keys
          return .step keys bounds body code allocated next
      else none

def needsReuse (array : Nat) (body : Functional.Term) (stride : Int) : Nat → Int → List Int → Option Bool
  | 0,_,_ => some false
  | n+1,i,seen => do
      let accessed ← FunctionalWindowBody.accesses i array body
      if accessed.any (fun j => seen.contains j) || accessed.eraseDups.length != accessed.length then return true
      else needsReuse array body stride n (i+stride) (seen++accessed)

structure Artifact (size array : Nat) (source : Functional.Term) (stride : Int) (count : Nat) (start : Int) (producer : List Int) where
  code : List WindowTransport.Block
  isFIFO : Bool
  hasBuffer : Bool
  sound : ∀ s x y values, (s.arrays array).size = size →
    (isFIFO = true → CommunicationIR.Corresponds (arrayInput (s.arrays array)) producer values) →
    (WindowTransport.eval (arrayInput (s.arrays array)) x y code [] s values).map Prod.fst =
      Source.iterate (fun j t => source.eval j x y [t]) stride count start s

  window : Option (WindowView.View array size
    (fun x y s => Source.iterate (fun j t => source.eval j x y [t]) stride count start s)) := none

def Artifact.Contract (data : Array Int) (values : List Int) (a : Artifact size array source stride count start producer) : Prop :=
  a.isFIFO = true → CommunicationIR.Corresponds (arrayInput data) producer values

def Artifact.eval (data : Array Int) (x y : Int) (s : State) (values : List Int)
    (a : Artifact size array source stride count start producer) : Option State :=
  (WindowTransport.eval (arrayInput data) x y a.code [] s values).map Prod.fst

theorem Artifact.correct (a : Artifact size array source stride count start producer)
    (s : State) (sized : (s.arrays array).size = size) (x y : Int) (values : List Int)
    (contract : a.Contract (s.arrays array) values) :
    a.eval (s.arrays array) x y s values = Source.iterate (fun j t => source.eval j x y [t]) stride count start s :=
  a.sound s x y values sized contract

def original (body : Imperative.Cmd) (allocation : StateLowering.lower source = some body) :
    Artifact size array source stride count start producer where
  code := WindowTransport.original body stride count start
  isFIFO := false
  hasBuffer := false
  sound := by
    intro s x y values sized contract
    rw [WindowTransport.original_correct]
    simp only [Option.map_map,Function.comp_def,Option.map_id_fun]
    simpa using Source.iterate_congr _ _ (fun i t => StateLowering.lower_correct source body allocation i x y t [] []) stride count start s

def bufferedMemory (p : Plan size array source stride count start []) : Artifact size array source stride count start producer where
  code := WindowTransport.memory p.allocated
  isFIFO := false
  hasBuffer := true
  sound := by
    intro s x y values sized contract
    rw [WindowTransport.memory_correct]
    simp only [Option.map_map,Function.comp_def,Option.map_id_fun]
    rw [p.allocated_correct]
    simpa using p.functional_correct _ sized s rfl .nil x y

  window := some ⟨p.allocated,by
    intro s sized x y
    rw [p.allocated_correct]
    exact p.functional_correct _ sized s rfl .nil x y⟩

def fifo (buffered : Bool) (p : Plan size array source stride count start []) (r : WindowTransport.Routed p.allocated producer) :
    Artifact size array source stride count start producer where
  code := r.code
  isFIFO := true
  hasBuffer := buffered
  sound := by
    intro s x y values sized contract
    rw [(r.correct.correct (contract rfl) [] s x y).1,p.allocated_correct]
    simpa using p.functional_correct _ sized s rfl .nil x y

  window := some ⟨p.allocated,by
    intro s sized x y
    rw [p.allocated_correct]
    exact p.functional_correct _ sized s rfl .nil x y⟩

/-- Functional window substitution happens before allocation. Only fallback
    uses the original allocated body; the source Term is analyzed directly. -/
def compileWithReason (source : Functional.Term) (body : Imperative.Cmd) (allocation : StateLowering.lower source = some body)
    (size array : Nat) (start stride : Int) (count : Nat) (producer : List Int) :
    Artifact size array source stride count start producer × WindowTransport.Decision :=
  match needsReuse array source stride count start [] with
  | none => (original body allocation,.accessesUnresolved)
  | some reuse => match prepare reuse size array source stride count start [] with
    | none => (original body allocation,.windowUnavailable)
    | some p => match WindowTransport.route p.allocated producer with
      | none => (if reuse then bufferedMemory p else original body allocation,.supplyOrderMismatch reuse)
      | some r => (fifo reuse p r,.fifo reuse)

def compile (source : Functional.Term) (body : Imperative.Cmd) (allocation : StateLowering.lower source = some body)
    (size array : Nat) (start stride : Int) (count : Nat) (producer : List Int) :
    Artifact size array source stride count start producer :=
  (compileWithReason source body allocation size array start stride count producer).1

theorem Artifact.finishes (a : Artifact size array source stride count start producer)
    (s : State) (sized : (s.arrays array).size = size) (x y : Int) (values : List Int)
    (contract : a.Contract (s.arrays array) values) :
    ∃ steps remaining, WindowControl.run (arrayInput (s.arrays array)) x y steps
      (.start (WindowControl.lower a.code) [] s values) =
      .stopped (Source.iterate (fun j t => source.eval j x y [t]) stride count start s) remaining := by
  obtain ⟨steps,errorQueue,run⟩ := WindowControl.lower_finishes (input:=arrayInput (s.arrays array)) (x:=x) (y:=y) a.code [] s values
  have same := a.correct s sized x y values contract
  cases he : WindowTransport.eval (arrayInput (s.arrays array)) x y a.code [] s values with
  | none =>
    change Option.map Prod.fst _ = _ at same
    simp only [he,Option.map_none] at same
    exact ⟨steps,errorQueue,by simpa [he,WindowControl.resultEnd,← same] using run⟩
  | some pair =>
    obtain ⟨t,tail⟩ := pair
    change Option.map Prod.fst _ = _ at same
    simp only [he,Option.map_some] at same
    exact ⟨steps,tail,by simpa [he,WindowControl.resultEnd,← same] using run⟩

end IRComparison.FunctionalWindowPlan
