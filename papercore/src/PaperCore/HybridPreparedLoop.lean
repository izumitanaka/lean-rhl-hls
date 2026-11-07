import PaperCore.HybridLoop
import PaperCore.LoopClock

namespace PaperCore.Hybrid.PreparedLoop
open AccessAnalysis

/-- A successful analysis keeps equations relating every component to the
    actual input, so code generation cannot substitute a fixture program. -/
structure Prepared (policy : Array → Bool) (classify : Op → Option Arithmetic) (source : Source Op) where
  counter : Var
  start : Int
  stop : Int
  step : Int
  body : Source Op
  targetBody : MixedTarget.Code Op
  summary : Summary
  counterAfter : Affine
  original : source = .loop counter (.num start) stop step body
  analyzed : analyze classify (Env.initial counter) body = .ok summary
  lowered : Body.lower policy body = .ok targetBody
  counterKnown : summary.env counter = some counterAfter

def prepare (policy : Array → Bool) (classify : Op → Option Arithmetic) (source : Source Op) :
    Except String (Prepared policy classify source) :=
  match source with
  | .loop counter (.num start) stop step body =>
    match ha : analyze classify (Env.initial counter) body with
    | .error reason => .error reason
    | .ok summary =>
      match hl : Body.lower policy body with
      | .error reason => .error reason
      | .ok targetBody =>
        match hc : summary.env counter with
        | none => .error "loop-counter-after-body-unknown"
        | some counterAfter => .ok ⟨counter,start,stop,step,body,targetBody,summary,counterAfter,rfl,ha,hl,hc⟩
  | .loop .. => .error "symbolic-loop-initializer-not-yet-supported"
  | _ => .error "expected-single-loop-region"

def Prepared.events (p : Prepared policy classify source) : List SymbolicAccess :=
  p.summary.accesses.filter (fun e => policy e.array)

def Prepared.arrays (p : Prepared policy classify source) : List Array :=
  (p.events.map (·.array)).eraseDups

theorem Prepared.tracked (p : Prepared policy classify source) :
    ∀ event ∈ p.events, event.array ∈ p.arrays := by
  intro event member
  simp only [Prepared.arrays,List.mem_eraseDups]
  exact List.mem_map.mpr ⟨event,member,rfl⟩

def Prepared.code {Op : Type} {classify : Op → Option Arithmetic} {source : Source Op} (p : Prepared policy classify source) : MixedTarget.Code Op :=
  .loop p.counter (.num p.start) p.stop p.step p.targetBody

def layout : BodyCursorSMT.Layout := fun array => "cursor.input." ++ array

/-- An input interface specifies the initial queue's index sequence for
    each accessed array. Values/definedness come from Corresponds. -/
structure Interface where
  queues : Array → IndexSequence.Values
  low : Int
  high : Int

def Prepared.clock (p : Prepared policy classify source) : Option (LoopClock.Clock p.start p.stop p.step p.counterAfter) :=
  LoopClock.select p.start p.stop p.step p.counterAfter

def Prepared.exitCoordinate (p : Prepared policy classify source) : Int :=
  match p.clock with
  | some clock => clock.trips
  | none => p.stop

def Prepared.shape (p : Prepared policy classify source) (params : String → Int) (input : Interface) : Int → IndexMap → Prop :=
  match p.clock with
  | some clock => OrdinalCursorSMT.shape params p.arrays layout p.start clock.delta clock.trips
  | none => LoopCursorSMT.shape params p.arrays layout input.low input.high

def entryCondition (p : Prepared policy classify source) (input : Interface) (time low high : Int) : PaperCore.SMT :=
  PaperCore.SMT.conj (LoopCursorSMT.domain low high (.num time) ::
    p.arrays.map (fun a =>
      let q := input.queues a
      LoopCursorSMT.sameSequence ⟨.num q.first,.num q.step,.num q.count⟩
        (BodyCursorSMT.template (layout a) (.num time))))

def initialCondition (p : Prepared policy classify source) (input : Interface) : PaperCore.SMT :=
  match p.clock with
  | some clock => entryCondition p input 0 0 clock.trips
  | none => entryCondition p input p.start input.low input.high

def loopCondition (p : Prepared policy classify source) (input : Interface) : PaperCore.SMT :=
  match p.clock with
  | some clock => OrdinalCursorSMT.query p.events p.start clock.delta clock.trips p.arrays layout
  | none => LoopCursorSMT.query {p.summary with accesses := p.events} p.counterAfter p.arrays layout input.low input.high p.stop p.step

def query (p : Prepared policy classify source) (input : Interface) : PaperCore.SMT :=
  PaperCore.SMT.conj [initialCondition p input,loopCondition p input]

def Initial (p : Prepared policy classify source) (input : Interface) (indices : IndexMap) : Prop :=
  ∀ a ∈ p.arrays, indices.lookup a = some (input.queues a).sequence

theorem entry_sound (p : Prepared policy classify source)
    (model : PaperCore.SMTMeaning.eval zero params vars (entryCondition p input time low high) = .boolean true)
    (initial : Initial p input indices) :
    LoopCursorSMT.shape params p.arrays layout low high time indices := by
  have hc : PaperCore.SMTMeaning.eval zero params vars (.num time) = .integer time := by
    simp [PaperCore.SMTMeaning.eval]
  have bound := PaperCore.SMTMeaning.conj_member _ _ zero params vars model (List.mem_cons_self ..)
  have bounds := (LoopCursorSMT.domain_correct hc).mp bound
  refine ⟨bounds.1,bounds.2,?_⟩
  intro a tracked
  have part := PaperCore.SMTMeaning.conj_member _ _ zero params vars model
    (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a,tracked,rfl⟩))
  have template := BodyCursorSMT.evaluates (name := layout a) hc
  have lit : ∀ v : Int, PaperCore.SMTMeaning.eval zero params vars (.num v) = .integer v := by
    intro v; simp [PaperCore.SMTMeaning.eval]
  have equal := (IndexSequence.equality_correct (lit _) (lit _) (lit _)
    template.first template.step template.count).mp part
  exact (initial a tracked).trans (congrArg some equal.2.2)

theorem initial_sound (p : Prepared policy classify source)
    (model : PaperCore.SMTMeaning.eval zero params vars (initialCondition p input) = .boolean true)
    (initial : Initial p input indices) : p.shape params input p.start indices := by
  cases hc : p.clock with
  | none =>
    simp only [initialCondition,hc] at model
    simpa only [Prepared.shape,hc] using entry_sound p model initial
  | some clock =>
    simp only [initialCondition,hc] at model
    have entry := entry_sound p model initial
    simp only [Prepared.shape,hc]
    exact ⟨0,by simp,entry⟩

theorem loop_sound (p : Prepared policy classify source)
    (model : PaperCore.SMTMeaning.eval zero params vars (loopCondition p input) = .boolean true) :
    Loop.Obligation policy p.summary p.counterAfter (p.shape params input) p.stop p.step := by
  cases hc : p.clock with
  | none =>
    simp only [loopCondition,hc] at model
    simpa only [Prepared.shape,hc] using LoopCursorSMT.query_sound p.tracked model
  | some clock =>
    simp only [loopCondition,hc] at model
    have valid := OrdinalCursorSMT.query_sound_step clock.endpoint p.tracked model
    intro k indices holds nonzero
    simp only [Prepared.shape,hc] at holds
    obtain ⟨after,consumed,next⟩ := valid k indices holds nonzero
    refine ⟨after,consumed,?_⟩
    simpa only [Prepared.shape,hc,clock.increment] using next

theorem shape_at_end (p : Prepared policy classify source) (holds : p.shape params input p.stop indices) :
    BodyCursorSMT.MatchesOn (fun a => a ∈ p.arrays) params p.exitCoordinate layout indices := by
  cases hc : p.clock with
  | none =>
    simp only [Prepared.shape,hc] at holds
    simpa only [Prepared.exitCoordinate,hc] using holds.2.2
  | some clock =>
    simp only [Prepared.shape,hc] at holds
    simpa only [Prepared.exitCoordinate,hc] using LoopClock.matches_at_end clock holds

theorem model_correct_framed (p : Prepared policy classify source)
    (ops : ArithmeticSound classify meaning)
    (typed : BufferView.Typed ordinary p.body) (counterTyped : ordinary p.counter)
    (model : PaperCore.SMTMeaning.eval zero params vars (query p input) = .boolean true)
    (extra : IndexMap → Prop)
    (stable : ∀ before after, (∀ a, a ∉ p.arrays → after.lookup a = before.lookup a) → extra before → extra after) :
    Translation meaning ordinary (fun a => policy a = true)
      (fun _ _ indices => Initial p input indices ∧ extra indices)
      source p.code
      (loopPost (Loop.invariant p.counter
        (fun k indices => p.shape params input k indices ∧ extra indices))
        p.counter p.stop) := by
  have entry := PaperCore.SMTMeaning.conj_member _ _ zero _ _ model (by simp : initialCondition p input ∈ _)
  have loop := PaperCore.SMTMeaning.conj_member _ _ zero _ _ model (by simp :
    loopCondition p input ∈ _)
  have valid := loop_sound p loop
  have framedValid : Loop.Obligation policy p.summary p.counterAfter
      (fun k indices => p.shape params input k indices ∧ extra indices) p.stop p.step := by
    intro k before holds nonzero
    obtain ⟨after,consumed,next⟩ := valid k before holds.1 nonzero
    refine ⟨after,consumed,next,stable before after ?_ holds.2⟩
    intro a notMember
    apply DirectBody.consume_frame _ _ consumed
    intro event member equal
    obtain ⟨symbolic,he,rfl⟩ := List.mem_map.mp member
    exact notMember (equal ▸ p.tracked symbolic he)
  have certified := Loop.correct_ordinary (arrays := fun a => policy a = true) ops p.analyzed p.lowered typed counterTyped p.counterKnown
    (fun _ _ => Iff.rfl) framedValid (by trivial)
    (start := Expr.num p.start)
  rw [← p.original] at certified
  apply Translation.consequence certified
  · intro regs heap indices initial
    intro k hk
    have same : k = p.start := by simpa [Expr.eval] using hk.symm
    subst k
    exact ⟨p.start,lookup_put_same ..,initial_sound p entry initial.1,initial.2⟩
  · intro regs heap indices holds; exact holds


#print axioms model_correct_framed
end PaperCore.Hybrid.PreparedLoop
