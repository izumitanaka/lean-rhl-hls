import PaperCore.MemoryBufferBody
import PaperCore.MemoryWindowSchedule
import PaperCore.WindowAnalysis
import PaperCore.WindowNames

namespace PaperCore.MemoryWindowPlan
open AccessAnalysis OrientedWindow MemoryWindowSchedule

/-- A generated memory-window candidate. This is deliberately not a
SourcePass.Prepared: MemoryWindowProgram proves the whole-loop simulation
under coverage, and MemoryBufferPass discharges coverage before acceptance. -/
structure Candidate (classify : Op → Option Arithmetic) (source : Source Op) where
  counter : Var
  start : Int
  stop : Int
  step : Int
  body : Source Op
  input : Array
  first : Int
  scale : Int
  reverse : Bool
  overlap : Nat
  reload : Nat
  variables : List Var
  add : Op
  mul : Op
  addClass : classify add = some .add
  mulClass : classify mul = some .mul
  original : source = .loop counter (.num start) stop step body
  substitution : MemoryBufferBody.Prepared classify
    (Layout.slots ⟨input,first,scale,reverse,
      WindowNames.names variables overlap ++ WindowNames.refillNames variables overlap reload⟩)
    input (Env.initial counter) body
  counterDelta : Int
  trips : Nat
  nonzero : counterDelta ≠ 0
  endpoint : stop = start+(trips:Int)*counterDelta
  counterKnown : substitution.after counter = some ⟨1,counterDelta-step⟩
  movement : scale*counterDelta = (reload:Int)*direction reverse
  counterMember : counter ∈ variables
  bodyVars : ∀ x ∈ BufferNames.sourceVars body, x ∈ variables

variable {Op : Type} {classify : Op → Option Arithmetic} {source : Source Op}

def Candidate.initialBuffers (p : Candidate classify source) : List Var := WindowNames.names p.variables p.overlap
def Candidate.refill (p : Candidate classify source) : List Var := WindowNames.refillNames p.variables p.overlap p.reload
def Candidate.buffers (p : Candidate classify source) : List Var := p.initialBuffers ++ p.refill
def Candidate.cursor (p : Candidate classify source) : Var := BufferNames.name p.variables (p.overlap+p.reload)
def Candidate.increment (p : Candidate classify source) : Var := BufferNames.name p.variables (p.overlap+p.reload+1)

def Candidate.iteration (p : Candidate classify source) : Source Op :=
  prepend (address p.add p.mul p.counter p.cursor p.increment p.scale
      (p.first+(p.overlap:Int)*direction p.reverse) (direction p.reverse) ++
      loads p.add p.input p.cursor p.increment p.refill)
    (appendTo p.substitution.code (shifts p.reload p.buffers))

def Candidate.code (p : Candidate classify source) : Source Op :=
  if p.start = p.stop then source else
  prepend (literalLoads p.input (p.scale*p.start+p.first) (direction p.reverse) p.initialBuffers)
    (.loop p.counter (.num p.start) p.stop p.step p.iteration)

/-- Required coverage, independent of any subsequent FIFO policy. -/
def Candidate.covered (p : Candidate classify source) (heap : Heap) : Prop :=
  MemoryCoverage.Covers heap p.input (p.scale*p.start+p.first) (direction p.reverse)
    (if p.start = p.stop then 0 else p.overlap+p.trips*p.reload)

/-- Arithmetic operators are explicit backend capabilities, not new syntax.
The classifier checks their interpretation before generating address code. -/
def prepare (classify : Op → Option Arithmetic) (add mul : Op) (reserved : List Var)
    (source : Source Op) : Except String (Candidate classify source) :=
  if addClass : classify add = some .add then
  if mulClass : classify mul = some .mul then
  match source with
  | .loop counter (.num start) stop step body => do
    let summary ← analyze classify (Env.initial counter) body
    let some afterCounter := summary.env counter | .error "memory-window-counter-unknown"
    let counterDelta := afterCounter.offset+step
    if nonzero : counterDelta ≠ 0 then
      let trips := ((stop-start)/counterDelta).toNat
      if endpoint : stop = start+(trips:Int)*counterDelta then
        match summary.accesses.filter (fun e => e.direction == .read) with
        | [] => .error "memory-window-no-input-read"
        | firstAccess :: _ => do
          let window ← WindowAnalysis.infer firstAccess.array summary.accesses
          let movement := window.scale*counterDelta
          let reverse := decide (movement < 0)
          let reload := movement.natAbs
          let width := (window.high-window.low).toNat+1
          if reload = 0 ∨ width ≤ reload then .error "memory-window-no-overlap" else
          let overlap := width-reload
          let first := if reverse then window.high else window.low
          let variables := reserved ++ (counter :: BufferNames.sourceVars body)
          let slots := Layout.slots ⟨window.array,first,window.scale,reverse,
            WindowNames.names variables overlap ++ WindowNames.refillNames variables overlap reload⟩
          let substitution ← MemoryBufferBody.prepare classify slots window.array (Env.initial counter) body
          if known : substitution.after counter = some ⟨1,counterDelta-step⟩ then
            return ⟨counter,start,stop,step,body,window.array,first,window.scale,reverse,overlap,reload,
              variables,add,mul,addClass,mulClass,rfl,substitution,counterDelta,trips,nonzero,endpoint,known,by
                change movement = (movement.natAbs:Int)*direction (decide (movement < 0))
                by_cases negative : movement < 0
                · simp [direction,negative]; omega
                · simp [direction,negative]; omega,
              by simp [variables],by intro x hx; simp [variables,hx]⟩
          else .error "memory-window-counter-not-affine"
      else .error "memory-window-endpoint-not-reached"
    else .error "memory-window-zero-net-step"
  | _ => .error "memory-window-expected-literal-start-loop"
  else .error "memory-window-multiplication-operator-unavailable"
  else .error "memory-window-addition-operator-unavailable"

#print axioms prepare
end PaperCore.MemoryWindowPlan
