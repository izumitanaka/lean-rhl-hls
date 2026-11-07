import IRComparison.Core.ProgramControlBody

namespace IRComparison.CommunicationIR
open ProgramControlIR

/-- A static access protocol. Addresses are proof/planning data, never tokens.
    Bodies can contain arbitrary local computation and can fail early. -/
inductive Protocol : List Instr → Int → List Int → Int → Prop where
  | nil : Protocol [] i [] i
  | frame : Protocol rest f.index xs j → Protocol (.setFrame f::rest) i xs j
  | left : Protocol rest i xs j → Protocol (.readLeft o::rest) i ((i+o)::xs) j
  | right : Protocol rest i xs j → Protocol (.readRight o::rest) i ((i+o)::xs) j
  | retain : Protocol rest i xs j → Protocol (.retain::rest) i xs j
  | advance : Protocol rest (i+d) xs j → Protocol (.advance d::rest) i xs j
  | body : Protocol rest i xs j → Protocol (.body b::rest) i xs j
  | zero : Protocol rest i xs j → Protocol (.repeat 0 b::rest) i xs j
  | repeat : Protocol (b ++ .repeat n b::rest) i xs j → Protocol (.repeat (n+1) b::rest) i xs j
  | branch : Protocol (a++rest) i xs j → Protocol (b++rest) i xs j →
      Protocol (.testReg r a b::rest) i xs j

structure Plan (code : List Instr) (index : Int) where
  addresses : List Int
  finalIndex : Int
  correct : Protocol code index addresses finalIndex

/-- Bounded analysis, not a bound on accepted source semantics. Failure keeps
    the memory implementation. Both branches must have the same read protocol. -/
def plan : Nat → (code : List Instr) → (index : Int) → Option (Plan code index)
  | 0,_,_ => none
  | _+1,[],i => some ⟨[],i,.nil⟩
  | fuel+1,.setFrame f::rest,_ => do
      let p ← plan fuel rest f.index
      return ⟨p.addresses,p.finalIndex,.frame p.correct⟩
  | fuel+1,.readLeft o::rest,i => do
      let p ← plan fuel rest i
      return ⟨(i+o)::p.addresses,p.finalIndex,.left p.correct⟩
  | fuel+1,.readRight o::rest,i => do
      let p ← plan fuel rest i
      return ⟨(i+o)::p.addresses,p.finalIndex,.right p.correct⟩
  | fuel+1,.retain::rest,i => do
      let p ← plan fuel rest i
      return ⟨p.addresses,p.finalIndex,.retain p.correct⟩
  | fuel+1,.advance d::rest,i => do
      let p ← plan fuel rest (i+d)
      return ⟨p.addresses,p.finalIndex,.advance p.correct⟩
  | fuel+1,.body b::rest,i => do
      let p ← plan fuel rest i
      return ⟨p.addresses,p.finalIndex,.body p.correct⟩
  | fuel+1,.repeat 0 b::rest,i => do
      let p ← plan fuel rest i
      return ⟨p.addresses,p.finalIndex,.zero p.correct⟩
  | fuel+1,.repeat (n+1) b::rest,i => do
      let p ← plan fuel (b ++ .repeat n b::rest) i
      return ⟨p.addresses,p.finalIndex,.repeat p.correct⟩
  | fuel+1,.testReg r a b::rest,i => do
      let p ← plan fuel (a++rest) i
      let q ← plan fuel (b++rest) i
      if hx : p.addresses = q.addresses then
        if hi : p.finalIndex = q.finalIndex then
          return ⟨p.addresses,p.finalIndex,.branch p.correct (hx ▸ hi ▸ q.correct)⟩
        else none
      else none

/-- A producer contract relates the actual FIFO values to the memory snapshot.
    Equal lengths and order are explicit; there are no error/undefined tokens. -/
inductive Corresponds (input : Input) : List Int → List Int → Prop where
  | nil : Corresponds input [] []
  | cons : input i = some x → Corresponds input is xs → Corresponds input (i::is) (x::xs)

/-- FIFO mode changes only external reads. Local body arrays stay memory.
    `.readLeft/.readRight` consume one token; their offsets are ignored here. -/
structure FIFOConfig where
  control : Config
  queue : List Int

def step : FIFOConfig → FIFOConfig
  | ⟨.running (.readLeft _::rest) s f, x::xs⟩ =>
      ⟨.running rest s {f with left := x},xs⟩
  | ⟨.running (.readRight _::rest) s f, x::xs⟩ =>
      ⟨.running rest s {f with right := x},xs⟩
  | ⟨.running (.readLeft _::_) _ _,[]⟩ => ⟨.stopped none,[]⟩
  | ⟨.running (.readRight _::_) _ _,[]⟩ => ⟨.stopped none,[]⟩
  | ⟨c,q⟩ => ⟨ProgramControlIR.step (fun _ => none) c,q⟩

/-- Remaining protocol, including unused suffix after early termination. -/
inductive Pending : Config → List Int → Prop where
  | running : Protocol code f.index xs j → Pending (.running code s f) xs
  | body : Protocol rest f.index xs j → Pending (.inBody rest f b) xs
  | stopped : Pending (.stopped result) xs

theorem step_correct (h : Pending c xs) (hq : Corresponds input xs q) :
    (step ⟨c,q⟩).control = ProgramControlIR.step input c ∧
    ∃ ys, Pending (ProgramControlIR.step input c) ys ∧ Corresponds input ys (step ⟨c,q⟩).queue := by
  cases h with
  | stopped => exact ⟨rfl,_,.stopped,hq⟩
  | @body rest f xs j b hp =>
    cases b with
    | stopped r =>
      cases r with
      | none => exact ⟨rfl,_,.stopped,hq⟩
      | some s => exact ⟨rfl,_,.running hp,hq⟩
    | running => exact ⟨rfl,_,.body hp,hq⟩
    | inSnapshots => exact ⟨rfl,_,.body hp,hq⟩
  | running hp =>
    cases hp with
    | nil => exact ⟨rfl,_,.stopped,hq⟩
    | frame hp => exact ⟨rfl,_,.running hp,hq⟩
    | left hp =>
      cases hq with
      | cons hval htail =>
        simp only [step,ProgramControlIR.step,hval]
        exact ⟨True.intro,_,.running hp,htail⟩
    | right hp =>
      cases hq with
      | cons hval htail =>
        simp only [step,ProgramControlIR.step,hval]
        exact ⟨True.intro,_,.running hp,htail⟩
    | retain hp => exact ⟨rfl,_,.running hp,hq⟩
    | advance hp => exact ⟨rfl,_,.running hp,hq⟩
    | body hp => exact ⟨rfl,_,.body hp,hq⟩
    | zero hp => exact ⟨rfl,_,.running hp,hq⟩
    | «repeat» hp => exact ⟨rfl,_,.running hp,hq⟩
    | branch ha hb =>
      simp only [step,ProgramControlIR.step]
      split
      · exact ⟨True.intro,_,.running ha,hq⟩
      · exact ⟨True.intro,_,.running hb,hq⟩

def run : Nat → FIFOConfig → FIFOConfig
  | 0,c => c
  | n+1,c => run n (step c)

theorem run_correct (h : Pending c xs) (hq : Corresponds input xs q) (n : Nat) :
    (run n ⟨c,q⟩).control = ProgramControlIR.run input n c := by
  induction n generalizing c xs q with
  | zero => rfl
  | succ n ih =>
    obtain ⟨same,ys,hp,hv⟩ := step_correct h hq
    have next := ih hp hv
    simpa only [run,ProgramControlIR.run,← same] using next

theorem selected_correct (p : Plan code f.index) (same : p.addresses = producerOrder)
    (hq : Corresponds input producerOrder q) (s : State) (n : Nat) :
    (run n ⟨.running code s f,q⟩).control =
      ProgramControlIR.run input n (.running code s f) := by
  exact run_correct (.running p.correct) (same ▸ hq) n

inductive MemoryReason where
  | unknownProtocol
  | orderMismatch
  deriving Repr, DecidableEq

/-- This is a mode change: in FIFO mode reads consume tokens, in memory mode
    they retain their original addresses and semantics. -/
inductive Transport (code : List Instr) (index : Int) (producerOrder : List Int) where
  | memory (reason : MemoryReason)
  | fifo (plan : Plan code index) (order : plan.addresses = producerOrder)

def compile (fuel : Nat) (code : List Instr) (index : Int) (producerOrder : List Int) :
    Transport code index producerOrder :=
  match plan fuel code index with
  | none => .memory .unknownProtocol
  | some p => if h : p.addresses = producerOrder then .fifo p h else .memory .orderMismatch

def Transport.isFIFO : Transport code index producerOrder → Bool
  | .memory _ => false
  | .fifo .. => true

def Transport.Contract (input : Input) (values : List Int) : Transport code index producerOrder → Prop
  | .memory _ => True
  | .fifo .. => Corresponds input producerOrder values

def Transport.execute (input : Input) (values : List Int) (s : State) (f : Frame)
    (steps : Nat) : Transport code index producerOrder → Config
  | .memory _ => ProgramControlIR.run input steps (.running code s f)
  | .fifo .. => (run steps ⟨.running code s f,values⟩).control

theorem Transport.execute_correct (t : Transport code f.index producerOrder)
    (h : t.Contract input values) (s : State) (steps : Nat) :
    t.execute input values s f steps = ProgramControlIR.run input steps (.running code s f) := by
  cases t with
  | memory => rfl
  | fifo p order => exact selected_correct p order h s steps

/-- Always decide buffering first. A failed FIFO selection keeps that buffered
    memory code; it does not retry an unrelated direct-FIFO optimization. -/
def compileOptimized (fuel : Nat) (body : List ControlIR.Instr) (start stride : Int)
    (count : Nat) (left right : Int) (producerOrder : List Int) :=
  compile fuel (optimizedLoopCode start stride count left right body) initial.index producerOrder

theorem compileOptimized_finishes (fuel : Nat) (body : List ControlIR.Instr) (meaning : Step State)
    (bodyCorrect : ∀ i x y s, ∃ n, ControlIR.run i x y n (.running body s []) = .stopped (meaning i x y s))
    (start stride : Int) (count : Nat) (left right : Int) (producerOrder : List Int)
    (input : Input) (values : List Int) (s : State)
    (contract : (compileOptimized fuel body start stride count left right producerOrder).Contract input values) :
    ∃ steps, (compileOptimized fuel body start stride count left right producerOrder).execute
        input values s initial steps =
      .stopped (BodyBackends.runSource meaning start stride count left right input s) := by
  obtain ⟨steps,h⟩ := optimizedBody_finishes body meaning bodyCorrect start stride count left right input s
  exact ⟨steps,(Transport.execute_correct _ contract s steps).trans h⟩

/-- Reference producer: emits values in its declared order. It never changes
    that order to make a consumer pass selection. This is not a concurrent or
    capacity-bounded producer scheduler. -/
def emit (input : Input) : List Int → Option (List Int)
  | [] => some []
  | i::is => do return (← input i) :: (← emit input is)

theorem emit_correct (h : emit input indices = some values) : Corresponds input indices values := by
  induction indices generalizing values with
  | nil => simp [emit] at h; subst values; exact .nil
  | cons i is ih =>
    cases hv : input i <;> simp [emit,hv] at h
    cases ht : emit input is <;> simp [ht] at h
    subst values
    exact .cons hv (ih ht)

/-- Imperative IR pipeline: reuse analysis/buffering, control lowering, then
    communication selection. Arbitrary sequences and branches are preserved. -/
def compileImperative (fuel : Nat) (source : Imperative.Program) (producerOrder : List Int) :=
  compile fuel (ProgramControlIR.lower (Imperative.transform source)) initial.index producerOrder

theorem compileImperative_finishes (fuel : Nat) (source : Imperative.Program) (producerOrder : List Int)
    (input : Input) (values : List Int) (s : State)
    (contract : (compileImperative fuel source producerOrder).Contract input values) :
    ∃ steps, (compileImperative fuel source producerOrder).execute input values s initial steps =
      .stopped (source.eval input s) := by
  obtain ⟨steps,h⟩ := ProgramControlIR.lower_finishes (Imperative.transform source) input s initial
  rw [Imperative.transform_correct] at h
  exact ⟨steps,(Transport.execute_correct _ contract s steps).trans h⟩

structure FunctionalArtifact (source : Functional.Program) (producerOrder : List Int) where
  control : List Instr
  correct : ProgramControlIR.lowerFunctional (Functional.transform source) = some control
  transport : Transport control initial.index producerOrder

def compileFunctional (fuel : Nat) (source : Functional.Program) (producerOrder : List Int) :
    Option (FunctionalArtifact source producerOrder) :=
  match h : ProgramControlIR.lowerFunctional (Functional.transform source) with
  | none => none
  | some code => some ⟨code,h,compile fuel code initial.index producerOrder⟩

theorem FunctionalArtifact.finishes (a : FunctionalArtifact source producerOrder)
    (input : Input) (values : List Int) (s : State)
    (contract : a.transport.Contract input values) :
    ∃ steps, a.transport.execute input values s initial steps = .stopped (source.eval input s) := by
  obtain ⟨steps,h⟩ := ProgramControlIR.lowerFunctional_finishes _ _ a.correct input s initial
  rw [Functional.transform_correct] at h
  exact ⟨steps,(Transport.execute_correct _ contract s steps).trans h⟩

end IRComparison.CommunicationIR
