import PaperCore.Semantics

namespace PaperCore.MixedTarget

/-- The existing control syntax is unchanged. Each action chooses ordinary
memory or FIFO storage. Selection/alias policy belongs to the compiler. -/
inductive Action (Op : Type) where
  | memory (command : MemoryAction Op)
  | stream (command : StreamAction)
  deriving Repr, DecidableEq

abbrev Storage := Heap × Streams
abbrev Code (Op : Type) := Stmt Op (Action Op)

/-- One storage representation for each array throughout a transformation region.
Names here are storage identities, not shadowable source-level binder names. -/
inductive Representation where
  | memory
  | fifo
  deriving Repr, DecidableEq

abbrev Policy := Array → Representation

def Action.storage : Action Op → Array
  | .memory (.read _ array _) | .memory (.write array _ _) => array
  | .stream (.read _ array) | .stream (.write array _) => array

def Action.representation : Action Op → Representation
  | .memory _ => .memory
  | .stream _ => .fifo

/-- Checks both branches and every loop body, irrespective of which path executes.
This checks storage selection only; it does not certify a FIFO conversion. -/
def respects (policy : Policy) : Code Op → Bool
  | .action command => decide (policy command.storage = command.representation)
  | .assign _ _ => true
  | .seq a b | .branch _ a b => respects policy a && respects policy b
  | .loop _ _ _ _ body | .kernel body => respects policy body

def actions : Code Op → List (Action Op)
  | .action command => [command]
  | .assign _ _ => []
  | .seq a b | .branch _ a b => actions a ++ actions b
  | .loop _ _ _ _ body | .kernel body => actions body

theorem respects_iff : respects policy code = true ↔
    ∀ command ∈ actions code, policy command.storage = command.representation := by
  induction code with
  | action command => simp [respects, actions]
  | assign name value => simp [respects, actions]
  | seq a b ha hb | branch test a b ha hb =>
    simp only [respects, Bool.and_eq_true, ha, hb, actions, List.mem_append]
    constructor
    · rintro ⟨a, b⟩ command (h | h)
      · exact a command h
      · exact b command h
    · intro h
      exact ⟨fun command hc => h command (.inl hc), fun command hc => h command (.inr hc)⟩
  | loop counter start stop step body ih | kernel body ih => exact ih

/-- Two accesses to the same array cannot choose different representations,
including accesses in distinct branches or loop iterations. -/
theorem same_storage_same_representation
    (valid : respects policy code = true)
    (first : a ∈ actions code) (second : b ∈ actions code)
    (same : a.storage = b.storage) : a.representation = b.representation := by
  have ha := respects_iff.mp valid a first
  have hb := respects_iff.mp valid b second
  exact ha.symm.trans ((congrArg policy same).trans hb)

/-- A failed whole-code consistency check never yields a partial candidate. -/
def checkPolicy (policy : Policy) (code : Code Op) :
    Option { result : Code Op // result = code ∧ respects policy result = true } :=
  if h : respects policy code = true then some ⟨code, rfl, h⟩ else none

def memoryState (state : State Heap) (queues : Streams) : State Storage :=
  ⟨state.regs,(state.memory,queues)⟩

def streamState (state : State Streams) (heap : Heap) : State Storage :=
  ⟨state.regs,(heap,state.memory)⟩

inductive Step (meaning : Op → Int → Int → Int) : Action Op → State Storage → State Storage → Prop where
  | memory (run : MemoryStep meaning command source target) :
      Step meaning (.memory command) (memoryState source queues) (memoryState target queues)
  | stream (run : StreamStep command source target) :
      Step meaning (.stream command) (streamState source heap) (streamState target heap)

abbrev Execution (meaning : Op → Int → Int → Int) := Exec meaning (Step meaning)

/-- Structural embedding only: no array access is analyzed or FIFO-converted. -/
def mapActions (map : A → B) : Stmt Op A → Stmt Op B
  | .action command => .action (map command)
  | .assign name value => .assign name value
  | .seq a b => .seq (mapActions map a) (mapActions map b)
  | .branch test yes no => .branch test (mapActions map yes) (mapActions map no)
  | .loop counter start stop step body => .loop counter start stop step (mapActions map body)
  | .kernel body => .kernel (mapActions map body)

def retain (source : Source Op) : Code Op := mapActions Action.memory source

def includeFifo (target : Target Op) : Code Op := mapActions Action.stream target

/-- Shared simulation for both unchanged memory code and existing proved FIFO
code. The other storage component is preserved by the embedding. -/
theorem map_execution {meaning : Op → Int → Int → Int}
    {sourceStep : A → State M → State M → Prop} {targetStep : B → State N → State N → Prop}
    (map : A → B) (embed : State M → State N)
    (registers : ∀ s, (embed s).regs = s.regs)
    (setReg : ∀ s name value, embed (s.setReg name value) = (embed s).setReg name value)
    (action : ∀ command s t, sourceStep command s t → targetStep (map command) (embed s) (embed t))
    (run : Exec meaning sourceStep code s t) : Exec meaning targetStep (mapActions map code) (embed s) (embed t) := by
  induction run with
  | action h => exact .action (action _ _ _ h)
  | assign value =>
    simp only [mapActions,setReg]
    exact .assign (by simpa only [registers] using value)
  | seq _ _ first second => exact .seq first second
  | ifTrue value nonzero _ body =>
    exact .ifTrue (by simpa only [registers] using value) nonzero body
  | ifFalse value _ body => exact .ifFalse (by simpa only [registers] using value) body
  | kernel _ body => exact .kernel body
  | forExit value =>
    simp only [mapActions,setReg]
    exact .forExit (by simpa only [registers] using value)
  | forLoop value nonzero _ counter _ body rest =>
    exact .forLoop (by simpa only [registers] using value) nonzero
      (by simpa only [setReg] using body) (by simpa only [registers] using counter) rest

/-- Retained source code executes unchanged and leaves all FIFOs untouched. -/
theorem retain_forward (run : SourceExec meaning source s t) (queues : Streams) :
    Execution meaning (retain source) (memoryState s queues) (memoryState t queues) :=
  map_execution Action.memory (fun state => memoryState state queues)
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ h => .memory h) run

/-- Existing FIFO proofs remain usable and preserve all ordinary memory. -/
theorem includeFifo_forward (run : TargetExec meaning target s t) (heap : Heap) :
    Execution meaning (includeFifo target) (streamState s heap) (streamState t heap) :=
  map_execution Action.stream (fun state => streamState state heap)
    (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ h => .stream h) run

#print axioms retain_forward
#print axioms includeFifo_forward
end PaperCore.MixedTarget
