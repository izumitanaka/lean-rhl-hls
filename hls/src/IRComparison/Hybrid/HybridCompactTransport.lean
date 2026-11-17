import IRComparison.Hybrid.HybridCompactFIFO

namespace IRComparison.HybridCompactTransport

inductive Selected (baseCode : HybridSymbolicLoop.Code) (producer : CompactSequence.Seq) where
  | memory
  | fifo (plan : HybridCompactFIFO.Plan baseCode producer)

def select (baseCode : HybridSymbolicLoop.Code) (producer : CompactSequence.Seq) : Selected baseCode producer :=
  match HybridCompactFIFO.compile baseCode producer with
  | none => .memory
  | some p => .fifo p

def Selected.eval (p : Selected baseCode producer) (input : Input) (x y : Int) (s : State) (q : List Int) : Option State :=
  match p with
  | .memory => baseCode.eval input x y s
  | .fifo plan => (plan.code.eval x y s q).map Prod.fst

theorem Selected.correct (p : Selected baseCode producer)
    (hq : CommunicationIR.Corresponds input producer.entries q) :
    p.eval input x y s q = baseCode.eval input x y s := by
  cases p with
  | memory => rfl
  | fifo plan => exact plan.correct s q hq

structure SolverSelection (baseCode : HybridSymbolicLoop.Code) (producer : CompactSequence.Seq) where
  candidate : CompactSequence.Seq
  same : candidate.entries = producer.entries
  selected : Selected baseCode candidate

def SolverSelection.eval (p : SolverSelection baseCode producer) := p.selected.eval

theorem SolverSelection.correct (p : SolverSelection baseCode producer)
    (hq : CommunicationIR.Corresponds input producer.entries q) :
    p.eval input x y s q = baseCode.eval input x y s := by
  apply p.selected.correct
  simpa only [p.same] using hq

/-- This is an actual solver-backed compilation entry. SAT parameters are
    checked against the requested sequence before FIFO code is selected.
    A failed query retains the counted baseCode code. -/
def solveAndSelect (baseCode : HybridSymbolicLoop.Code) (producer : CompactSequence.Seq)
    (directory : System.FilePath) : IO (CompactSequence.Transcript × SolverSelection baseCode producer) := do
  let (transcript,candidate) ← CompactSequence.solve producer directory
  match candidate with
  | none => return (transcript,⟨producer,rfl,.memory⟩)
  | some certified => return (transcript,⟨certified.sequence,certified.correct,select baseCode certified.sequence⟩)

end IRComparison.HybridCompactTransport
