import IRComparison.Memory.WindowFIFO
import IRComparison.Hybrid.HybridWindowPlan

namespace IRComparison.HybridWindowTransport
open CommunicationIR HybridIR

structure Block where
  index : Int
  loads : List WindowFIFO.Load
  body : MemoryCmd

def eval (input : Input) (x y : Int) : List Block → List Int → State → List Int → Option (State × List Int)
  | [],_,s,q => some (s,q)
  | b::rest,old,s,q => do
      let (values,remaining) ← WindowFIFO.execute input old b.loads q
      let next ← b.body.eval b.index x y s values
      eval input x y rest values next remaining

inductive Routes : List HybridWindowPlan.Block → List Int → List Block → List Int → Prop where
  | nil : Routes [] indices [] indices
  | cons : WindowFIFO.Routes b.loads indices loads middle → Routes rest middle code tail →
      Routes (b::rest) indices (⟨b.index,loads,b.body⟩::code) tail

structure Routed (source : List HybridWindowPlan.Block) (indices : List Int) where
  code : List Block
  remaining : List Int
  correct : Routes source indices code remaining

def route : (source : List HybridWindowPlan.Block) → (indices : List Int) → Option (Routed source indices)
  | [],indices => some ⟨[],indices,.nil⟩
  | b::rest,indices => do
      let first ← WindowFIFO.route b.loads indices
      let next ← route rest first.remaining
      return ⟨⟨b.index,first.code,b.body⟩::next.code,next.remaining,.cons first.correct next.correct⟩

theorem Routes.correct (h : Routes source indices code remaining)
    (hq : Corresponds input indices queue) (old : List Int) (s : State) (x y : Int) :
    (eval input x y code old s queue).map Prod.fst = HybridWindowPlan.eval input x y source old s ∧
    ∀ out tail, eval input x y code old s queue = some (out,tail) → Corresponds input remaining tail := by
  induction h generalizing old s queue with
  | nil => exact ⟨rfl,by intros; simp_all [eval]⟩
  | @cons indices loads middle rest code tail b first next ih =>
    obtain ⟨eq,suffix⟩ := first.correct hq old
    cases hload : WindowFIFO.execute input old loads queue with
    | none => simp [eval,HybridWindowPlan.eval,← eq,hload]
    | some pair =>
      obtain ⟨values,after⟩ := pair
      have related := suffix values after hload
      cases hbody : b.body.eval b.index x y s values with
      | none => simp [eval,HybridWindowPlan.eval,← eq,hload,hbody]
      | some t =>
        obtain ⟨same,endRelated⟩ := ih related values t
        constructor
        · simpa [eval,HybridWindowPlan.eval,← eq,hload,hbody] using same
        · intro out qs hr
          apply endRelated out qs
          simpa [eval,hload,hbody] using hr

def memoryLoads : List WindowSchedule.Load → List WindowFIFO.Load
  | [] => []
  | .memory a::ls => .memory a::memoryLoads ls
  | .saved j::ls => .saved j::memoryLoads ls

theorem memoryLoads_correct (loads : List WindowSchedule.Load) (old q : List Int) :
    WindowFIFO.execute input old (memoryLoads loads) q =
      (WindowSchedule.execute input old loads).map (fun vs => (vs,q)) := by
  induction loads with
  | nil => rfl
  | cons l ls ih =>
    cases l with
    | memory a =>
      cases hv : input a <;> cases ht : WindowSchedule.execute input old ls <;>
        simp [memoryLoads,WindowFIFO.execute,WindowFIFO.Load.eval,WindowSchedule.execute,WindowSchedule.Load.eval,ih,hv,ht]
    | saved j =>
      cases hv : old[j]? <;> cases ht : WindowSchedule.execute input old ls <;>
        simp [memoryLoads,WindowFIFO.execute,WindowFIFO.Load.eval,WindowSchedule.execute,WindowSchedule.Load.eval,ih,hv,ht]

def memory (blocks : List HybridWindowPlan.Block) : List Block :=
  blocks.map (fun b => ⟨b.index,memoryLoads b.loads,b.body⟩)

theorem memory_correct (blocks : List HybridWindowPlan.Block) (old : List Int) (s : State) (q : List Int) :
    eval input x y (memory blocks) old s q = (HybridWindowPlan.eval input x y blocks old s).map (fun t => (t,q)) := by
  induction blocks generalizing old s with
  | nil => rfl
  | cons b rest ih =>
    simp only [memory,List.map_cons,eval,HybridWindowPlan.eval,memoryLoads_correct]
    cases hl : WindowSchedule.execute input old b.loads with
    | none => rfl
    | some vs =>
      simp only [Option.map_some,bind,Option.bind]
      cases hb : b.body.eval b.index x y s vs with
      | none => rfl
      | some t => exact ih vs t

def original (body : MemoryCmd) (stride : Int) : Nat → Int → List Block
  | 0,_ => []
  | n+1,i => ⟨i,[],body⟩ :: original body stride n (i+stride)

theorem original_correct (body : MemoryCmd) (stride : Int) (n : Nat) (i : Int) (s : State) (q : List Int) :
    eval input x y (original body stride n i) [] s q =
      (Source.iterate (fun j => body.eval j x y) stride n i s).map (fun t => (t,q)) := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih =>
    simp only [original,eval,WindowFIFO.execute,bind,Option.bind,Source.iterate]
    cases hb : body.eval i x y s [] with
    | none => rfl
    | some t => exact ih (i+stride) t

/-- One selected input array is FIFO throughout the region. Other arrays remain
    body memory. The buffered candidate is fixed before routing is attempted. -/
inductive Selected (size array : Nat) (body : MemoryCmd) (stride : Int) (count : Nat)
    (start : Int) (producer : List Int) where
  | memory (buffer : HybridWindowPlan.Result size array body stride count start)
  | fifo (buffered : Bool) (buffer : HybridWindowPlan.Plan size array body stride count start [])
      (routed : Routed buffer.blocks producer)

/-- Explain an optimization miss without rejecting the source program. -/
inductive Decision where
  | fifo (buffered : Bool)
  | accessesUnresolved
  | windowUnavailable
  | supplyOrderMismatch (bufferRetained : Bool)
  deriving Repr, DecidableEq

def compileWithReason (size array : Nat) (body : MemoryCmd) (stride : Int) (count : Nat)
    (start : Int) (producer : List Int) : Selected size array body stride count start producer × Decision :=
  match HybridWindowPlan.needsReuse array body stride count start [] with
  | none => (.memory .memory,.accessesUnresolved)
  | some reuse => match HybridWindowPlan.prepareWith reuse size array body stride count start [] with
    | none => (.memory .memory,.windowUnavailable)
    | some p => match route p.blocks producer with
      | none => (if reuse then .memory (.buffered p) else .memory .memory,.supplyOrderMismatch reuse)
      | some r => (.fifo reuse p r,.fifo reuse)

def compile (size array : Nat) (body : MemoryCmd) (stride : Int) (count : Nat)
    (start : Int) (producer : List Int) : Selected size array body stride count start producer :=
  (compileWithReason size array body stride count start producer).1

def Selected.isFIFO : Selected size array body stride count start producer → Bool
  | .memory _ => false
  | .fifo .. => true

def Selected.hasBuffer : Selected size array body stride count start producer → Bool
  | .memory .memory => false
  | .memory (.buffered _) => true
  | .fifo buffered _ _ => buffered

def Selected.Contract (data : Array Int) (values : List Int) : Selected size array body stride count start producer → Prop
  | .memory _ => True
  | .fifo .. => Corresponds (arrayInput data) producer values

def Selected.eval (data : Array Int) (x y : Int) (s : State) (values : List Int) :
    Selected size array body stride count start producer → Option State
  | .memory b => b.eval data x y s
  | .fifo _ _ r => (HybridWindowTransport.eval (arrayInput data) x y r.code [] s values).map Prod.fst

theorem Selected.correct (selected : Selected size array body stride count start producer)
    (s : State) (sized : (s.arrays array).size = size) (x y : Int) (values : List Int)
    (contract : selected.Contract (s.arrays array) values) :
    selected.eval (s.arrays array) x y s values =
      Source.iterate (fun j => body.eval j x y) stride count start s := by
  cases selected with
  | memory b => exact b.correct s sized x y
  | fifo buffered p r =>
    exact (r.correct.correct contract [] s x y).1.trans (p.blocks_correct _ sized s rfl .nil x y)

def Selected.code : Selected size array body stride count start producer → List Block
  | .memory .memory => original body stride count start
  | .memory (.buffered p) => HybridWindowTransport.memory p.blocks
  | .fifo _ _ r => r.code

theorem Selected.code_correct (selected : Selected size array body stride count start producer)
    (data : Array Int) (x y : Int) (s : State) (values : List Int) :
    (HybridWindowTransport.eval (arrayInput data) x y selected.code [] s values).map Prod.fst = selected.eval data x y s values := by
  cases selected with
  | memory b =>
    cases b with
    | memory => simp [Selected.code,Selected.eval,HybridWindowPlan.Result.eval,original_correct,Option.map_map,Function.comp_def]
    | buffered p => simp [Selected.code,Selected.eval,HybridWindowPlan.Result.eval,memory_correct,Option.map_map,Function.comp_def]
  | fifo => rfl

end IRComparison.HybridWindowTransport
