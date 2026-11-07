import IRComparison.Circuit.Structured
import IRComparison.Hybrid.HybridUnifiedPipeline
import IRComparison.Circuit.SendBudget

namespace IRComparison.Circuit

structure Interval where
  lo : Int
  hi : Int
  deriving Repr

def wordRange : Interval := ⟨0,4294967295⟩

def bits (n : Nat) : Nat := max 1 (n.log2+1)
def signedWidth (r : Interval) : Nat := bits (max r.lo.natAbs r.hi.natAbs)+1


def union (a b : Interval) : Interval := ⟨min a.lo b.lo,max a.hi b.hi⟩

/-- Recognize the existing modular encoding, without changing its evaluation. -/
def wrapped? : Expr → Option Expr
  | .bin .sub a (.bin .mul (.bin .div b (.lit 4294967296)) (.lit 4294967296)) =>
      if a == b then some a else none
  | _ => none

def binRange (op : Bin) (u v : Interval) : Interval :=
  match op with
  | .add => ⟨u.lo+v.lo,u.hi+v.hi⟩
  | .sub => ⟨u.lo-v.hi,u.hi-v.lo⟩
  | .mul =>
      let m := Int.ofNat (max u.lo.natAbs u.hi.natAbs * max v.lo.natAbs v.hi.natAbs)
      ⟨-m,m⟩
  | .div => if u.lo ≥ 0 && v.lo ≥ 0 then ⟨0,max 0 u.hi⟩ else
      let m := Int.ofNat (max u.lo.natAbs u.hi.natAbs + 1)
      ⟨-m,m⟩
  | .lt => ⟨0,1⟩

def range (wires : Nat → Interval) (e : Expr) : Interval :=
  if (wrapped? e).isSome then wordRange else
  match e with
  | .fail => ⟨0,0⟩
  | .lit n => ⟨n,n⟩
  | .wire n => wires n
  | .reg _ | .memory .. => wordRange
  | .natIndex a => let r := range wires a; ⟨max 0 r.lo,max 0 r.hi⟩
  | .select _ a b => union (range wires a) (range wires b)
  | .seq _ b => range wires b
  | .bin op a b =>
      let u := range wires a
      let v := range wires b
      binRange op u v

structure Build where
  wires : Array Interval := #[wordRange,wordRange]
  memories : Array (Nat × Nat) := #[]
  queues : Array (Nat × Nat) := #[]
  nextArray : Nat := 0
  nextQueue : Nat := 0

abbrev Builder := StateM Build

def Build.addWire (b : Build) (r : Interval) : Build :=
  { b with wires := b.wires.push ⟨min 0 r.lo,max 0 r.hi⟩ }

def Build.exprRange (b : Build) (e : Expr) : Interval :=
  range (fun n => b.wires[n]?.getD wordRange) e

def fresh (r : Interval := wordRange) : Builder Nat :=
  fun b => (b.wires.size,b.addWire r)

def bounds (e : Expr) : Builder Interval := fun b => (b.exprRange e,b)

def freshFor (e : Expr) : Builder Nat := fun b => fresh (b.exprRange e) b

def queue (capacity : Nat) : Builder Nat := do
  let b ← get
  set { b with queues := b.queues.push (b.nextQueue,capacity),nextQueue := b.nextQueue+1 }
  return b.nextQueue

def snapshot (source : Nat) (sizes : Nat → Nat) : Builder Nat := do
  let b ← get
  set { b with memories := b.memories.push (b.nextArray,sizes source),nextArray := b.nextArray+1 }
  return b.nextArray

/-- Counter updates are explicit clocked actions; the body cannot implicitly
change the captured loop bound. -/
def counterLoop (k : Nat) (limit : Expr) (body : Schedule) : Schedule :=
  .seq (.step (.wire k (.lit 0)))
    (.loop (.bin .lt (.wire k) limit)
      (.seq body (.step (.wire k (.bin .add (.wire k) (.lit 1))))))

def command (i : Expr) (locals : List Expr) (output : Nat) : HybridIR.Cmd → Builder Schedule
  | .skip => pure .skip
  | .assign r e => pure (.step (.assign r (read i (.wire 0) (.wire 1) locals [] e)))
  | .store a j e => pure (.step (.store a (read i (.wire 0) (.wire 1) locals [] j)
      (read i (.wire 0) (.wire 1) locals [] e)))
  | .send e => pure (.step (.send output (read i (.wire 0) (.wire 1) locals [] e)))
  | .letValue e b => do
      let e := read i (.wire 0) (.wire 1) locals [] e
      let v ← freshFor e
      return .seq (.step (.wire v e)) (← command i (.wire v::locals) output b)
  | .seq a b => do
      let first ← command i locals output a
      return .seq first (← command i locals output b)
  | .branch e a b => do
      let yes ← command i locals output a
      let no ← command i locals output b
      return .branch (read i (.wire 0) (.wire 1) locals [] e) yes no
  | .repeat n b => do
      let k ← fresh ⟨0,n⟩
      return counterLoop k (.lit n) (← command i locals output b)
  | .forRange e b => do
      let e := Expr.natIndex (read i (.wire 0) (.wire 1) locals [] e)
      let n ← freshFor e
      let k ← fresh (← bounds e)
      let body ← command i (.wire k::locals) output b
      return .seq (.step (.wire n e)) (counterLoop k (.wire n) body)

/-- Throw away each token with a destructive receive; no random-access peek. -/
def take (q slot : Nat) (discard : Expr) : Builder Schedule := do
  let count := Expr.natIndex discard
  let n ← freshFor count
  let k ← fresh (← bounds count)
  let unused ← fresh
  return .seq (.step (.wire n count))
    (.seq (counterLoop k (.wire n) (.step (.receive q unused))) (.step (.receive q slot)))

def loadOne (input q : Nat) (old : List Expr) (slot : Nat) : WindowFIFO.Load → Builder Schedule
  | .memory a => pure (.step (.wire slot (.memory input (.lit a))))
  | .saved n => pure (.step (.wire slot (lookup old n)))
  | .take n => take q slot (.lit n)

def expandedLoads (input q : Nat) (old : List Expr) :
    List WindowFIFO.Load → List Nat → Builder Schedule
  | [],_ => pure .skip
  | _,[] => pure (.step (.wire 0 .fail))
  | l::ls,v::vs => do
      let first ← loadOne input q old v l
      return .seq first (← expandedLoads input q old ls vs)

def newSlots : Nat → Builder (List Nat)
  | 0 => pure []
  | n+1 => do
      let v ← fresh
      return v :: (← newSlots n)

def blocks (input qi qo : Nat) (old : List Expr) : List HybridIR.Block → Builder Schedule
  | [] => pure .skip
  | b::bs => do
      let vs ← newSlots b.loads.length
      let load ← expandedLoads input qi old b.loads vs
      let body ← command (.lit b.index) (vs.map Expr.wire) qo b.body
      let tail ← blocks input qi qo (vs.map Expr.wire) bs
      return .seq load (.seq body tail)

def preload (input q : Nat) : List Int → Schedule
  | [] => .skip
  | i::is => .seq (.step (.send q (.memory input (.lit i)))) (preload input q is)

structure InstructionLayout where
  frozen : Nat
  inputQueue : Nat
  outputQueue : Nat
  body : Schedule

def chooseInputQueue (channels : Nat → Nat) : GlobalPipeline.InputMode → Builder Nat
  | .channel a => pure (channels a)
  | .memory _ order fifo => queue (if fifo then order.length else 0)

def chooseOutputQueue (channels : Nat → Nat) (budget : Nat) : Option Nat → Builder Nat
  | some a => pure (channels a)
  | none => queue budget

def prepareInstruction (sizes : Nat → Nat) (channels : Nat → Nat) (c : HybridIR.Instruction) :
    Builder InstructionLayout := do
  let input ← snapshot c.input sizes
  let qi ← chooseInputQueue channels c.mode
  let qo ← chooseOutputQueue channels ((blocksBudget c.blocks).getD 0) c.output
  let body ← blocks input qi qo [] c.blocks
  return ⟨input,qi,qo,body⟩

def InstructionLayout.schedule (a : InstructionLayout) (c : HybridIR.Instruction) : Schedule :=
  let init := match c.mode with
    | .channel _ => Schedule.skip
    | .memory array order fifo => .seq (.step (.clear a.inputQueue))
        (if fifo then preload array a.inputQueue order else .skip)
  let erase := match c.output with
    | some array => Schedule.step (.erase array)
    | none => .skip
  .seq (.step (.snapshot a.frozen c.input))
    (.seq init (.seq (.step (.clear a.outputQueue)) (.seq erase
      (.seq a.body (.seq erase (.step (.clear a.inputQueue)))))))

def instruction (sizes : Nat → Nat) (channels : Nat → Nat) (c : HybridIR.Instruction) : Builder Schedule := do
  let a ← prepareInstruction sizes channels c
  return a.schedule c

def instructions (sizes : Nat → Nat) (channels : Nat → Nat) :
    List HybridIR.Instruction → Builder Schedule
  | [] => pure .skip
  | c::cs => do
      let first ← instruction sizes channels c
      return .seq first (← instructions sizes channels cs)

def linear (i : Expr) (a : AffineAddress.Linear) : Expr :=
  .bin .add (.bin .mul (.lit a.coefficient) i) (.lit a.offset)

inductive Load where
  | memory (address : AffineAddress.Linear)
  | saved (slot : Nat)
  | take (discard : AffineAddress.Linear)

def fromMemoryLoad : SymbolicWindowSchedule.Load → Load
  | .memory a => .memory a
  | .saved n => .saved n
def fromFIFOLoad : CompactRouting.Load → Load
  | .take n => .take n
  | .saved n => .saved n

def compactLoadOne (i : Expr) (input qi : Nat) (old : List Expr) (slot : Nat) : Load → Builder Schedule
  | .memory a => pure (.step (.wire slot (.memory input (linear i a))))
  | .saved n => pure (.step (.wire slot (lookup old n)))
  | .take n => take qi slot (linear i n)

def loads (i : Expr) (input qi : Nat) (old : List Expr) : List Load → List Nat → Builder Schedule
  | [],_ => pure .skip
  | _,[] => pure (.step (.wire 0 .fail))
  | l::ls,v::vs => do
      let first ← compactLoadOne i input qi old v l
      return .seq first (← loads i input qi old ls vs)

def copies : List Nat → List Nat → Schedule
  | [],_ | _,[] => .skip
  | d::ds,s::ss => .seq (.step (.wire d (.wire s))) (copies ds ss)

/-- Allocation and operation order retained as a proof witness for the
compact controller. Its runtime data remains in the finite machine banks. -/
structure CountedLayout where
  counter : Nat
  held : List Nat
  scratch : List Nat
  firstLoads : Schedule
  firstBody : Schedule
  firstRefill : Schedule
  laterLoads : Schedule
  laterBody : Schedule

def prepareCounted (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) : Builder CountedLayout := do
  let k ← fresh ⟨0,count⟩
  let i := Expr.bin .add (.lit start) (.bin .mul (.wire k) (.lit stride))
  let held ← newSlots (max initial.length refill.length)
  let scratch ← newSlots refill.length
  let firstLoads ← loads i input qi [] initial (held.take initial.length)
  let firstBody ← command i ((held.take initial.length).map Expr.wire) qo body
  let firstRefill ← loads i input qi ((held.take initial.length).map Expr.wire) refill scratch
  let laterLoads ← loads i input qi ((held.take refill.length).map Expr.wire) refill scratch
  let laterBody ← command i ((held.take refill.length).map Expr.wire) qo body
  return ⟨k,held,scratch,firstLoads,firstBody,firstRefill,laterLoads,laterBody⟩

def CountedLayout.round (c : CountedLayout) (refillSize : Nat) : Schedule :=
  let later := Schedule.seq
    (.branch (.bin .sub (.wire c.counter) (.lit 1)) c.laterLoads c.firstRefill)
    (.seq (copies (c.held.take refillSize) c.scratch) c.laterBody)
  .branch (.wire c.counter) later (.seq c.firstLoads c.firstBody)

def counted (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) : Builder Schedule := do
  if count = 0 then return .skip
  let c ← prepareCounted start stride count initial refill body input qi qo
  return counterLoop c.counter (.lit count) (c.round refill.length)

def tailCode (sizes : Nat → Nat) (incoming : Nat) : HybridCompactChainControl.Code → Builder Schedule
  | .finish r => do
      let unusedOutput ← queue 0
      let body ← counted r.start r.stride r.count (r.initial.map fromFIFOLoad)
        (r.refill.map fromFIFOLoad) r.body.target 0 incoming unusedOutput
      return .seq (.step (.clear unusedOutput)) body
  | .stage a s rest => do
      let out ← queue (max (sizes a) (s.count * (sendBound s.body).getD 0))
      let body ← counted s.start s.stride s.count (s.initial.map fromFIFOLoad)
        (s.refill.map fromFIFOLoad) s.body 0 incoming out
      let tail ← tailCode sizes out rest
      return .seq (.step (.erase a)) (.seq (.step (.clear out))
        (.seq body (.seq (.step (.erase a)) tail)))

def rootCode (sizes : Nat → Nat) (r : HybridCompactChainControl.RootCode) : Builder Schedule := do
  let out ← queue (max (sizes r.output) (r.sender.count * (sendBound r.sender.body).getD 0))
  let unusedInput ← queue 0
  let input ← snapshot r.inputArray sizes
  let s := r.sender
  let body ← counted s.start s.stride s.count (s.initial.map fromMemoryLoad)
    (s.refill.map fromMemoryLoad) s.body input unusedInput out
  let tail ← tailCode sizes out r.tail
  return .seq (.step (.erase r.output)) (.seq (.step (.snapshot input r.inputArray))
    (.seq (.step (.clear out)) (.seq body (.seq (.step (.erase r.output)) tail))))

structure Artifact where
  machine : Machine
  wires : Array Interval
  memories : Array (Nat × Nat)
  originalMemories : Array (Nat × Nat)
  deriving Repr

/-- Retain the structured layout as a proof witness. Only the machine is
serialized to RTL; it is produced by the generally proved assembler. -/
structure Scheduled where
  schedule : Schedule
  build : Build

def allocateChannels (capacity : Nat → Nat) : List Nat → Builder (List (Nat × Nat))
  | [] => pure []
  | a::ids => do
      let q ← queue (capacity a)
      return (a,q)::(← allocateChannels capacity ids)

def channelLookup (mapping : List (Nat × Nat)) (a : Nat) : Nat :=
  ((mapping.find? (fun p => p.1 == a)).map Prod.snd).getD 0

/-- Layout lists all source arrays. Missing arrays are diagnosed by RTL
validation; no data-dependent source execution is performed during lowering. -/
def schedule (layout : Array (Nat × Nat)) (code : HybridUnifiedPipeline.Code) : Scheduled := Id.run do
  let sizes := fun a => ((layout.toList.find? (fun p => p.1 == a)).map Prod.snd).getD 0
  let nextArray := layout.foldl (fun n p => max n (p.1+1)) 0
  let build : Builder Schedule := do
    match code with
    | .expanded cs =>
      let ids := (cs.filterMap (·.output)).eraseDups
      let mapping ← allocateChannels (fun a => max (sizes a) (outputBudget cs a)) ids
      let channels := channelLookup mapping
      instructions sizes channels cs
    | .compact c => rootCode sizes c
  let (control,b) := build.run { memories := layout, nextArray := nextArray }
  return ⟨control,b⟩

def lower (layout : Array (Nat × Nat)) (code : HybridUnifiedPipeline.Code) : Artifact :=
  let generated := schedule layout code
  let b := generated.build
  ⟨generated.schedule.assemble b.queues,b.wires,b.memories,layout⟩

end IRComparison.Circuit
