import IRComparison.Circuit.SharedGraphSound
import IRComparison.Circuit.ChannelCountedLower

namespace IRComparison.Circuit.Shared

/-- Only already-small counter/address schedules pass through this adapter.
ReadCode-bearing bodies go through `command` or `channel` directly. -/
def small (builder : Builder Circuit.Schedule) : Builder (Schedule Program) := fun b =>
  let (s,b') := builder b
  (s.mapExpressions ofExpr,b')

def expandedLoads (input q : Nat) (old : List Circuit.Expr) (ls : List WindowFIFO.Load) (vs : List Nat) :=
  small (Circuit.expandedLoads input q old ls vs)
def loads (i : Circuit.Expr) (input q : Nat) (old : List Circuit.Expr) (ls : List Circuit.Load) (vs : List Nat) :=
  small (Circuit.loads i input q old ls vs)
def preload (input q : Nat) (is : List Int) := (Circuit.preload input q is).mapExpressions ofExpr
def copies (dst src : List Nat) := (Circuit.copies dst src).mapExpressions ofExpr

def blocks (input qi qo : Nat) (old : List Expr) : List HybridIR.Block → Builder (Schedule Program)
  | [] => pure .skip
  | b::bs => do
      let vs ← newSlots b.loads.length
      let load ← expandedLoads input qi old b.loads vs
      let body ← command (.lit b.index) (vs.map Expr.wire) qo b.body
      let tail ← blocks input qi qo (vs.map Expr.wire) bs
      return .seq load (.seq body tail)


structure InstructionLayout where
  frozen : Nat
  inputQueue : Nat
  outputQueue : Nat
  body : Schedule Program


def prepareInstruction (sizes : Nat → Nat) (channels : Nat → Nat) (c : HybridIR.Instruction) :
    Builder InstructionLayout := do
  let input ← snapshot c.input sizes
  let qi ← chooseInputQueue channels c.mode
  let qo ← chooseOutputQueue channels ((blocksBudget c.blocks).getD 0) c.output
  let body ← blocks input qi qo [] c.blocks
  return ⟨input,qi,qo,body⟩

def InstructionLayout.schedule (a : InstructionLayout) (c : HybridIR.Instruction) : Schedule Program :=
  let init := match c.mode with
    | .channel _ => (Schedule.skip (α:=Program))
    | .memory array order fifo => .seq (.step (.clear a.inputQueue))
        (if fifo then preload array a.inputQueue order else .skip)
  let erase := match c.output with
    | some array => (Schedule.step (α:=Program)) (.erase array)
    | none => .skip
  .seq (.step (.snapshot a.frozen c.input))
    (.seq init (.seq (.step (.clear a.outputQueue)) (.seq erase
      (.seq a.body (.seq erase (.step (.clear a.inputQueue)))))))

def instruction (sizes : Nat → Nat) (channels : Nat → Nat) (c : HybridIR.Instruction) : Builder (Schedule Program) := do
  let a ← prepareInstruction sizes channels c
  return a.schedule c

def instructions (sizes : Nat → Nat) (channels : Nat → Nat) :
    List HybridIR.Instruction → Builder (Schedule Program)
  | [] => pure .skip
  | c::cs => do
      let first ← instruction sizes channels c
      return .seq first (← instructions sizes channels cs)


structure CountedLayout where
  counter : Nat
  held : List Nat
  scratch : List Nat
  firstLoads : Schedule Program
  firstBody : Schedule Program
  firstRefill : Schedule Program
  laterLoads : Schedule Program
  laterBody : Schedule Program

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

def CountedLayout.round (c : CountedLayout) (refillSize : Nat) : Schedule Program :=
  let later := (Schedule.seq (α:=Program))
    (.branch (ofExpr (.bin .sub (.wire c.counter) (.lit 1))) c.laterLoads c.firstRefill)
    (.seq (copies (c.held.take refillSize) c.scratch) c.laterBody)
  .branch (ofExpr (.wire c.counter)) later (.seq c.firstLoads c.firstBody)

def counted (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) : Builder (Schedule Program) := do
  if count = 0 then return .skip
  let c ← prepareCounted start stride count initial refill body input qi qo
  return counterLoop c.counter (.lit count) (c.round refill.length)

def tailCode (sizes : Nat → Nat) (incoming : Nat) : HybridCompactChainControl.Code → Builder (Schedule Program)
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

def rootCode (sizes : Nat → Nat) (r : HybridCompactChainControl.RootCode) : Builder (Schedule Program) := do
  let out ← queue (max (sizes r.output) (r.sender.count * (sendBound r.sender.body).getD 0))
  let unusedInput ← queue 0
  let input ← snapshot r.inputArray sizes
  let s := r.sender
  let body ← counted s.start s.stride s.count (s.initial.map fromMemoryLoad)
    (s.refill.map fromMemoryLoad) s.body input unusedInput out
  let tail ← tailCode sizes out r.tail
  return .seq (.step (.erase r.output)) (.seq (.step (.snapshot input r.inputArray))
    (.seq (.step (.clear out)) (.seq body (.seq (.step (.erase r.output)) tail))))


structure Scheduled where
  schedule : Schedule Program
  build : Build


def regionCode (sizes : Nat → Nat) (r : HybridRegions.Region) : Builder (Schedule Program) := do
  let qi ← queue 0
  let qo ← queue 0
  let input ← snapshot r.array sizes
  let c := r.producer
  let body ← counted c.start c.stride c.count
    (c.initial.map fromMemoryLoad) (c.refill.map fromMemoryLoad) c.body input qi qo
  return .seq (.step (.snapshot input r.array)) (.seq (.step (.clear qo)) body)

def regionsCode (sizes : Nat → Nat) : List HybridRegions.Region → Builder (Schedule Program)
  | [] => pure .skip
  | r::rs => do
    let first ← regionCode sizes r
    let rest ← regionsCode sizes rs
    return .seq first rest



open HybridSymbolicGlobal (Instruction)


abbrev CountedBuilder := Int → Int → Nat → List Load → List Load → HybridIR.Cmd → Nat → Nat → Nat → Builder (Schedule Program)

def prepareSymbolicWith (countedBuilder : CountedBuilder) (sizes channels : Nat → Nat) (c : Instruction) : Builder InstructionLayout := do
  let input ← snapshot (symbolicInput c) sizes
  let qi ← chooseInputQueue channels (symbolicMode c)
  let qo ← chooseOutputQueue channels (symbolicBudget c) (symbolicOutput c)
  let core := symbolicBody c
  let body ← countedBuilder core.start core.stride core.count (symbolicInitial c) (symbolicRefill c) core.body input qi qo
  return ⟨input,qi,qo,body⟩

def prepareSymbolic := prepareSymbolicWith counted

/-- Schedule only metadata and one counted body; no reference-block list is
constructed by the executable compiler. -/
def symbolicSchedule (a : InstructionLayout) (c : Instruction) : Schedule Program :=
  let init := match symbolicMode c with
    | .channel _ => (Schedule.skip (α:=Program))
    | .memory _ _ _ => .seq (.step (.clear a.inputQueue)) .skip
  let erase := match symbolicOutput c with
    | some array => (Schedule.step (α:=Program)) (.erase array)
    | none => .skip
  .seq (.step (.snapshot a.frozen (symbolicInput c)))
    (.seq init (.seq (.step (.clear a.outputQueue)) (.seq erase
      (.seq a.body (.seq erase (.step (.clear a.inputQueue)))))))

def symbolicInstructionWith (countedBuilder : CountedBuilder) (sizes channels : Nat → Nat) (c : Instruction) : Builder (Schedule Program) := do
  return symbolicSchedule (← prepareSymbolicWith countedBuilder sizes channels c) c

def symbolicInstructionsWith (countedBuilder : CountedBuilder) (sizes channels : Nat → Nat) (cs : List Instruction) : Builder (Schedule Program) :=
  match cs with
  | [] => pure .skip
  | c::cs => do
      let first ← symbolicInstructionWith countedBuilder sizes channels c
      return .seq first (← symbolicInstructionsWith countedBuilder sizes channels cs)

def symbolicInstruction := symbolicInstructionWith counted
def symbolicInstructions := symbolicInstructionsWith counted


def symbolicProgramWith (countedBuilder : CountedBuilder) (sizes : Nat → Nat) (cs : List Instruction) : Builder (Schedule Program) := do
  let channels ← allocateChannels (symbolicCapacity cs) (symbolicChannels cs)
  symbolicInstructionsWith countedBuilder sizes (channelLookup channels) cs

def symbolicProgram := symbolicProgramWith counted

/-- Layout lists all source arrays. Missing arrays are diagnosed by RTL
validation; no data-dependent source execution is performed during lowering. -/
def scheduleWith (countedBuilder : CountedBuilder) (layout : Array (Nat × Nat)) (code : HybridUnifiedPipeline.Code) : Scheduled := Id.run do
  let sizes := fun a => ((layout.toList.find? (fun p => p.1 == a)).map Prod.snd).getD 0
  let nextArray := layout.foldl (fun n p => max n (p.1+1)) 0
  let build : Builder (Schedule Program) := do
    match code with
    | .expanded cs =>
      let ids := (cs.filterMap (·.output)).eraseDups
      let mapping ← allocateChannels (fun a => max (sizes a) (outputBudget cs a)) ids
      let channels := channelLookup mapping
      instructions sizes channels cs
    | .symbolic cs => symbolicProgramWith countedBuilder sizes cs
    | .compact c => rootCode sizes c
    | .regions rs => regionsCode sizes rs
  let (control,b) := build.run { memories := layout, nextArray := nextArray }
  return ⟨control,b⟩

def schedule := scheduleWith counted


/-- Production named-buffer lowering now creates shared graphs immediately. -/
def namedCounted (start stride : Int) (count : Nat) (initial refill : List Circuit.Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) : Builder (Schedule Program) := fun b =>
  let c := ChannelCounted.command input qi qo start stride count initial refill body
  channel (ChannelLower.bankFor c b) (.lit 0) [] c (ChannelLower.reserve c b)

def pipeline (layout : Array (Nat × Nat)) (code : HybridUnifiedPipeline.Code) : Scheduled :=
  scheduleWith namedCounted layout code

end IRComparison.Circuit.Shared
