import IRComparison.Core.VersionedMemoryMachine
import IRComparison.Core.VersionedFIFOMachine
import IRComparison.Hybrid.HybridCompactTransport

namespace IRComparison.VersionedOrder
abbrev Body := VersionedHybrid.Term

/-- FIFO selection is made while the body is still versioned. -/
inductive Routing (memory : VersionedLoop.Code) (supplier : CompactSequence.Seq) where
  | memory
  | fifo (plan : VersionedFIFO.Plan memory supplier)

/-- Empty routing is not reported as a memory-to-FIFO optimization. -/
def hasReads (count : Nat) (initial refill : List SymbolicWindowSchedule.Load) : Bool :=
  count > 0 && (initial.any (fun l => match l with | .memory _ => true | _ => false) ||
    (count > 1 && refill.any (fun l => match l with | .memory _ => true | _ => false)))

def route (memory : VersionedLoop.Code) (supplier : CompactSequence.Seq) : Routing memory supplier :=
  if hasReads memory.count memory.initial memory.refill then
    match VersionedFIFO.compile memory supplier with
    | none => .memory
    | some p => .fifo p
  else .memory

structure LatePlan (size array : Nat) (body : Body) (start stride : Int) (count : Nat) (supplier : CompactSequence.Seq) where
  window : VersionedLoop.Selected size array body start stride count
  routing : Routing window.code supplier

def planLate (size array : Nat) (body : Body) (start stride : Int) (count : Nat) (supplier : CompactSequence.Seq) :
    LatePlan size array body start stride count supplier :=
  let w := VersionedLoop.select size array body start stride count
  ⟨w,route w.code supplier⟩

inductive Code where
  | lateMemory (code : VersionedMemoryMachine.Code)
  | lateFIFO (code : VersionedFIFOMachine.Code)
  | earlyMemory (code : HybridSymbolicLoop.Code)
  | earlyFIFO (code : HybridCompactFIFO.Code)

def Code.eval (code : Code) (input : Input) (x y : Int) (s : State) (q : List Int) : Option State :=
  match code with
  | .lateMemory c => c.eval input x y s
  | .lateFIFO c => (c.eval x y s q).map Prod.fst
  | .earlyMemory c => c.eval input x y s
  | .earlyFIFO c => (c.eval x y s q).map Prod.fst

def materialize (p : LatePlan size array body start stride count supplier) : Code :=
  match p.routing with
  | .memory => .lateMemory (VersionedMemoryMachine.allocate p.window.code)
  | .fifo f => .lateFIFO (VersionedFIFOMachine.allocate f.code)

theorem materialize_correct (p : LatePlan size array body start stride count supplier)
    (s : State) (sized : (s.arrays array).size = size)
    (hq : CommunicationIR.Corresponds (arrayInput (s.arrays array)) supplier.entries q) :
    (materialize p).eval (arrayInput (s.arrays array)) x y s q =
      Source.iterate (fun i => VersionedWindow.run body i x y) stride count start s := by
  cases h : p.routing with
  | memory =>
    simp only [materialize,h,Code.eval,VersionedMemoryMachine.correct]
    exact p.window.correct s sized
  | fifo f =>
    simp only [materialize,h,Code.eval,VersionedFIFOMachine.correct]
    exact (f.correct s q hq).trans (p.window.correct s sized)

structure Artifact (size array : Nat) (body : Body) (start stride : Int) (count : Nat) (supplier : CompactSequence.Seq) where
  code : Code
  correct : ∀ s, (s.arrays array).size = size → ∀ x y q,
    CommunicationIR.Corresponds (arrayInput (s.arrays array)) supplier.entries q →
    code.eval (arrayInput (s.arrays array)) x y s q =
      Source.iterate (fun i => VersionedWindow.run body i x y) stride count start s

def late (size array : Nat) (body : Body) (start stride : Int) (count : Nat) (supplier : CompactSequence.Seq) :
    Artifact size array body start stride count supplier :=
  let p := planLate size array body start stride count supplier
  ⟨materialize p,fun s hs x y q hq => materialize_correct p s hs hq⟩

/-- Baseline: commit to mutable current storage (or explicit snapshots) before
    memory optimization. Snapshot optimization is deliberately not invented. -/
def early (size array : Nat) (body : Body) (start stride : Int) (count : Nat) (supplier : CompactSequence.Seq) :
    Artifact size array body start stride count supplier :=
  match allocation : VersionedAllocation.lower body with
  | none =>
    let c := VersionedMemoryMachine.allocate (VersionedLoop.direct body start stride count)
    ⟨.lateMemory c,by
      intro s hs x y q hq
      exact (VersionedMemoryMachine.correct _).trans (VersionedLoop.direct_correct body s)⟩
  | some memory =>
    let window := HybridSymbolicLoop.select size array memory start stride count
    let routed := if hasReads window.code.count window.code.initial window.code.refill then
      HybridCompactTransport.select window.code supplier else .memory
    let code := match routed with
      | .memory => Code.earlyMemory window.code
      | .fifo f => Code.earlyFIFO f.code
    ⟨code,by
      intro s hs x y q hq
      have lowered : Source.iterate (fun i => memory.eval i x y) stride count start s =
          Source.iterate (fun i => VersionedWindow.run body i x y) stride count start s :=
        Source.iterate_congr _ _ (fun i t => VersionedAllocation.lower_correct body memory allocation i x y t [] []) stride count start s
      have hw := (window.correct (x:=x) (y:=y) s hs).trans lowered
      cases hr : routed with
      | memory => simpa only [code,hr,Code.eval] using hw
      | fifo f => simpa only [code,hr,Code.eval] using (f.correct s q hq).trans hw⟩

theorem orders_agree (a b : Artifact size array body start stride count supplier) (s : State)
    (sized : (s.arrays array).size = size)
    (hq : CommunicationIR.Corresponds (arrayInput (s.arrays array)) supplier.entries q) :
    a.code.eval (arrayInput (s.arrays array)) x y s q = b.code.eval (arrayInput (s.arrays array)) x y s q :=
  (a.correct s sized x y q hq).trans (b.correct s sized x y q hq).symm
end IRComparison.VersionedOrder
