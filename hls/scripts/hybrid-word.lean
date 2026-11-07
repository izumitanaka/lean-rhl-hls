import IRComparison.Examples.WordFrontendExamples
import IRComparison.Examples.WordWorkloads
open IRComparison
open HybridWord
set_option maxRecDepth 512
set_option maxHeartbeats 8000000

def kernels : List HybridWord.Kernel :=
  [WordFrontendExamples.producer.kernel 4 0 0 1 4 (fun _ => [0,1,2,3]),
   WordFrontendExamples.consumer.kernel 4 1 0 1 3 (fun _ => [0,1,2,3])]
def initial : HybridWord.State :=
  ⟨fun _ => 0,fun a => if a = 0 then #[4294967295,1,2,3] else #[0,0,0,0]⟩

def isCompact (p : HybridUnifiedPipeline.Plan outputs sizes ks) : Bool :=
  match p with
  | .compact _ => true
  | .expanded _ => false

def check (ks : List HybridWord.Kernel) (initial : HybridWord.State) : IO Unit := do
  IO.println "starting BV32 compiler"
  let directory : System.FilePath := "artifacts/hybrid-word/smt"
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "request.smt2") ""
  IO.FS.writeFile (directory / "response.txt") ""
  let some plan ← compileProgramWithSMT [2] (fun _ => 4) ks directory
    | throw (IO.userError "BV32 whole-program compilation failed")
  unless isCompact plan do
    throw (IO.userError "expected compact path: BV32 address guards were not recognized")
  let request ← IO.FS.readFile (directory / "request.smt2")
  let response ← IO.FS.readFile (directory / "response.txt")
  unless (CompactSequence.accept ⟨0,1,4⟩ request response).isSome do
    throw (IO.userError "solver transcript was not produced and accepted in this run")
  for rejected in ["unsat", "unknown", "sat\n((p0 4) (p1 0) (p2 2))"] do
    unless (CompactSequence.accept ⟨0,1,4⟩ request rejected).isNone do
      throw (IO.userError "invalid SMT result accepted")
  IO.println "compact pipeline selected; fresh Z3 response checked"
  let expected := (HybridWord.source 0 0 ks initial).map (fun s => (s.arrays 2).map HybridWord.encode)
  let actual := (plan.eval 0 0 initial.encode).map (fun s => s.arrays 2)
  unless actual == expected && actual == some #[2,5,7,0] do
    throw (IO.userError s!"BV32 output mismatch: {actual} / {expected}")
  unless (plan.eval 0 0 initial.encode).map (fun s => (s.arrays 1).isEmpty) == some true do
    throw (IO.userError "intermediate array was not eliminated")
  match HybridUnifiedPipeline.run 0 0 10000 (HybridUnifiedPipeline.start (HybridUnifiedPipeline.lower plan) initial.encode) with
  | .stopped result =>
    unless result.map (fun s => s.arrays 2) == expected do
      throw (IO.userError "BV32 control mismatch")
  | _ => throw (IO.userError "BV32 control did not finish")
  IO.println "BV32 overflow, whole-array elimination, SMT entry, and control execution agree"

def checkGlobal (name : String) (outputs : List Nat) (ks : List HybridWord.Kernel)
    (hidden : List Nat) : IO Unit := do
  let some plan := compileProgram outputs (fun _ => 4) ks
    | throw (IO.userError s!"{name}: compile failed")
  let obs := fun s : IRComparison.State => (outputs.map s.arrays,[s.regs 0,s.regs 2])
  let expected := (HybridWord.source 0 0 ks initial).map (fun t => obs t.encode)
  let actual := plan.eval 0 0 initial.encode
  unless actual.isSome && actual.map obs == expected do
    throw (IO.userError s!"{name}: source mismatch")
  for a in [1,5] do
    unless actual.map (fun s => (s.arrays a).isEmpty) == some (decide (a ∈ hidden)) do
      throw (IO.userError s!"{name}: wrong whole-array decision for {a}")
  match HybridUnifiedPipeline.run 0 0 10000 (HybridUnifiedPipeline.start (HybridUnifiedPipeline.lower plan) initial.encode) with
  | .stopped r => unless r.map obs == expected do
      throw (IO.userError s!"{name}: control mismatch")
  | _ => throw (IO.userError s!"{name}: unfinished")
  IO.println s!"{name}: source, whole-array policy, and control agree"

def checkWindow (name : String) (k : HybridWord.Kernel) (fifo buffered : Bool) : IO Unit := do
  let s : HybridWord.State := ⟨fun _ => 0,fun a => if a = 0 then
    ((List.range 64).map (fun j => BitVec.ofNat 32 (4294967290+j))).toArray else Array.replicate 64 0⟩
  let plan := HybridWord.compile 64 k.array k.body k.stride k.count k.start (k.supplier ())
  unless plan.isFIFO == fifo && plan.hasBuffer == buffered do
    throw (IO.userError s!"{name}: unexpected FIFO/buffer decisions {plan.isFIFO}/{plan.hasBuffer}")
  let q := (CommunicationIR.emit (arrayInput (s.encode.arrays k.array)) (k.supplier ())).getD []
  let actual := plan.eval (s.encode.arrays k.array) 0 0 s.encode q
  let expected := (k.source 0 0 s).map (fun t => t.encode.arrays 1)
  unless actual.isSome && actual.map (fun t => t.arrays 1) == expected do
    throw (IO.userError s!"{name}: window result mismatch")
  let blocks := HybridIR.memoryBlocks plan.code
  match HybridBlocksControl.run (arrayInput (s.encode.arrays k.array)) 0 0 10000 (.start blocks [] s.encode q []) with
  | .stopped r => unless r.map (fun t => t.1.arrays 1) == expected do
      throw (IO.userError s!"{name}: window control mismatch")
  | _ => throw (IO.userError s!"{name}: window control unfinished")
  IO.println s!"{name}: native BV32 source, window/FIFO and control agree"

def checkCounter (name : String) (start stride : Int) (count : Nat) : IO Unit := do
  let k := WordFrontendExamples.producer.kernel 4 0 start stride count (fun _ => [0,1,2,3])
  let p := HybridWord.compile 4 0 k.body stride count start (k.supplier ())
  let q := [4294967295,1,2,3]
  let expected := (k.source 0 0 initial).map (fun t => t.encode.arrays 1)
  let actual := (p.eval (initial.encode.arrays 0) 0 0 initial.encode q).map (fun t => t.arrays 1)
  unless actual == expected do throw (IO.userError s!"{name}: counter wrap changed semantics")
  match HybridBlocksControl.run (arrayInput (initial.encode.arrays 0)) 0 0 10000
      (.start (HybridIR.memoryBlocks p.code) [] initial.encode q []) with
  | .stopped r => unless r.map (fun t => t.1.arrays 1) == expected do
      throw (IO.userError s!"{name}: counter control mismatch")
  | _ => throw (IO.userError s!"{name}: counter control unfinished")
  IO.println s!"{name}: wrapped counter and failure behavior agree"

def main : IO Unit := do
  check kernels initial
  let a := WordWorkloads.Global.producerA.kernel 4 0 0 1 3 (fun _ => [])
  let b := WordWorkloads.Global.producerB.kernel 4 0 0 1 3 (fun _ => [])
  let c := WordWorkloads.Global.consumerA.kernel 4 1 0 1 3 (fun _ => [0,1,2])
  let d := WordWorkloads.Global.consumerB.kernel 4 5 0 1 3 (fun _ => [0,1,2])
  let mark := WordWorkloads.Global.independent.kernel 4 0 0 1 1 (fun _ => [])
  let observe := WordWorkloads.Global.observing.kernel 4 0 0 1 1 (fun _ => [])
  checkGlobal "interleaved" [2,6] [a,b,c,d] [1,5]
  checkGlobal "nonadjacent" [2,3] [a,mark,c] [1]
  checkGlobal "intervening-read" [2,3] [a,observe,c] []
  checkGlobal "public-output" [1,2,3] [a,mark,c] []
  let ascending := fun _ => (List.range 64).map Int.ofNat
  let descending := fun _ => ((List.range 64).map Int.ofNat).reverse
  checkWindow "filter" (WordWorkloads.Window.filterCode.kernel 64 0 0 1 3 ascending) true true
  checkWindow "reverse-address" (WordWorkloads.Window.filterAltCode.kernel 64 0 0 1 3 descending) true true
  checkWindow "stride-two" (WordWorkloads.Window.filterSkipCode.kernel 64 0 0 1 3 ascending) true true
  checkWindow "dilated" (WordWorkloads.Window.filterDilatedCode.kernel 64 0 0 1 3 ascending) true true
  checkWindow "dilated-reverse" (WordWorkloads.Window.filterDilatedAltCode.kernel 64 0 0 1 3 descending) true true
  checkWindow "negative-step" (WordWorkloads.Window.filterDilatedRevCode.kernel 64 0 2 (-1) 3 descending) true true
  checkWindow "reverse-memory" (WordWorkloads.Window.filterDilatedRevCode.kernel 64 0 2 (-1) 3 ascending) false true

  checkCounter "zero-count" 4294967295 1 0
  checkCounter "wrapped-start" 4294967296 1 2
  checkCounter "negative-counter" 0 (-1) 2
