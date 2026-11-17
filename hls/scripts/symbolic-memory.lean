import IRComparison.Examples.CertifiedHLSExamples
import IRComparison.Examples.WordWorkloads

open IRComparison Circuit Circuit.Pipelining CertifiedHLS CertifiedHLSExamples
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def assertPass (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError name)
  IO.println s!"PASS {name}"

def loops : Circuit.Schedule → Nat
  | .skip | .step _ => 0
  | .seq a b | .branch _ a b => loops a + loops b
  | .loop _ a => 1 + loops a

def forbiddenSupplier (_ : Unit) : List Int := panic! "iteration supplier was forced"

def kind {outputs : List Nat} {sizes : Nat → Nat} {ks : List HybridIR.Kernel} (p : HybridUnifiedPipeline.Plan outputs sizes ks) : String :=
  match p with
  | .symbolic _ => "symbolic"
  | .regions => "regions"
  | .compact _ => "compact"
  | .expanded _ => "expanded"

def sample (size : Nat) : HybridWord.State :=
  ⟨fun _ => 0,fun a => if a = 0 then (List.range size).toArray.map
    (fun i => BitVec.ofNat 32 (4294967290+i)) else Array.replicate size 0⟩

def check (name : String) (ks : List HybridWord.Kernel) (outputs : List Nat)
    (size : Nat := 64) (x y : HybridWord.Word := 0) : IO Unit := do
  let some p := HybridWord.compileProgram outputs (fun _ => size) ks
    | throw (IO.userError s!"{name}: no plan")
  assertPass (name++"/not-expanded") (kind p != "expanded")
  let s := sample size
  let observe := fun s : State => (outputs.map s.arrays,[s.regs 0,s.regs 2])
  let native := (HybridWord.source x y ks s).map (fun s => observe s.encode)
  assertPass (name++"/native") ((p.eval (HybridWord.encode x) (HybridWord.encode y) s.encode).map observe == native)
  let generated := schedule #[(0,size),(1,size),(2,size),(3,size),(4,size),(5,size),(6,size)] (HybridUnifiedPipeline.lower p)
  let tree := structuredTree generated.schedule
  let actual := (tree.assemble generated.build.queues).run 30000 ((wordPayload s x y).at 1)
  assertPass (name++"/scheduled-machine") (actual.result.map (Option.map observe) == some native)
  IO.println s!"SHAPE {name}: {kind p}, loops={loops generated.schedule}, nodes={tree.size+1}"

def geometry (n : Nat) : IO (Nat × Nat × Nat) := do
  let size := n+2
  let ks := [(WordWorkloads.Window.filterCode.kernel size 0 0 1 n forbiddenSupplier).lower]
  let some p := HybridUnifiedPipeline.compile [1] (fun _ => size) ks
    | throw (IO.userError "geometry compile")
  let code := HybridUnifiedPipeline.lower p
  let .symbolic cs := code | throw (IO.userError "expected symbolic")
  let some (.memory _ r) := cs.head? | throw (IO.userError "missing memory loop")
  assertPass s!"count-{n}/three-point-window" (r.count == n && r.initial.length == 3 && r.refill.length == 3)
  let g := schedule #[(0,size),(1,size)] code
  let shape := (loops g.schedule,(structuredTree g.schedule).size+1,g.build.wires.size)
  IO.println s!"GEOMETRY count={n} loops={shape.1} nodes={shape.2.1} wires={shape.2.2}"
  return shape

def main : IO Unit := do
  for n in [0,1,2,8,32] do
    let k := WordWorkloads.Window.filterCode.kernel 64 0 0 1 n forbiddenSupplier
    check s!"filter-{n}" [k] [1]
  check "reverse" [WordWorkloads.Window.filterDilatedRevCode.kernel 64 0 12 (-1) 8 forbiddenSupplier] [1]
  check "stride-two" [WordWorkloads.Window.filterCode.kernel 64 0 0 2 8 forbiddenSupplier] [1]
  check "reverse-address" [WordWorkloads.Window.filterAltCode.kernel 64 0 0 1 8 forbiddenSupplier] [1]
  check "dilated" [WordWorkloads.Window.filterDilatedCode.kernel 64 0 0 1 8 forbiddenSupplier] [1]
  check "out-of-bounds" [WordWorkloads.Window.filterCode.kernel 64 0 63 1 1 forbiddenSupplier] [1]
  check "wrapped-counter" [WordWorkloads.Window.filterCode.kernel 64 0 4294967296 1 2 forbiddenSupplier] [1]
  let a := WordWorkloads.Global.producerA.kernel 64 0 0 1 8 forbiddenSupplier
  let b := WordWorkloads.Global.producerB.kernel 64 0 0 1 8 forbiddenSupplier
  let c := WordWorkloads.Global.consumerA.kernel 64 1 0 1 8 forbiddenSupplier
  let d := WordWorkloads.Global.consumerB.kernel 64 5 0 1 8 forbiddenSupplier
  check "interleaved-memory-regions" [a,b,c,d] [1,2,5,6]
  check "public-intermediate-memory" [a,c] [1,2]
  check "counted-fifo-chain" [a,c] [2]
  check "empty-program" [] [0,1]
  let small ← geometry 8
  let medium ← geometry 32
  let billion ← geometry 1000000000
  assertPass "same-control-shape-8-32-billion" (small == medium && medium == billion)
