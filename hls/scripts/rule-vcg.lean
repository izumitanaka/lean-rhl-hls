import IRComparison.Frontend.CertifiedHLS
import IRComparison.Examples.WordWorkloads

open IRComparison HybridSymbolicGlobal
open Circuit Circuit.Pipelining
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

def initial : HybridWord.State :=
  ⟨fun _ => 0,fun _ => Array.replicate 8 0⟩
def noSupplier (_ : Unit) : List Int := panic! "supplier enumeration"

def stageOf (k : HybridWord.Kernel) : CertifiedHLS.Stage :=
  ⟨k.native,k.size,k.array,k.start,k.stride,k.count,k.supplier⟩

def entryOf : (ks : List HybridWord.Kernel) → CertifiedHLS.Entry (ks.map stageOf)
  | [] => .nil
  | k::ks => .cons ⟨k.body,k.correct⟩ (entryOf ks)

def sourceLayout : Array (Nat × Nat) := (List.range 7).toArray.map (fun a => (a,8))

def checkRTL (name : String) (ks : List HybridWord.Kernel) (outputs policy : List Nat) : IO Unit := do
  let built ← IO.ofExcept (← CertifiedHLS.compileWithSMT (entryOf ks) outputs (fun _ => 8)
    sourceLayout (System.FilePath.mk "artifacts/rule-vcg" / name))
  unless built.backend.route == "structured" do
    throw (IO.userError s!"{name}: named-body route fell back: {built.backend.fallbackReason}")
  let .symbolic chosen := built.plan | throw (IO.userError s!"{name}: not symbolic")
  unless chosen.policy == policy do throw (IO.userError s!"{name}: unexpected integrated policy {chosen.policy}")
  let source := CertifiedHLS.runSource (ks.map stageOf) 0 0 initial
  let r : RTL.InterfaceState built.backend.artifact.storageShape :=
    ⟨FiniteRuntime.pack built.backend.artifact.storageShape (built.backend.initial initial 0 0),true⟩
  let some actual := SystemVerilog.runText built.text built.backend.artifact.storageShape 2048 r
    | throw (IO.userError s!"{name}: parsed RTL did not run")
  unless actual.core.done && !actual.busy do throw (IO.userError s!"{name}: did not finish")
  match source with
  | none => unless actual.core.error do throw (IO.userError s!"{name}: missing source error")
  | some expected =>
    unless !actual.core.error do throw (IO.userError s!"{name}: spurious RTL error")
    for a in outputs do
      unless actual.core.decode.data.arrays a == expected.encode.arrays a do
        throw (IO.userError s!"{name}: RTL public output {a}")
  let out := System.FilePath.mk "artifacts/rule-vcg" / name
  IO.FS.createDirAll out
  IO.FS.writeFile (out / "output.sv") built.text
  let observed := outputs.map fun a => Lean.Json.mkObj
    [("array",Lean.toJson a),("values",Lean.toJson ((source.map (fun s => (s.encode.arrays a).toList)).getD []))]
  IO.FS.writeFile (out / "expected.json") (Lean.Json.mkObj
    [("outputs",Lean.toJson observed),("error",Lean.toJson source.isNone),("policy",Lean.toJson policy)]).pretty
  IO.println s!"PASS {name}: SMT → named counted body → parsed RTL ({built.backend.route})"

def check (name : String) (ks : List HybridWord.Kernel) (outputs expectedPolicy : List Nat) : IO Unit := do
  let ps := HybridUnifiedPipeline.compactStages (ks.map HybridWord.Kernel.lower)
  let some p ← compileWithSMT outputs (fun _ => 8) ps (System.FilePath.mk "artifacts/rule-vcg" / name)
    | throw (IO.userError s!"{name}: no plan")
  unless p.policy == expectedPolicy do throw (IO.userError s!"{name}: policy {p.policy}, expected {expectedPolicy}")
  let observe := fun s : State => outputs.map s.arrays
  let expected := (HybridWord.source 0 0 ks initial).map (fun s => observe s.encode)
  let actual := p.eval 0 0 initial.encode
  unless actual.map observe == expected && actual.isSome do throw (IO.userError s!"{name}: source mismatch")
  for a in expectedPolicy do
    unless actual.map (fun s => (s.arrays a).isEmpty) == some true do throw (IO.userError s!"{name}: memory not eliminated")
  IO.println s!"PASS {name}: policy={p.policy}, loops={p.plan.code.length}, native output agrees"
  checkRTL name ks outputs expectedPolicy

def window (i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 1)[i.toNat]?
  let b ← (s.arrays 1)[(i+1).toNat]?
  let c ← (s.arrays 1)[(i+2).toNat]?
  s.write 2 i ((a+b+c)/3)
hls_word window as windowCode

def dilated (i _x _y : HybridWord.Word) (s : HybridWord.State) : Option HybridWord.State := do
  let a ← (s.arrays 1)[i.toNat]?
  let b ← (s.arrays 1)[(i+2).toNat]?
  let c ← (s.arrays 1)[(i+4).toNat]?
  s.write 2 i ((a+b+c)/3)
hls_word dilated as dilatedCode

def main : IO Unit := do
  let a := WordWorkloads.Global.producerA.kernel 8 0 0 1 8 noSupplier
  let b := WordWorkloads.Global.producerB.kernel 8 0 0 1 8 noSupplier
  let c := WordWorkloads.Global.consumerA.kernel 8 1 0 1 8 noSupplier
  let d := WordWorkloads.Global.consumerB.kernel 8 5 0 1 8 noSupplier
  let side := WordWorkloads.Global.independent.kernel 8 0 0 1 1 noSupplier
  let readSide := WordWorkloads.Global.observing.kernel 8 0 0 1 1 noSupplier
  check "chain" [a,c] [2] [1]
  check "nonadjacent" [a,side,c] [2,3] [1]
  check "interleaved" [a,b,c,d] [2,6] [1,5]
  check "intervening-read" [a,readSide,c] [2,3] []
  check "public-array" [a,c] [1,2] []
  let ra := WordWorkloads.Global.producerA.kernel 8 0 7 (-1) 8 noSupplier
  let rc := WordWorkloads.Global.consumerA.kernel 8 1 7 (-1) 8 noSupplier
  check "reverse" [ra,side,rc] [2,3] [1]
  check "reverse-mismatch" [a,side,rc] [2,3] []
  check "window" [a,windowCode.kernel 8 1 0 1 6 noSupplier] [2] [1]
  check "reverse-window" [ra,windowCode.kernel 8 1 5 (-1) 6 noSupplier] [2] [1]
  check "dilated-window" [a,dilatedCode.kernel 8 1 0 1 4 noSupplier] [2] [1]
  check "stride-two" [a,WordWorkloads.Global.consumerA.kernel 8 1 0 2 4 noSupplier] [2] [1]
  check "empty" [WordWorkloads.Global.producerA.kernel 8 0 0 1 0 noSupplier,
    WordWorkloads.Global.consumerA.kernel 8 1 0 1 0 noSupplier] [2] []
  check "singleton" [WordWorkloads.Global.producerA.kernel 8 0 0 1 1 noSupplier,
    WordWorkloads.Global.consumerA.kernel 8 1 0 1 1 noSupplier] [2] [1]
  let memory := (HybridUnifiedPipeline.compactStage
    (WordWorkloads.Global.consumerA.kernel 8 1 0 2 4 noSupplier).lower).code
  let sequence : CompactSequence.Seq := ⟨0,1,8⟩
  let transcriptRoot ← HybridRoutingVC.freshDirectory "artifacts/rule-vcg/boundary"
  let some _ ← HybridRoutingVC.solve memory sequence transcriptRoot
    | throw (IO.userError "fresh routing model not found")
  let #[entry] ← transcriptRoot.readDir | throw (IO.userError "expected one isolated solver transcript")
  let req ← IO.FS.readFile (entry.path / "request.smt2")
  let resp ← IO.FS.readFile (entry.path / "response.txt")
  unless (HybridRoutingVC.accept memory sequence req resp).isSome do
    throw (IO.userError "valid model rejected")
  for bad in ["unknown", "unsat", "sat", "sat\n((p0 0) (p1 0) (p2 0) (p3 0))"] do
    unless (HybridRoutingVC.accept memory sequence req bad).isNone do
      throw (IO.userError "invalid SMT reply accepted")
  unless (HybridRoutingVC.accept memory sequence "(check-sat)" resp).isNone do
    throw (IO.userError "unrelated request accepted")
  IO.println "PASS SMT boundary: unknown/unsat/malformed/wrong coefficients/unrelated request rejected"
  let n := 1000000000
  let big := [WordWorkloads.Global.producerA.kernel n 0 0 1 n noSupplier,
    WordWorkloads.Global.independent.kernel n 0 0 1 1 noSupplier,
    WordWorkloads.Global.consumerA.kernel n 1 0 1 n noSupplier]
  let ps := HybridUnifiedPipeline.compactStages (big.map HybridWord.Kernel.lower)
  let some p ← compileWithSMT [2,3] (fun _ => n) ps "artifacts/rule-vcg/billion"
    | throw (IO.userError "billion compilation failed")
  unless p.policy == [1] && p.plan.code.length == 3 do throw (IO.userError "billion geometry")
  let g := scheduleWith CountedBackend.named.build #[(0,n),(1,n),(2,n),(3,n)] (.symbolic p.plan.code)
  let small := [WordWorkloads.Global.producerA.kernel 8 0 0 1 8 noSupplier,
    WordWorkloads.Global.independent.kernel 8 0 0 1 1 noSupplier,
    WordWorkloads.Global.consumerA.kernel 8 1 0 1 8 noSupplier]
  let some q ← HybridUnifiedPipeline.compileWithSMT [2,3] (fun _ => 8)
    (small.map HybridWord.Kernel.lower) "artifacts/rule-vcg/small-shape"
    | throw (IO.userError "small geometry")
  let smallG := scheduleWith CountedBackend.named.build #[(0,8),(1,8),(2,8),(3,8)] (HybridUnifiedPipeline.lower q)
  unless (structuredTree g.schedule).size == (structuredTree smallG.schedule).size &&
      g.build.wires.size == smallG.build.wires.size do throw (IO.userError "count-dependent control expansion")
  IO.println s!"PASS billion: same counted circuit shape as count 8, {(structuredTree g.schedule).size} control nodes; not executed"
