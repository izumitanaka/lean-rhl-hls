import IRComparison.Examples.PipeliningExamples
import IRComparison.Circuit.Pipelining.Compiler

open IRComparison IRComparison.Circuit IRComparison.Circuit.Pipelining
open IRComparison.PipeliningExamples

def check (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {label}")
  IO.println s!"PASS\t{label}"

def filterRTL (n ii : Nat) (start : Int := 0) (stride : Int := 1) :=
  match filterPipeline n ii start stride with
  | (.original _,_) => none
  | (.scheduled code plan,b) =>
    let r := realize code plan.cycles b.wires
    let a := declarationArtifact r.batches r.widths #[(0,n+1),(1,n)] #[(0,n+1),(1,n)] #[]
    some (r,a,code,plan,b)

def main : IO Unit := do
  IO.FS.createDirAll "artifacts/pipelining/rtl"
  for (name,n,ii,start,stride) in [
      ("filter",4,1,0,1),("filter-II2",4,2,0,1),("filter-reverse",4,1,3,-1),
      ("filter-empty",0,1,0,1),("filter-long",16,1,0,1),("filter-oob",4,1,4,1)] do
    let some (r,a,code,plan,b) := filterRTL n ii start stride | throw (IO.userError "unexpected fallback")
    check (name ++ "/widths") (batchWidthsSafe r.widths.toList r.batches)
    check (name ++ "/allocation") r.allocation.accepted
    if n > 1 then check (name ++ "/reuse") (r.widths.size < b.wires.size)
    let s := initial ((List.range (n+1)).toArray.map (fun k => BitVec.ofNat 32 ((k+1)*10))) n
    let p := wordPayload s 0 0
    let before := runCycles (fun _ => 0) code plan.cycles p
    let reused := runBatches (fun _ => 0) r.batches p
    check (name ++ "/allocation-result") (reused.map (·.data.arrays 1) == before.map (·.data.arrays 1))
    let rtl := batchProgram r.batches #[]
    let result := (rtl.run (Frame.get r.widths.toList) (r.batches.length+1) (p.at 0)).result
    check (name ++ "/rtl-result") (result.map (Option.map (·.arrays 1)) == some (before.map (·.data.arrays 1)))
    let text ← match emitBatches a r.batches [1] with
      | .ok text => pure text
      | .error why => throw (IO.userError s!"{name}: {why}")
    IO.FS.writeFile s!"artifacts/pipelining/rtl/{name}.sv" text
    check (name ++ "/parse") (SystemVerilog.Concrete.parseModule text).isSome
    let built ← match compileWordCircuit (filterKernel n start stride) #[(0,n+1),(1,n)] ii [1] with
      | .ok built => pure built
      | .error why => throw (IO.userError s!"compiler: {why}")
    check (name ++ "/compiler-entry") (built.module.text == text)
    IO.println s!"RTL\t{name}\tvirtual={b.wires.size}\tphysical={r.widths.size}\tactions={code.size}\tclocks={r.batches.length+1}"
  let bs : Batches := [[.wire 2 (.lit 3),.wire 3 (.lit 4)],[.assign 0 (.wire 2),.assign 1 (.wire 3)]]
  let bad := chooseAllocation bs #[0,1,2,2]
  check "live-alias/rejected" (!bad.accepted)
  let lastRead : Batches := [[.wire 2 (.lit 3)],[.wire 3 (.bin .add (.wire 2) (.lit 1))],[.assign 0 (.wire 3)]]
  let good := chooseAllocation lastRead #[0,1,2,2]
  check "same-edge-last-read/accepted" good.accepted
  check "same-edge-last-read/result"
    ((runBatches (fun _ => 0) (renamed good.mapping lastRead) emptyPayload).map (·.data.regs 0) == some 4)
  let inputs : Batches := [[.assign 0 (.wire 0)]]
  check "input-register-remap/rejected" (!(chooseAllocation inputs #[1,0]).accepted)
  let narrowCode : Array Action := #[.wire 2 (.lit 3),.wire 3 (.bin .add (.wire 2) (.lit 1)),.assign 0 (.wire 3)]
  let narrow := realize narrowCode [[0],[1],[2]] #[wordRange,wordRange,⟨0,3⟩,⟨0,4⟩]
  check "width-widening/allocation-fallback" (!narrow.allocation.accepted)
  check "width-widening/original-widths-valid" (batchWidthsSafe narrow.widths.toList narrow.batches)
  let badBanks : Batches := [[.store 0 (.lit 0) (.lit 3),.store 0 (.lit 1) (.lit 4)]]
  let bankLayout := declarationArtifact badBanks #[wordRange,wordRange] #[(0,2)] #[(0,2)] #[]
  check "multiple-writes-same-bank/emission-rejected" (match emitBatches bankLayout badBanks [0] with | .error _ => true | _ => false)
  let gatherKernel := gatherCode.kernel 4 0 0 1 4 (fun _ => [])
  let gatherBuilt ← match compileWordCircuit gatherKernel #[(0,4),(1,4),(2,4)] 1 [2] with
    | .ok built => pure built
    | .error why => throw (IO.userError s!"gather: {why}")
  IO.FS.writeFile "artifacts/pipelining/rtl/gather.sv" gatherBuilt.module.text
  check "gather/compiler-entry" gatherBuilt.scheduleAccepted
  check "gather/reuse" (gatherBuilt.realization.widths.size < gatherBuilt.virtualWires)
