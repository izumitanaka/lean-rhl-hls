import IRComparison.Circuit.SharedRTL

/-! Shared combinational net emission. Uses existing concrete SystemVerilog
operator templates. SharedEmitConnection proves expression-level correspondence;
SharedCompiler integrates this emitter into the normal structured HLS path
and proves source-wide, multiple-clock preservation.
Local references are resolved to nets, never to clocked holding registers. -/
namespace IRComparison.Circuit.Shared.NetEmission

abbrev Wires := Array SystemVerilog.Wire
abbrev Builder := StateT Wires (Except String)

def fresh (rhs : SystemVerilog.Expr) (width : Nat) : Builder Signal := fun st =>
  if positive : 0 < width then
    let name := SystemVerilog.Name.temporary st.size
    .ok (⟨name,.bit true,width,positive⟩,st.push ⟨name,width,rhs,positive⟩)
  else .error "zero-width shared combinational net"

def term (a : Artifact) (locals : Option (Array Signal)) (e : RTL.Term) : Builder Signal := do
  if let some refs := locals then
    if let .wire n := e then
      if let some ref := refs[n]? then return ref
      else throw s!"shared combinational reference {n} is not defined"
  let children ← e.children.attach.mapM fun child => term a locals child.val
  let (rhs,width) ← termTemplate a e children
  fresh rhs width
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ child.property

def validity (a : Artifact) (locals : Option (Array Signal)) : RTL.Validity → Builder SystemVerilog.Expr
  | .yes => pure (.bit true)
  | .no => pure (.bit false)
  | .and x y => return .binary .and (← validity a locals x) (← validity a locals y)
  | .address n j => do
    let _ ← memorySize a n
    let js ← term a locals j
    let value := SystemVerilog.Expr.reference js.name
    pure (.binary .and (.binary .ge value (.integer 0))
      (.binary .lt value (.unsigned (.reference (.length n)))))
  | .mux c yesGuard noGuard => do
    let cs ← term a locals c
    return .select (.binary .ne (.reference cs.name) (.integer 0))
      (← validity a locals yesGuard) (← validity a locals noGuard)

structure Pair where
  value : Signal
  valid : Signal

def expression (a : Artifact) (locals : Option (Array Signal)) (e : RTL.Combinational) : Builder Pair := do
  let value ← term a locals e.value
  let guard ← validity a locals e.valid
  -- A signed two-bit net represents Boolean 0/1 exactly.
  let valid ← fresh (.select guard (.integer 1) (.integer 0)) 2
  pure ⟨value,valid⟩

def code (a : Artifact) (refs : Array Signal) : LocalRTL.Code → Builder Pair
  | .source e => expression a none e
  | .localNode e => expression a (some refs) e

/-- Two references per source node; each validity formula is materialized once. -/
def graph (a : Artifact) : List LocalRTL.Code → Builder (Array Signal)
  | [] => pure #[]
  | n::ns => do
    let refs ← graph a ns
    let p ← code a refs n
    pure ((refs.push p.value).push p.valid)

structure Output where
  declarations : Wires
  result : Pair

/-- Emit a whole shared expression into an existing declaration sequence. Local
references are fresh for this graph; physical references retain their scope. -/
def append (a : Artifact) (p : LocalRTL.Program) : Builder Pair := fun before => do
  let (refs,declarations) ← graph a p.code before
  let some value := refs[2*p.result]? | throw "missing shared result value"
  let some valid := refs[2*p.result+1]? | throw "missing shared result validity"
  pure (⟨value,valid⟩,declarations)

def generate (a : Artifact) (p : LocalRTL.Program) : Except String Output :=
  (append a p #[]).map (fun result => ⟨result.2,result.1⟩)

def Output.text (o : Output) : String :=
  SystemVerilog.Concrete.print (o.declarations.toList.flatMap SystemVerilog.Concrete.wire)

end IRComparison.Circuit.Shared.NetEmission
