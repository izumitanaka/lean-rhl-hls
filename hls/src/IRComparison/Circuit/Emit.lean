import IRComparison.Circuit.SystemVerilog.ConcreteModule

namespace IRComparison.Circuit

structure Signal where
  name : SystemVerilog.Name
  valid : SystemVerilog.Expr
  width : Nat
  positive : 0 < width

structure Emission where
  text : Array SystemVerilog.Wire := #[]
  cache : Array (RTL.Term × Signal) := #[]

abbrev EmitM := StateT Emission (Except String)

def line (s : SystemVerilog.Wire) : EmitM Unit := modify fun e => { e with text := e.text.push s }
def require (condition : Bool) (message : String) : EmitM Unit :=
  if condition then pure () else throw message

def unsigned (s : String) := "$signed({1'b0," ++ s ++ "})"

def widen (s : Signal) (w : Nat) (positive : 0 < w) : SystemVerilog.Expr := .cast w (.reference s.name) positive
def number (n : Int) (w : Nat) := if n < 0 then s!"-{w}'sd{n.natAbs}" else s!"{w}'sd{n.toNat}"

def memorySize (a : Artifact) (id : Nat) : Except String Nat :=
  match a.memories.toList.find? (fun p => p.1 == id) with
  | some (_,size) => pure size
  | none => throw s!"missing array {id} in hardware layout"

def RTL.Term.children : RTL.Term → List RTL.Term
  | .cell _ j | .resize _ j | .nonnegative j => [j]
  | .binary _ u v => [u,v]
  | .mux c u v => [c,u,v]
  | _ => []

theorem RTL.Term.child_size (e child : RTL.Term) (member : child ∈ e.children) : sizeOf child < sizeOf e := by
  cases e <;> simp only [children,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals first
    | contradiction
    | (rcases member with rfl | rfl | rfl <;> simp +arith)
    | (rcases member with rfl | rfl <;> simp +arith)
    | (subst child; simp +arith)

/-- A single node's concrete expression template. Child traversal and sharing
are handled uniformly by `termText`; this function never allocates a signal. -/
def termTemplate (a : Artifact) (e : RTL.Term) (args : List Signal) : Except String (SystemVerilog.Expr × Nat) := do
  match e,args with
  | .literal n,[] =>
      let w := bits n.natAbs+2
      pure (.literal w n (by unfold w; omega),w)
  | .wire n,[] =>
      unless n < a.wires.size do throw s!"unknown holding register {n}"
      pure (.reference (.holding n),signedWidth (a.wires[n]?.getD wordRange))
  | .register n,[] => pure (.unsigned (.reference (.register n)),33)
  | .length n,[] =>
      let size ← memorySize a n
      pure (.unsigned (.reference (.length n)),bits size+1)
  | .cell n _,[js] =>
      let _ ← memorySize a n
      let value : SystemVerilog.Expr := .reference js.name
      let ix : SystemVerilog.Expr := .select (.binary .lt value (.integer 0)) (.integer 0) value
      let ok : SystemVerilog.Expr := .binary .lt ix (.unsigned (.reference (.length n)))
      pure (.select ok (.unsigned (.index (.memory n) ix)) (.integer 0),33)
  | .resize w _,[vs] =>
      if positive : 0 < w then pure (widen vs w positive,w)
      else throw "zero-width RTL expression"
  | .nonnegative _,[vs] =>
      let value : SystemVerilog.Expr := .reference vs.name
      pure (.select (.binary .lt value (.integer 0)) (.integer 0) value,vs.width)
  | .mux ..,[cs,ys,ns] =>
      let w := max ys.width ns.width
      pure (.select (.binary .ne (.reference cs.name) (.integer 0))
        (widen ys w (by have := ys.positive; omega)) (widen ns w (by have := ns.positive; omega)),w)
  | .binary op ..,[us,vs] =>
      let w := us.width+vs.width+2
      let x := widen us w (by omega)
      let y := widen vs w (by omega)
      let rhs := match op with
        | .add => SystemVerilog.Expr.binary .add x y
        | .sub => .binary .sub x y
        | .mul => .binary .mul x y
        | .lt => .select (.binary .lt x y) (.integer 1) (.integer 0)
        | .div => SystemVerilog.division x y
      pure (rhs,w)
  | _,_ => throw "internal expression child count mismatch"

/-- Allocate a shared signal after every child has been generated. -/
def recordTerm (e : RTL.Term) (rhs : SystemVerilog.Expr) (width : Nat) : EmitM Signal := fun st =>
  if positive : 0 < width then
    let signal : Signal := ⟨.temporary st.cache.size,.bit true,width,positive⟩
    .ok (signal,{
      text := st.text.push ⟨signal.name,width,rhs,positive⟩
      cache := st.cache.push (e,signal)})
  else .error "zero-width generated signal"

/-- Memoized postorder traversal. Every syntax case uses the same allocation
and sharing path; all source terms are still accepted under the same checks. -/
def termText (a : Artifact) (e : RTL.Term) : EmitM Signal := do
  if let some (_,v) := (← get).cache.toList.find? (fun p => p.1 == e) then return v
  let args ← e.children.attach.mapM fun child => termText a child.val
  let (rhs,width) ← termTemplate a e args
  recordTerm e rhs width
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ child.property

def validityText (a : Artifact) : RTL.Validity → EmitM SystemVerilog.Expr
  | .yes => pure (.bit true)
  | .no => pure (.bit false)
  | .and x y => return .binary .and (← validityText a x) (← validityText a y)
  | .address n j => do
      let _ ← memorySize a n
      let js ← termText a j
      let value : SystemVerilog.Expr := .reference js.name
      pure (.binary .and (.binary .ge value (.integer 0))
        (.binary .lt value (.unsigned (.reference (.length n)))))
  | .mux c yes no => do
      let cs ← termText a c
      return .select (.binary .ne (.reference cs.name) (.integer 0)) (← validityText a yes) (← validityText a no)

def expression (a : Artifact) (e : RTL.Combinational) : EmitM Signal := do
  let value ← termText a e.value
  return {value with valid := ← validityText a e.valid}

def next (n : Nat) := s!"pc <= {n};"
def fault := "done <= 1'b1; error <= 1'b1; busy <= 1'b0;"
def guarded (guard action : String) := s!"if ({guard}) begin {action} end else begin {fault} end"

def wordValue (_a : Artifact) (e : RTL.Combinational) : EmitM Unit := do
  let r := e.bounds
  require (0 ≤ r.lo && r.hi ≤ 4294967295)
    s!"32-bit destination cannot represent inferred range [{r.lo},{r.hi}]; refusing truncation"

def scalarCode (a : Artifact) : RTL.Scalar RTL.Combinational → EmitM SystemVerilog.Expr
  | .literal n => pure (.literal (bits n.natAbs+2) n (by omega))
  | .value e => return .reference (← expression a e).name
  | .queueHead q => do
      require ((a.machine.capacities.toList.find? (fun p => p.1 == q)).isSome) s!"unknown queue {q}"
      pure (.unsigned (.index (.queue q) (.integer 0)))

def testCode (a : Artifact) : RTL.Test RTL.Combinational → EmitM SystemVerilog.Expr
  | .valid e => return (← expression a e).valid
  | .nonzero e => return .binary .ne (.reference (← expression a e).name) (.integer 0)
  | .address id e => do
      let _ ← memorySize a id
      let j ← expression a e
      let value : SystemVerilog.Expr := .reference j.name
      pure (.binary .and j.valid (.binary .and (.binary .ge value (.integer 0))
        (.binary .lt value (.unsigned (.reference (.length id))))))
  | .room q => do
      require ((a.machine.capacities.toList.find? (fun p => p.1 == q)).isSome) s!"unknown queue {q}"
      pure (.binary .lt (.reference (.used q)) (.integer (a.machine.capacity q)))
  | .nonempty q => do
      require ((a.machine.capacities.toList.find? (fun p => p.1 == q)).isSome) s!"unknown queue {q}"
      pure (.binary .lt (.integer 0) (.reference (.used q)))
  | .and u v => return .binary .and (← testCode a u) (← testCode a v)

/-- Expand bank operations into ordinary SystemVerilog assignments and fixed
loops. No source-RTL operation is embedded as an opaque output string. -/
def statementCode (a : Artifact) : RTL.Statement RTL.Combinational → EmitM SystemVerilog.Statement
  | .skip => pure .skip
  | .seq u v => return .seq (← statementCode a u) (← statementCode a v)
  | .branch g u v => return .branch (← testCode a g) (← statementCode a u) (← statementCode a v)
  | .assign target rhs => do
      let v ← scalarCode a rhs
      match target with
      | .pc => pure (.assign (.reference .pc) v)
      | .done => pure (.seq (.assign (.reference .done) (.binary .ne v (.integer 0)))
          (.assign (.reference .busy) (.binary .eq v (.integer 0))))
      | .error => pure (.assign (.reference .error) (.binary .ne v (.integer 0)))
      | .wire k =>
          require (k < a.wires.size) s!"unknown destination register {k}"
          pure (.assign (.reference (.holding k)) v)
      | .data k =>
          if let .value e := rhs then wordValue a e
          pure (.assign (.reference (.register k)) v)
  | .memory id rhs => do
      let size ← memorySize a id
      match rhs with
      | .empty => pure (.assign (.reference (.length id)) (.integer 0))
      | .copy src =>
          let ss ← memorySize a src
          require (size = ss) s!"snapshot size mismatch: {src} -> {id}"
          pure (.seq (.forRange .loopIndex size
            (.assign (.index (.memory id) (.reference .loopIndex)) (.index (.memory src) (.reference .loopIndex))))
            (.assign (.reference (.length id)) (.reference (.length src))))
      | .set src index value =>
          require (src = id) "array update must target its source bank"
          wordValue a value
          let j ← expression a index
          let v ← expression a value
          pure (.assign (.index (.memory id) (.reference j.name)) (.reference v.name))
  | .queue q rhs => do
      require ((a.machine.capacities.toList.find? (fun p => p.1 == q)).isSome) s!"unknown queue {q}"
      match rhs with
      | .empty => pure (.assign (.reference (.used q)) (.integer 0))
      | .append src e =>
          require (src = q) "FIFO append must target its source bank"
          wordValue a e
          let v ← expression a e
          pure (.seq (.assign (.index (.queue q) (.reference (.used q))) (.reference v.name))
            (.assign (.reference (.used q)) (.binary .add (.reference (.used q)) (.bit true))))
      | .tail src =>
          require (src = q) "FIFO shift must target its source bank"
          let cap := a.machine.capacity q
          pure (.seq (.forRange (.shiftIndex q) (cap-1)
            (.assign (.index (.queue q) (.reference (.shiftIndex q)))
              (.index (.queue q) (.binary .add (.reference (.shiftIndex q)) (.integer 1)))))
            (.assign (.reference (.used q)) (.binary .sub (.reference (.used q)) (.bit true))))

/-- The very same netlist and statement code consumed by the text renderer. -/
def generateCode (a : Artifact) : Except String (List SystemVerilog.Statement × Emission) :=
  ((RTL.artifactProgram a).cases.toList.mapM (statementCode a)).run {}

/-- SystemVerilog serialization of the finite-state realization. The bus
initializes memories/registers while idle; completed public arrays are read
through the same addressed interface. Internal FIFO state is not exposed. -/
def checkModuleArtifact (a : Artifact) : Except String Unit := do
  unless SystemVerilog.InterfaceLayout a do throw "inconsistent interface memory layout"
  unless a.machine.entry < a.machine.nodes.size do throw "invalid circuit entry"
  unless (a.memories.toList.map Prod.fst).eraseDups.length = a.memories.size do
    throw "duplicate array declarations"
  unless (a.machine.capacities.toList.map Prod.fst).eraseDups.length = a.machine.capacities.size do
    throw "duplicate FIFO declarations"
  for n in a.machine.nodes do
    let successors := match n with
      | .halt => []
      | .branch _ yes no => [yes,no]
      | .jump next | .wire _ _ next | .assign _ _ next | .store _ _ _ next
      | .snapshot _ _ next | .erase _ next | .clear _ next | .send _ _ next | .receive _ _ next => [next]
    unless successors.all (fun pc => pc < a.machine.nodes.size) do throw "invalid circuit edge"

def checkReadOutputs (a : Artifact) (outputs : List Nat) : Except String Unit := do
  for id in outputs do let _ ← memorySize a id

/-- Validated module assembly. The same module is interpreted by the proof
and handed to the renderer; the emitter does not reconstruct a second body. -/
def generateModule (a : Artifact) (outputs : List Nat) : Except String SystemVerilog.ModuleCode := do
  checkModuleArtifact a
  let (cases,es) ← generateCode a
  checkReadOutputs a outputs
  return SystemVerilog.moduleCode a outputs cases es.text

def emit (a : Artifact) (outputs : List Nat) : Except String String := do
  return (← generateModule a outputs).text

end IRComparison.Circuit
