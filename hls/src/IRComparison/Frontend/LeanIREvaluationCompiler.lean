import IRComparison.Frontend.LeanIRSelect
import IRComparison.Frontend.LeanProofApplication
import IRComparison.Core.ScopedFacts

namespace IRComparison.LeanIREvaluationCompiler
open Lean4Lean LeanTyped LeanIRQuotation LeanIREvaluation LeanTypeInference
variable {env : VEnv} {U : Nat} {context : List VExpr}

structure Inputs (env : VEnv) (U : Nat) (context : List VExpr) where
  i : VExpr
  x : VExpr
  y : VExpr
  state : VExpr
  indexTyped : env.HasType U context i intType
  leftTyped : env.HasType U context x intType
  rightTyped : env.HasType U context y intType
  stateTyped : env.HasType U context state stateType
  locals : VExpr := nilInts

structure Artifact (inputs : Inputs env U context) (e : Expr) where
  value : VExpr
  valueTyped : env.HasType U context value intType
  codeTyped : env.HasType U context (code e) expressionType
  proof : VExpr
  correct : env.HasType U context proof
    (eqResult (eval (code e) inputs.i inputs.x inputs.y inputs.state inputs.locals) (someInt value))

private def typed (term type : VExpr) : Option (LeanProofApplication.Typed env U context) := do
  let h ← check env U context term type
  return ⟨term,type,h.down⟩

private def arguments (inputs : Inputs env U context) : Option (List (LeanProofApplication.Typed env U context)) := do
  let locals ← typed inputs.locals intList
  return [⟨inputs.i,intType,inputs.indexTyped⟩,⟨inputs.x,intType,inputs.leftTyped⟩,
    ⟨inputs.y,intType,inputs.rightTyped⟩,⟨inputs.state,stateType,inputs.stateTyped⟩,locals]

private def make (native : Lean.Environment) (inputs : Inputs env U context) (e : Expr)
    (value : VExpr) (factName : Lean.Name) (args : List (LeanProofApplication.Typed env U context)) :
    Option (Artifact inputs e) := do
  let fact ← LeanProofApplication.constant native env U context factName
  let result ← args.foldlM LeanProofApplication.apply fact
  let hv ← check env U context value intType
  let hc ← check env U context (code e) expressionType
  if same : result.type = eqResult (eval (code e) inputs.i inputs.x inputs.y inputs.state inputs.locals) (someInt value) then
    return ⟨value,hv.down,hc.down,result.term,same ▸ result.correct⟩
  else none

def literal (native : Lean.Environment) (inputs : Inputs env U context) (n : Int) :
    Option (Artifact inputs (.lit n)) := do
  let arg ← typed (integer n) intType
  make native inputs (.lit n) (integer n) ``ScopedFacts.literal (arg :: (← arguments inputs))

def slotExpr : Slot → Expr
  | .index => .index
  | .left => .left
  | .right => .right

def slot (native : Lean.Environment) (inputs : Inputs env U context) (which : Slot) :
    Option (Artifact inputs (slotExpr which)) := do
  let name := match which with
    | .index => ``ScopedFacts.index
    | .left => ``ScopedFacts.left
    | .right => ``ScopedFacts.right
  make native inputs (slotExpr which) (which.value inputs.i inputs.x inputs.y) name (← arguments inputs)

def binaryExpr : LeanScalar.Op → Expr → Expr → Expr
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div

def constructor : LeanScalar.Op → Lean.Name
  | .add => ``Expr.add
  | .sub => ``Expr.sub
  | .mul => ``Expr.mul
  | .div => ``Expr.div

def fact : LeanScalar.Op → Lean.Name
  | .add => ``ScopedFacts.add
  | .sub => ``ScopedFacts.sub
  | .mul => ``ScopedFacts.mul
  | .div => ``ScopedFacts.div

theorem code_binary (op : LeanScalar.Op) (a b : Expr) :
    code (binaryExpr op a b) = .app (.app (.const (constructor op) []) (code a)) (code b) := by
  cases op <;> rfl

def binary (native : Lean.Environment) (inputs : Inputs env U context)
    (op : LeanScalar.Op) (a : Artifact inputs left) (b : Artifact inputs right) :
    Option (Artifact inputs (binaryExpr op left right)) := do
  let value := VExpr.app (.app (.const op.primitive []) a.value) b.value
  make native inputs (binaryExpr op left right) value (fact op)
    ([⟨code left,expressionType,a.codeTyped⟩,⟨code right,expressionType,b.codeTyped⟩] ++ (← arguments inputs) ++
     [⟨a.value,intType,a.valueTyped⟩,⟨b.value,intType,b.valueTyped⟩,⟨a.proof,_,a.correct⟩,⟨b.proof,_,b.correct⟩])

def select (native : Lean.Environment) (inputs : Inputs env U context)
    (c : Artifact inputs condition) (a : Artifact inputs yes) (b : Artifact inputs no) :
    Option (Artifact inputs (.select condition yes no)) := do
  make native inputs (.select condition yes no) (LeanIRSelect.value c.value a.value b.value) ``ScopedFacts.select
    ([⟨code condition,expressionType,c.codeTyped⟩,⟨code yes,expressionType,a.codeTyped⟩,
      ⟨code no,expressionType,b.codeTyped⟩] ++ (← arguments inputs) ++
     [⟨c.value,intType,c.valueTyped⟩,⟨a.value,intType,a.valueTyped⟩,⟨b.value,intType,b.valueTyped⟩,
      ⟨c.proof,_,c.correct⟩,⟨a.proof,_,a.correct⟩,⟨b.proof,_,b.correct⟩])

def natIndex (native : Lean.Environment) (inputs : Inputs env U context) (a : Artifact inputs e) :
    Option (Artifact inputs (.natIndex e)) := do
  let value := VExpr.app (.const ``Int.ofNat []) (.app (.const ``Int.toNat []) a.value)
  make native inputs (.natIndex e) value ``ScopedFacts.natIndex
    ([⟨code e,expressionType,a.codeTyped⟩] ++ (← arguments inputs) ++
      [⟨a.value,intType,a.valueTyped⟩,⟨a.proof,_,a.correct⟩])

private def localParts : VExpr → Option (VExpr × VExpr)
  | .app (.app (.app (.const ``List.cons [.zero]) (.const ``Int [])) head) tail => some (head,tail)
  | _ => none

def localAt (native : Lean.Environment) (inputs : Inputs env U context) :
    (n : Nat) → Option (Artifact inputs (.local n))
  | 0 => do
    let (head,tail) ← localParts inputs.locals
    let h ← typed head intType
    let t ← typed tail intList
    make native inputs (.local 0) head ``ScopedFacts.localZero
      [h,t,⟨inputs.i,intType,inputs.indexTyped⟩,⟨inputs.x,intType,inputs.leftTyped⟩,
       ⟨inputs.y,intType,inputs.rightTyped⟩,⟨inputs.state,stateType,inputs.stateTyped⟩]
  | k+1 => do
    let (head,tail) ← localParts inputs.locals
    let h ← typed head intType
    let t ← typed tail intList
    let next ← localAt native { inputs with locals := tail } k
    let nk ← typed (numeral k) (.const ``Nat [])
    make native inputs (.local (k+1)) next.value ``ScopedFacts.localSucc
      [nk,h,t,⟨inputs.i,intType,inputs.indexTyped⟩,⟨inputs.x,intType,inputs.leftTyped⟩,
       ⟨inputs.y,intType,inputs.rightTyped⟩,⟨inputs.state,stateType,inputs.stateTyped⟩,
       ⟨next.value,intType,next.valueTyped⟩,⟨next.proof,_,next.correct⟩]
termination_by n => n

def localCount : VExpr → Nat
  | .app (.app (.app (.const ``List.cons [.zero]) (.const ``Int [])) _) tail => 1 + localCount tail
  | _ => 0

def compile (native : Lean.Environment) (inputs : Inputs env U context) :
    (e : Expr) → Option (Artifact inputs e)
  | .lit n => literal native inputs n
  | .index => slot native inputs .index
  | .left => slot native inputs .left
  | .right => slot native inputs .right
  | .local n => localAt native inputs n
  | .natIndex e => do natIndex native inputs (← compile native inputs e)
  | .add a b => return ← binary native inputs .add (← compile native inputs a) (← compile native inputs b)
  | .sub a b => return ← binary native inputs .sub (← compile native inputs a) (← compile native inputs b)
  | .mul a b => return ← binary native inputs .mul (← compile native inputs a) (← compile native inputs b)
  | .div a b => return ← binary native inputs .div (← compile native inputs a) (← compile native inputs b)
  | .select c a b => do select native inputs (← compile native inputs c) (← compile native inputs a) (← compile native inputs b)
  | _ => none

theorem compile_correct (inputs : Inputs env U context) (a : Artifact inputs e)
    (_accepted : compile nativeEnv inputs e = some a) :
    env.HasType U context a.proof
      (eqResult (eval (code e) inputs.i inputs.x inputs.y inputs.state inputs.locals) (someInt a.value)) := a.correct

end IRComparison.LeanIREvaluationCompiler
