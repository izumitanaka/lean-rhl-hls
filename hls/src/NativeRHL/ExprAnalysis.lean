import Lean
import NativeRHL.Arithmetic

namespace NativeRHL.ExprAnalysis
open Lean

/-- Integer variable assignments for an open Lean term. This is a proof-side
binder environment, not a new source AST or runtime memory. -/
abbrev Environment := Nat → Int

def bind (env : Environment) (value : Int) : Environment
  | 0 => value
  | n+1 => env n

def addHead : Expr :=
  .app (.app (.app (.app (.const ``HAdd.hAdd [.zero,.zero,.zero]) (.const ``Int []))
    (.const ``Int [])) (.const ``Int []))
    (.app (.app (.const ``instHAdd [.zero]) (.const ``Int [])) (.const ``Int.instAdd []))

def subHead : Expr :=
  .app (.app (.app (.app (.const ``HSub.hSub [.zero,.zero,.zero]) (.const ``Int []))
    (.const ``Int [])) (.const ``Int []))
    (.app (.app (.const ``instHSub [.zero]) (.const ``Int [])) (.const ``Int.instSub []))

def mulHead : Expr :=
  .app (.app (.app (.app (.const ``HMul.hMul [.zero,.zero,.zero]) (.const ``Int []))
    (.const ``Int [])) (.const ``Int []))
    (.app (.app (.const ``instHMul [.zero]) (.const ``Int [])) (.const ``Int.instMul []))

def divHead : Expr :=
  .app (.app (.app (.app (.const ``HDiv.hDiv [.zero,.zero,.zero]) (.const ``Int []))
    (.const ``Int [])) (.const ``Int []))
    (.app (.app (.const ``instHDiv [.zero]) (.const ``Int [])) (.const ``Int.instDiv []))

def modHead : Expr :=
  .app (.app (.app (.app (.const ``HMod.hMod [.zero,.zero,.zero]) (.const ``Int []))
    (.const ``Int [])) (.const ``Int []))
    (.app (.app (.const ``instHMod [.zero]) (.const ``Int [])) (.const ``Int.instMod []))

def checkAddHead : (head : Expr) → Option (PLift (head = addHead))
  | .app (.app (.app (.app (.const ``HAdd.hAdd [.zero,.zero,.zero]) (.const ``Int []))
      (.const ``Int [])) (.const ``Int []))
      (.app (.app (.const ``instHAdd [.zero]) (.const ``Int [])) (.const ``Int.instAdd [])) => some ⟨rfl⟩
  | _ => none

def checkSubHead : (head : Expr) → Option (PLift (head = subHead))
  | .app (.app (.app (.app (.const ``HSub.hSub [.zero,.zero,.zero]) (.const ``Int []))
      (.const ``Int [])) (.const ``Int []))
      (.app (.app (.const ``instHSub [.zero]) (.const ``Int [])) (.const ``Int.instSub [])) => some ⟨rfl⟩
  | _ => none

def checkMulHead : (head : Expr) → Option (PLift (head = mulHead))
  | .app (.app (.app (.app (.const ``HMul.hMul [.zero,.zero,.zero]) (.const ``Int []))
      (.const ``Int [])) (.const ``Int []))
      (.app (.app (.const ``instHMul [.zero]) (.const ``Int [])) (.const ``Int.instMul [])) => some ⟨rfl⟩
  | _ => none

def checkDivHead : (head : Expr) → Option (PLift (head = divHead))
  | .app (.app (.app (.app (.const ``HDiv.hDiv [.zero,.zero,.zero]) (.const ``Int []))
      (.const ``Int [])) (.const ``Int []))
      (.app (.app (.const ``instHDiv [.zero]) (.const ``Int [])) (.const ``Int.instDiv [])) => some ⟨rfl⟩
  | _ => none

def checkModHead : (head : Expr) → Option (PLift (head = modHead))
  | .app (.app (.app (.app (.const ``HMod.hMod [.zero,.zero,.zero]) (.const ``Int []))
      (.const ``Int [])) (.const ``Int []))
      (.app (.app (.const ``instHMod [.zero]) (.const ``Int [])) (.const ``Int.instMod [])) => some ⟨rfl⟩
  | _ => none

/-- Exact standard elaboration of the agreed scalar `test != 0` condition.
The decision proof supplied to `ite` is irrelevant for well-typed Lean terms. -/
@[match_pattern] def nonzeroCond (test : Expr) : Expr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool []))
    (.app (.app (.app (.app (.const ``bne [.zero]) (.const ``Int []))
      (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``Int []))
        (.const ``Int.instDecidableEq []))) test)
      (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Int [])) (.lit (.natVal 0)))
        (.app (.const ``instOfNat []) (.lit (.natVal 0)))))) (.const ``Bool.true [])

@[match_pattern] def conditional (test decision yes no : Expr) : Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) (.const ``Int []))
    (nonzeroCond test)) decision) yes) no

/-- Meaning of an explicitly delimited fragment of actual Lean.Expr. Constants
are the standard Int constants, with exact application shapes and levels.
This relation does not claim to formalize the full Lean kernel evaluator. -/
inductive Denotes : Expr → Environment → Int → Prop where
  | variable : Denotes (.bvar index) env (env index)
  | literal : Denotes (.app (.const ``Int.ofNat []) (.lit (.natVal n))) env (Int.ofNat n)
  | elaboratedLiteral : Denotes
      (.app (.const ``Int.ofNat [])
        (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Nat [])) (.lit (.natVal n)))
          (.app (.const ``instOfNatNat []) (.lit (.natVal n))))) env (Int.ofNat n)
  | neg (value : Denotes arg env v) : Denotes (.app (.const ``Int.neg []) arg) env (-v)
  | add (left : Denotes a env x) (right : Denotes b env y) :
      Denotes (.app (.app (.const ``Int.add []) a) b) env (Int.add x y)
  | sub (left : Denotes a env x) (right : Denotes b env y) :
      Denotes (.app (.app (.const ``Int.sub []) a) b) env (Int.sub x y)
  | mul (left : Denotes a env x) (right : Denotes b env y) :
      Denotes (.app (.app (.const ``Int.mul []) a) b) env (Int.mul x y)
  | div (left : Denotes a env x) (right : Denotes b env y) :
      Denotes (.app (.app (.const ``Int.ediv []) a) b) env (Int.ediv x y)
  | mod (left : Denotes a env x) (right : Denotes b env y) :
      Denotes (.app (.app (.const ``Int.emod []) a) b) env (Int.emod x y)
  | surfaceLiteral : Denotes
      (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Int [])) (.lit (.natVal n)))
        (.app (.const ``instOfNat []) (.lit (.natVal n)))) env (Int.ofNat n)
  | surfaceNeg (value : Denotes arg env v) : Denotes
      (.app (.app (.app (.const ``Neg.neg [.zero]) (.const ``Int [])) (.const ``Int.instNegInt [])) arg) env (-v)
  | surfaceAdd (left : Denotes a env x) (right : Denotes b env y) :
      Denotes (.app (.app addHead a) b) env (Int.add x y)
  | surfaceSub (left : Denotes a env x) (right : Denotes b env y) :
      Denotes (.app (.app subHead a) b) env (Int.sub x y)
  | surfaceMul (left : Denotes a env x) (right : Denotes b env y) :
      Denotes (.app (.app mulHead a) b) env (Int.mul x y)
  | surfaceDiv (left : Denotes a env x) (right : Denotes b env y) :
      Denotes (.app (.app divHead a) b) env (Int.ediv x y)
  | surfaceMod (left : Denotes a env x) (right : Denotes b env y) :
      Denotes (.app (.app modHead a) b) env (Int.emod x y)
  | branch (condition : Denotes test env c) (left : Denotes yes env x)
      (right : Denotes no env y) :
      Denotes (conditional test decision yes no) env (if c ≠ 0 then x else y)
  | letValue (initial : Denotes value env v) (bodyValue : Denotes body (bind env v) result) :
      Denotes (.letE name (.const ``Int []) value body nonDependent) env result
  | metadata (value : Denotes arg env v) : Denotes (.mdata data arg) env v

theorem denotes_unique_of_eq {a b : Expr} {env : Environment} {x y : Int}
    (first : Denotes a env x) (second : Denotes b env y) (same : a = b) : x = y := by
  induction first generalizing b y <;> cases second <;> simp_all [addHead,subHead,mulHead,divHead,modHead,conditional,nonzeroCond] <;> grind

theorem denotes_unique {source : Expr} {env : Environment} {x y : Int}
    (first : Denotes source env x) (second : Denotes source env y) : x = y :=
  denotes_unique_of_eq first second rfl

/-- The result records the interpreted native function and a universally
quantified correspondence. The parser itself must construct this evidence. -/
structure Analysis (source : Expr) where
  value : Environment → Int
  correct : ∀ env, Denotes source env (value env)

/-- Total, executable analysis of actual Lean.Expr. Unsupported shapes fail;
there is no metaprogram traversal or algorithm-candidate matching here. -/
def analyze : (source : Expr) → Option (Analysis source)
  | .bvar index => some ⟨fun env => env index, fun _ => .variable⟩
  | .app (.const ``Int.ofNat []) (.lit (.natVal n)) =>
      some ⟨fun _ => Int.ofNat n, fun _ => .literal⟩
  | .app (.const ``Int.ofNat [])
      (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Nat [])) (.lit (.natVal n)))
        (.app (.const ``instOfNatNat []) (.lit (.natVal m)))) =>
      if same : n = m then
        some ⟨fun _ => Int.ofNat n, by intro env; subst m; exact .elaboratedLiteral⟩
      else none
  | .app (.const ``Int.neg []) arg => do
      let a ← analyze arg
      return ⟨fun env => -(a.value env), fun env => .neg (a.correct env)⟩
  | .app (.app (.const ``Int.add []) left) right => do
      let a ← analyze left
      let b ← analyze right
      return ⟨fun env => Int.add (a.value env) (b.value env), fun env => .add (a.correct env) (b.correct env)⟩
  | .app (.app (.const ``Int.sub []) left) right => do
      let a ← analyze left
      let b ← analyze right
      return ⟨fun env => Int.sub (a.value env) (b.value env), fun env => .sub (a.correct env) (b.correct env)⟩
  | .app (.app (.const ``Int.mul []) left) right => do
      let a ← analyze left
      let b ← analyze right
      return ⟨fun env => Int.mul (a.value env) (b.value env), fun env => .mul (a.correct env) (b.correct env)⟩
  | .app (.app (.const ``Int.ediv []) left) right => do
      let a ← analyze left
      let b ← analyze right
      return ⟨fun env => Int.ediv (a.value env) (b.value env), fun env => .div (a.correct env) (b.correct env)⟩
  | .app (.app (.const ``Int.emod []) left) right => do
      let a ← analyze left
      let b ← analyze right
      return ⟨fun env => Int.emod (a.value env) (b.value env), fun env => .mod (a.correct env) (b.correct env)⟩
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Int [])) (.lit (.natVal n)))
      (.app (.const ``instOfNat []) (.lit (.natVal m))) =>
    if same : n = m then
      some ⟨fun _ => Int.ofNat n, by intro env; subst m; exact .surfaceLiteral⟩
    else none
  | .app (.app (.app (.const ``Neg.neg [.zero]) (.const ``Int [])) (.const ``Int.instNegInt [])) arg => do
    let a ← analyze arg
    return ⟨fun env => -(a.value env),fun env => .surfaceNeg (a.correct env)⟩
  | conditional test decision yes no => do
    let c ← analyze test
    let a ← analyze yes
    let b ← analyze no
    return ⟨fun env => if c.value env ≠ 0 then a.value env else b.value env,
      fun env => .branch (decision := decision) (c.correct env) (a.correct env) (b.correct env)⟩
  | .app (.app head left) right => do
    let a ← analyze left
    let b ← analyze right
    if let some same := checkAddHead head then
      return ⟨fun env => Int.add (a.value env) (b.value env), by
        intro env; rw [same.down]; exact .surfaceAdd (a.correct env) (b.correct env)⟩
    if let some same := checkSubHead head then
      return ⟨fun env => Int.sub (a.value env) (b.value env), by
        intro env; rw [same.down]; exact .surfaceSub (a.correct env) (b.correct env)⟩
    if let some same := checkMulHead head then
      return ⟨fun env => Int.mul (a.value env) (b.value env), by
        intro env; rw [same.down]; exact .surfaceMul (a.correct env) (b.correct env)⟩
    if let some same := checkDivHead head then
      return ⟨fun env => Int.ediv (a.value env) (b.value env), by
        intro env; rw [same.down]; exact .surfaceDiv (a.correct env) (b.correct env)⟩
    if let some same := checkModHead head then
      return ⟨fun env => Int.emod (a.value env) (b.value env), by
        intro env; rw [same.down]; exact .surfaceMod (a.correct env) (b.correct env)⟩
    else none
  | .letE name (.const ``Int []) value body nonDependent => do
      let a ← analyze value
      let b ← analyze body
      return ⟨fun env => b.value (bind env (a.value env)),
        fun env => .letValue (name := name) (nonDependent := nonDependent)
          (a.correct env) (b.correct (bind env (a.value env)))⟩
  | .mdata data arg => do
      let a ← analyze arg
      return ⟨a.value, fun env => .metadata (data := data) (a.correct env)⟩
  | _ => none

/-- Universal parser soundness. No per-input semantic hypothesis or solver
assumption is required; source is the actual input to `analyze`. -/
theorem analyze_correct (source : Expr) (result : Analysis source)
    (_accepted : analyze source = some result) (env : Environment) :
    Denotes source env (result.value env) := result.correct env

#print axioms denotes_unique
#print axioms analyze_correct
end NativeRHL.ExprAnalysis
