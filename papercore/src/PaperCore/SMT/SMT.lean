import Lean
namespace PaperCore
open Lean
inductive SMT where
  | num (n : Int)
  | var (name : String)
  | param (name : String)
  | app (op : String) (args : List SMT)
  | all (vars : List String) (body : SMT)
  deriving Repr, ToJson, FromJson
namespace SMT
def op (name : String) (a b : SMT) : SMT := .app name [a,b]
def eq := op "="
def add := op "+"
def sub := op "-"
def mul := op "*"
def le := op "<="
def lt := op "<"
def conj (xs : List SMT) : SMT := .app "and" xs
def disj (xs : List SMT) : SMT := .app "or" xs
def neg (x : SMT) : SMT := .app "not" [x]
def implies := op "=>"
def truth : SMT := .app "and" []
def quantify (xs : List String) (s : SMT) : SMT := if xs.isEmpty then s else .all xs.eraseDups s

/-- C-like truncating division expressed using SMT's Euclidean division.
    Definedness (nonzero divisor) remains a separate VC obligation. -/
def truncDiv (a b : SMT) : SMT :=
  .app "ite" [lt a (.num 0), .app "-" [.app "div" [.app "-" [a], b]],
    .app "div" [a,b]]

def truncMod (a b : SMT) : SMT := sub a (mul b (truncDiv a b))

def params : SMT → List String
  | .param x => [x]
  | .app _ xs => (xs.flatMap params).eraseDups
  | .all _ b => params b
  | _ => []
def freeVars : SMT → List String
  | .var x => [x]
  | .app _ xs => (xs.flatMap freeVars).eraseDups
  | .all vs b => b.freeVars.filter (fun v => !vs.contains v)
  | _ => []
def subst (x : String) (e : SMT) : SMT → SMT
  | .var y => if x == y then e else .var y
  | .app op xs => .app op (xs.map (subst x e))
  | .all vs b => if vs.contains x then .all vs b else .all vs (subst x e b)
  | t => t

def render (ps : List String) : SMT → String
  | .num n => if n < 0 then "(- "++toString (-n)++")" else toString n
  | .var x => "|v:"++x++"|"
  | .param x => "p"++toString (ps.idxOf x)
  | .app "and" [] => "true"
  | .app "or" [] => "false"
  | .app op xs => "("++op++(if xs.isEmpty then "" else " "++String.intercalate " " (xs.map (render ps)))++")"
  | .all vs b => "(forall ("++String.intercalate " " (vs.map (fun v => "(|v:"++v++"| Int)"))++") "++render ps b++")"

def script (formula : SMT) : String :=
  let ps := formula.params
  "(set-option :produce-models true)\n(set-option :timeout 10000)\n" ++
  String.join ((List.range ps.length).map (fun j => s!"(declare-const p{j} Int)\n")) ++
  "(assert "++formula.render ps++")\n(check-sat)\n" ++
  (if ps.isEmpty then "" else "(get-value ("++String.intercalate " " ((List.range ps.length).map (fun j=>s!"p{j}"))++"))\n")

def extremum (maximum : Bool) (xs : List SMT) : SMT :=
  match xs with
  | [] => .num 0
  | x::xs => xs.foldl (fun acc e => .app "ite" [.app (if maximum then ">=" else "<=") [acc,e],acc,e]) x
end SMT

structure Obligation where
  name : String
  kind : String
  formula : SMT
  params : List String
  freeVars : List String
  script : String
  deriving Repr, ToJson, FromJson

def obligation (name kind : String) (constraints : List SMT) (closeFree : Bool := false) : Obligation :=
  let f := SMT.conj constraints
  let f := if closeFree then SMT.quantify f.freeVars f else f
  ⟨name,kind,f,f.params,f.freeVars,SMT.script f⟩
end PaperCore
