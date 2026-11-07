import PaperCore.SMT.SMTSemantics
import PaperCore.SMT.SMTReply
namespace PaperCore.SMTRequest
open SMTMeaning

inductive SMTSort where | integer | boolean
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

def safeQuoted (name : String) : Bool := name.toList.all fun c =>
  c != '|' && c != '\\' && c != '(' && c != ')' &&
  c != ' ' && c != '\t' && c != '\r' && c != '\n' && c != ';'

def operatorSort (op : String) (ss : List (Option SMTSort)) : Option SMTSort :=
  match op,ss with
  | "+",[some .integer,some .integer] | "-",[some .integer,some .integer]
  | "*",[some .integer,some .integer] | "div",[some .integer,some .integer]
  | "mod",[some .integer,some .integer] | "-",[some .integer] => some .integer
  | "=",[some .integer,some .integer] | "distinct",[some .integer,some .integer]
  | "<",[some .integer,some .integer] | "<=",[some .integer,some .integer]
  | ">",[some .integer,some .integer] | ">=",[some .integer,some .integer] => some .boolean
  | "not",[some .boolean] | "=>",[some .boolean,some .boolean] => some .boolean
  | "ite",[some .boolean,some a,some b] => if a==b then some a else none
  | "and",xs | "or",xs => if xs.all (· == some .boolean) then some .boolean else none
  | _,_ => none

def sortOf (count : Nat) (bound : List String) : Indexed → Option SMTSort
  | .num _ => some .integer
  | .param n => if n<count then some .integer else none
  | .var x => if safeQuoted x && bound.contains x then some .integer else none
  | .app op xs => operatorSort op (xs.map (sortOf count bound))
  | .all xs b =>
    if !xs.isEmpty && xs.all safeQuoted && xs.Nodup then
      if sortOf count (xs++bound) b == some .boolean then some .boolean else none
    else none

def tokens : Indexed → List String
  | .num n => SMTReply.integerTokens n
  | .var x => ["|v:"++x++"|"]
  | .param n => ["p"++toString n]
  | .app "and" [] => ["true"]
  | .app "or" [] => ["false"]
  | .app op xs => ["(",op] ++ xs.flatMap tokens ++ [")"]
  | .all xs b => ["(","forall","("] ++
      xs.flatMap (fun x => ["(","|v:"++x++"|","Int",")"]) ++ [")"] ++ tokens b ++ [")"]

def scriptTokens (count : Nat) (term : Indexed) : List String :=
  ["(","set-option",":produce-models","true",")","(","set-option",":timeout","10000",")"] ++
  (List.range count).flatMap (fun j => ["(","declare-const","p"++toString j,"Int",")"]) ++
  ["(","assert"] ++ tokens term ++ [")","(","check-sat",")"] ++
  (if count=0 then [] else ["(","get-value","("] ++
    (List.range count).map (fun j => "p"++toString j) ++ [")",")"])

/-- Grammar/typing of the exact wire request: one assertion, only integer declarations,
    all variables bound, and get-value for precisely p0,...,p(count-1).
    This is the supported SMT-LIB request grammar, not an assumption about source programs. -/
def Syntax (text : String) (count : Nat) (term : Indexed) : Prop :=
  sortOf count [] term = some .boolean ∧ SMTReply.lex text = scriptTokens count term

def check (formula : SMT) (text : String) : Bool :=
  let term := encode formula.params formula
  sortOf formula.params.length [] term == some .boolean &&
    SMTReply.lex text == scriptTokens formula.params.length term

theorem check_sound {formula : SMT} {text : String} (h : check formula text = true) :
    Syntax text formula.params.length (encode formula.params formula) := by
  simpa [check,Syntax,Bool.and_eq_true,beq_iff_eq] using h

#print axioms check_sound
end PaperCore.SMTRequest
