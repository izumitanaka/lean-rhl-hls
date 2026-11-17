import PaperCore.SMT.SMT
namespace PaperCore.SMTMeaning

inductive Value where
  | integer (value : Int)
  | boolean (value : Bool)
  | invalid
  deriving DecidableEq, Repr

/-- SMT-LIB leaves division/modulo by zero unspecified. Encoding must preserve any interpretation. -/
structure ZeroDivision where
  div : Int → Int
  mod : Int → Int

def booleans : List Value → Option (List Bool)
  | [] => some []
  | .boolean b::bs => (b::·) <$> booleans bs
  | _ => none

def operation (zero : ZeroDivision) (op : String) (vs : List Value) : Value :=
  match op,vs with
  | "+",[.integer a,.integer b] => .integer (a+b)
  | "-",[.integer a,.integer b] => .integer (a-b)
  | "-",[.integer a] => .integer (-a)
  | "*",[.integer a,.integer b] => .integer (a*b)
  | "div",[.integer a,.integer b] => .integer (if b=0 then zero.div a else a/b)
  | "mod",[.integer a,.integer b] => .integer (if b=0 then zero.mod a else a%b)
  | "=",[.integer a,.integer b] => .boolean (a==b)
  | "distinct",[.integer a,.integer b] => .boolean (a != b)
  | "<",[.integer a,.integer b] => .boolean (a<b)
  | "<=",[.integer a,.integer b] => .boolean (a≤b)
  | ">",[.integer a,.integer b] => .boolean (a>b)
  | ">=",[.integer a,.integer b] => .boolean (a≥b)
  | "not",[.boolean a] => .boolean (!a)
  | "=>",[.boolean a,.boolean b] => .boolean (!a || b)
  | "ite",[.boolean c,a,b] => if c then a else b
  | "and",xs => match booleans xs with | some bs => .boolean (bs.all id) | none => .invalid
  | "or",xs => match booleans xs with | some bs => .boolean (bs.any id) | none => .invalid
  | _,_ => .invalid

/-- Simultaneous rebinding of precisely the names in a quantified binder. -/
def AgreeOutside (names : List String) (before after : String → Int) : Prop :=
  ∀ x, x ∉ names → after x = before x

noncomputable def eval (zero : ZeroDivision) (params vars : String → Int) : SMT → Value
  | .num n => .integer n
  | .var x => .integer (vars x)
  | .param x => .integer (params x)
  | .app op xs => operation zero op (xs.map (eval zero params vars))
  | .all names body => by
    classical
    exact .boolean (decide (∀ next, AgreeOutside names vars next → eval zero params next body = .boolean true))

/-- Integer parameter names on the wire are p0,p1,..., independently of source identifiers. -/
inductive Indexed where
  | num (n : Int)
  | var (name : String)
  | param (index : Nat)
  | app (op : String) (args : List Indexed)
  | all (names : List String) (body : Indexed)
  deriving Repr

noncomputable def evalIndexed (zero : ZeroDivision) (params : Nat → Int) (vars : String → Int) : Indexed → Value
  | .num n => .integer n
  | .var x => .integer (vars x)
  | .param i => .integer (params i)
  | .app op xs => operation zero op (xs.map (evalIndexed zero params vars))
  | .all names body => by
    classical
    exact .boolean (decide (∀ next, AgreeOutside names vars next → evalIndexed zero params next body = .boolean true))

def encode (schema : List String) : SMT → Indexed
  | .num n => .num n
  | .var x => .var x
  | .param x => .param (schema.idxOf x)
  | .app op xs => .app op (xs.map (encode schema))
  | .all names b => .all names (encode schema b)

/-- Parameter renaming preserves every operator and quantifier, including arbitrary zero-division interpretations. -/
theorem encode_correct (s : SMT) (schema : List String) (zero : ZeroDivision)
    (params : Nat → Int) (vars : String → Int) :
    evalIndexed zero params vars (encode schema s) =
      eval zero (fun x => params (schema.idxOf x)) vars s := by
  cases s with
  | num n => simp only [encode,evalIndexed,eval]
  | var x => simp only [encode,evalIndexed,eval]
  | param x => simp only [encode,evalIndexed,eval]
  | app op xs =>
    simp only [encode,evalIndexed,eval,List.map_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    exact encode_correct x schema zero params vars
  | all names b =>
    simp only [encode,evalIndexed,eval]
    congr 2
    apply propext
    constructor
    · intro h next ha
      rw [← encode_correct b schema zero params next]
      exact h next ha
    · intro h next ha
      rw [encode_correct b schema zero params next]
      exact h next ha
termination_by s

#print axioms encode_correct
end PaperCore.SMTMeaning
