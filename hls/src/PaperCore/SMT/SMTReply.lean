import PaperCore.SMT.Model
namespace PaperCore.SMTReply

/-- Lexer for the unquoted SMT get-value subset. Every nonseparator character is retained.
    Comments, quoted symbols and non-integer values are deliberately not accepted by the reply grammar. -/
def flush (word : List Char) (out : List String) : List String :=
  if word.isEmpty then out else String.ofList word.reverse :: out

def lexChars : List Char → List Char → List String → List String
  | [],word,out => (flush word out).reverse
  | c::cs,word,out =>
    if c==' ' || c=='\t' || c=='\r' || c=='\n' then lexChars cs [] (flush word out)
    else if c=='(' || c==')' then lexChars cs [] (String.singleton c :: flush word out)
    else lexChars cs (c::word) out

def lex (text : String) : List String := lexChars text.toList [] []

def integerTokens : Int → List String
  | .ofNat n => [toString n]
  | .negSucc n => ["(","-",toString (n+1),")"]

inductive IntegerSyntax : List String → Int → Prop where
  | nonnegative (n : Nat) : IntegerSyntax [toString n] (Int.ofNat n)
  | negative (n : Nat) : IntegerSyntax ["(","-",toString (n+1),")"] (Int.negSucc n)

def entries : Nat → List Int → List String
  | _,[] => []
  | i,v::vs => ["(","p"++toString i] ++ integerTokens v ++ [")"] ++ entries (i+1) vs

inductive EntriesSyntax : Nat → List String → List Int → Prop where
  | nil (i : Nat) : EntriesSyntax i [] []
  | cons (hi : IntegerSyntax literal v) (ht : EntriesSyntax (i+1) tail vs) :
      EntriesSyntax i (["(","p"++toString i] ++ literal ++ [")"] ++ tail) (v::vs)

inductive ResponseSyntax : List String → List Int → Prop where
  | noParameters : ResponseSyntax ["sat"] []
  | values (hs : EntriesSyntax 0 body (v::vs)) :
      ResponseSyntax (["sat","("]++body++[")"]) (v::vs)

def responseTokens : List Int → List String
  | [] => ["sat"]
  | v::vs => ["sat","("]++entries 0 (v::vs)++[")"]

theorem integer_correct (v : Int) : IntegerSyntax (integerTokens v) v := by
  cases v with
  | ofNat n => exact .nonnegative n
  | negSucc n => exact .negative n

theorem entries_correct (i : Nat) (values : List Int) : EntriesSyntax i (entries i values) values := by
  induction values generalizing i with
  | nil => exact .nil i
  | cons v vs ih => exact .cons (integer_correct v) (ih (i+1))

theorem response_correct (values : List Int) : ResponseSyntax (responseTokens values) values := by
  cases values with
  | nil => exact .noParameters
  | cons v vs => exact .values (entries_correct 0 (v::vs))

/-- The proposal parser is untrusted: only an exact token-level correspondence is accepted. -/
def accept (schema : List String) (response : String) (proposal : List Int) : Option (List (String × Int)) :=
  if lex response == responseTokens proposal then Model.decode schema proposal else none

theorem accept_sound {schema : List String} {response : String} {proposal : List Int}
    {bindings : List (String × Int)} (h : accept schema response proposal = some bindings) :
    ResponseSyntax (lex response) proposal ∧ Model.decode schema proposal = some bindings := by
  unfold accept at h
  split at h
  next he =>
    have heq : lex response = responseTokens proposal := beq_iff_eq.mp he
    exact ⟨heq ▸ response_correct proposal,h⟩
  next => contradiction

/-- Checked wire reply -> named parameter used by the actual transformer. -/
theorem lookup_correct {schema : List String} {response : String} {proposal : List Int}
    {bindings : List (String × Int)} (h : accept schema response proposal = some bindings)
    (i : Nat) (hi : i<schema.length) :
    ResponseSyntax (lex response) proposal ∧ bindings.lookup schema[i] = proposal[i]? :=
  ⟨(accept_sound h).1,Model.decode_correct (accept_sound h).2 i hi⟩

/-- Proposal generation is not a trusted parser: accept checks its result against the original tokens. -/
def proposeEntries : List String → Option (List Int)
  | [")"] => some []
  | "("::_key::"("::"-"::n::")"::")"::tail => do
      let magnitude ← n.toInt?
      let rest ← proposeEntries tail
      return (-magnitude)::rest
  | "("::_key::n::")"::tail => do
      let value ← n.toInt?
      let rest ← proposeEntries tail
      return value::rest
  | _ => none

def propose (response : String) : Option (List Int) :=
  match lex response with
  | ["sat"] => some []
  | "sat"::"("::tail => proposeEntries tail
  | _ => none

example : accept ["slope","offset"] "sat\n((p0 2)\n(p1 (- 3)))\n" [2,-3] =
    some [("slope",2),("offset",-3)] := by decide
example : accept ["slope"] "sat\n((p0 2))" [3] = none := by decide
example : accept ["slope"] "sat\n((p0 2)(p0 3))" [2] = none := by decide
example : accept ["slope"] "sat\n((p0 2)) garbage" [2] = none := by decide
example : accept ["slope"] "unsat" [2] = none := by decide
example : accept ["slope"] "unknown" [2] = none := by decide
#print axioms lookup_correct
end PaperCore.SMTReply
