import IRComparison.Circuit.SystemVerilog.Lexical

namespace IRComparison.Circuit.SystemVerilog.Concrete

/-- Native SV delimiters. This is a concrete-syntax tree, not an optimization
IR. Whitespace separates tokens; the decoder reconstructs nesting from text. -/
inductive Delimiter where
  | round | square | brace | block | cases | module
  deriving Repr, DecidableEq

def Delimiter.opening : Delimiter → String
  | .round => "(" | .square => "[" | .brace => "{"
  | .block => "begin" | .cases => "case" | .module => "module"
def Delimiter.closing : Delimiter → String
  | .round => ")" | .square => "]" | .brace => "}"
  | .block => "end" | .cases => "endcase" | .module => "endmodule"
def opening : String → Option Delimiter
  | "(" => some .round | "[" => some .square | "{" => some .brace
  | "begin" => some .block | "case" => some .cases | "module" => some .module
  | _ => none
def closing : String → Option Delimiter
  | ")" => some .round | "]" => some .square | "}" => some .brace
  | "end" => some .block | "endcase" => some .cases | "endmodule" => some .module
  | _ => none

def WordSafe (s : String) : Prop := s.toList ≠ [] ∧ ' ' ∉ s.toList ∧
  opening s = none ∧ closing s = none

instance (s : String) : Decidable (WordSafe s) := by unfold WordSafe; infer_instance

structure Word where
  text : String
  safe : WordSafe text
  deriving Repr, DecidableEq

inductive Tree where
  | atom (word : Word)
  | group (delimiter : Delimiter) (children : List Tree)
  deriving Repr

def Tree.tokens : Tree → List String
  | .atom w => [w.text]
  | .group d children => d.opening :: (children.flatMap Tree.tokens ++ [d.closing])

/-- A stack parser has no source AST or expected syntax tree as an input. -/
structure ParseState where
  current : List Tree := []
  stack : List (Delimiter × List Tree) := []
  deriving Repr

def step (state : ParseState) (token : String) : Option ParseState :=
  match opening token with
  | some d => some ⟨[],(d,state.current)::state.stack⟩
  | none => match closing token with
    | some d => match state.stack with
      | (expected,parent)::rest =>
          if d = expected then some ⟨.group d state.current.reverse::parent,rest⟩ else none
      | [] => none
    | none => if h : WordSafe token then some ⟨.atom ⟨token,h⟩::state.current,state.stack⟩ else none

def readTokens : List String → ParseState → Option ParseState
  | [],state => some state
  | token::rest,state => (step state token).bind (readTokens rest)

theorem readTokens_append (xs ys : List String) (state : ParseState) :
    readTokens (xs++ys) state = (readTokens xs state).bind (readTokens ys) := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,readTokens,Option.bind_assoc]
    cases step state x <;> simp only [Option.bind_none,Option.bind_some,ih]

theorem step_atom (w : Word) (state : ParseState) :
    step state w.text = some ⟨.atom w::state.current,state.stack⟩ := by
  simp only [step,w.safe.2.2.1,w.safe.2.2.2,dif_pos w.safe]

theorem step_open (d : Delimiter) (state : ParseState) :
    step state d.opening = some ⟨[],(d,state.current)::state.stack⟩ := by
  cases d <;> rfl

theorem step_close (d : Delimiter) (xs parent : List Tree) (stack) :
    step ⟨xs,(d,parent)::stack⟩ d.closing = some ⟨.group d xs.reverse::parent,stack⟩ := by
  cases d <;> simp [step,Delimiter.closing,opening,closing]

mutual
theorem Tree.read_tokens (tree : Tree) (state : ParseState) :
    readTokens tree.tokens state = some ⟨tree::state.current,state.stack⟩ := by
  cases tree with
  | atom w => simp only [Tree.tokens,readTokens,step_atom,Option.bind_some]
  | group d children =>
    simp only [Tree.tokens,readTokens,step_open,Option.bind_some,readTokens_append]
    rw [read_children children ⟨[],(d,state.current)::state.stack⟩]
    simp only [Option.bind_some,List.append_nil,step_close,List.reverse_reverse]
termination_by sizeOf tree

theorem read_children (children : List Tree) (state : ParseState) :
    readTokens (children.flatMap Tree.tokens) state =
      some ⟨children.reverse ++ state.current,state.stack⟩ := by
  cases children with
  | nil => rfl
  | cons first rest =>
    simp only [List.flatMap_cons,readTokens_append]
    rw [Tree.read_tokens first state]
    simp only [Option.bind_some]
    rw [read_children rest ⟨first::state.current,state.stack⟩]
    simp [List.reverse_cons,List.append_assoc]
termination_by sizeOf children
end

def parseTokens (tokens : List String) : Option (List Tree) := do
  let result ← readTokens tokens {}
  if result.stack.isEmpty then some result.current.reverse else none

theorem parse_tokens (trees : List Tree) :
    parseTokens (trees.flatMap Tree.tokens) = some trees := by
  unfold parseTokens
  rw [read_children]
  simp

theorem Tree.tokens_injective {a b : Tree} (h : a.tokens = b.tokens) : a = b := by
  have parsed := congrArg parseTokens h
  have ha := parse_tokens [a]
  have hb := parse_tokens [b]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil] at ha hb
  rw [ha,hb] at parsed
  exact List.cons.inj (Option.some.inj parsed) |>.1

instance : DecidableEq Tree := fun a b =>
  if h : a.tokens = b.tokens then isTrue (Tree.tokens_injective h)
  else isFalse (fun equal => h (congrArg Tree.tokens equal))

structure WordState where
  current : List Char := []
  done : List String := []

def charStep (s : WordState) (c : Char) : WordState :=
  if c = ' ' then
    if s.current.isEmpty then s else ⟨[],String.ofList s.current.reverse::s.done⟩
  else ⟨c::s.current,s.done⟩

def readChars : List Char → WordState → WordState
  | [],s => s
  | c::cs,s => readChars cs (charStep s c)

theorem readChars_append (xs ys : List Char) (s : WordState) :
    readChars (xs++ys) s = readChars ys (readChars xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih => exact ih _

theorem readChars_word (xs : List Char) (s : WordState) (noSpace : ' ' ∉ xs) :
    readChars xs s = ⟨xs.reverse++s.current,s.done⟩ := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    have ne : c ≠ ' ' := by intro h; subst c; simp at noSpace
    have tail : ' ' ∉ cs := fun h => noSpace (List.mem_cons_of_mem c h)
    simp only [readChars,charStep,ne,↓reduceIte]
    rw [ih _ tail]
    simp [List.reverse_cons,List.append_assoc]

/-- Every token has a trailing separator. This intentionally simple layout
avoids implicit lexical boundaries such as `a` followed immediately by `b`.
It is ordinary SystemVerilog whitespace, not metadata encoding an AST. -/
def tokenChars (tokens : List String) : List Char :=
  tokens.flatMap (fun token => token.toList ++ [' '])

def render (tokens : List String) : String := String.ofList (tokenChars tokens)

def words (text : String) : List String :=
  let s := readChars text.toList {}
  (charStep s ' ').done.reverse

theorem readChars_tokens (tokens done : List String)
    (safe : ∀ t ∈ tokens, t.toList ≠ [] ∧ ' ' ∉ t.toList) :
    readChars (tokenChars tokens) ⟨[],done⟩ = ⟨[],tokens.reverse++done⟩ := by
  induction tokens generalizing done with
  | nil => rfl
  | cons t ts ih =>
    have ht := safe t (by simp)
    simp only [tokenChars,List.flatMap_cons,readChars_append]
    rw [readChars_word _ _ ht.2]
    simp only [List.append_nil,readChars,charStep,↓reduceIte]
    have nonempty : t.toList.reverse ≠ [] := by simpa using ht.1
    simp only [List.isEmpty_iff,nonempty,↓reduceIte,List.reverse_reverse,String.ofList_toList]
    rw [show ts.flatMap (fun token => token.toList ++ [' ']) = tokenChars ts from rfl]
    rw [ih _ (fun x hx => safe x (by simp [hx]))]
    simp [List.reverse_cons,List.append_assoc]

theorem words_render (tokens : List String)
    (safe : ∀ t ∈ tokens, t.toList ≠ [] ∧ ' ' ∉ t.toList) :
    words (render tokens) = tokens := by
  unfold words render
  rw [String.toList_ofList,readChars_tokens _ _ safe]
  simp [charStep]

mutual
theorem Tree.tokens_safe (tree : Tree) :
    ∀ token ∈ tree.tokens, token.toList ≠ [] ∧ ' ' ∉ token.toList := by
  cases tree with
  | atom w => simpa [Tree.tokens] using And.intro w.safe.1 w.safe.2.1
  | group d children =>
    intro token member
    simp only [Tree.tokens,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
    rcases member with rfl | member | rfl
    · cases d <;> decide
    · exact children_safe children token member
    · cases d <;> decide
termination_by sizeOf tree

theorem children_safe (trees : List Tree) :
    ∀ token ∈ trees.flatMap Tree.tokens, token.toList ≠ [] ∧ ' ' ∉ token.toList := by
  cases trees with
  | nil => simp
  | cons t ts =>
    intro token member
    simp only [List.flatMap_cons,List.mem_append] at member
    rcases member with h | h
    · exact Tree.tokens_safe t token h
    · exact children_safe ts token h
termination_by sizeOf trees
end

def print (trees : List Tree) : String := render (trees.flatMap Tree.tokens)
def parse (text : String) : Option (List Tree) := parseTokens (words text)

/-- A genuine text round trip: only characters are passed to `parse`. The
result is unique because `parse` is a deterministic executable function. -/
theorem parse_print (trees : List Tree) : parse (print trees) = some trees := by
  unfold parse print
  rw [words_render _ (children_safe trees),parse_tokens]

end IRComparison.Circuit.SystemVerilog.Concrete
