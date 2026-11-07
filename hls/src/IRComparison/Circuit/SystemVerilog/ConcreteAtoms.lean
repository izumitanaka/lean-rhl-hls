import IRComparison.Circuit.SystemVerilog.ConcreteSyntax

namespace IRComparison.Circuit.SystemVerilog.Concrete

theorem opening_sound {s : String} {d : Delimiter} (h : opening s = some d) :
    s = d.opening := by
  unfold opening at h
  split at h <;> cases h <;> rfl

theorem closing_sound {s : String} {d : Delimiter} (h : closing s = some d) :
    s = d.closing := by
  unfold closing at h
  split at h <;> cases h <;> rfl

theorem not_delimiter (decode : String → Option α) (s : String) (value : α)
    (yes : decode s = some value)
    (opens : ∀ d : Delimiter, decode d.opening = none)
    (closes : ∀ d : Delimiter, decode d.closing = none) : opening s = none ∧ closing s = none := by
  constructor
  · cases h : opening s with
    | none => rfl
    | some d => rw [opening_sound h,opens] at yes; contradiction
  · cases h : closing s with
    | none => rfl
    | some d => rw [closing_sound h,closes] at yes; contradiction

theorem decimal_noSpace (n : Nat) : ' ' ∉ (toString n).toList := by
  intro h
  have impossible := decimal_characters n ' ' h
  contradiction

theorem Name.noSpace (n : SystemVerilog.Name) : ' ' ∉ n.text.toList := by
  cases n <;> simp only [SystemVerilog.Name.text,String.toList_append,List.mem_append,not_or]
  all_goals first | decide | exact ⟨by decide,decimal_noSpace _⟩

theorem nameSafe (n : SystemVerilog.Name) : WordSafe n.text := by
  refine ⟨?_,Name.noSpace n,not_delimiter SystemVerilog.Name.decode n.text n
    (SystemVerilog.Name.decode_text n) (by intro d; cases d <;> rfl) (by intro d; cases d <;> rfl)⟩
  intro empty
  have h := SystemVerilog.Name.decode_text n
  have textEmpty : n.text = "" := by simpa using congrArg String.ofList empty
  rw [textEmpty] at h
  contradiction

theorem naturalSafe (n : Nat) : WordSafe (toString n) := by
  exact ⟨decimal_nonempty n,decimal_noSpace n,
    not_delimiter (fun s => decimal s.toList) (toString n) n (decimal_toString n)
      (by intro d; cases d <;> rfl) (by intro d; cases d <;> rfl)⟩

theorem signedSafe (w n : Nat) (positive : 0 < w) : WordSafe (toString w ++ "'sd" ++ toString n) := by
  have read := signedDecimal_print w n positive
  refine ⟨?_,?_,not_delimiter signedDecimal _ _ read
    (by intro d; cases d <;> rfl) (by intro d; cases d <;> rfl)⟩
  · intro empty
    have textEmpty : (toString w ++ "'sd" ++ toString n) = "" := by
      simpa using congrArg String.ofList empty
    rw [textEmpty] at read
    contradiction
  · simp only [String.toList_append,List.mem_append,not_or]
    exact ⟨⟨decimal_noSpace w,by decide⟩,decimal_noSpace n⟩

def atom (s : String) (safe : WordSafe s := by decide) : Tree := .atom ⟨s,safe⟩
def name (n : SystemVerilog.Name) : Tree := atom n.text (nameSafe n)
def natural (n : Nat) : Tree := atom (toString n) (naturalSafe n)
def signed (w n : Nat) (positive : 0 < w) : Tree :=
  atom (toString w ++ "'sd" ++ toString n) (signedSafe w n positive)
def operator (op : Operator) : Tree := atom op.text (by cases op <;> decide)

def readAtom : Tree → Option String
  | .atom w => some w.text | _ => none
def readName (t : Tree) : Option SystemVerilog.Name := (readAtom t).bind SystemVerilog.Name.parse
def readNatural (t : Tree) : Option Nat := (readAtom t).bind fun s => decimal s.toList
def readOperator (t : Tree) : Option Operator := (readAtom t).bind Operator.decode

@[simp] theorem read_name (n : SystemVerilog.Name) : readName (name n) = some n := by
  exact SystemVerilog.Name.parse_text n
@[simp] theorem read_natural (n : Nat) : readNatural (natural n) = some n := by
  exact decimal_toString n
@[simp] theorem read_operator (op : Operator) : readOperator (operator op) = some op := by
  exact Operator.decode_text op

end IRComparison.Circuit.SystemVerilog.Concrete
