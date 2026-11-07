import IRComparison.Circuit.SystemVerilog.Syntax

namespace IRComparison.Circuit.SystemVerilog

/-- Decimal decoding is independent of the printer. No host-language numeric
parser or `native_decide` is part of these proofs. -/
def decimalDigit : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3 | '4' => some 4
  | '5' => some 5 | '6' => some 6 | '7' => some 7 | '8' => some 8 | '9' => some 9
  | _ => none

def decimalFold : List Char → Nat → Option Nat
  | [], n => some n
  | c :: cs, n => (decimalDigit c).bind fun d => decimalFold cs (10*n+d)

def decimal (cs : List Char) : Option Nat :=
  if cs.isEmpty then none else decimalFold cs 0

theorem decimalDigit_digitChar (n : Nat) (h : n < 10) :
    decimalDigit (Nat.digitChar n) = some n := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem decimalFold_digitsCore (fuel n : Nat) (tail : List Char) (enough : n < fuel) :
    decimalFold (Nat.toDigitsCore 10 fuel n tail) 0 = decimalFold tail n := by
  induction fuel generalizing n tail with
  | zero => omega
  | succ fuel ih =>
    rw [Nat.toDigitsCore]
    split
    · rename_i zero
      simp only [decimalFold,decimalDigit_digitChar _ (Nat.mod_lt _ (by decide)),Option.bind_some]
      have small : n < 10 := by omega
      simp [Nat.mod_eq_of_lt small]
    · rename_i nonzero
      rw [ih (n/10) (Nat.digitChar (n%10)::tail) (by omega)]
      simp only [decimalFold,decimalDigit_digitChar _ (Nat.mod_lt _ (by decide)),Option.bind_some]
      congr 1
      omega

theorem digitsCore_nonempty (fuel n : Nat) (tail : List Char) (enough : n < fuel) :
    Nat.toDigitsCore 10 fuel n tail ≠ [] := by
  induction fuel generalizing n tail with
  | zero => omega
  | succ fuel ih =>
    rw [Nat.toDigitsCore]
    split
    · simp
    · exact ih _ _ (by omega)

theorem decimal_toString (n : Nat) : decimal (toString n).toList = some n := by
  change decimal (String.ofList (Nat.toDigitsCore 10 (n+1) n [])).toList = some n
  simp only [String.toList_ofList,decimal]
  have ne := digitsCore_nonempty (n+1) n [] (by omega)
  simp only [List.isEmpty_iff, ne, ↓reduceIte]
  exact decimalFold_digitsCore (n+1) n [] (by omega)

theorem decimal_text_injective {a b : Nat} (h : toString a = toString b) : a = b := by
  have := congrArg (fun s : String => decimal s.toList) h
  simpa only [decimal_toString,Option.some.injEq] using this

/-- Split a generated identifier before its numeric suffix. The split is
computed from characters, not from the structured `Name` it may represent. -/
def splitNumeric : List Char → List Char × List Char
  | [] => ([],[])
  | c :: cs => if (decimalDigit c).isSome then ([],c::cs) else
      let (stem,suffix) := splitNumeric cs
      (c::stem,suffix)

theorem splitNumeric_digitsCore (fuel n : Nat) (tail : List Char)
    (good : ∀ c ∈ tail, (decimalDigit c).isSome = true) :
    splitNumeric (Nat.toDigitsCore 10 fuel n tail) = ([],Nat.toDigitsCore 10 fuel n tail) := by
  induction fuel generalizing n tail with
  | zero =>
    cases tail with
    | nil => rfl
    | cons c cs => simp [Nat.toDigitsCore,splitNumeric,good c (by simp)]
  | succ fuel ih =>
    rw [Nat.toDigitsCore]
    split
    · simp [splitNumeric,decimalDigit_digitChar _ (Nat.mod_lt _ (by decide))]
    · apply ih
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · simp [decimalDigit_digitChar _ (Nat.mod_lt _ (by decide))]
      · exact good c hc

theorem splitNumeric_decimal (n : Nat) :
    splitNumeric (toString n).toList = ([],(toString n).toList) := by
  change splitNumeric (String.ofList (Nat.toDigitsCore 10 (n+1) n [])).toList = ([],(String.ofList (Nat.toDigitsCore 10 (n+1) n [])).toList)
  simp only [String.toList_ofList]
  exact splitNumeric_digitsCore (n+1) n [] (by simp)

theorem splitNumeric_prefix (stem suffix : List Char)
    (letters : ∀ c ∈ stem, decimalDigit c = none)
    (numeric : splitNumeric suffix = ([],suffix)) :
    splitNumeric (stem ++ suffix) = (stem,suffix) := by
  induction stem with
  | nil => exact numeric
  | cons c cs ih =>
    simp only [List.cons_append,splitNumeric,letters c (by simp),Option.isSome_none,Bool.false_eq_true,↓reduceIte]
    rw [ih (fun d hd => letters d (by simp [hd]))]

def Name.decode (text : String) : Option Name :=
  let (stem,suffix) := splitNumeric text.toList
  if suffix.isEmpty then
    match String.ofList stem with
    | "pc" => some .pc | "busy" => some .busy | "done" => some .done | "error" => some .error
    | "x" => some .x | "y" => some .y | "cfg_data" => some .configData
    | "cfg_addr" => some .configAddress | "cfg_id" => some .configId
    | "cfg_reg" => some .configRegister | "j" => some .loopIndex
    | _ => none
  else do
    let n ← decimal suffix
    match String.ofList stem with
    | "e" => some (.temporary n) | "w" => some (.holding n) | "r" => some (.register n)
    | "m" => some (.memory n) | "len" => some (.length n) | "q" => some (.queue n)
    | "used" => some (.used n) | "shift" => some (.shiftIndex n)
    | _ => none

theorem decimal_nonempty (n : Nat) : (toString n).toList ≠ [] := by
  intro h
  have := decimal_toString n
  rw [h] at this
  contradiction

private theorem decode_indexed (stem : String) (n : Nat)
    (letters : ∀ c ∈ stem.toList, decimalDigit c = none) :
    splitNumeric (stem ++ toString n).toList = (stem.toList,(toString n).toList) := by
  rw [String.toList_append]
  exact splitNumeric_prefix _ _ letters (splitNumeric_decimal n)

theorem Name.decode_text (name : Name) : Name.decode name.text = some name := by
  cases name <;> simp only [Name.text]
  all_goals first
    | rfl
    | (rename_i n
       unfold Name.decode
       rw [decode_indexed _ n (by decide)]
       simp only [List.isEmpty_iff,decimal_nonempty,↓reduceIte,decimal_toString]
       rfl)

/-- Distinct physical identifiers cannot alias because of serialization. -/
theorem Name.text_injective {a b : Name} (h : a.text = b.text) : a = b := by
  have := congrArg Name.decode h
  simpa only [Name.decode_text,Option.some.injEq] using this

/-- Accept only the generated spelling. In SV `e00` and `e0` are distinct
identifiers, even though their decimal suffixes have equal numeric values. -/
def Name.parse (text : String) : Option Name := do
  let name ← Name.decode text
  if name.text = text then some name else none

theorem Name.parse_text (name : Name) : Name.parse name.text = some name := by
  unfold Name.parse
  rw [Name.decode_text]
  simp

theorem Name.parse_sound {text : String} {name : Name} (h : Name.parse text = some name) :
    name.text = text := by
  unfold Name.parse at h
  cases decoded : Name.decode text with
  | none => simp [decoded,bind,Option.bind] at h
  | some other =>
    simp only [decoded,bind,Option.bind] at h
    split at h
    · rename_i same
      cases Option.some.inj h
      exact same
    · contradiction

def Operator.decode : String → Option Operator
  | "+" => some .add | "-" => some .sub | "*" => some .mul | "/" => some .div
  | "%" => some .mod | "<" => some .lt | ">=" => some .ge | "==" => some .eq
  | "!=" => some .ne | "&&" => some .and | _ => none

theorem Operator.decode_text (op : Operator) : Operator.decode op.text = some op := by
  cases op <;> rfl

theorem Operator.text_injective {a b : Operator} (h : a.text = b.text) : a = b := by
  have := congrArg Operator.decode h
  simpa only [Operator.decode_text,Option.some.injEq] using this

theorem digitsCore_decimal (fuel n : Nat) (tail : List Char)
    (good : ∀ c ∈ tail, (decimalDigit c).isSome = true) :
    ∀ c ∈ Nat.toDigitsCore 10 fuel n tail, (decimalDigit c).isSome = true := by
  induction fuel generalizing n tail with
  | zero => exact good
  | succ fuel ih =>
    have hd : ∀ c ∈ Nat.digitChar (n%10)::tail, (decimalDigit c).isSome = true := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · simp [decimalDigit_digitChar _ (Nat.mod_lt _ (by decide))]
      · exact good c hc
    rw [Nat.toDigitsCore]
    split
    · exact hd
    · exact ih _ _ hd

theorem decimal_characters (n : Nat) :
    ∀ c ∈ (toString n).toList, (decimalDigit c).isSome = true := by
  change ∀ c ∈ (String.ofList (Nat.toDigitsCore 10 (n+1) n [])).toList, _
  simp only [String.toList_ofList]
  exact digitsCore_decimal _ _ _ (by simp)

/-- Maximal decimal prefix; unlike `decimalFold`, this leaves punctuation
for the enclosing concrete-syntax parser. -/
def takeDigits : List Char → List Char × List Char
  | [] => ([],[])
  | c :: cs => if (decimalDigit c).isSome then
      let (digits,rest) := takeDigits cs
      (c::digits,rest)
    else ([],c::cs)

theorem takeDigits_append (digits tail : List Char)
    (good : ∀ c ∈ digits, (decimalDigit c).isSome = true)
    (stop : takeDigits tail = ([],tail)) :
    takeDigits (digits ++ tail) = (digits,tail) := by
  induction digits with
  | nil => exact stop
  | cons c cs ih =>
    simp only [List.cons_append,takeDigits,good c (by simp),↓reduceIte]
    rw [ih (fun d hd => good d (by simp [hd]))]

/-- Parse a whole explicitly sized, signed decimal SV literal. Signs are
not accepted here: the printed payload is the unsigned bit pattern. -/
def signedDecimal (text : String) : Option (Nat × Nat) := do
  let (width,rest) := takeDigits text.toList
  let w ← decimal width
  if w = 0 then none else
    match rest with
    | '\'' :: 's' :: 'd' :: payload => return (w,← decimal payload)
    | _ => none

theorem signedDecimal_print (w n : Nat) (positive : 0 < w) :
    signedDecimal (toString w ++ "'sd" ++ toString n) = some (w,n) := by
  unfold signedDecimal
  simp only [String.toList_append,List.append_assoc]
  rw [takeDigits_append _ _ (decimal_characters w) (by rfl)]
  simp only [decimal_toString,bind,Option.bind]
  simp only [show ¬ w = 0 by omega,↓reduceIte]
  change (decimal (toString n).toList).bind (fun v => some (w,v)) = _
  rw [decimal_toString]
  rfl

end IRComparison.Circuit.SystemVerilog
