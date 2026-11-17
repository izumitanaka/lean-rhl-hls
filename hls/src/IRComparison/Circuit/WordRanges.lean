import IRComparison.Circuit.WidenProgress
import IRComparison.Hybrid.WordTyping

/-! The word-expression frontend itself establishes the BV32 write-range
condition. No source execution or successful interval analysis is assumed. -/
namespace IRComparison.Circuit.WordRanges

def Word (wires : Nat → Interval) (e : Expr) : Prop := isWord (range wires e) = true

theorem bounds (h : Word wires e) : 0 ≤ (range wires e).lo ∧ (range wires e).hi ≤ 4294967295 := by
  simpa only [Word,isWord,Bool.and_eq_true,decide_eq_true_eq] using h

theorem wordRange_word : isWord wordRange = true := rfl

theorem wrap (v : HybridIR.Value) :
    Word wires (value i x y locals temps (HybridWord.wrap v)) := by
  simp [Word,HybridWord.wrap,HybridWord.modulus,value,range,wrapped?,wordRange,isWord]

theorem literal (v : HybridWord.Word) : Word wires (.lit (HybridWord.encode v)) := by
  have bound := v.isLt
  simp only [Word,range,wrapped?,Option.isSome_none,Bool.false_eq_true,↓reduceIte,isWord,
    Bool.and_eq_true,decide_eq_true_eq,HybridWord.encode]
  constructor
  · omega
  · change v.toNat < 4294967296 at bound
    omega

theorem register (n : Nat) : Word wires (.reg n) := rfl

theorem memory (a : Nat) (j : Expr) : Word wires (.memory a j) := rfl

theorem wire_of_within (fits : Frame.within frame top = true)
    (word : isWord (top.get n) = true) : Word frame.get (.wire n) := by
  have inside := Frame.within_get fits n
  have outer : 0 ≤ (top.get n).lo ∧ (top.get n).hi ≤ 4294967295 := by
    simpa [isWord] using word
  change isWord (frame.get n) = true
  simp only [isWord,Bool.and_eq_true,decide_eq_true_eq]
  constructor <;> unfold Interval.Inside at inside <;> omega

theorem seq (a : Expr) (h : Word wires b) : Word wires (.seq a b) := h

theorem natIndex (h : Word wires e) : Word wires (.natIndex e) := by
  have b := bounds h
  change isWord ⟨max 0 (range wires e).lo,max 0 (range wires e).hi⟩ = true
  simp only [isWord,Bool.and_eq_true,decide_eq_true_eq]
  constructor <;> omega

theorem select (c : Expr) (ha : Word wires a) (hb : Word wires b) : Word wires (.select c a b) := by
  have ah := bounds ha
  have bh := bounds hb
  simp only [Word,range,wrapped?,Option.isSome_none,Bool.false_eq_true,↓reduceIte,isWord,
    Bool.and_eq_true,decide_eq_true_eq,union]
  constructor <;> omega

theorem divide (ha : Word wires a) (hb : Word wires b) : Word wires (.bin .div a b) := by
  have ah := bounds ha
  have bh := bounds hb
  change isWord (binRange .div (range wires a) (range wires b)) = true
  simp only [binRange,ah.1,bh.1,decide_true,Bool.true_and,↓reduceIte,isWord,
    Bool.and_eq_true,decide_eq_true_eq]
  constructor <;> omega

theorem lookup (h : ∀ e ∈ locals, Word wires e) (n : Nat) : Word wires (Circuit.lookup locals n) := by
  cases found : locals[n]? with
  | none => simp [Circuit.lookup,found,Word,range,wrapped?,isWord]
  | some e =>
    simp only [Circuit.lookup,found,Option.getD_some]
    exact h e (List.mem_of_getElem? found)

theorem value_word (typed : HybridIR.WordValue localTypes tempTypes v)
    (hx : Word wires x) (hy : Word wires y)
    (hl : ∀ n, localTypes n → Word wires (Circuit.lookup locals n))
    (ht : ∀ n, tempTypes n → Word wires (Circuit.lookup temps n)) :
    Word wires (value i x y locals temps v) := by
  induction typed with
  | lit n lo hi =>
    simp only [Word,value,range,wrapped?,Option.isSome_none,Bool.false_eq_true,↓reduceIte,isWord,
      Bool.and_eq_true,decide_eq_true_eq]
    constructor <;> omega
  | left => exact hx
  | right => exact hy
  | «local» n word => exact hl n word
  | temp n word => exact ht n word
  | wrap v => exact wrap v
  | div a b ha hb => exact divide ha hb

/-- A structural word derivation survives lowering to actual circuit
expressions, including the value captured by each read binding. -/
theorem read_word (typed : HybridIR.WordRead localTypes tempTypes e)
    (hx : Word wires x) (hy : Word wires y)
    (hl : ∀ n, localTypes n → Word wires (Circuit.lookup locals n))
    (ht : ∀ n, tempTypes n → Word wires (Circuit.lookup temps n)) :
    Word wires (read i x y locals temps e) := by
  induction typed generalizing temps with
  | pure hv => exact value_word hv hx hy hl ht
  | register r => exact register r
  | memory a j => exact memory a _
  | bind a b ha hb =>
    have first := ha ht
    apply seq
    apply hb
    intro n word
    cases n with
    | zero => simpa [Circuit.lookup] using first
    | succ n => simpa [Circuit.lookup] using ht n word
  | branch a b ha hb => exact select _ (ha ht) (hb ht)

/-- Arbitrary word expressions, including unused failing reads, selection,
unsigned division and nested wrapping arithmetic. Locals and scalar arguments
must have word ranges; the integer loop-index expression need not have one. -/
theorem lower (e : HybridWord.Expr) (hx : Word wires x) (hy : Word wires y)
    (hl : ∀ held ∈ locals, Word wires held) :
    Word wires (read i x y locals temps e.lower) :=
  read_word (e.lower_word (fun _ => False)) hx hy (fun n _ => lookup hl n)
    (fun _ impossible => False.elim impossible)

/-- A static signed range binds an unbounded ordinal in the target, then
converts it to the source's word index. The ordinal itself need not be BV32. -/
theorem lower_affine (e : HybridWord.Expr) (hx : Word wires x) (hy : Word wires y)
    (hl : ∀ n, n ≠ slot → Word wires (Circuit.lookup locals n)) :
    Word wires (read i x y locals temps (e.lower.affineLocal slot start stride)) :=
  read_word ((e.lower_word (fun _ => False)).affineLocal
    (newLocals := fun n => n ≠ slot) (fun _ _ ne => ne)) hx hy hl
    (fun _ impossible => False.elim impossible)

/-- The source expression theorem discharges the actual write-range test.
Empty frames are unreachable and produce no successors, as in transfer. -/
theorem transfer_store (e : HybridWord.Expr) (hx : Word frame.get x) (hy : Word frame.get y)
    (hl : ∀ held ∈ locals, Word frame.get held) (array : Nat) (address : Expr) (next : Nat) :
    transfer frame (.store array address (read i x y locals temps e.lower) next) =
      .ok (if frame.empty then [] else [(next,frame)]) := by
  have word := lower (i := i) (temps := temps) e hx hy hl
  simp only [transfer]
  split
  · rfl
  · simp only [Word] at word
    simp [word,pure,Except.pure,bind,Except.bind]

theorem transfer_assign (e : HybridWord.Expr) (hx : Word frame.get x) (hy : Word frame.get y)
    (hl : ∀ held ∈ locals, Word frame.get held) (reg next : Nat) :
    transfer frame (.assign reg (read i x y locals temps e.lower) next) =
      .ok (if frame.empty then [] else [(next,frame)]) := by
  have word := lower (i := i) (temps := temps) e hx hy hl
  simp only [transfer]
  split
  · rfl
  · simp only [Word] at word
    simp [word,pure,Except.pure,bind,Except.bind]

end IRComparison.Circuit.WordRanges
