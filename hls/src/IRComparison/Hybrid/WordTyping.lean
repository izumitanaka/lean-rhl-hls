import IRComparison.Hybrid.HybridWordCommand

/-! Proof-only distinction between source words and integer administrative
locals. It adds neither an IR constructor nor a source restriction. -/
namespace IRComparison.HybridIR

abbrev WordBindings := Nat → Prop

def pushWord (word : Prop) (bindings : WordBindings) : WordBindings
  | 0 => word
  | n+1 => bindings n

inductive WordValue (locals temps : WordBindings) : Value → Prop where
  | lit (n : Int) : 0 ≤ n → n < 4294967296 → WordValue locals temps (.lit n)
  | left : WordValue locals temps .left
  | right : WordValue locals temps .right
  | local (n : Nat) : locals n → WordValue locals temps (.local n)
  | temp (n : Nat) : temps n → WordValue locals temps (.temp n)
  | wrap (v : Value) : WordValue locals temps (HybridWord.wrap v)
  | div : WordValue locals temps a → WordValue locals temps b → WordValue locals temps (.div a b)

inductive WordRead (locals : WordBindings) : WordBindings → ReadCode → Prop where
  | pure : WordValue locals temps v → WordRead locals temps (.pure v)
  | register (r : Nat) : WordRead locals temps (.register r)
  | memory (a : Nat) (j : Value) : WordRead locals temps (.memory a j)
  | bind : WordRead locals temps a → WordRead locals (pushWord True temps) b → WordRead locals temps (.bind a b)
  | branch : WordRead locals temps a → WordRead locals temps b → WordRead locals temps (.branch c a b)

theorem WordValue.weaken (h : WordValue locals temps v)
    (hl : ∀ n, locals n → other n) : WordValue other temps v := by
  induction h with
  | lit n lo hi => exact .lit n lo hi
  | left => exact .left
  | right => exact .right
  | «local» n hn => exact .local n (hl n hn)
  | temp n hn => exact .temp n hn
  | wrap v => exact .wrap v
  | div _ _ a b => exact .div a b

theorem WordRead.weaken (h : WordRead locals temps e)
    (hl : ∀ n, locals n → other n) : WordRead other temps e := by
  induction h with
  | pure hv => exact .pure (hv.weaken hl)
  | register r => exact .register r
  | memory a j => exact .memory a j
  | bind _ _ a b => exact .bind a b
  | branch _ _ a b => exact .branch a b

/-- Buffer bindings follow the pre-existing lexical locals. -/
def bufferWords (depth : Nat) (locals : WordBindings) : WordBindings :=
  fun n => if n < depth then locals n else True

theorem bufferWords_keep (n : Nat) : locals n → bufferWords depth locals n := by
  intro h
  unfold bufferWords
  split <;> trivial

theorem bufferWords_push :
    bufferWords (depth+1) (pushWord kind locals) = pushWord kind (bufferWords depth locals) := by
  funext n
  cases n with
  | zero => simp [bufferWords,pushWord]
  | succ n => simp [bufferWords,pushWord,Nat.succ_lt_succ_iff]

/-- Replacing a word source index with a wrapped integer ordinal removes the
need for that underlying ordinal to fit in a data word. Other locals retain
exactly their previous obligations. -/
theorem WordValue.affineLocal (h : WordValue locals temps v)
    (keep : ∀ n, locals n → n ≠ slot → newLocals n) :
    WordValue newLocals temps (v.affineLocal slot start stride) := by
  induction h with
  | lit n lo hi => exact .lit n lo hi
  | left => exact .left
  | right => exact .right
  | «local» n word =>
    simp only [Value.affineLocal]
    split
    · exact .wrap _
    · exact .local n (keep n word (by assumption))
  | temp n word => exact .temp n word
  | wrap v => exact .wrap _
  | div a b ha hb => exact .div ha hb

theorem WordRead.affineLocal (h : WordRead locals temps e)
    (keep : ∀ n, locals n → n ≠ slot → newLocals n) :
    WordRead newLocals temps (e.affineLocal slot start stride) := by
  induction h with
  | pure hv => exact .pure (hv.affineLocal keep)
  | register r => exact .register r
  | memory a j => exact .memory a _
  | bind a b ha hb => exact .bind ha hb
  | branch a b ha hb => exact .branch ha hb

/-- Data writes and captures contain words. Integer loop ordinals may occur
in addresses and wrapped value expressions without becoming data words. -/
inductive WordCommand : WordBindings → Cmd → Prop where
  | skip : WordCommand locals .skip
  | assign : WordRead locals (fun _ => False) e → WordCommand locals (.assign r e)
  | send : WordRead locals (fun _ => False) e → WordCommand locals (.send e)
  | store : WordRead locals (fun _ => False) e → WordCommand locals (.store a j e)
  | letValue : WordRead locals (fun _ => False) e → WordCommand (pushWord True locals) b →
      WordCommand locals (.letValue e b)
  | seq : WordCommand locals a → WordCommand locals b → WordCommand locals (.seq a b)
  | branch : WordCommand locals a → WordCommand locals b → WordCommand locals (.branch e a b)
  | repeat : WordCommand locals b → WordCommand locals (.repeat n b)
  | forWord : WordRead locals (fun _ => False) e → WordCommand (pushWord True locals) b →
      WordCommand locals (.forRange e b)
  | forInteger : WordCommand (pushWord False locals) b → WordCommand locals (.forRange e b)

private theorem push_keep (keep : ∀ n, locals n → n ≠ slot → newLocals n) (word : Prop) :
    ∀ n, pushWord word locals n → n ≠ slot+1 → pushWord word newLocals n := by
  intro n value different
  cases n with
  | zero => exact value
  | succ n => exact keep n value (fun eq => different (congrArg Nat.succ eq))

theorem WordCommand.affineLocal {c : MemoryCmd} (h : WordCommand locals c.target)
    (keep : ∀ n, locals n → n ≠ slot → newLocals n) :
    WordCommand newLocals (c.affineLocal slot start stride).target := by
  induction c generalizing locals slot newLocals with
  | skip => exact .skip
  | assign r e => cases h with | assign he => exact .assign (he.affineLocal keep)
  | store a j e => cases h with | store he => exact .store (he.affineLocal keep)
  | letValue e b ih =>
    cases h with | letValue he hb => exact .letValue (he.affineLocal keep) (ih hb (push_keep keep True))
  | seq a b ha hb => cases h with | seq pa pb => exact .seq (ha pa keep) (hb pb keep)
  | branch e a b ha hb => cases h with | branch pa pb => exact .branch (ha pa keep) (hb pb keep)
  | «repeat» n b ih => cases h with | «repeat» hb => exact .repeat (ih hb keep)
  | forRange e b ih =>
    cases h with
    | forWord he hb => exact .forWord (he.affineLocal keep) (ih hb (push_keep keep True))
    | forInteger hb => exact .forInteger (ih hb (push_keep keep False))

@[simp] theorem pushWord_true : pushWord True (fun _ => True) = (fun _ => True) := by
  funext n
  cases n <;> rfl

end IRComparison.HybridIR

namespace IRComparison.HybridWord
open HybridIR

/-- Every source expression has a word result under word-valued source locals;
the proof is parametric in already-captured administrative temporaries. -/
theorem Expr.lower_word (e : Expr) (temps : WordBindings) :
    WordRead (fun _ => True) temps e.lower := by
  induction e generalizing temps with
  | lit v =>
    apply WordRead.pure
    apply WordValue.lit
    · simp [encode]
    · have bound := v.isLt
      change v.toNat < 4294967296 at bound
      simp only [encode]
      omega
  | index => exact .pure (.wrap _)
  | left => exact .pure .left
  | right => exact .pure .right
  | «local» n => exact .pure (.local n trivial)
  | reg r => exact .register r
  | read a j ih => exact .bind (ih _) (.memory a _)
  | readNat a j => exact .memory a _
  | add a b ha hb | sub a b ha hb | mul a b ha hb =>
    exact .bind (ha _) (.bind (hb _) (.pure (.wrap _)))
  | div a b ha hb =>
    exact .bind (ha _) (.bind (hb _) (.pure (.div (.temp 1 trivial) (.temp 0 trivial))))
  | select c a b hc ha hb => exact .bind (hc _) (.branch (ha _) (hb _))

/-- All source commands, including nested signed static loops and complete
array copies, retain the distinction between word data and integer counters. -/
theorem Cmd.lower_word (c : Cmd) : WordCommand (fun _ => True) c.lower.target := by
  induction c with
  | skip => exact .skip
  | assign r e => exact .assign (e.lower_word _)
  | store a j e => exact .store (e.lower_word _)
  | letValue e b ih => exact .letValue (e.lower_word _) (by simpa using ih)
  | seq a b ha hb => exact .seq ha hb
  | branch e a b ha hb => exact .branch ha hb
  | «repeat» n b ih => exact .repeat ih
  | forRange e b ih => exact .forWord (e.lower_word _) (by simpa using ih)
  | forStatic start stop stride b ih =>
    apply WordCommand.forInteger
    apply ih.affineLocal
    intro n _ different
    cases n with
    | zero => exact False.elim (different rfl)
    | succ n => trivial
  | copy dst src count => exact .forInteger (.store (.memory src _))

end IRComparison.HybridWord
