import IRComparison.Hybrid.HybridSource
import IRComparison.Hybrid.HybridWord

namespace IRComparison.HybridIR

/-- Change one lexical binding, leaving its position and all other bindings intact. -/
def replaceLocal (slot : Nat) (f : Int → Int) : List Int → List Int
  | [] => []
  | a :: rest => match slot with
    | 0 => f a :: rest
    | n+1 => a :: replaceLocal n f rest

theorem replaceLocal_get (slot n : Nat) (f : Int → Int) (ls : List Int) :
    (replaceLocal slot f ls)[n]? =
      if n = slot then ls[n]?.map f else ls[n]? := by
  induction ls generalizing slot n with
  | nil => simp [replaceLocal]
  | cons a rest ih =>
    cases slot <;> cases n <;> simp_all [replaceLocal]

/-- Interpret the ordinal of a counted loop as its BV32 source index. -/
def affineWord (start stride value : Int) : Int :=
  HybridWord.encode (BitVec.ofInt 32 (start + value * stride))

def Value.affineLocal (slot : Nat) (start stride : Int) : Value → Value
  | .local n => if n = slot then
      HybridWord.wrap (.add (.lit start) (.mul (.local n) (.lit stride))) else .local n
  | .wrap32 v => .wrap32 (v.affineLocal slot start stride)
  | .natIndex v => .natIndex (v.affineLocal slot start stride)
  | .add a b => .add (a.affineLocal slot start stride) (b.affineLocal slot start stride)
  | .sub a b => .sub (a.affineLocal slot start stride) (b.affineLocal slot start stride)
  | .mul a b => .mul (a.affineLocal slot start stride) (b.affineLocal slot start stride)
  | .div a b => .div (a.affineLocal slot start stride) (b.affineLocal slot start stride)
  | v => v

theorem Value.affineLocal_correct (v : Value) :
    (v.affineLocal slot start stride).eval i x y ls ts =
      v.eval i x y (replaceLocal slot (affineWord start stride) ls) ts := by
  induction v with
  | lit | index | left | right | temp => rfl
  | «local» n =>
    simp only [affineLocal,eval,replaceLocal_get]
    split
    · simp only [HybridWord.wrap_correct,eval]
      cases ls[n]? <;> rfl
    · rfl
  | natIndex v ih | wrap32 v ih => simp only [affineLocal,eval,ih]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb =>
    simp only [affineLocal,eval,ha,hb]

def ReadCode.affineLocal (slot : Nat) (start stride : Int) : ReadCode → ReadCode
  | .pure v => .pure (v.affineLocal slot start stride)
  | .register r => .register r
  | .memory a j => .memory a (j.affineLocal slot start stride)
  | .bind a b => .bind (a.affineLocal slot start stride) (b.affineLocal slot start stride)
  | .branch c a b => .branch (c.affineLocal slot start stride)
      (a.affineLocal slot start stride) (b.affineLocal slot start stride)

theorem ReadCode.affineLocal_correct (e : ReadCode) :
    (e.affineLocal slot start stride).eval i x y s ls ts =
      e.eval i x y s (replaceLocal slot (affineWord start stride) ls) ts := by
  induction e generalizing ts with
  | pure | register | memory => simp [affineLocal,eval,Value.affineLocal_correct]
  | bind a b ha hb => simp only [affineLocal,eval,ha,hb]
  | branch c a b ha hb => simp only [affineLocal,eval,Value.affineLocal_correct,ha,hb]

def MemoryCmd.affineLocal (slot : Nat) (start stride : Int) : MemoryCmd → MemoryCmd
  | .skip => .skip
  | .assign r e => .assign r (e.affineLocal slot start stride)
  | .store a j e => .store a (j.affineLocal slot start stride) (e.affineLocal slot start stride)
  | .letValue e b => .letValue (e.affineLocal slot start stride) (b.affineLocal (slot+1) start stride)
  | .seq a b => .seq (a.affineLocal slot start stride) (b.affineLocal slot start stride)
  | .branch e a b => .branch (e.affineLocal slot start stride)
      (a.affineLocal slot start stride) (b.affineLocal slot start stride)
  | .repeat n b => .repeat n (b.affineLocal slot start stride)
  | .forRange e b => .forRange (e.affineLocal slot start stride) (b.affineLocal (slot+1) start stride)

theorem MemoryCmd.affineLocal_correct (c : MemoryCmd) :
    (c.affineLocal slot start stride).eval i x y s ls =
      c.eval i x y s (replaceLocal slot (affineWord start stride) ls) := by
  induction c generalizing slot s ls with
  | skip => rfl
  | assign | store => simp only [affineLocal,eval,ReadCode.affineLocal_correct]
  | letValue e b ih =>
    simp only [affineLocal,eval,ReadCode.affineLocal_correct]
    cases e.eval i x y s (replaceLocal slot (affineWord start stride) ls) [] with
    | none => rfl
    | some v => exact ih (slot:=slot+1) (ls:=v::ls)
  | seq a b ha hb => simp only [affineLocal,eval,ha,hb]
  | branch e a b ha hb => simp only [affineLocal,eval,ReadCode.affineLocal_correct,ha,hb]
  | «repeat» n b ih => simp only [affineLocal,eval,ih]
  | forRange e b ih =>
    simp only [affineLocal,eval,ReadCode.affineLocal_correct]
    cases e.eval i x y s (replaceLocal slot (affineWord start stride) ls) [] with
    | none => rfl
    | some n => simp only [bind,Option.bind,ih,replaceLocal]

end IRComparison.HybridIR
