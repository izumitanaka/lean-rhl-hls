import IRComparison.Hybrid.HybridValues

/-! BV32 arithmetic embedded in the existing mixed IR. Int is a carrier here,
not the source arithmetic: every wrapping operation normalizes its result. -/
namespace IRComparison.HybridWord
open HybridIR

abbrev Word := BitVec 32
def encode (w : Word) : Int := w.toNat
def modulus : Int := 4294967296

def wrap (v : Value) : Value :=
  .sub v (.mul (.div v (.lit modulus)) (.lit modulus))

theorem encode_ofInt (z : Int) : encode (BitVec.ofInt 32 z) = z % modulus := by
  simp only [encode, BitVec.toNat_ofInt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (by decide))

theorem wrap_correct (v : Value) :
    (wrap v).eval i x y ls ts =
      (v.eval i x y ls ts).map (fun z => encode (BitVec.ofInt 32 z)) := by
  simp only [wrap, Value.eval]
  cases h : v.eval i x y ls ts with
  | none => rfl
  | some z =>
    change some (z - z / modulus * modulus) = some (encode (BitVec.ofInt 32 z))
    rw [encode_ofInt]
    have h := Int.emod_add_ediv_mul z modulus
    congr 1
    omega

theorem decode_encode (w : Word) : BitVec.ofInt 32 (encode w) = w := by
  simp [encode]

def add (a b : Value) := wrap (.add a b)
def sub (a b : Value) := wrap (.sub a b)
def mul (a b : Value) := wrap (.mul a b)
def udiv (a b : Value) : Value := .div a b

theorem encode_add (a b : Word) :
    encode (a+b) = encode (BitVec.ofInt 32 (encode a + encode b)) := by
  rw [BitVec.ofInt_add, decode_encode, decode_encode]

theorem encode_mul (a b : Word) :
    encode (a*b) = encode (BitVec.ofInt 32 (encode a * encode b)) := by
  rw [BitVec.ofInt_mul, decode_encode, decode_encode]

theorem encode_sub (a b : Word) :
    encode (a-b) = encode (BitVec.ofInt 32 (encode a - encode b)) := by
  apply congrArg encode
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub, encode, BitVec.toNat_ofInt]
  omega

theorem encode_udiv (a b : Word) : encode (a / b) = encode a / encode b := by
  simp [encode, BitVec.toNat_udiv, Int.natCast_ediv]

theorem add_correct (ha : a.eval i x y ls ts = some (encode u))
    (hb : b.eval i x y ls ts = some (encode v)) :
    (add a b).eval i x y ls ts = some (encode (u+v)) := by
  simp [add, wrap_correct, Value.eval, ha, hb, ← encode_add]

theorem sub_correct (ha : a.eval i x y ls ts = some (encode u))
    (hb : b.eval i x y ls ts = some (encode v)) :
    (sub a b).eval i x y ls ts = some (encode (u-v)) := by
  simp [sub, wrap_correct, Value.eval, ha, hb, ← encode_sub]

theorem mul_correct (ha : a.eval i x y ls ts = some (encode u))
    (hb : b.eval i x y ls ts = some (encode v)) :
    (mul a b).eval i x y ls ts = some (encode (u*v)) := by
  simp [mul, wrap_correct, Value.eval, ha, hb, ← encode_mul]

theorem udiv_correct (ha : a.eval i x y ls ts = some (encode u))
    (hb : b.eval i x y ls ts = some (encode v)) :
    (udiv a b).eval i x y ls ts = some (encode (u/v)) := by
  simp [udiv, Value.eval, ha, hb, encode_udiv]

end IRComparison.HybridWord
