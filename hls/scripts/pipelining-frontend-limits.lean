import IRComparison.Frontend.LeanWordCommand

open IRComparison HybridWord

-- Existing frontend limitation, separate from the control-IR scheduling pass.
-- Keep this witness until the ordinary-Lean source connection supports it.
def nestedForWitness (_i x y : Word) (s : HybridWord.State) : Option HybridWord.State := do
  let mut t := s
  for k in List.range y.toNat do
    if x != 0 then
      for j in List.range 2 do
        t ← t.write 0 (BitVec.ofNat 32 k) (x + BitVec.ofNat 32 j)
        t ← t.write 1 (BitVec.ofNat 32 k) (x + 2)
    else
      t ← t.write 0 (BitVec.ofNat 32 k) 9
  return t

/-- error: BV32 frontend could not construct the formal source connection. No unproved output was generated. -/
#guard_msgs in
hls_word nestedForWitness as unsupportedNestedFor
