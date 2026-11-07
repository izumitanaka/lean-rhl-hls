import NativeRHL.TargetFacts

namespace NativeRHL.ScalarCode

inductive Op where
  | add | sub | mul | div | mod
  deriving Repr, DecidableEq

def meaning : Op → Int → Int → Int
  | .add => Int.add
  | .sub => Int.sub
  | .mul => Int.mul
  | .div => Int.ediv
  | .mod => Int.emod

end NativeRHL.ScalarCode
