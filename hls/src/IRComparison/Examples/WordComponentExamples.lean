import IRComparison.Components.WordComponent

namespace IRComparison.WordComponentExamples
open ClockedComponent WordComponent

-- Illustrative latency choices only; no physical operator timing claim.
def extra (r : Request) : Nat := match r.op with
  | .add | .sub => 0
  | .mul => 1
  | .udiv => 3

def hold : WordComponent.Input := ⟨none,false⟩
def take : WordComponent.Input := ⟨none,true⟩
def addOverflow : Request := ⟨.add,4294967295,2⟩
def division : Request := ⟨.udiv,4294967295,2⟩
def zeroDivisor : Request := ⟨.udiv,7,0⟩
def attempt (r : Request) : WordComponent.Input := ⟨some r,true⟩

-- The next operation is presented too soon. It must not replace the captured
-- divider inputs, nor be silently counted as an accepted request.
def stalledDivision : List WordComponent.Input :=
  [attempt division, attempt addOverflow, take, hold, take, hold, hold, take, take]

example : run Request.eval extra .idle stalledDivision = .idle := by decide +kernel
example : accepts Request.eval extra .idle stalledDivision = [division] := by decide +kernel
example : results Request.eval extra .idle stalledDivision = [2147483647] := by decide +kernel
example : run Request.eval extra .idle [attempt addOverflow,hold,hold,hold] =
    .response addOverflow 1 := by decide +kernel

-- Back-to-back acknowledgement/request attempts are not pipelined here.
-- The source must retain valid/operands until the component is ready.
example : accepts Request.eval extra .idle
    [attempt addOverflow, hold, attempt division, attempt division] =
    [addOverflow,division] := by decide +kernel

example : run Request.eval extra .idle (attempt zeroDivisor :: List.replicate 4 hold) =
    .response zeroDivisor 0 := by decide +kernel
example : run Request.eval extra .idle (attempt division :: List.replicate 3 hold) =
    .busy 0 division := by decide +kernel
example : run Request.eval extra .idle
    [attempt ⟨.sub,0,1⟩,hold] = .response ⟨.sub,0,1⟩ 4294967295 := by decide +kernel
example : run Request.eval extra .idle
    [attempt ⟨.mul,2147483648,2⟩,hold,hold] = .response ⟨.mul,2147483648,2⟩ 0 := by decide +kernel

-- Closed controller: acceptance at edge 1, response valid at edge 5,
-- captured exactly once at edge 6. Finishing early is explicitly checked.
example : ClockedOperation.run Request.eval extra 5 (ClockedOperation.start division) =
    ⟨.awaiting,.response division 2147483647⟩ := by decide +kernel
example : ClockedOperation.run Request.eval extra 6 (ClockedOperation.start division) =
    ClockedOperation.stop 2147483647 := by decide +kernel
example : ClockedOperation.run Request.eval extra 9 (ClockedOperation.start division) =
    ClockedOperation.stop 2147483647 := by decide +kernel

end IRComparison.WordComponentExamples
