import IRComparison.Core.Frontend
import IRComparison.Examples.Examples

namespace IRComparison.FrontendExamples

open Source Frontend

def mean : Scalar := .div (.add (.reg 1) (.reg 2)) (.lit 2)

def filterBody (next : Scalar) (tail : Cmd := .store 0 .index mean) : Cmd :=
  .seq (.load 1 .index) (.seq (.load 2 next) tail)

def filterProgram : Cmd := .loop 0 1 3 (filterBody (.add .index (.lit 1)))

/-- Execute the ordinary source and both complete compiled paths. -/
def check (p : Cmd) (xs : Array Int) (size : Nat)
    (expected : Option (Int × Array Int)) : Bool :=
  let input := arrayInput xs
  let s := Examples.initial size
  Examples.observe (p.eval input 0 s) == expected &&
  Examples.observe ((compileImperative p).eval runImperative input 0 s) == expected &&
  Examples.observe ((compileFunctional p).eval runFunctional input 0 s) == expected

def buffers (countCode : Code → Nat) : Target Code → Nat
  | .original _ => 0
  | .code p => countCode p
  | .seq a b | .branch _ a b => buffers countCode a + buffers countCode b
  | .loop _ _ _ b => buffers countCode b

def countI : Imperative.Program → Nat
  | .buffered .. => 1
  | .seq a b | .branch _ a b => countI a + countI b
  | _ => 0

def countF : Functional.Program → Nat
  | .carried .. => 1
  | .letResult a b | .branch _ a b => countF a + countF b
  | _ => 0

theorem filter_result : check filterProgram #[2,4,6,8] 3 (some (0,#[3,5,7])) = true := by decide

/-- Rule out a vacuous compiler which simply returns all source programs unchanged. -/
theorem filter_is_optimized :
    buffers countI (compileImperative filterProgram) = 1 ∧
    buffers countF (compileFunctional filterProgram) = 1 := by decide

theorem reverse_result :
    check (.loop 3 (-1) 3 (filterBody (.sub .index (.lit 1))))
      #[2,4,6,8] 4 (some (0,#[0,3,5,7])) = true := by decide

theorem stride_two_result :
    check (.loop 0 2 2 (filterBody (.add .index (.lit 2))))
      #[0,2,4,6,8] 5 (some (0,#[2,0,6,0,0])) = true := by decide

theorem empty_result :
    check (.loop (-1) 1 0 (filterBody (.add .index (.lit 1))))
      #[] 0 (some (0,#[])) = true := by decide

theorem out_of_bounds_result : check filterProgram #[2,4] 3 none = true := by decide

def clobber : Cmd := .loop 0 1 3 (filterBody (.add .index (.lit 1))
  (.seq (.store 0 .index mean) (.seq (.assign 1 (.lit 99)) (.assign 2 (.lit 88)))))

theorem overwritten_read_registers_result :
    check clobber #[2,4,6,8] 3 (some (0,#[3,5,7])) = true := by decide

def aliasedDestinations : Cmd := .loop 0 1 3
  (.seq (.load 1 .index)
    (.seq (.load 1 (.add .index (.lit 1))) (.store 0 .index (.reg 1))))

theorem aliased_destinations_result :
    check aliasedDestinations #[2,4,6,8] 3 (some (0,#[4,6,8])) = true := by decide

theorem alias_is_optimized : buffers countI (compileImperative aliasedDestinations) = 1 := by decide

def conditionalLoad : Cmd := .loop 0 1 1
  (.seq (.load 1 .index)
    (.branch (.reg 0) (.load 2 (.add .index (.lit 1))) (.assign 2 (.lit 42))))

/-- The absent second element must never be speculatively read. -/
theorem conditional_read_result :
    check (.seq conditionalLoad (.store 0 (.lit 0) (.reg 2)))
      #[5] 1 (some (0,#[42])) = true := by decide

theorem conditional_read_not_optimized :
    buffers countI (compileImperative conditionalLoad) = 0 ∧
    buffers countF (compileFunctional conditionalLoad) = 0 := by decide

def dynamicLoad : Cmd := .loop 0 1 1
  (.seq (.load 1 .index) (.seq (.load 2 (.reg 1)) (.store 0 .index (.reg 2))))

theorem dynamic_address_result :
    check dynamicLoad #[1,7] 1 (some (0,#[7])) = true := by decide

theorem dynamic_address_not_optimized : buffers countI (compileImperative dynamicLoad) = 0 := by decide

def noOverlap : Cmd := .loop 0 1 2 (filterBody (.add .index (.lit 2)))

theorem no_overlap_result : check noOverlap #[2,4,6,8] 2 (some (0,#[4,6])) = true := by decide

theorem no_overlap_not_buffered :
    buffers countI (compileImperative noOverlap) = 0 ∧
    buffers countF (compileFunctional noOverlap) = 0 := by decide

def updateLocal : Cmd := .loop 0 1 3 (filterBody (.add .index (.lit 1))
  (.seq (.branch (.reg 1)
    (.store 0 (.lit 0) (.add (.read 0 (.lit 0)) (.reg 2)))
    (.store 0 (.lit 0) (.lit 99)))
    (.assign 0 (.read 0 (.lit 0)))))

theorem local_array_dependency_result :
    check updateLocal #[1,2,3,4] 1 (some (9,#[9])) = true := by decide

/-- Outer index must be restored after the inner loop (the inner ends at 2). -/
def nested : Cmd := .loop 0 1 2
  (.seq filterProgram (.assign 0 (.add (.reg 0) .index)))

theorem nested_index_result : check nested #[2,4,6,8] 3 (some (1,#[3,5,7])) = true := by decide

theorem nested_inner_optimized : buffers countI (compileImperative nested) = 1 := by decide

/-- An unoptimized data-dependent input load after an optimized loop. -/
theorem mixed_result :
    check (.seq filterProgram (.seq (.load 0 (.reg 1)) (.assign 0 (.reg 0))))
      #[2,4,6,8,10,12,14] 3 (some (14,#[3,5,7])) = true := by decide

end IRComparison.FrontendExamples
