import IRComparison.Core.Bridge

namespace IRComparison.Examples

def initial (size : Nat) : State :=
  ⟨fun _ => 0, fun _ => Array.replicate size 0⟩

def mean : Expr := .div (.add .left .right) (.lit 2)
def output : Imperative.Cmd := .store 0 .index mean

def observe (result : Option State) : Option (Int × Array Int) :=
  result.map (fun s => (s.regs 0, s.arrays 0))

/-- Check four actual evaluators, rather than just two hand-written algorithms. -/
def check (p : Imperative.Program) (xs : Array Int) (size : Nat)
    (expected : Option (Int × Array Int)) : Bool :=
  let input := arrayInput xs
  let s := initial size
  observe (p.eval input s) == expected &&
  observe ((Imperative.transform p).eval input s) == expected &&
  observe ((lowerProgram p).eval input s) == expected &&
  observe ((Functional.transform (lowerProgram p)).eval input s) == expected

theorem forward_example :
    check (.loop 0 1 3 0 1 output) #[2,4,6,8] 3 (some (0,#[3,5,7])) = true := by decide

theorem reverse_example :
    check (.loop 3 (-1) 3 0 (-1) output) #[2,4,6,8] 4 (some (0,#[0,3,5,7])) = true := by decide

theorem stride_two_example :
    check (.loop 0 2 2 0 2 output) #[0,2,4,6,8] 5 (some (0,#[2,0,6,0,0])) = true := by decide

theorem shifted_example :
    check (.loop 0 1 2 1 2 output) #[2,4,6,8] 2 (some (0,#[5,7])) = true := by decide

theorem empty_example :
    check (.loop (-10) 1 0 0 1 output) #[] 0 (some (0,#[])) = true := by decide

theorem missing_first_example :
    check (.loop 0 1 1 0 1 output) #[] 1 none = true := by decide

theorem missing_later_example :
    check (.loop 0 1 3 0 1 output) #[2,4,6] 3 none = true := by decide

theorem negative_address_example :
    check (.loop 0 (-1) 1 0 (-1) output) #[2] 1 none = true := by decide

theorem invalid_store_example :
    check (.loop 0 1 1 0 1 output) #[2,4] 0 none = true := by decide

def updateThenRead : Imperative.Cmd :=
  .seq (.branch .left
    (.store 0 (.lit 0) (.add (.read 0 (.lit 0)) .right))
    (.store 0 (.lit 0) (.lit 99)))
    (.assign 0 (.read 0 (.lit 0)))

/-- Each iteration sees the previous iteration's write to the same local array. -/
theorem state_dependency_example :
    check (.loop 0 1 3 0 1 updateThenRead) #[1,2,3,4] 1
      (some (9,#[9])) = true := by decide

theorem branch_false_example :
    check (.loop 0 1 1 0 1 updateThenRead) #[0,2] 1
      (some (99,#[99])) = true := by decide

theorem nested_repeat_example :
    check (.loop 0 1 3 0 1 (.repeat 2 (.assign 0 (.add (.reg 0) (.lit 1)))))
      #[1,2,3,4] 0 (some (6,#[])) = true := by decide

theorem no_overlap_example :
    check (.loop 0 1 2 0 2 output) #[2,4,6,8] 2
      (some (0,#[4,6])) = true := by decide

theorem no_overlap_kept (b : Imperative.Cmd) :
    Imperative.transform (.loop 0 1 2 0 2 b) = .loop 0 1 2 0 2 b := rfl

theorem functional_no_overlap_kept (b : Functional.Term) :
    Functional.transform (.loop 0 1 2 0 2 b) = .loop 0 1 2 0 2 b := rfl

theorem composition_example :
    check (.seq (.effect (.assign 0 (.lit 1)))
      (.branch 0 (.loop 0 1 1 0 1 output) (.effect .skip)))
      #[2,4] 1 (some (1,#[3])) = true := by decide

/-- Functional-only example: old array version survives an update.
    Version 1 still contains the original array, while version 0 has value 7. -/
def oldVersion : Functional.Term :=
  .letWrite 0 0 (.lit 0) (.lit 7)
    (.letSet 1 0 (.read 0 (.lit 0)) (.yield 0))

theorem old_version_example :
    observe (oldVersion.eval 0 0 0 [initial 1]) = some (0,#[0]) := by decide

/-- Both versions can be used: evaluate a subterm on the old snapshot,
    then return the new snapshot retained in the enclosing environment. -/
def keepNewVersion : Functional.Term :=
  .letWrite 0 0 (.lit 0) (.lit 7)
    (.letResult 1 (.yield 0) (.yield 1))

theorem new_version_example :
    observe (keepNewVersion.eval 0 0 0 [initial 1]) = some (0,#[7]) := by decide

end IRComparison.Examples
