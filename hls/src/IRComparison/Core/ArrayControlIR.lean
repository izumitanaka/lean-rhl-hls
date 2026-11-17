import IRComparison.Core.ArrayIR
import IRComparison.Core.BoundedReadIR

namespace IRComparison.ArrayControlIR

/-- Array-entry controllers: map is executed element by element, while a
    bounded-index entry performs one memory read. Neither is a clocked RTL. -/
inductive Operation where
  | map (body : Expr)
  | load (index : Nat)
  deriving Repr

inductive Result where
  | array (value : Array Int)
  | scalar (value : Int)
  deriving Repr, DecidableEq

inductive Config where
  | ready (operation : Operation) (input : Array Int)
  | mapping (body : Expr) (remaining output : List Int)
  | stopped (result : Option Result)
  deriving Repr

def step : Config → Config
  | .ready (.map e) a => .mapping e a.toList []
  | .ready (.load k) a => .stopped ((a[k]?).map Result.scalar)
  | .mapping _ [] out => .stopped (some (.array out.toArray))
  | .mapping e (v::vs) out =>
    match ArrayIR.value e v with
    | none => .stopped none
    | some w => .mapping e vs (out ++ [w])
  | .stopped r => .stopped r

def run : Nat → Config → Config
  | 0,s => s
  | n+1,s => run n (step s)

@[simp] theorem run_stopped (n : Nat) (r : Option Result) : run n (.stopped r) = .stopped r := by
  induction n <;> simp_all [run,step]

theorem mapping_correct (e : Expr) (xs out : List Int) :
    run (xs.length+1) (.mapping e xs out) = .stopped
      ((xs.foldlM (fun out v => do return out ++ [← ArrayIR.value e v]) out).map
        (fun (ys : List Int) => Result.array ys.toArray)) := by
  induction xs generalizing out with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.length_cons,run,step,List.foldlM_cons]
    cases h : ArrayIR.value e v with
    | none => simp [h]
    | some w =>
      simpa only [h,bind,Option.bind,pure] using ih (out ++ [w])

def lowerImperative : ArrayIR.Imperative → Operation | .generate e => .map e
def lowerFunctional : ArrayIR.Functional → Operation | .map e => .map e

theorem imperative_correct (p : ArrayIR.Imperative) (a : Array Int) :
    run (a.size+2) (.ready (lowerImperative p) a) = .stopped ((p.eval a).map Result.array) := by
  cases p with
  | generate e =>
    have h := mapping_correct e a.toList []
    change run (a.size+1) (.mapping e a.toList []) = _
    simp only [Array.length_toList] at h
    rw [h]
    simp only [ArrayIR.Imperative.eval]
    cases a.toList.foldlM (fun out v => do return out ++ [← ArrayIR.value e v]) [] <;> rfl

theorem functional_correct (p : ArrayIR.Functional) (a : Array Int) :
    run (a.size+2) (.ready (lowerFunctional p) a) = .stopped ((p.eval a).map Result.array) := by
  cases p with
  | map e =>
    have h := mapping_correct e a.toList []
    rw [ArrayIR.fold_map] at h
    simpa [run,step,lowerFunctional,ArrayIR.Functional.eval,Option.map_map] using h

theorem load_correct (a : Array Int) (k : Nat) :
    run 1 (.ready (.load k) a) = .stopped ((a[k]?).map Result.scalar) := rfl

def lowerImperativeGet (_ : BoundedReadIR.Imperative) (k : Nat) : Operation := .load k
def lowerFunctionalGet (_ : BoundedReadIR.Functional) (k : Nat) : Operation := .load k

theorem imperative_get_correct (p : BoundedReadIR.Imperative) (a : Array Int) (k : Nat) :
    run 1 (.ready (lowerImperativeGet p k) a) = .stopped ((p.eval a k).map Result.scalar) := rfl

theorem functional_get_correct (p : BoundedReadIR.Functional) (a : Array Int) (k : Nat) :
    run 1 (.ready (lowerFunctionalGet p k) a) = .stopped ((p.eval a k).map Result.scalar) := rfl

end IRComparison.ArrayControlIR
