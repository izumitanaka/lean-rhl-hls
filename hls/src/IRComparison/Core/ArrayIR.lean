import IRComparison.Core.Common

namespace IRComparison.ArrayIR

def emptyState : State := ⟨fun _ => 0, fun _ => #[]⟩

def value (e : Expr) (v : Int) : Option Int :=
  e.eval (Int.ofNat Nat.zero) v (Int.ofNat Nat.zero) emptyState []

/-- Imperative generation: visit input elements in order and append results. -/
inductive Imperative where
  | generate (body : Expr)
  deriving Repr

def Imperative.eval : Imperative → Array Int → Option (Array Int)
  | .generate e, a => do
      let result ← a.toList.foldlM (fun out v => do return out ++ [← value e v]) []
      return result.toArray

/-- Functional mapping: a pure element computation lifted over the input. -/
inductive Functional where
  | map (body : Expr)
  deriving Repr

def Functional.eval : Functional → Array Int → Option (Array Int)
  | .map e, a => (a.toList.mapM (value e)).map List.toArray

theorem fold_map (f : Int → Option Int) (xs out : List Int) :
    xs.foldlM (fun out v => do return out ++ [← f v]) out =
      (xs.mapM f).map (out ++ ·) := by
  induction xs generalizing out with
  | nil => simp
  | cons v xs ih =>
      simp only [List.foldlM_cons, List.mapM_cons]
      cases h : f v with
      | none => simp [h]
      | some v =>
          simp only [h, bind, Option.bind, pure]
          apply Eq.trans (ih (out ++ [v]))
          cases hxs : xs.mapM f <;> simp [hxs, List.append_assoc]

theorem map_total (f : Int → Option Int) (g : Int → Int)
    (h : ∀ v, f v = some (g v)) (xs : List Int) :
    xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons v xs ih => simp [List.mapM_cons,h,ih]

theorem imperative_correct (e : Expr) (f : Int → Int) (a : Array Int)
    (h : ∀ v, e.eval (Int.ofNat Nat.zero) v (Int.ofNat Nat.zero) emptyState [] = some (f v)) :
    (Imperative.generate e).eval a = some (a.map f) := by
  simp only [Imperative.eval]
  rw [fold_map, map_total (value e) f h]
  simp only [Option.map_some, List.nil_append, bind, Option.bind, pure]
  congr 1
  apply Array.toList_inj.mp
  simp

theorem functional_correct (e : Expr) (f : Int → Int) (a : Array Int)
    (h : ∀ v, e.eval (Int.ofNat Nat.zero) v (Int.ofNat Nat.zero) emptyState [] = some (f v)) :
    (Functional.map e).eval a = some (a.map f) := by
  simp only [Functional.eval]
  rw [map_total (value e) f h]
  simp only [Option.map_some]
  congr 1
  apply Array.toList_inj.mp
  simp

end IRComparison.ArrayIR
