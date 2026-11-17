import IRComparison.Core.Relational

/-! Generic relational rules for scheduling existing partial state actions.
The checker is executable and its soundness is proved once, not assumed for
each input. A schedule contains operation identifiers, never replacement code. -/
namespace IRComparison.Circuit.Pipelining

def evalList (act : α → σ → Option σ) : List α → σ → Option σ
  | [], s => some s
  | a :: as, s => (act a s).bind (evalList act as)

theorem evalList_append (act : α → σ → Option σ) (as bs : List α) (s : σ) :
    evalList act (as ++ bs) s = (evalList act as s).bind (evalList act bs) := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append, evalList, funext ih, Option.bind_assoc]

/-- Relational judgement; both computations may fail. -/
abbrev RHL (R : σ → σ → Prop) (a b : σ → Option σ)
    (S : Option σ → Option σ → Prop) : Prop := Relational.Judgment R a b S

def Commutes (act : α → σ → Option σ) (a b : α) : Prop :=
  ∀ s, (act a s).bind (act b) = (act b s).bind (act a)

theorem rhl_swap (h : Commutes act a b) :
    RHL Eq (evalList act [a,b]) (evalList act [b,a]) Eq := by
  intro s t e; subst t
  simpa [evalList] using h s

/-- Extract exactly one requested operation, crossing only certified
independent operations. Duplicate/missing identifiers cannot disappear. -/
def pull [DecidableEq α] (independent : α → α → Bool) (wanted : α) :
    List α → Option (List α)
  | [] => none
  | a :: as => if wanted = a then some as else
      if independent wanted a then (pull independent wanted as).map (a :: ·) else none

theorem pull_sound [DecidableEq α] (act : α → σ → Option σ)
    (independent : α → α → Bool)
    (sound : ∀ a b, independent a b = true → Commutes act a b)
    (as rest : List α) (wanted : α) (h : pull independent wanted as = some rest) :
    ∀ s, evalList act as s = (act wanted s).bind (evalList act rest) := by
  induction as generalizing rest with
  | nil => simp [pull] at h
  | cons a as ih =>
    by_cases eq : wanted = a
    · subst a; simp [pull] at h; subst rest; intro s; rfl
    · by_cases hi : independent wanted a = true
      · cases hp : pull independent wanted as with
        | none => simp [pull,eq,hi,hp] at h
        | some tail =>
          simp [pull,eq,hi,hp] at h; subst rest
          intro s
          simp only [evalList, funext (ih tail hp), ← Option.bind_assoc]
          rw [← sound wanted a hi s]
      · simp [pull,eq,hi] at h

def reorder [DecidableEq α] (independent : α → α → Bool) : List α → List α → Bool
  | [], source => source.isEmpty
  | a :: target, source => match pull independent a source with
    | none => false
    | some rest => reorder independent target rest

theorem reorder_sound [DecidableEq α] (act : α → σ → Option σ)
    (independent : α → α → Bool)
    (sound : ∀ a b, independent a b = true → Commutes act a b)
    (target source : List α) (h : reorder independent target source = true) :
    ∀ s, evalList act target s = evalList act source s := by
  induction target generalizing source with
  | nil => cases source <;> simp_all [reorder,evalList]
  | cons a target ih =>
    cases hp : pull independent a source with
    | none => simp [reorder,hp] at h
    | some rest =>
      simp only [reorder,hp] at h
      intro s
      rw [pull_sound act independent sound source rest a hp s]
      simp only [evalList, funext (ih rest h)]

theorem reorder_rhl [DecidableEq α] (act : α → σ → Option σ)
    (independent : α → α → Bool)
    (sound : ∀ a b, independent a b = true → Commutes act a b)
    (h : reorder independent target source = true) :
    RHL Eq (evalList act source) (evalList act target) Eq := by
  intro s t e; subst t
  exact (reorder_sound act independent sound target source h s).symm

end IRComparison.Circuit.Pipelining
