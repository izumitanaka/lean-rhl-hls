import PaperCore.SMT.SMTSemantics

namespace PaperCore.SMTMeaning

/-- SMT evaluation depends only on free variables, including under binders. -/
theorem eval_free_congr (f : SMT) (zero : ZeroDivision) (params a b : String → Int)
    (agree : ∀ x ∈ f.freeVars, a x = b x) :
    eval zero params a f = eval zero params b f := by
  cases f with
  | num n => simp [eval]
  | param x => simp [eval]
  | var x => simp [eval, agree x (by simp [SMT.freeVars])]
  | app op fs =>
    simp only [eval]
    congr 1
    apply List.map_congr_left
    intro f hf
    apply eval_free_congr f zero params a b
    intro x hx
    apply agree x
    simp only [SMT.freeVars, List.mem_eraseDups, List.mem_flatMap]
    exact ⟨f, hf, hx⟩
  | all names f =>
    simp only [eval]
    congr 2
    apply propext
    have transfer (a b : String → Int)
        (agree : ∀ x ∈ (SMT.all names f).freeVars, a x = b x)
        (h : ∀ next, AgreeOutside names a next → eval zero params next f = .boolean true) :
        ∀ next, AgreeOutside names b next → eval zero params next f = .boolean true := by
      intro next hn
      let prev := fun x => if x ∈ names then next x else a x
      have hp : AgreeOutside names a prev := by
        intro x hx
        simp [prev, hx]
      have he : eval zero params prev f = eval zero params next f := by
        apply eval_free_congr f zero params prev next
        intro x hx
        by_cases hn' : x ∈ names
        · simp [prev, hn']
        · have hab := agree x (by simpa [SMT.freeVars, hx] using hn')
          simp [prev, hn', hn x hn', hab]
      rw [← he]
      exact h prev hp
    exact ⟨transfer a b agree, transfer b a (fun x hx => (agree x hx).symm)⟩
termination_by f

theorem quantify_same (names : List String) (f : SMT) (zero : ZeroDivision)
    (params vars : String → Int)
    (h : eval zero params vars (SMT.quantify names f) = .boolean true) :
    eval zero params vars f = .boolean true := by
  unfold SMT.quantify at h
  split at h
  · exact h
  · simp only [eval, Value.boolean.injEq, decide_eq_true_eq] at h
    exact h vars (fun _ _ => rfl)

/-- Closing all free variables allows instantiation at any source valuation. -/
theorem close_instantiate (f : SMT) (zero : ZeroDivision) (params before vars : String → Int)
    (h : eval zero params before (SMT.quantify f.freeVars f) = .boolean true) :
    eval zero params vars f = .boolean true := by
  by_cases empty : f.freeVars.isEmpty = true
  · have same := quantify_same f.freeVars f zero params before h
    rw [← eval_free_congr f zero params before vars]
    · exact same
    · intro x hx
      have : f.freeVars = [] := List.isEmpty_iff.mp empty
      simp [this] at hx
  · simp [SMT.quantify, empty, eval] at h
    let next := fun x => if x ∈ f.freeVars then vars x else before x
    have outside : AgreeOutside f.freeVars.eraseDups before next := by
      intro x hx
      simp only [List.mem_eraseDups] at hx
      simp [next, hx]
    have same := h next outside
    rw [← eval_free_congr f zero params next vars]
    · exact same
    · intro x hx
      simp [next, hx]

private theorem booleans_true_members (vs : List Value)
    (h : (match booleans vs with | some bs => Value.boolean (bs.all id) | none => .invalid) =
      .boolean true) : ∀ v ∈ vs, v = .boolean true := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    cases v with
    | integer n => simp [booleans] at h
    | invalid => simp [booleans] at h
    | boolean b =>
      cases hb : booleans vs with
      | none => simp [booleans, hb] at h
      | some bs =>
        simp [booleans, hb] at h
        intro v hv
        rcases List.mem_cons.mp hv with hv | hv
        · simpa [hv] using congrArg Value.boolean h.1
        · exact ih (by simp [hb, h.2]) v hv

theorem conj_member (fs : List SMT) (f : SMT) (zero : ZeroDivision)
    (params vars : String → Int)
    (h : eval zero params vars (SMT.conj fs) = .boolean true) (hf : f ∈ fs) :
    eval zero params vars f = .boolean true := by
  apply booleans_true_members (fs.map (eval zero params vars))
  · simpa [SMT.conj, eval, operation] using h
  · exact List.mem_map.mpr ⟨f,hf,rfl⟩

theorem conj_intro (fs : List SMT) (zero : ZeroDivision) (params vars : String → Int)
    (members : ∀ f ∈ fs, eval zero params vars f = .boolean true) :
    eval zero params vars (SMT.conj fs) = .boolean true := by
  have booleans_true : booleans (fs.map (eval zero params vars)) = some (fs.map (fun _ => true)) := by
    induction fs with
    | nil => rfl
    | cons f fs ih =>
      have head := members f (by simp)
      have tail := ih (fun g hg => members g (by simp [hg]))
      simp [List.map_cons,booleans,head,tail]
  simp [SMT.conj,eval,operation,booleans_true]

theorem implies_elim (a b : SMT) (zero : ZeroDivision) (params vars : String → Int)
    (h : eval zero params vars (SMT.implies a b) = .boolean true)
    (ha : eval zero params vars a = .boolean true) :
    eval zero params vars b = .boolean true := by
  cases hb : eval zero params vars b <;>
    simp_all [SMT.implies, SMT.op, eval, operation]

#print axioms close_instantiate
#print axioms conj_member
end PaperCore.SMTMeaning
