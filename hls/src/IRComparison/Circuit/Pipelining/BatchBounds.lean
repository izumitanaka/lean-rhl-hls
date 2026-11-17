import IRComparison.Circuit.Pipelining.Bounds
import IRComparison.Circuit.Pipelining.Allocation

namespace IRComparison.Circuit.Pipelining

def ContentBound (f : Frame) : Cell → Content → Prop
  | .reg _,.scalar v => wordRange.Contains v
  | .wire k,.scalar v => (f.get k).Contains v
  | .array _,.array xs => ∀ (n : Nat) (v : Int), xs[n]? = some v → wordRange.Contains v
  | .queue _,.queue xs => ∀ v ∈ xs, wordRange.Contains v
  | _,_ => True

theorem get_bound (h : WidthBound f p) (c : Cell) : ContentBound f c (get p c) := by
  cases c with
  | reg k => exact h.data.regs k
  | wire k => exact h.wires k
  | array k => exact h.data.arrays k
  | queue k => exact h.queues k

theorem put_bound (h : WidthBound f p) (hv : ContentBound f c v) :
    WidthBound f (put p c v) := by
  cases c <;> cases v <;> try exact h
  case reg.scalar k v => exact ⟨h.data.set hv,h.wires,h.queues⟩
  case wire.scalar k v =>
    refine ⟨h.data,?_,h.queues⟩
    intro n; change (f.get n).Contains (if n = k then v else p.wires n)
    split
    · rename_i eq; subst n; exact hv
    · exact h.wires n
  case array.array k v => exact ⟨h.data.replace hv,h.wires,h.queues⟩
  case queue.queue k v =>
    refine ⟨h.data,h.wires,?_⟩
    intro n x hx
    change x ∈ (if n = k then v else p.queues n) at hx
    split at hx
    · exact hv x hx
    · exact h.queues n x hx

theorem get_put_self (u : Update) (good : GoodUpdate u) (p : Payload) :
    get (put p u.1 u.2) u.1 = u.2 := by
  rcases u with ⟨c,v⟩
  cases c <;> cases v <;> simp_all [GoodUpdate,get,put,IRComparison.State.set]

theorem get_commit_absent (us : List Update) (p : Payload) (hc : c ∉ us.map Prod.fst) :
    get (commit us p) c = get p c := by
  induction us generalizing p with
  | nil => rfl
  | cons u us ih =>
    have hn : c ≠ u.1 ∧ c ∉ us.map Prod.fst := by simpa using hc
    rw [show commit (u::us) p = commit us (put p u.1 u.2) from rfl,ih _ hn.2]
    exact get_put_other p u.1 c u.2 hn.1.symm

theorem get_commit_member (us : List Update) (p : Payload) (unique : (us.map Prod.fst).Nodup)
    (good : ∀ u ∈ us, GoodUpdate u) (hu : u ∈ us) : get (commit us p) u.1 = u.2 := by
  induction us generalizing p with
  | nil => cases hu
  | cons v vs ih =>
    have hn : v.1 ∉ vs.map Prod.fst ∧ (vs.map Prod.fst).Nodup := by simpa using unique
    rcases List.mem_cons.mp hu with rfl | hu
    · change get (commit vs (put p u.1 u.2)) u.1 = u.2
      rw [get_commit_absent _ _ hn.1,get_put_self u (good u (by simp))]
    · exact ih _ hn.2 (fun u hu => good u (by simp [hu])) hu

theorem prepare_bounds (h : actionWidthSafe f a = true) (hb : WidthBound f p)
    (hp : prepare cap a p = some us) : ∀ u ∈ us, ContentBound f u.1 u.2 := by
  have eval : a.eval cap p = some (commit us p) := by rw [← prepare_correct,hp]; rfl
  have bound := action_width_preserved h hb eval
  have shape := prepare_shape hp
  have unique : (us.map Prod.fst).Nodup := by rw [shape.1]; cases a <;> simp [actionWrites]
  intro u hu
  have hg := get_bound bound u.1
  rwa [get_commit_member us p unique shape.2 hu] at hg

theorem commit_bound (us : List Update) (h : ∀ u ∈ us, ContentBound f u.1 u.2)
    (hb : WidthBound f p) : WidthBound f (commit us p) := by
  induction us generalizing p with
  | nil => exact hb
  | cons u us ih => exact ih (fun v hv => h v (by simp [hv])) (put_bound hb (h u (by simp)))

theorem allPrepared_bounds (as : List Action) (h : ∀ a ∈ as, actionWidthSafe f a = true)
    (hb : WidthBound f p) (hp : allPrepared cap p as = some us) :
    ∀ u ∈ us, ContentBound f u.1 u.2 := by
  induction as generalizing us with
  | nil => simp [allPrepared] at hp; subst us; simp
  | cons a as ih =>
    cases ha : prepare cap a p <;> cases hs : allPrepared cap p as <;> simp [allPrepared,ha,hs] at hp
    subst us
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact prepare_bounds (h a (by simp)) hb ha u hu
    · exact ih (fun b hm => h b (by simp [hm])) hs u hu

/-- Unlike serial equivalence, width preservation does not require disjoint
read/write sets. This matters when an old value is read for the last time on
the same edge that its physical holding register is reused. -/
theorem batch_width_preserved (as : List Action) (h : ∀ a ∈ as, actionWidthSafe f a = true)
    (hb : WidthBound f p) (he : clock cap as p = some q) : WidthBound f q := by
  simp only [clock,clockFrom_prepared] at he
  cases hp : allPrepared cap p as <;> simp [hp] at he
  subst q
  exact commit_bound _ (allPrepared_bounds as h hb hp) hb

def batchWidthsSafe (f : Frame) (bs : Batches) : Bool := bs.all (fun as => as.all (actionWidthSafe f))

end IRComparison.Circuit.Pipelining
