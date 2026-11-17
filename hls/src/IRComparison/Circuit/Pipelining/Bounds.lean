import IRComparison.Circuit.Pipelining.Schedule
import IRComparison.Circuit.TransferSound

namespace IRComparison.Circuit.Pipelining

def actionWidthSafe (f : Frame) (a : Action) : Bool :=
  match transfer f (a.node 0) with
  | .error _ => false
  | .ok edges => edges.all (fun e => e.2.within f)

def WidthBound (f : Frame) (p : Payload) : Prop := RuntimeBound f (p.at 0)

theorem action_width_preserved (h : actionWidthSafe f a = true)
    (bound : WidthBound f p) (he : a.eval cap p = some q) : WidthBound f q := by
  have ex : execute cap (a.node 0) (p.at 0) = some (q.at 0) := by
    rw [Action.execute_eq,he]; rfl
  cases ht : transfer f (a.node 0) with
  | error why => simp [actionWidthSafe,ht] at h
  | ok edges =>
    have tr := transfer_sound (a.node 0) bound ht ex
    rcases tr with bad | ⟨g,member,hg⟩
    · cases bad
    · have all : edges.all (fun e => e.2.within f) = true := by simpa [actionWidthSafe,ht] using h
      exact hg.within (List.all_eq_true.mp all _ member)

theorem list_width_preserved (as : List Action)
    (h : ∀ a ∈ as, actionWidthSafe f a = true)
    (bound : WidthBound f p) (he : evalList (Action.eval cap) as p = some q) : WidthBound f q := by
  induction as generalizing p with
  | nil => cases he; exact bound
  | cons a as ih =>
    cases ha : a.eval cap p with
    | none => simp [evalList,ha] at he
    | some r =>
      simp only [evalList,ha,Option.bind_some] at he
      exact ih (fun b hb => h b (by simp [hb])) (action_width_preserved (h a (by simp)) bound ha) he

theorem clock_width_preserved (as : List Action) (hs : BundleSafe as)
    (h : ∀ a ∈ as, actionWidthSafe f a = true)
    (bound : WidthBound f p) (he : clock cap as p = some q) : WidthBound f q := by
  rw [clock_correct _ hs] at he
  exact list_width_preserved as h bound he

def widthsSafe (f : Frame) (code : Array Action) (cycles : Cycles) : Bool :=
  cycles.all (fun ids => ids.all (fun id => actionWidthSafe f (actionAt code id)))

theorem clock_bound_head (hs : safe code (ids :: rest) = true)
    (hw : widthsSafe f code (ids :: rest) = true) (bound : WidthBound f p)
    (he : clock cap (ids.map (actionAt code)) p = some q) : WidthBound f q := by
  have hs' : BundleSafe (ids.map (actionAt code)) ∧ safe code rest = true := by simpa [safe] using hs
  have hw' : ids.all (fun id => actionWidthSafe f (actionAt code id)) = true ∧ widthsSafe f code rest = true := by
    simpa [widthsSafe] using hw
  apply clock_width_preserved _ hs'.1 _ bound he
  intro a ha
  obtain ⟨id,hi,rfl⟩ := List.mem_map.mp ha
  exact List.all_eq_true.mp hw'.1 _ hi

end IRComparison.Circuit.Pipelining
