import PaperCore.LoopCursorSMT

namespace PaperCore.OrdinalCursorSMT
open AccessAnalysis

/-- Reparameterize only the logical cursor constraints; the source loop and
    generated scalar calculations retain their original counter and step. -/
def reindex (start delta : Int) (event : SymbolicAccess) : SymbolicAccess :=
  {event with index := ⟨event.index.scale*delta,event.index.scale*start+event.index.offset⟩}

theorem reindex_eval (event : SymbolicAccess) :
    (reindex start delta event).eval ordinal = event.eval (start+ordinal*delta) := by
  cases event with
  | mk direction array index =>
    simp [reindex,SymbolicAccess.eval,Affine.eval,Int.mul_add,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.add_comm,Int.add_left_comm,Int.add_assoc]

def query (events : List SymbolicAccess) (start delta trips : Int) (arrays : List Array) (layout : BodyCursorSMT.Layout) : PaperCore.SMT :=
  LoopCursorSMT.query ⟨fun _ => none,events.map (reindex start delta)⟩ ⟨1,0⟩ arrays layout 0 trips trips 1

def shape (params : String → Int) (arrays : List Array) (layout : BodyCursorSMT.Layout)
    (start delta trips k : Int) (indices : IndexMap) : Prop :=
  ∃ t, k = start+t*delta ∧ LoopCursorSMT.shape params arrays layout 0 trips t indices

theorem query_sound_step {delta : Int}
    (endPoint : stop = start+trips*delta)
    (tracked : ∀ event ∈ events, event.array ∈ arrays)
    (model : PaperCore.SMTMeaning.eval zero params vars (query events start delta trips arrays layout) = .boolean true) :
    ∀ k indices, shape params arrays layout start delta trips k indices → k ≠ stop →
      ∃ after, DirectBody.consume indices (events.map (SymbolicAccess.eval k)) = some after ∧
        shape params arrays layout start delta trips (k+delta) after := by
  have valid := LoopCursorSMT.query_sound (summary := ⟨fun _ => none,events.map (reindex start delta)⟩)
    (by
      intro e member
      obtain ⟨original,he,rfl⟩ := List.mem_map.mp member
      exact tracked original he) model
  intro k indices holds nonzero
  obtain ⟨t,counter,atHead⟩ := holds
  have notEnd : t ≠ trips := by intro same; subst t; exact nonzero (counter.trans endPoint.symm)
  obtain ⟨after,consumed,next⟩ := valid t indices atHead notEnd
  refine ⟨after,?_,t+1,?_,?_⟩
  · simpa only [List.map_map,Function.comp_def,reindex_eval,← counter] using consumed
  · rw [counter,Int.add_mul,Int.one_mul,Int.add_assoc]
  · simpa [Affine.eval] using next

#print axioms query_sound_step
end PaperCore.OrdinalCursorSMT
