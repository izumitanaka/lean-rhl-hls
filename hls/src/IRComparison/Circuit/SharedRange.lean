import IRComparison.Circuit.SharedLowerSound
import IRComparison.Circuit.TransferSound

namespace IRComparison.Circuit.Shared

/-- Counter guards are already small ordinary leaves. Inspecting a leaf never
unfolds graph references or reconstructs a tree. Other guards conservatively
retain the incoming frame. -/
def refine (f : Frame) (p : Program) (yes : Bool) : Frame :=
  match p with
  | ⟨[.input e],0⟩ => f.refine e yes
  | _ => f

theorem refine_sound (f : Frame) (hb : InputsBound s w f.get)
    (he : p.eval s w = some v) (hv : (v != 0) = yes) : (refine f p yes).contains w := by
  unfold refine
  split
  · rename_i e eq
    exact Frame.refine_sound f hb (by simpa [Program.eval,values,get,Node.eval] using he) hv
  · exact hb.wires

instance : ExpressionRange Program where
  range wr p := p.range wr
  correct := by intro p s w wr v hb he; exact p.range_correct hb he
  refine := Shared.refine
  refine_sound := by intro f s w e v yes hb he hv; exact Shared.refine_sound f hb he hv

end IRComparison.Circuit.Shared
