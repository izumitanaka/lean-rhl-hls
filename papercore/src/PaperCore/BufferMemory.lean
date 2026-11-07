import PaperCore.BufferView

namespace PaperCore.BufferMemory
open AccessAnalysis BufferView

def SlotsFor (slots : Slots) (input : Array) : Prop :=
  ∀ a index buffer, slots a index = some buffer → a = input

theorem view_write (only : SlotsFor slots input) (other : array ≠ input)
    (view : View slots counter heap regs) :
    View slots counter (put heap (array,index) value) regs := by
  intro a affine buffer found
  obtain ⟨v,cell,held⟩ := view a affine buffer found
  have different : (a,affine.eval counter) ≠ (array,index) := by
    intro equal
    have same := (Prod.mk.inj equal).1
    exact other (same.symm.trans (only a affine buffer found))
  exact ⟨v,by simpa [lookup_put_other _ _ _ _ different] using cell,held⟩


end PaperCore.BufferMemory
