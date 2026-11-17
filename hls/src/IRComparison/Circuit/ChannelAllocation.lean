import IRComparison.Circuit.ChannelLower

namespace IRComparison.Circuit.ChannelLower
open HybridIR

/-- Allocate private buffers once. Values use the existing word range;
definedness cells are separate one-bit quantities. The checked backend rejects
programs whose actual arithmetic cannot fit the declared ranges. -/
def reserve (c : ChannelCmd) (b : Build) : Build :=
  {b with wires := b.wires ++ Array.ofFn (fun k : Fin (2*bufferCount c) =>
    if k.val % 2 = 0 then wordRange else ⟨0,1⟩)}

def bankFor (c : ChannelCmd) (b : Build) : Buffers := ⟨b.wires.size,bufferCount c⟩

theorem reserve_size : (reserve c b).wires.size = (bankFor c b).stop := by
  simp [reserve,bankFor,Buffers.stop]


end IRComparison.Circuit.ChannelLower
