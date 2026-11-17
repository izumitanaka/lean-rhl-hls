import IRComparison.Circuit.SystemVerilog.ConcreteFields

namespace IRComparison.Circuit.SystemVerilog.Concrete

/-- Tail-recursive declaration collection. The accumulator stores parsed wires
in reverse order; it does not impose a budget on declaration count. -/
def readWiresTail.go (input : List Tree) (acc : List Wire) : Option (List Wire × List Tree) :=
  match input with
  | .atom ⟨"wire",_⟩ :: .atom ⟨"signed",_⟩ :: range :: n :: .atom ⟨"=",_⟩ :: e :: .atom ⟨";",_⟩ :: rest => do
      let width ← readWidth range
      let ident ← readName n
      let value ← readExpression e
      if positive : 0 < width then
        readWiresTail.go rest (⟨ident,width,value,positive⟩ :: acc)
      else none
  | rest => some (acc.reverse,rest)

def readWiresTail (input : List Tree) : Option (List Wire × List Tree) := readWiresTail.go input []

theorem readWiresTail_go_eq (input : List Tree) (acc : List Wire) :
    readWiresTail.go input acc = (readWires input).map (fun p => (acc.reverse ++ p.1,p.2)) := by
  induction input using readWires.induct generalizing acc with
  | case1 sw ss range n se e sc rest ih =>
    simp only [readWiresTail.go,readWires]
    cases hw : readWidth range <;> simp only [hw,bind,Option.bind,Option.map_none]
    rename_i width
    cases hn : readName n <;> simp only [hn,bind,Option.bind,Option.map_none]
    rename_i ident
    cases he : readExpression e <;> simp only [he,bind,Option.bind,Option.map_none]
    rename_i value
    split
    · rw [ih]
      cases h : readWires rest <;> simp [h,List.reverse_cons,List.append_assoc,bind,Option.bind]
    · rfl
  | case2 rest notWire =>
    rw [readWiresTail.go,readWires] <;> simp_all

theorem readWiresTail_eq (input : List Tree) : readWiresTail input = readWires input := by
  simp [readWiresTail,readWiresTail_go_eq]

end IRComparison.Circuit.SystemVerilog.Concrete
