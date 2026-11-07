import IRComparison.Circuit.Lower

namespace IRComparison.Circuit

def readArrays : HybridIR.ReadCode → List Nat
  | .pure _ | .register _ => []
  | .memory a _ => [a]
  | .bind a b => readArrays a ++ readArrays b
  | .branch _ a b => readArrays a ++ readArrays b

/-- Include condition reads as well as stores. -/
def allCommandArrays : HybridIR.Cmd → List Nat
  | .skip => []
  | .assign _ e | .send e => readArrays e
  | .store a j e => a :: readArrays j ++ readArrays e
  | .letValue e b | .forRange e b => readArrays e ++ allCommandArrays b
  | .seq a b => allCommandArrays a ++ allCommandArrays b
  | .branch e a b => readArrays e ++ allCommandArrays a ++ allCommandArrays b
  | .repeat _ b => allCommandArrays b

def tailArrays : HybridCompactChainControl.Code → List Nat
  | .finish r => allCommandArrays r.body.target
  | .stage a r tail => a :: allCommandArrays r.body ++ tailArrays tail

def sourceArrays : HybridUnifiedPipeline.Code → List Nat
  | .expanded cs => cs.flatMap fun c =>
      c.input :: c.output.toList ++
        (match c.mode with | .channel a => [a] | .memory a _ _ => [a]) ++
        c.blocks.flatMap (fun b => allCommandArrays b.body)
  | .compact c => c.inputArray :: c.output :: allCommandArrays c.sender.body ++ tailArrays c.tail

def layoutCovers (layout : Array (Nat × Nat)) (code : HybridUnifiedPipeline.Code) : Bool :=
  (sourceArrays code).all fun id => layout.any fun entry => entry.1 == id

theorem layoutCovers_sound (h : layoutCovers layout code = true) (id : Nat) (member : id ∈ sourceArrays code) :
    ∃ size, (id,size) ∈ layout.toList := by
  have hh := (List.all_eq_true.mp h) id member
  simp only [Array.any_eq_true,beq_iff_eq] at hh
  obtain ⟨entry,he,hi⟩ := hh
  refine ⟨layout[entry].2,?_⟩
  rw [← hi]
  change layout[entry] ∈ layout.toList
  exact Array.getElem_mem_toList he

/-- Validate source IDs *before* allocating private snapshot memories. Checking
only the final layout could accidentally interpret an undeclared source array
as a newly allocated snapshot of another array. -/
def checkLayout (layout : Array (Nat × Nat)) (code : HybridUnifiedPipeline.Code) : Except String Unit := do
  unless (layout.toList.map Prod.fst).eraseDups.length = layout.size do
    throw "duplicate original array declarations"
  unless layoutCovers layout code do
    let missing := (sourceArrays code).filter fun id => !(layout.any fun entry => entry.1 == id)
    throw s!"source arrays missing from original layout: {missing.eraseDups}"

end IRComparison.Circuit
