import IRComparison.Memory.SymbolicWindowBody

namespace IRComparison.SymbolicWindowSchedule
open WindowSchedule AffineAddress SymbolicWindowExpr

inductive Load where
  | memory (address : Linear)
  | saved (slot : Nat)
  deriving Repr, DecidableEq

def Load.eval (input : Input) (i : Int) (old : List Int) : Load → Option Int
  | .memory a => input (a.eval i)
  | .saved n => old[n]?

def execute (input : Input) (i : Int) (old : List Int) : List Load → Option (List Int)
  | [] => some []
  | l::ls => do return (← l.eval input i old)::(← execute input i old ls)

def initial (coefficient : Int) (offsets : List Int) : List Load :=
  offsets.map (fun o => .memory ⟨coefficient,o⟩)

def refill (coefficient displacement : Int) (previous : List Int) : List Int → List Load
  | [] => []
  | o::os => (match slot (o+displacement) previous with
      | some j => .saved j.val
      | none => .memory ⟨coefficient,o⟩) :: refill coefficient displacement previous os

theorem initial_correct (offsets : List Int) :
    execute input i old (initial coefficient offsets) = CommunicationIR.emit input (keys coefficient offsets i) := by
  induction offsets with
  | nil => rfl
  | cons o os ih =>
    simp only [initial,keys] at ih
    simp [initial,execute,Load.eval,Linear.eval,keys,CommunicationIR.emit,ih]

theorem refill_correct (held : Matches input (keys coefficient previous i) old) (offsets : List Int) :
    execute input (i+stride) old (refill coefficient (coefficient*stride) previous offsets) =
      CommunicationIR.emit input (keys coefficient offsets (i+stride)) := by
  induction offsets with
  | nil => rfl
  | cons o os ih =>
    simp only [refill,execute,keys,List.map_cons,CommunicationIR.emit]
    cases hs : slot (o+coefficient*stride) previous with
    | none => simpa [Load.eval,Linear.eval,ih,keys]
    | some j =>
      have hkey : (keys coefficient previous i)[j.val]? = some (coefficient*(i+stride)+o) := by
        simp [keys,List.getElem?_map,j.property,Int.mul_add,Int.add_assoc,Int.add_comm,Int.add_left_comm]
      obtain ⟨len,point⟩ := held
      obtain ⟨v,hv,hi⟩ := point j.val _ hkey
      simp [Load.eval,hv,hi,ih,keys]

def coverageGuards (size : Nat) (coefficient : Int) (offsets : List Int) : List Linear :=
  offsets.flatMap (fun o => [⟨coefficient,o⟩,⟨-coefficient,(size:Int)-1-o⟩])

theorem coverage_sound (h : Valid (coverageGuards size coefficient offsets) i) :
    ∀ j ∈ keys coefficient offsets i, 0 ≤ j ∧ j < (size:Int) := by
  intro j hj
  obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hj
  have lo := h ⟨coefficient,o⟩ (List.mem_flatMap.mpr ⟨o,ho,by simp⟩)
  have hi := h ⟨-coefficient,(size:Int)-1-o⟩ (List.mem_flatMap.mpr ⟨o,ho,by simp⟩)
  simp only [Linear.eval,Int.neg_mul] at lo hi
  constructor <;> omega

end IRComparison.SymbolicWindowSchedule
