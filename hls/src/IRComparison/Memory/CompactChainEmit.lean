import IRComparison.Memory.CompactStage

namespace IRComparison.CompactChainEmit
open CompactStage StreamState StreamConsumer StreamChainState

structure Plan (hidden : List Nat) (stage : Stage) (supplier : CompactSequence.Seq) (output size : Nat) where
  duplex : CompactDuplex.Plan output size stage.code supplier
  fresh : output ∉ hidden
  clear : CompactStage.Clear hidden stage.code.body

def compile (hidden : List Nat) (stage : Stage) (supplier : CompactSequence.Seq) (output size : Nat) :
    Option (Plan hidden stage supplier output size) := do
  if fresh : output ∉ hidden then
    return ⟨← CompactDuplex.compile output size stage.code supplier,fresh,← CompactStage.check hidden stage.code.body⟩
  else none

def compileWithSMT (hidden : List Nat) (stage : Stage) (supplier : CompactSequence.Seq) (output size : Nat)
    (directory : System.FilePath) : IO (Option (Plan hidden stage supplier output size)) := do
  if fresh : output ∉ hidden then
    let some clear := CompactStage.check hidden stage.code.body | return none
    let some duplex ← CompactDuplex.compileWithSMT output size stage.code supplier directory | return none
    return some ⟨duplex,fresh,clear⟩
  else return none

def Plan.eval (p : Plan hidden stage supplier output size) (x y : Int) (s : State) (q : List Int) : Option (State × List Int) :=
  (p.duplex.code.eval x y (erase output s) q).map (fun (t,out) => (erase output t,out))

inductive Result (hidden : List Nat) (output : Nat) (keys : List Int) :
    Option State → Option (State × List Int) → Prop where
  | none : Result hidden output keys none none
  | some : eraseMany hidden s = t → CommunicationIR.Corresponds (arrayInput (s.arrays output)) keys q →
      Result hidden output keys (some s) (some (t,q))

theorem Plan.correct (p : Plan hidden stage supplier output size) (s : State)
    (inputSize : (s.arrays stage.array).size = stage.size)
    (outputSize : (s.arrays output).size = size) (x y : Int) (q : List Int)
    (hq : CommunicationIR.Corresponds (arrayInput (s.arrays stage.array)) supplier.entries q) :
    Result (output::hidden) output p.duplex.sender.sequence.entries
      (stage.source x y s) (p.eval x y (eraseMany hidden s) q) := by
  have sized : ((eraseMany hidden s).arrays output).size = size := by
    rw [eraseMany_array p.fresh]; exact outputSize
  have relation : Related output size [] (eraseMany hidden s) (erase output (eraseMany hidden s)) [] :=
    ⟨erase_agree _,sized,.nil⟩
  let input := arrayInput (s.arrays stage.array)
  have hp := p.duplex.sender.correct (input:=input) (x:=x) (y:=y)
    (eraseMany hidden s) (erase output (eraseMany hidden s)) relation
  rw [p.clear.correct,stage.correct s inputSize x y] at hp
  simp only [Plan.eval,p.duplex.routing_correct _ q hq]
  cases hs : stage.source x y s <;>
    cases ht : p.duplex.sender.code.eval input x y (erase output (eraseMany hidden s)) <;>
    simp only [hs,ht,Option.map_none,Option.map_some] at hp
  · exact .none
  · cases hp
  · cases hp
  · rename_i u pair
    obtain ⟨t,qo⟩ := pair
    cases hp with
    | some hr =>
      apply Result.some
      · exact StreamConsumer.Agree.erase_eq hr.agree
      · simpa only [eraseMany_array p.fresh] using hr.values

end IRComparison.CompactChainEmit
