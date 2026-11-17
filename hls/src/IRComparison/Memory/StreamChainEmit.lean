import IRComparison.Memory.StreamChainState

namespace IRComparison.StreamChainEmit
open StreamState StreamConsumer StreamChainState WindowPipeline

inductive InputSafe (hidden : List Nat) (stage : Stage) where
  | memory (retained : stage.array ∉ hidden)
  | fifo (closed : LoadsClosed stage.code)

structure Plan (hidden : List Nat) (stage : Stage) (output size : Nat) where
  sender : StreamProducerBlocks.Compiled output size [] stage.code
  fresh : output ∉ hidden
  clear : Clear hidden stage.code
  inputSafe : InputSafe hidden stage
  different : stage.array ≠ output

/-- A stage may consume one channel and produce the next. Previously removed
    arrays stay removed; they are never reconstructed at a stage boundary. -/
def compile (hidden : List Nat) (stage : Stage) (output size : Nat) : Option (Plan hidden stage output size) := do
  if fresh : output ∉ hidden then
    let sender ← StreamProducerBlocks.compile output size [] stage.code
    let clear ← check hidden stage.code
    if different : stage.array ≠ output then
      match checkLoads stage.code with
      | some closed => return ⟨sender,fresh,clear,.fifo closed,different⟩
      | none => if retained : stage.array ∉ hidden then return ⟨sender,fresh,clear,.memory retained,different⟩ else none
    else none
  else none

def Plan.eval (p : Plan hidden stage output size) (x y : Int) (s : State) (q : List Int) : Option (State × List Int) :=
  (StreamProducerBlocks.eval (arrayInput (s.arrays stage.array)) x y p.sender.code [] (erase output s) q []).map
    (fun (t,_,qo) => (erase output t,qo))

inductive Result (hidden : List Nat) (output : Nat) (keys : List Int) :
    Option State → Option (State × List Int) → Prop where
  | none : Result hidden output keys none none
  | some : eraseMany hidden s = t → CommunicationIR.Corresponds (arrayInput (s.arrays output)) keys q →
      Result hidden output keys (some s) (some (t,q))

theorem Plan.correct (p : Plan hidden stage output size) (s : State)
    (inputSize : (s.arrays stage.array).size = stage.size)
    (outputSize : (s.arrays output).size = size) (x y : Int) (q : List Int)
    (hq : stage.fifo = true → CommunicationIR.Corresponds (arrayInput (s.arrays stage.array)) stage.producer q) :
    Result (output::hidden) output p.sender.after (stage.source x y s) (p.eval x y (eraseMany hidden s) q) := by
  have sized : ((eraseMany hidden s).arrays output).size = size := by
    rw [eraseMany_array p.fresh]; exact outputSize
  have relation : Related output size [] (eraseMany hidden s) (erase output (eraseMany hidden s)) [] :=
    ⟨erase_agree _,sized,.nil⟩
  let input := arrayInput ((eraseMany hidden s).arrays stage.array)
  have hp := p.sender.correct input x y [] (eraseMany hidden s)
    (erase output (eraseMany hidden s)) q [] relation
  have sourceEq := stage.correct s inputSize x y q hq
  have inputEq : WindowTransport.eval (arrayInput (s.arrays stage.array)) x y stage.code [] s q =
      WindowTransport.eval input x y stage.code [] s q := by
    cases p.inputSafe with
    | memory retained => simp only [input,eraseMany_array retained]
    | fifo closed => exact closed.correct
  rw [inputEq] at sourceEq
  have erased := p.clear.correct (input:=input) (x:=x) (y:=y) (old:=[]) (s:=s) (q:=q)
  rw [erased] at hp
  cases hs : WindowTransport.eval input x y stage.code [] s q with
  | none =>
    simp only [hs,Option.map_none] at hp sourceEq
    rw [← sourceEq]
    cases ht : StreamProducerBlocks.eval input x y p.sender.code [] (erase output (eraseMany hidden s)) q [] with
    | none =>
      simp only [input] at ht
      simp only [Plan.eval,ht,Option.map_none]; exact .none
    | some pair => rw [ht] at hp; cases hp
  | some pair =>
    obtain ⟨u,rest⟩ := pair
    simp only [hs,Option.map_some] at hp sourceEq
    rw [← sourceEq]
    cases ht : StreamProducerBlocks.eval input x y p.sender.code [] (erase output (eraseMany hidden s)) q [] with
    | none => rw [ht] at hp; cases hp
    | some triple =>
      obtain ⟨v,qi,qo⟩ := triple
      rw [ht] at hp
      cases hp with
      | some hr =>
        simp only [input] at ht
        simp only [Plan.eval,ht,Option.map_some]
        apply Result.some
        · exact StreamConsumer.Agree.erase_eq hr.agree
        · simpa only [eraseMany_array p.fresh] using hr.values

end IRComparison.StreamChainEmit
