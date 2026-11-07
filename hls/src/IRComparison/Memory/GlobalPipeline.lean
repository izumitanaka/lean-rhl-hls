import IRComparison.Memory.StreamChain
import IRComparison.Memory.GlobalEffects
import IRComparison.Memory.AlternativeStageFusion

namespace IRComparison.GlobalPipeline
open WindowPipeline StreamConsumer StreamChainState PipelineShapes PipelineUse

abbrev Queues := Nat → List Int
abbrev Interface := List (Nat × List (List Int))
def Related (env : Interface) (s : State) (qs : Queues) : Prop :=
  ∀ a alternatives, (a,alternatives) ∈ env → ∃ keys ∈ alternatives,
    CommunicationIR.Corresponds (arrayInput (s.arrays a)) keys (qs a)
def remove (a : Nat) (env : Interface) : Interface := env.filter (fun p => p.1 != a)
def put (qs : Queues) (a : Nat) (q : List Int) : Queues := fun b => if b = a then q else qs b

inductive InputMode where
  | memory (array : Nat) (order : List Int) (fifo : Bool)
  | channel (array : Nat)
  deriving Repr

def InputMode.eval (mode : InputMode) (s : State) (qs : Queues) : Option (List Int) :=
  match mode with
  | .memory a order fifo => if fifo then CommunicationIR.emit (arrayInput (s.arrays a)) order else some []
  | .channel a => some (qs a)

structure Prepared (hidden : List Nat) (env : Interface) (p : Stage) where
  mode : InputMode
  code : List WindowTransport.Block
  clear : StreamChainState.Clear hidden code
  correct : ∀ s, p.Ready s → ∀ qs, Related env s qs → ∀ x y,
    ∃ q, mode.eval (eraseMany hidden s) qs = some q ∧
      (WindowTransport.eval (arrayInput ((eraseMany hidden s).arrays p.array)) x y code [] s q).map Prod.fst = p.source x y s

/-- The global policy fixes a representation for the whole array. A selected
    array is never silently materialized from memory at a later boundary. -/
def prepare (policy hidden : List Nat) (env : Interface) (p : Stage) : Option (Prepared hidden env p) := do
  if selected : p.array ∈ policy then
    let alternatives ← env.lookup p.array
    if member : (p.array,alternatives) ∈ env then
      let view ← p.window
      let receiver ← AlternativeRouting.compile view.blocks alternatives
      let closed ← checkLoads receiver.code
      let clear ← StreamChainState.check hidden receiver.code
      return ⟨.channel p.array,receiver.code,clear,by
        intro s ready qs related x y
        obtain ⟨keys,hk,hq⟩ := related p.array alternatives member
        refine ⟨qs p.array,rfl,?_⟩
        rw [← closed.correct (input:=arrayInput (s.arrays p.array))]
        exact (receiver.eval_correct hk hq [] s x y).trans (view.correct s ready.1 x y)⟩
    else none
  else if retained : p.array ∉ hidden then
    let clear ← StreamChainState.check hidden p.code
    return ⟨.memory p.array p.producer p.fifo,p.code,clear,by
      intro s ready qs related x y
      obtain ⟨q,hq,hc⟩ := p.queue_ready s ready
      refine ⟨q,?_,?_⟩
      · simpa only [InputMode.eval,Stage.queue,eraseMany_array retained] using hq
      · rw [eraseMany_array retained]
        exact p.correct s ready.1 x y q hc⟩
  else none

inductive Action where
  | keep (code : List WindowTransport.Block)
  | send (array : Nat) (code : List StreamProducerBlocks.Block)

structure Instruction where
  input : Nat
  mode : InputMode
  action : Action

def Instruction.eval (instruction : Instruction) (x y : Int) (s : State) (qs : Queues) : Option (State × Queues) := do
  let q ← instruction.mode.eval s qs
  match instruction.action with
  | .keep code =>
    let (t,_) ← WindowTransport.eval (arrayInput (s.arrays instruction.input)) x y code [] s q
    return (t,put qs instruction.input [])
  | .send a code =>
    let (t,_,qo) ← StreamProducerBlocks.eval (arrayInput (s.arrays instruction.input)) x y code [] (erase a s) q []
    return (erase a t,put (put qs instruction.input []) a qo)

inductive Result (hidden : List Nat) (env : Interface) : Option State → Option (State × Queues) → Prop where
  | none : Result hidden env none none
  | some : eraseMany hidden s = t → Related env s qs → Result hidden env (some s) (some (t,qs))

structure Step (sizes : Nat → Nat) (hidden : List Nat) (env : Interface) (p : Stage) where
  instruction : Instruction
  nextHidden : List Nat
  nextEnv : Interface
  correct : ∀ s, Layout sizes s → p.Ready s → ∀ qs, Related env s qs → ∀ x y,
    Result nextHidden nextEnv (p.source x y s) (instruction.eval x y (eraseMany hidden s) qs)

theorem related_rest (h : Related env s qs)
    (preserved : ∀ a alternatives, (a,alternatives) ∈ env → t.arrays a = s.arrays a) :
    Related (remove input env) t (put qs input []) := by
  intro a alternatives member
  have hm := List.mem_filter.mp member
  have different : a ≠ input := by simpa using hm.2
  obtain ⟨keys,hk,hq⟩ := h a alternatives hm.1
  exact ⟨keys,hk,by simpa [put,different,preserved a alternatives hm.1] using hq⟩

/-- Compile one instruction against the policy chosen for the complete program.
    Existing channels survive arbitrary intervening instructions. -/
def compileStep (policy : List Nat) (sizes : Nat → Nat) (hidden : List Nat) (env : Interface) (p : Stage) :
    Option (Step sizes hidden env p) := do
  let prepared ← prepare policy hidden env p
  if untouched : ∀ pair ∈ env, pair.1 ∉ GlobalEffects.blockWrites p.code then
    let outputs := (GlobalEffects.blockWrites p.code).eraseDups.filter (· ∈ policy)
    match selectedOutputs : outputs with
    | [] =>
      -- Prevent an unrecognized access to a selected, not-yet-produced array.
      let _ ← StreamChainState.check policy prepared.code
      return ⟨⟨p.array,prepared.mode,.keep prepared.code⟩,hidden,remove p.array env,by
        intro s layout ready qs related x y
        obtain ⟨q,hq,sourceEq⟩ := prepared.correct s ready qs related x y
        simp only [Instruction.eval,hq,bind,Option.bind]
        rw [prepared.clear.correct]
        cases he : WindowTransport.eval (arrayInput ((eraseMany hidden s).arrays p.array)) x y prepared.code [] s q with
        | none =>
          simp only [he,Option.map_none] at sourceEq
          rw [← sourceEq]
          exact .none
        | some pair =>
          obtain ⟨t,rest⟩ := pair
          simp only [he,Option.map_some] at sourceEq
          rw [← sourceEq]
          apply Result.some rfl
          exact related_rest related (by
            intro a alternatives member
            exact GlobalEffects.stage_preserves p (untouched (a,alternatives) member) ready sourceEq.symm)⟩
    | [output] =>
      if fresh : output ∉ hidden then
        if different : p.array ≠ output then
          let _ ← StreamChainState.check (policy.filter (· != output)) prepared.code
          let sender ← AlternativeProducerBlocks.compile output (sizes output) [[]] prepared.code
          return ⟨⟨p.array,prepared.mode,.send output sender.code⟩,output::hidden,
            (output,sender.after)::remove p.array env,by
            intro s layout ready qs related x y
            obtain ⟨q,hq,sourceEq⟩ := prepared.correct s ready qs related x y
            have sized : ((eraseMany hidden s).arrays output).size = sizes output := by
              rw [eraseMany_array fresh]; exact layout output
            have relation : StreamState.Related output (sizes output) [] (eraseMany hidden s) (erase output (eraseMany hidden s)) [] :=
              ⟨erase_agree _,sized,.nil⟩
            have hp := sender.correct [] (by simp) (arrayInput ((eraseMany hidden s).arrays p.array)) x y []
              (eraseMany hidden s) (erase output (eraseMany hidden s)) q [] relation
            rw [prepared.clear.correct] at hp
            simp only [Instruction.eval,hq,bind,Option.bind]
            cases hs : WindowTransport.eval (arrayInput ((eraseMany hidden s).arrays p.array)) x y prepared.code [] s q <;>
              cases ht : StreamProducerBlocks.eval (arrayInput ((eraseMany hidden s).arrays p.array)) x y sender.code []
                (erase output (eraseMany hidden s)) q [] <;> simp only [hs,ht,Option.map_none,Option.map_some] at hp sourceEq
            · rw [← sourceEq]; exact .none
            · cases hp
            · cases hp
            · rename_i original transformed
              obtain ⟨u,rest⟩ := original
              obtain ⟨v,remaining,qo⟩ := transformed
              cases hp with
              | some member hr =>
                rw [← sourceEq]
                apply Result.some (by simpa only [eraseMany] using StreamConsumer.Agree.erase_eq hr.agree)
                intro a alternatives ha
                rcases List.mem_cons.mp ha with same | hm
                · cases same
                  exact ⟨_,member,by simpa [put,eraseMany_array fresh] using hr.values⟩
                · have restRelated := related_rest (input:=p.array) related (t:=u) (by
                    intro b alternatives hb
                    exact GlobalEffects.stage_preserves p (untouched (b,alternatives) hb) ready sourceEq.symm)
                  obtain ⟨keys,hk,hv⟩ := restRelated a alternatives hm
                  have notOutput : a ≠ output := by
                    intro eq
                    subst a
                    have originalMember := (List.mem_filter.mp hm).1
                    exact (untouched (output,alternatives) originalMember) (by
                      have hmem : output ∈ (GlobalEffects.blockWrites p.code).eraseDups.filter (· ∈ policy) := by
                        change output ∈ outputs
                        rw [selectedOutputs]
                        simp
                      simpa using (List.mem_filter.mp hmem).1)
                  exact ⟨keys,hk,by simpa [put,notOutput] using hv⟩⟩
        else none
      else none
    | _ => none
  else none

inductive Plan (outputs : List Nat) (sizes : Nat → Nat) : List Nat → Interface → List Stage → Type where
  | nil (privateHidden : ∀ a ∈ hidden, a ∉ outputs) : Plan outputs sizes hidden env []
  | cons (first : Step sizes hidden env p) (tail : Plan outputs sizes first.nextHidden first.nextEnv ps) :
      Plan outputs sizes hidden env (p::ps)

def Plan.code : Plan outputs sizes hidden env ps → List Instruction
  | .nil _ => []
  | .cons first tail => first.instruction :: tail.code

def execute (x y : Int) : List Instruction → State → Queues → Option State
  | [],s,_ => some s
  | c::cs,s,qs => do
    let (t,rest) ← c.eval x y s qs
    execute x y cs t rest

theorem Plan.correct (plan : Plan outputs sizes hidden env ps) (s : State)
    (layout : Layout sizes s) (ready : Ready x y ps s) (qs : Queues) (related : Related env s qs) :
    (execute x y plan.code (eraseMany hidden s) qs).map (observe outputs) =
      (source x y ps s).map (observe outputs) := by
  induction plan generalizing s qs with
  | nil privateHidden => exact congrArg some (StreamChain.observe_many privateHidden s)
  | @cons hidden env p ps first tail ih =>
    have h := first.correct s layout ready.1 qs related x y
    simp only [Plan.code,execute,source]
    cases hs : p.source x y s <;> cases ht : first.instruction.eval x y (eraseMany hidden s) qs <;>
      simp only [hs,ht] at h
    · rfl
    · cases h
    · cases h
    · rename_i u pair
      obtain ⟨v,rest⟩ := pair
      cases h with
      | some same hr =>
        subst v
        exact ih u (layout.after (stage_same p ready.1 hs)) (ready.2 u hs) rest hr

def compilePolicy (outputs : List Nat) (sizes : Nat → Nat) (policy hidden : List Nat) (env : Interface) :
    (ps : List Stage) → Option (Plan outputs sizes hidden env ps)
  | [] =>
    if privateHidden : ∀ a ∈ hidden, a ∉ outputs then
      if policy.all (· ∈ hidden) then some (.nil privateHidden) else none
    else none
  | p::ps => do
    let first ← compileStep policy sizes hidden env p
    return .cons first (← compilePolicy outputs sizes policy first.nextHidden first.nextEnv ps)

structure Program (outputs : List Nat) (sizes : Nat → Nat) (ps : List Stage) where
  policy : List Nat
  plan : Plan outputs sizes [] [] ps

def candidates (outputs : List Nat) (ps : List Stage) : List Nat :=
  (ps.flatMap (fun p => GlobalEffects.blockWrites p.code)).eraseDups.filter (· ∉ outputs)

def combinations (count : Nat) : List Nat → List (List Nat)
  | [] => if count = 0 then [[]] else []
  | a::as => match count with
    | 0 => [[]]
    | n+1 => (combinations n as).map (a::·) ++ combinations (n+1) as

/-- Try whole-array policies in descending number of eliminated arrays.
    Every candidate is validated against every instruction, in source order. -/
def compile (outputs : List Nat) (sizes : Nat → Nat) (ps : List Stage) : Option (Program outputs sizes ps) :=
  let arrays := candidates outputs ps
  ((List.range (arrays.length+1)).reverse.flatMap (fun n => combinations n arrays)).findSome? fun policy =>
    (compilePolicy outputs sizes policy [] [] ps).map (fun plan => ⟨policy,plan⟩)

def Program.eval (program : Program outputs sizes ps) (x y : Int) (s : State) :=
  execute x y program.plan.code s (fun _ => [])

theorem Program.correct (program : Program outputs sizes ps) (s : State)
    (layout : Layout sizes s) (ready : Ready x y ps s) :
    (program.eval x y s).map (observe outputs) = (source x y ps s).map (observe outputs) :=
  program.plan.correct s layout ready (fun _ => []) (by intro a alternatives h; cases h)

end IRComparison.GlobalPipeline
