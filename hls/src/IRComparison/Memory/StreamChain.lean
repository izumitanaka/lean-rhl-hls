import IRComparison.Memory.StreamChainEmit

namespace IRComparison.StreamChain
open WindowPipeline StreamChainState StreamConsumer PipelineShapes PipelineUse

inductive Plan (outputs : List Nat) (sizes : Nat → Nat) : List Nat → Stage → List Stage → Type where
  | last (clear : StreamChainState.Clear hidden stage.code) (closed : LoadsClosed stage.code) :
      Plan outputs sizes hidden stage []
  | next (emit : StreamChainEmit.Plan hidden stage following.array following.size)
      (order : following.producer = emit.sender.after) (sizeOK : following.size = sizes following.array)
      (privateOutput : following.array ∉ outputs)
      (tail : Plan outputs sizes (following.array::hidden) following rest) :
      Plan outputs sizes hidden stage (following::rest)

def compile (outputs : List Nat) (sizes : Nat → Nat) (hidden : List Nat) (stage : Stage) :
    (rest : List Stage) → Option (Plan outputs sizes hidden stage rest)
  | [] => do return .last (← StreamChainState.check hidden stage.code) (← checkLoads stage.code)
  | following::rest => do
    if privateOutput : following.array ∉ outputs then
      if sizeOK : following.size = sizes following.array then
        let emit ← StreamChainEmit.compile hidden stage following.array following.size
        if order : following.producer = emit.sender.after then
          return .next emit order sizeOK privateOutput (← compile outputs sizes (following.array::hidden) following rest)
        else none
      else none
    else none

def Plan.eval (p : Plan outputs sizes hidden stage rest) (x y : Int) (s : State) (q : List Int) : Option State :=
  match p with
  | .last .. => (WindowTransport.eval (fun _ => none) x y stage.code [] s q).map Prod.fst
  | .next emit _ _ _ tail => do
      let (t,qo) ← emit.eval x y s q
      tail.eval x y t qo

def Plan.channels : Plan outputs sizes hidden stage rest → List Nat
  | .last .. => []
  | @Plan.next _ _ _ _ following _ _ _ _ _ tail => following.array :: tail.channels

theorem observe_many (privateHidden : ∀ a ∈ hidden, a ∉ outputs) (s : State) :
    observe outputs (eraseMany hidden s) = observe outputs s := by
  induction hidden with
  | nil => rfl
  | cons a as ih =>
    rw [eraseMany,observe_erase (privateHidden a (by simp))]
    exact ih (by intro b hb; exact privateHidden b (by simp [hb]))

theorem Plan.correct (p : Plan outputs sizes hidden stage rest) (s : State)
    (layout : Layout sizes s) (ready : Ready x y (stage::rest) s)
    (privateHidden : ∀ a ∈ hidden, a ∉ outputs)
    (hq : stage.fifo = true → CommunicationIR.Corresponds (arrayInput (s.arrays stage.array)) stage.producer q) :
    (p.eval x y (eraseMany hidden s) q).map (observe outputs) =
      (source x y (stage::rest) s).map (observe outputs) := by
  induction p generalizing s q with
  | @last hidden stage clear closed =>
    have hs := stage.correct s ready.1.1 x y q hq
    rw [closed.correct (other:=fun _ => none)] at hs
    simp only [Plan.eval,clear.correct,Option.map_map,Function.comp_def]
    have hobs := congrArg (Option.map (observe outputs)) hs
    simp only [Option.map_map,Function.comp_def] at hobs
    cases hr : stage.source x y s <;> simpa only [source,hr,bind,Option.bind,observe_many privateHidden] using hobs
  | @next hidden stage following rest emit order sizeOK privateOutput tail ih =>
    have hp := emit.correct s ready.1.1 ((layout following.array).trans sizeOK.symm) x y q hq
    simp only [Plan.eval,source]
    cases hs : stage.source x y s <;> cases ht : emit.eval x y (eraseMany hidden s) q <;>
      simp only [hs,ht] at hp
    · rfl
    · cases hp
    · cases hp
    · rename_i u pair
      obtain ⟨v,qo⟩ := pair
      cases hp with
      | some same correspondence =>
        subst v
        simp only [bind,Option.bind]
        apply ih u (layout.after (stage_same stage ready.1 hs)) (ready.2 u hs)
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact privateOutput
          · exact privateHidden a ha
        · intro _
          simpa only [order] using correspondence

end IRComparison.StreamChain
