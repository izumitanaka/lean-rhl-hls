import IRComparison.Memory.CompactChainEmit
import IRComparison.Memory.StreamChain

namespace IRComparison.CompactChain
open CompactStage StreamConsumer StreamChainState PipelineShapes PipelineUse

theorem fifo_many (c : CompactStage.Clear hidden code.body) :
    (CompactFIFO.Code.eval code x y s q).map (fun (t,qs) => (eraseMany hidden t,qs)) =
      code.eval x y (eraseMany hidden s) q := by
  induction hidden with
  | nil => simp [eraseMany]
  | cons a as ih =>
    rw [eraseMany,← CompactFusion.fifo_erase (c.bodies a (by simp))]
    rw [← ih ⟨by intro b hb; exact c.bodies b (by simp [hb])⟩]
    simp only [Option.map_map,Function.comp_def,eraseMany]

inductive Tail (outputs : List Nat) (sizes : Nat → Nat) : List Nat → Stage → List Stage → CompactSequence.Seq → Type where
  | last (sizeOK : stage.size = sizes stage.array)
      (receiver : CompactFusion.Receiver stage.code supplier) (clear : CompactStage.Clear hidden stage.code.body) :
      Tail outputs sizes hidden stage [] supplier
  | next (sizeOK : stage.size = sizes stage.array)
      (emit : CompactChainEmit.Plan hidden stage supplier following.array following.size)
      (outputSize : following.size = sizes following.array) (privateOutput : following.array ∉ outputs)
      (tail : Tail outputs sizes (following.array::hidden) following rest emit.duplex.sender.sequence) :
      Tail outputs sizes hidden stage (following::rest) supplier

def compileTail (outputs : List Nat) (sizes : Nat → Nat) (hidden : List Nat) (stage : Stage)
    (supplier : CompactSequence.Seq) : (rest : List Stage) → Option (Tail outputs sizes hidden stage rest supplier)
  | [] => do
    if sizeOK : stage.size = sizes stage.array then
      return .last sizeOK (CompactFusion.receiver (← CompactFIFO.compile stage.code supplier)) (← CompactStage.check hidden stage.code.body)
    else none
  | following::rest => do
    if sizeOK : stage.size = sizes stage.array then
      if outputSize : following.size = sizes following.array then
        if privateOutput : following.array ∉ outputs then
          let emit ← CompactChainEmit.compile hidden stage supplier following.array following.size
          return .next sizeOK emit outputSize privateOutput
            (← compileTail outputs sizes (following.array::hidden) following emit.duplex.sender.sequence rest)
        else none
      else none
    else none

def compileTailWithSMT (outputs : List Nat) (sizes : Nat → Nat) (hidden : List Nat) (stage : Stage)
    (supplier : CompactSequence.Seq) (directory : System.FilePath) :
    (rest : List Stage) → IO (Option (Tail outputs sizes hidden stage rest supplier))
  | [] => do
    if sizeOK : stage.size = sizes stage.array then
      let some clear := CompactStage.check hidden stage.code.body | return none
      let (_,certificate) ← CompactSequence.solve supplier directory
      let some certificate := certificate | return none
      let some routing := CompactFIFO.compile stage.code certificate.sequence | return none
      return some (.last sizeOK (CompactFusion.candidateReceiver certificate routing) clear)
    else return none
  | following::rest => do
    if sizeOK : stage.size = sizes stage.array then
      if outputSize : following.size = sizes following.array then
        if privateOutput : following.array ∉ outputs then
          let some emit ← CompactChainEmit.compileWithSMT hidden stage supplier following.array following.size directory | return none
          let some tail ← compileTailWithSMT outputs sizes (following.array::hidden) following emit.duplex.sender.sequence (directory / "next") rest | return none
          return some (.next sizeOK emit outputSize privateOutput tail)
        else return none
      else return none
    else return none

def Tail.eval (p : Tail outputs sizes hidden stage rest supplier) (x y : Int) (s : State) (q : List Int) : Option State :=
  match p with
  | .last _ receiver _ => (receiver.code.eval x y s q).map Prod.fst
  | .next _ emit _ _ tail => do
      let (t,qo) ← emit.eval x y s q
      tail.eval x y t qo

theorem Tail.correct (p : Tail outputs sizes hidden stage rest supplier) (s : State)
    (layout : Layout sizes s) (privateHidden : ∀ a ∈ hidden, a ∉ outputs)
    (hq : CommunicationIR.Corresponds (arrayInput (s.arrays stage.array)) supplier.entries q) :
    (p.eval x y (eraseMany hidden s) q).map (observe outputs) =
      (CompactStage.source x y (stage::rest) s).map (observe outputs) := by
  induction p generalizing s q with
  | @last supplier hidden stage sizeOK receiver clear =>
    have hs := (receiver.correct (arrayInput (s.arrays stage.array)) x y s q hq).trans
      (stage.correct s ((layout stage.array).trans sizeOK.symm) x y)
    simp only [Tail.eval,← fifo_many (code:=receiver.code) (receiver.body.symm ▸ clear),Option.map_map,Function.comp_def,StreamChain.observe_many privateHidden]
    have hobs := congrArg (Option.map (observe outputs)) hs
    simp only [Option.map_map,Function.comp_def] at hobs
    cases hr : stage.source x y s <;> simpa only [CompactStage.source,hr,bind,Option.bind] using hobs
  | @next hidden stage supplier following rest sizeOK emit outputSize privateOutput tail ih =>
    have sized := (layout stage.array).trans sizeOK.symm
    have hp := emit.correct s sized ((layout following.array).trans outputSize.symm) x y q hq
    simp only [Tail.eval,CompactStage.source]
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
        apply ih u (layout.after (stage.same sized hs))
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact privateOutput
          · exact privateHidden a ha
        · exact correspondence

structure Plan (outputs : List Nat) (sizes : Nat → Nat) (first following : Stage) (rest : List Stage) where
  sizeFirst : first.size = sizes first.array
  sizeOutput : following.size = sizes following.array
  privateOutput : following.array ∉ outputs
  different : first.array ≠ following.array
  sender : SymbolicProducerLoop.Plan following.array following.size first.code
  tail : Tail outputs sizes [following.array] following rest sender.sequence

def compile (outputs : List Nat) (sizes : Nat → Nat) (first following : Stage) (rest : List Stage) :
    Option (Plan outputs sizes first following rest) := do
  if sizeFirst : first.size = sizes first.array then
    if sizeOutput : following.size = sizes following.array then
      if privateOutput : following.array ∉ outputs then
        if different : first.array ≠ following.array then
          let sender ← SymbolicProducerLoop.compile following.array following.size first.code
          let tail ← compileTail outputs sizes [following.array] following sender.sequence rest
          return ⟨sizeFirst,sizeOutput,privateOutput,different,sender,tail⟩
        else none
      else none
    else none
  else none

def compileWithSMT (outputs : List Nat) (sizes : Nat → Nat) (first following : Stage) (rest : List Stage)
    (directory : System.FilePath) : IO (Option (Plan outputs sizes first following rest)) := do
  if sizeFirst : first.size = sizes first.array then
    if sizeOutput : following.size = sizes following.array then
      if privateOutput : following.array ∉ outputs then
        if different : first.array ≠ following.array then
          let some sender := SymbolicProducerLoop.compile following.array following.size first.code | return none
          let some tail ← compileTailWithSMT outputs sizes [following.array] following sender.sequence directory rest | return none
          return some ⟨sizeFirst,sizeOutput,privateOutput,different,sender,tail⟩
        else return none
      else return none
    else return none
  else return none

def Plan.eval (p : Plan outputs sizes first following rest) (x y : Int) (s : State) : Option State := do
  let initial := erase following.array s
  let (t,q) ← p.sender.code.eval (arrayInput (initial.arrays first.array)) x y initial
  p.tail.eval x y (erase following.array t) q

theorem Plan.correct (p : Plan outputs sizes first following rest) (s : State) (layout : Layout sizes s) :
    (p.eval x y s).map (observe outputs) =
      (CompactStage.source x y (first::following::rest) s).map (observe outputs) := by
  have sized := (layout first.array).trans p.sizeFirst.symm
  have relation : StreamState.Related following.array following.size [] s (erase following.array s) [] :=
    ⟨erase_agree s,(layout following.array).trans p.sizeOutput.symm,.nil⟩
  have hp := p.sender.correct (input:=arrayInput (s.arrays first.array)) (x:=x) (y:=y) s (erase following.array s) relation
  rw [first.correct s sized x y] at hp
  have inputEq : (erase following.array s).arrays first.array = s.arrays first.array := by simp [erase,p.different]
  simp only [Plan.eval,inputEq,CompactStage.source]
  cases hs : first.source x y s <;>
    cases ht : p.sender.code.eval (arrayInput (s.arrays first.array)) x y (erase following.array s) <;>
    simp only [hs,ht] at hp
  · rfl
  · cases hp
  · cases hp
  · rename_i u pair
    obtain ⟨t,q⟩ := pair
    cases hp with
    | some h =>
      simp only [bind,Option.bind]
      rw [← StreamConsumer.Agree.erase_eq h.agree]
      exact p.tail.correct u (layout.after (first.same sized hs))
        (by intro a ha; simpa using (List.mem_singleton.mp ha ▸ p.privateOutput)) h.values

end IRComparison.CompactChain
