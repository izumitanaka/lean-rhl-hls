import IRComparison.Hybrid.HybridCompactChain
import IRComparison.Hybrid.HybridEffects
import IRComparison.Hybrid.HybridRoutingVC

/-! Compose loop-preserving memory translations in source order. The interface
tracks each array separately; it is not a single incoming/outgoing chain. -/
namespace IRComparison.HybridSymbolicGlobal
open HybridCompactStage StreamConsumer StreamChainState PipelineShapes PipelineUse
abbrev Queues := Nat → List Int
abbrev Interface := List (Nat × CompactSequence.Seq)
def Related (env : Interface) (s : State) (qs : Queues) : Prop :=
  ∀ a sequence, (a,sequence) ∈ env →
    CommunicationIR.Corresponds (arrayInput (s.arrays a)) sequence.entries (qs a)
def remove (a : Nat) (env : Interface) := env.filter (fun p => p.1 != a)
def put (qs : Queues) (a : Nat) (q : List Int) : Queues := fun b => if b = a then q else qs b

/-- A frame obligation for unrelated channels. No iteration enumeration. -/
theorem loop_frame (code : HybridSymbolicLoop.Code) (safe : a ∉ HybridEffects.writes code.body)
    (h : code.loop input x y n k old s = some t) : t.arrays a = s.arrays a := by
  induction n generalizing k old s with
  | zero => cases h; rfl
  | succ n ih =>
    rw [HybridSymbolicLoop.Code.loop] at h
    cases hb : code.body.eval (HybridSymbolicLoop.index code.start code.stride k) x y s old <;>
      simp only [hb,bind,Option.bind] at h
    · cases h
    · rename_i u
      have frame := HybridEffects.body_preserves code.body safe hb
      cases n with
      | zero => cases h; exact frame
      | succ m =>
        cases hl : SymbolicWindowSchedule.execute input (HybridSymbolicLoop.index code.start code.stride (k+1)) old code.refill <;>
          simp only [hl,bind,Option.bind] at h
        · cases h
        · exact (ih h).trans frame

theorem code_frame (code : HybridSymbolicLoop.Code) (safe : a ∉ HybridEffects.writes code.body)
    (h : code.eval input x y s = some t) : t.arrays a = s.arrays a := by
  unfold HybridSymbolicLoop.Code.eval at h
  cases hc : code.count <;> simp only [hc] at h
  · cases h; rfl
  · cases hl : SymbolicWindowSchedule.execute input code.start [] code.initial <;> simp only [hl,bind,Option.bind] at h
    · cases h
    · exact loop_frame code safe h

theorem stage_frame (p : Stage) (safe : a ∉ HybridEffects.writes p.code.body)
    (sized : (s.arrays p.array).size = p.size) (h : p.source x y s = some t) :
    t.arrays a = s.arrays a :=
  code_frame p.code safe ((p.correct s sized x y).trans h)

theorem related_rest (h : Related env s qs)
    (same : ∀ a seq, (a,seq) ∈ env → t.arrays a = s.arrays a) :
    Related (remove input env) t (put qs input []) := by
  intro a seq member
  have hm := (List.mem_filter.mp member).1
  have ne : a ≠ input := by simpa using (List.mem_filter.mp member).2
  simpa only [same a seq hm,put,if_neg ne] using h a seq hm

inductive Instruction where
  | memory (input : Nat) (code : HybridSymbolicLoop.Code)
  | producer (input output : Nat) (code : HybridSymbolicProducerLoop.Code)
  | receiver (input : Nat) (code : HybridCompactFIFO.Code)
  | duplex (input output : Nat) (code : HybridCompactDuplex.Code)

def Instruction.body : Instruction → HybridIR.Cmd
  | .memory _ c => c.body.target
  | .producer _ _ c => c.body
  | .receiver _ c => c.body.target
  | .duplex _ _ c => c.body

def Instruction.eval (c : Instruction) (x y : Int) (s : State) (qs : Queues) : Option (State × Queues) :=
  match c with
  | .memory a code => (code.eval (arrayInput (s.arrays a)) x y s).map (fun t => (t,put qs a []))
  | .producer a b code =>
      (code.eval (arrayInput (s.arrays a)) x y (erase b s)).map (fun (t,out) => (erase b t,put (put qs a []) b out))
  | .receiver a code => (code.eval x y s (qs a)).map (fun (t,_) => (t,put qs a []))
  | .duplex a b code =>
      (code.eval x y (erase b s) (qs a)).map (fun (t,out) => (erase b t,put (put qs a []) b out))

inductive Result (hidden : List Nat) (env : Interface) : Option State → Option (State × Queues) → Prop where
  | none : Result hidden env none none
  | some : eraseMany hidden s = t → Related env s qs → Result hidden env (some s) (some (t,qs))

structure Step (sizes : Nat → Nat) (hidden : List Nat) (env : Interface) (p : Stage) where
  instruction : Instruction
  bodyShape : HybridSymbolicProducer.BodyShape p.code.body instruction.body
  nextHidden : List Nat
  nextEnv : Interface
  correct : ∀ s, Layout sizes s → (s.arrays p.array).size = p.size → ∀ qs, Related env s qs → ∀ x y,
    Result nextHidden nextEnv (p.source x y s) (instruction.eval x y (eraseMany hidden s) qs)

/-- Tr-Seq's intermediate relation carries all live channels. -/
inductive Plan (outputs : List Nat) (sizes : Nat → Nat) : List Nat → Interface → List Stage → Type where
  | nil (privateHidden : ∀ a ∈ hidden, a ∉ outputs) : Plan outputs sizes hidden env []
  | cons (first : Step sizes hidden env p) (tail : Plan outputs sizes first.nextHidden first.nextEnv ps) :
      Plan outputs sizes hidden env (p::ps)

def Plan.code : Plan outputs sizes hidden env ps → List Instruction
  | .nil _ => []
  | .cons h t => h.instruction :: t.code

def execute (x y : Int) : List Instruction → State → Queues → Option State
  | [],s,_ => some s
  | c::cs,s,qs => do
    let (t,rest) ← c.eval x y s qs
    execute x y cs t rest

theorem Plan.correct (p : Plan outputs sizes hidden env ps) (s : State)
    (layout : Layout sizes s) (sized : ∀ p ∈ ps, (s.arrays p.array).size = p.size)
    (qs : Queues) (related : Related env s qs) :
    (execute x y p.code (eraseMany hidden s) qs).map (observe outputs) =
      (HybridCompactStage.source x y ps s).map (observe outputs) := by
  induction p generalizing s qs with
  | nil privateHidden => exact congrArg some (StreamChain.observe_many privateHidden s)
  | @cons hidden env p ps first tail ih =>
    have hp := sized p (by simp)
    have h := first.correct s layout hp qs related x y
    simp only [Plan.code,execute,HybridCompactStage.source]
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
        exact ih u (layout.after (p.same hp hs))
          (fun q hq => (p.same hp hs q.array).symm.trans (sized q (by simp [hq]))) rest hr



/-- Tr-Seq/frame: writing unrelated arrays preserves all other correspondences. -/
def keepMemory (p : Stage) (retained : p.array ∉ hidden)
    (clear : Clear hidden p.code.body)
    (untouched : ∀ pair ∈ env, pair.1 ∉ HybridEffects.writes p.code.body) :
    Step sizes hidden env p where
  instruction := .memory p.array p.code
  bodyShape := .memory
  nextHidden := hidden
  nextEnv := remove p.array env
  correct := by
    intro s layout sized qs related x y
    simp only [Instruction.eval,eraseMany_array retained,clear.correct,p.correct s sized x y]
    cases hs : p.source x y s with
    | none => exact .none
    | some t =>
      apply Result.some rfl
      exact related_rest related (fun a seq hm => stage_frame p (untouched _ hm) sized hs)

def receive (p : Stage) (member : (p.array,seq) ∈ env)
    (receiver : HybridCompactReceiver.Receiver p.code seq)
    (clear : Clear hidden p.code.body)
    (untouched : ∀ pair ∈ env, pair.1 ∉ HybridEffects.writes p.code.body) :
    Step sizes hidden env p where
  instruction := .receiver p.array receiver.code
  bodyShape := by simpa only [Instruction.body,receiver.body] using
    (HybridSymbolicProducer.BodyShape.memory (c:=p.code.body))
  nextHidden := hidden
  nextEnv := remove p.array env
  correct := by
    intro s layout sized qs related x y
    have he := (receiver.correct _ x y s (qs p.array) (related _ _ member)).trans (p.correct s sized x y)
    have erased := HybridCompactChain.fifo_many (code:=receiver.code) (receiver.body.symm ▸ clear) (s:=s) (x:=x) (y:=y) (q:=qs p.array)
    simp only [Instruction.eval,← erased,Option.map_map,Function.comp_def]
    cases hr : receiver.code.eval x y s (qs p.array) with
    | none => simp only [hr,Option.map_none] at he; rw [← he]; exact .none
    | some pair =>
      obtain ⟨t,rest⟩ := pair
      simp only [hr,Option.map_some] at he
      rw [← he]
      apply Result.some rfl
      exact related_rest related (fun a seq hm => stage_frame p (untouched _ hm) sized he.symm)

/-- Combine write replacement and send insertion, carrying unrelated queues.
The semantic premise is supplied by the generally proved producer rule. -/
def sendStep (p : Stage) (output : Nat) (seq : CompactSequence.Seq)
    (fresh : output ∉ hidden)
    (written : output ∈ HybridEffects.writes p.code.body)
    (untouched : ∀ pair ∈ env, pair.1 ∉ HybridEffects.writes p.code.body)
    (instruction : Instruction)
    (bodyShape : HybridSymbolicProducer.BodyShape p.code.body instruction.body)
    (run : Int → Int → State → Queues → Option (State × List Int))
    (shape : ∀ x y s qs, instruction.eval x y s qs =
      (run x y s qs).map (fun (t,out) => (erase output t,put (put qs p.array []) output out)))
    (sound : ∀ s, Layout sizes s → (s.arrays p.array).size = p.size → ∀ qs, Related env s qs → ∀ x y,
      StreamState.Result output (sizes output) seq.entries
        ((p.source x y s).map (eraseMany hidden)) (run x y (eraseMany hidden s) qs)) :
    Step sizes hidden env p where
  instruction := instruction
  bodyShape := bodyShape
  nextHidden := output::hidden
  nextEnv := (output,seq)::remove p.array env
  correct := by
    intro s layout sized qs related x y
    have hp := sound s layout sized qs related x y
    rw [shape]
    cases hs : p.source x y s <;> cases ht : run x y (eraseMany hidden s) qs <;>
      simp only [hs,ht,Option.map_none,Option.map_some] at hp
    · exact .none
    · cases hp
    · cases hp
    · rename_i u pair
      obtain ⟨v,out⟩ := pair
      cases hp with
      | some relation =>
        apply Result.some (by simpa only [eraseMany] using StreamConsumer.Agree.erase_eq relation.agree)
        intro a sequence hm
        rcases List.mem_cons.mp hm with eq | hm
        · cases eq
          simpa [put,eraseMany_array fresh] using relation.values
        · have rest := related_rest (input:=p.array) related (t:=u)
            (fun b seq hb => stage_frame p (untouched _ hb) sized hs)
          have ne : a ≠ output := by
            intro eq
            subst a
            exact (untouched _ (List.mem_filter.mp hm).1) written
          simpa only [put,if_neg ne] using rest a sequence hm

def sendMemory (p : Stage) (output : Nat)
    (retained : p.array ∉ hidden) (different : p.array ≠ output)
    (fresh : output ∉ hidden) (written : output ∈ HybridEffects.writes p.code.body)
    (clear : Clear hidden p.code.body)
    (untouched : ∀ pair ∈ env, pair.1 ∉ HybridEffects.writes p.code.body)
    (sender : HybridSymbolicProducerLoop.Plan output (sizes output) p.code) :
    Step sizes hidden env p :=
  sendStep p output sender.sequence fresh written untouched (.producer p.array output sender.code)
    sender.body.shape
    (fun x y s _ => sender.code.eval (arrayInput (s.arrays p.array)) x y (erase output s))
    (by intros; rfl) (by
      intro s layout sized qs related x y
      have relation : StreamState.Related output (sizes output) [] (eraseMany hidden s) (erase output (eraseMany hidden s)) [] :=
        ⟨erase_agree _,by rw [eraseMany_array fresh]; exact layout output,.nil⟩
      have hp := sender.correct (input:=arrayInput (s.arrays p.array)) (x:=x) (y:=y) _ _ relation
      rw [clear.correct,p.correct s sized x y] at hp
      simpa only [eraseMany_array retained] using hp)

def sendChannel (p : Stage) (output : Nat) (member : (p.array,seq) ∈ env)
    (fresh : output ∉ hidden) (written : output ∈ HybridEffects.writes p.code.body)
    (clear : Clear hidden p.code.body)
    (untouched : ∀ pair ∈ env, pair.1 ∉ HybridEffects.writes p.code.body)
    (duplex : HybridCompactDuplex.Plan output (sizes output) p.code seq) :
    Step sizes hidden env p :=
  sendStep p output duplex.sender.sequence fresh written untouched (.duplex p.array output duplex.code)
    duplex.sender.body.shape
    (fun x y s qs => duplex.code.eval x y (erase output s) (qs p.array))
    (by intros; rfl) (by
      intro s layout sized qs related x y
      dsimp only
      rw [duplex.routing_correct _ _ (related _ _ member)]
      have relation : StreamState.Related output (sizes output) [] (eraseMany hidden s) (erase output (eraseMany hidden s)) [] :=
        ⟨erase_agree _,by rw [eraseMany_array fresh]; exact layout output,.nil⟩
      have hp := duplex.sender.correct (input:=arrayInput (s.arrays p.array)) (x:=x) (y:=y) _ _ relation
      rw [clear.correct,p.correct s sized x y] at hp
      exact hp)



def fromOption [Monad m] (v : Option α) : OptionT m α := OptionT.mk (pure v)

def compileStepWith [Monad m]
    (routing : (c : HybridSymbolicLoop.Code) → (q : CompactSequence.Seq) → m (Option (HybridCompactFIFO.Plan c q)))
    (policy : List Nat) (sizes : Nat → Nat) (hidden : List Nat)
    (env : Interface) (p : Stage) : OptionT m (Step sizes hidden env p) := do
  let clear ← fromOption (HybridCompactStage.check hidden p.code.body)
  if untouched : ∀ pair ∈ env, pair.1 ∉ HybridEffects.writes p.code.body then
    let outputs := (HybridEffects.writes p.code.body).eraseDups.filter (· ∈ policy)
    match ho : outputs with
    | [] =>
      let _ ← fromOption (HybridCompactStage.check policy p.code.body)
      if selected : p.array ∈ policy then
        let seq ← fromOption (env.lookup p.array)
        if member : (p.array,seq) ∈ env then
          return receive p member (HybridCompactReceiver.receiver (← OptionT.mk (routing p.code seq))) clear untouched
        else failure
      else if retained : p.array ∉ hidden then
        return keepMemory p retained clear untouched
      else failure
    | [output] =>
      let _ ← fromOption (HybridCompactStage.check (policy.filter (· != output)) p.code.body)
      if fresh : output ∉ hidden then
        have written : output ∈ HybridEffects.writes p.code.body := by
          have hm : output ∈ outputs := by rw [ho]; simp
          simpa using (List.mem_filter.mp hm).1
        if selected : p.array ∈ policy then
          let seq ← fromOption (env.lookup p.array)
          if member : (p.array,seq) ∈ env then
            let sender ← fromOption (HybridSymbolicProducerLoop.compile output (sizes output) p.code)
            let receiver ← OptionT.mk (routing p.code seq)
            return sendChannel p output member fresh written clear untouched ⟨sender,seq,rfl,receiver⟩
          else failure
        else if retained : p.array ∉ hidden then
          if different : p.array ≠ output then
            return sendMemory p output retained different fresh written clear untouched
              (← fromOption (HybridSymbolicProducerLoop.compile output (sizes output) p.code))
          else failure
        else failure
      else failure
    | _ => failure
  else failure


def compileStep (policy : List Nat) (sizes : Nat → Nat) (hidden : List Nat) (env : Interface) (p : Stage) :=
  (compileStepWith (m:=Id) (fun c q => pure (HybridCompactFIFO.compile c q)) policy sizes hidden env p).run

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

/-- Stable source-write order; public outputs are never candidates. The
heuristic is deliberately simple and does not claim maximum FIFO coverage. -/
def candidates (outputs : List Nat) (ps : List Stage) : List Nat :=
  (ps.flatMap (fun p => HybridEffects.writes p.code.body)).eraseDups.filter (· ∉ outputs)

/-- Try one addition at a time, checking the entire policy after every addition.
A rejected candidate leaves the already certified plan intact. -/
def improve (best : Program outputs sizes ps) : List Nat → Program outputs sizes ps
  | [] => best
  | a::rest =>
    let policy := best.policy ++ [a]
    match compilePolicy outputs sizes policy [] [] ps with
    | some plan => improve ⟨policy,plan⟩ rest
    | none => improve best rest

theorem improve_selected (best : Program outputs sizes ps)
    (selected : compilePolicy outputs sizes best.policy [] [] ps = some best.plan)
    (arrays : List Nat) :
    compilePolicy outputs sizes (improve best arrays).policy [] [] ps =
      some (improve best arrays).plan := by
  induction arrays generalizing best with
  | nil => exact selected
  | cons a rest ih =>
    simp only [improve]
    split
    · exact ih _ (by assumption)
    · exact ih best selected

def compile (outputs : List Nat) (sizes : Nat → Nat) (ps : List Stage) : Option (Program outputs sizes ps) := do
  let baseline ← compilePolicy outputs sizes [] [] [] ps
  return improve ⟨[],baseline⟩ (candidates outputs ps)

theorem compile_selected (h : compile outputs sizes ps = some program) :
    compilePolicy outputs sizes program.policy [] [] ps = some program.plan := by
  cases base : compilePolicy outputs sizes [] [] [] ps with
  | none => simp [compile,base] at h
  | some baseline =>
    simp only [compile,base,bind,Option.bind,pure,Option.some.injEq] at h
    subst program
    exact improve_selected ⟨[],baseline⟩ base _

def Program.eval (p : Program outputs sizes ps) (x y : Int) (s : State) :=
  execute x y p.plan.code s (fun _ => [])

theorem Program.correct (p : Program outputs sizes ps) (s : State)
    (layout : Layout sizes s) (sized : ∀ p ∈ ps, (s.arrays p.array).size = p.size) :
    (p.eval x y s).map (observe outputs) = (HybridCompactStage.source x y ps s).map (observe outputs) :=
  p.plan.correct s layout sized (fun _ => []) (by intro a seq h; cases h)



def compilePolicyWithSMT (outputs : List Nat) (sizes : Nat → Nat) (policy hidden : List Nat)
    (env : Interface) (directory : System.FilePath) (deadline : Option Nat := none) :
    (ps : List Stage) → IO (Option (Plan outputs sizes hidden env ps))
  | [] => pure (compilePolicy outputs sizes policy hidden env [])
  | p::ps => do
    if let some stop := deadline then
      if (← IO.monoMsNow) ≥ stop then return none
    let routing := fun c q => do
      try HybridRoutingVC.solve c q directory deadline
      catch _ => pure none
    let some first ← (compileStepWith routing policy sizes hidden env p).run | return none
    let some tail ← compilePolicyWithSMT outputs sizes policy first.nextHidden first.nextEnv
      (directory / "next") deadline ps | return none
    return some (.cons first tail)

/-- One whole-policy check per candidate, starting with retained memory. A
budget limits optional optimization only; baseline construction has no such
limit. No cache is used, so routing requests cannot be reused out of context. -/
def compileWithSMT (outputs : List Nat) (sizes : Nat → Nat) (ps : List Stage)
    (directory : System.FilePath) (budgetMs : Nat := 30000) : IO (Option (Program outputs sizes ps)) := do
  let some baseline := compilePolicy outputs sizes [] [] [] ps | return none
  let retained ← IO.mkRef (⟨[],baseline⟩ : Program outputs sizes ps)
  try
    let deadline := (← IO.monoMsNow) + budgetMs
    let directory ← HybridRoutingVC.freshDirectory directory
    let mut decisions := "priority: first source-write occurrence; only whole-policy acceptance\n"
    for (a,j) in (candidates outputs ps).zipIdx do
      if (← IO.monoMsNow) ≥ deadline then
        decisions := decisions ++ "stopped: optimization deadline; retaining last plan\n"
        break
      let best ← retained.get
      let policy := best.policy ++ [a]
      try
        match ← compilePolicyWithSMT outputs sizes policy [] []
            (directory / s!"candidate-{j}-array-{a}") (some deadline) ps with
        | some plan =>
          retained.set ⟨policy,plan⟩
          decisions := decisions ++ s!"array {a}: accepted by whole-plan checker; policy {policy}\n"
        | none => decisions := decisions ++ s!"array {a}: rejected or deadline; prior policy retained\n"
      catch e =>
        decisions := decisions ++ s!"array {a}: external error {e}; prior policy retained\n"
    IO.FS.writeFile (directory / "policy.txt") decisions
    return some (← retained.get)
  catch _ => return some (← retained.get)

end IRComparison.HybridSymbolicGlobal
