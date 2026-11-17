import IRComparison.Circuit.ChannelCounted
import IRComparison.Circuit.ChannelAllocation
import IRComparison.Circuit.ChannelCapacity

namespace IRComparison.Circuit.ChannelCounted
open HybridIR ChannelLower

/-- Every previously certified bound is preserved. Literal range loops can
now also receive a bound when the older analysis returned none. -/
theorem command_budget (c : Cmd) (known : sendBound c = some n) :
    sendBudget (ChannelCommandBridge.command qo width padding c) = some n := by
  induction c generalizing width n with
  | skip | assign | store | send => exact known
  | letValue e b ih => exact ih known
  | seq a b ia ib | branch e a b ia ib =>
    cases ha : sendBound a <;> cases hb : sendBound b <;>
      simp only [sendBound,ha,hb,bind,Option.bind,pure,Option.some.injEq] at known
    all_goals try contradiction
    all_goals subst n; simp [ChannelCommandBridge.command,sendBudget,ia ha,ib hb]
  | «repeat» count b ih =>
    cases hb : sendBound b with
    | none => simp [sendBound,hb] at known
    | some m =>
      simp only [sendBound,hb,Option.map_some,Option.some.injEq] at known
      subst n
      simp [ChannelCommandBridge.command,sendBudget,ih hb]
  | forRange e b ih =>
    by_cases hb : sendBound b = some 0
    · simp only [sendBound,hb,ite_true,Option.some.injEq] at known
      subst n
      simp [ChannelCommandBridge.command,sendBudget,ih hb]
    · simp [sendBound,hb] at known

theorem command_support (c : Cmd) :
    ∀ q ∈ sentChannels (ChannelCommandBridge.command qo width padding c), q = qo := by
  induction c generalizing width with
  | skip | assign | store => simp [ChannelCommandBridge.command,sentChannels]
  | send => simp [ChannelCommandBridge.command,sentChannels]
  | letValue _ _ ih | forRange _ _ ih => exact ih
  | «repeat» _ _ ih => exact ih
  | seq a b ia ib | branch _ a b ia ib =>
    intro q h
    rcases List.mem_append.mp h with h | h
    · exact ia q h
    · exact ib q h

@[simp] theorem capture_budget (slots : List Nat) (c : ChannelCmd) :
    sendBudget (ChannelBuffers.capture slots c) = sendBudget c := by
  induction slots generalizing c with
  | nil => rfl
  | cons b bs ih => simpa [ChannelBuffers.capture,List.foldl_cons] using ih (.letBuffer b c)

@[simp] theorem capture_support (slots : List Nat) (c : ChannelCmd) :
    sentChannels (ChannelBuffers.capture slots c) = sentChannels c := by
  induction slots generalizing c with
  | nil => rfl
  | cons b bs ih => simpa [ChannelBuffers.capture,List.foldl_cons] using ih (.letBuffer b c)

@[simp] theorem loads_budget (ls : List ChannelWindow.Load) :
    sendBudget (ChannelWindow.loads input qi base width padding i ls) = some 0 := by
  induction ls generalizing base with
  | nil => rfl
  | cons l ls ih => cases l <;> simp [ChannelWindow.loads,ChannelWindow.Load.code,ChannelBuffers.take,sendBudget,ih]

@[simp] theorem loads_support (ls : List ChannelWindow.Load) :
    sentChannels (ChannelWindow.loads input qi base width padding i ls) = [] := by
  induction ls generalizing base with
  | nil => rfl
  | cons l ls ih => cases l <;> simp [ChannelWindow.loads,ChannelWindow.Load.code,ChannelBuffers.take,sentChannels,ih]

theorem piece_budget (known : sendBound body = some bound) :
    sendBudget (piece input qi qo width ls body) = some bound := by
  simp only [piece,sendBudget,capture_budget,loads_budget,command_budget body known]
  simp

theorem round_budget (known : sendBound body = some bound) :
    sendBudget (round input qi qo start stride initial refill body) = some bound := by
  simp only [round,sendBudget,piece_budget known]
  simp

theorem round_support : ∀ q ∈ sentChannels (round input qi qo start stride initial refill body), q = qo := by
  simp only [round,sentChannels,piece,capture_support,loads_support,List.nil_append,List.mem_append]
  intro q h
  rcases h with (h | h) | h <;> exact command_support body q h

theorem bounded_command (known : sendBound body = some bound)
    (fit : (s.queues qo).length + count*bound ≤ cap qo) :
    ChannelLower.bounded cap outer x y (command input qi qo start stride count initial refill body) s [] =
      (command input qi qo start stride count initial refill body).eval outer x y s [] := by
  let other := fun q => if q = qo then cap q else max (cap q) ((s.queues q).length)
  have same : ∀ q ∈ sentChannels (command input qi qo start stride count initial refill body), cap q = other q := by
    intro q h
    have eq := round_support (start:=start) (stride:=stride) q h
    subst q; simp [other]
  rw [bounded_congr _ same]
  have step := fun (k:Nat) => sendBudget_sound (round input qi qo start stride initial refill body)
    (round_budget known) (channels:=[qo]) (cap:=other) (i:=outer) (x:=x) (y:=y) (ls:=[(k:Int)])
    (fun q h => by simp [round_support (start:=start) (stride:=stride) q h])
  have folded := Budgeted.fold (List.range count) step
  have fits : ChannelLower.Fits other [qo] (count*bound) s := by
    intro q
    by_cases h : q = qo
    · simpa [other,h] using fit
    · simp [other,h]; exact Nat.le_max_right _ _
  have eq := (folded s (by simpa using fits)).1
  simpa [command,ChannelLower.bounded,ChannelCmd.eval,ReadCode.eval,Value.eval] using eq

/-- Use one private buffer bank and retain a counted loop in the circuit. -/
def lower (start stride : Int) (count : Nat) (initial refill : List Circuit.Load)
    (body : Cmd) (input qi qo : Nat) : Builder Schedule := fun b =>
  let c := command input qi qo start stride count initial refill body
  ChannelLower.lower (bankFor c b) (.lit 0) [] c (reserve c b)

theorem lower_reference (b : Build) (p : Payload) (inputs : 2 ≤ b.wires.size)
    (distinct : qi ≠ qo) (empty : p.queues qo = [])
    (readonly : input ∉ commandWrites body) (hx : p.wires 0 = x) (hy : p.wires 1 = y)
    (known : sendBound body = some bound) (capacity : count*bound ≤ cap qo) :
    ∃ r, (lower start stride count initial refill body input qi qo b).1.Eval cap p r ∧
      r.map (fun q => (q.data,q.queues)) =
        (HybridIR.blocksEval (arrayInput (p.data.arrays input)) x y
          (referenceBlocks start stride count initial refill body) [] p.data (p.queues qi) []).map
          (fun (t,rest,out) => (t,GlobalPipeline.put (GlobalPipeline.put p.queues qi rest) qo out)) := by
  let c := command input qi qo start stride count initial refill body
  have ctx : ChannelLower.Context (bankFor c b) (reserve c b).wires.size (.lit 0) [] p 0 x y [] :=
    ⟨inputs,by simp only [reserve_size,Nat.le_refl],.lit,by simp,rfl,hx,hy,matches_nil⟩
  obtain ⟨r,hr,he⟩ := ChannelLower.lower_correct c (bankFor c b) (reserve c b) (.lit 0) [] (Nat.le_refl _) p 0 x y [] ctx
  rw [bounded_command known (by simpa only [bankFor,Buffers.view,empty,List.length_nil,Nat.zero_add] using capacity)] at he
  have eq := congrArg (Option.map (fun t : ChannelState => (t.data,t.queues))) he
  rw [Option.map_map,command_correct distinct] at eq
  rw [sourceCountedFold_frozen _ _ readonly rfl] at eq
  refine ⟨r,hr,?_⟩
  rw [reference_eval,iterationEval_fold]
  simpa only [Option.map_map,Function.comp_def,c,bankFor,Buffers.view,empty] using eq

end IRComparison.Circuit.ChannelCounted
