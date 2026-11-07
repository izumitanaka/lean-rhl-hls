import IRComparison.Circuit.TailSound
import IRComparison.Circuit.RootProjection

namespace IRComparison.Circuit

def Build.allocateSnapshot (b : Build) (source : Nat) (sizes : Nat → Nat) : Build :=
  { b with memories := b.memories.push (b.nextArray,sizes source),nextArray := b.nextArray+1 }

theorem snapshot_run (b : Build) (source : Nat) (sizes : Nat → Nat) :
    snapshot source sizes b = (b.nextArray,b.allocateSnapshot source sizes) := rfl

theorem extends_snapshot (source : Nat) (sizes : Nat → Nat) : ExtendsBuild (snapshot source sizes) :=
  fun _ => ⟨Nat.le_refl _,fun _ h => h,Nat.le_refl _⟩

theorem queues_snapshot (source : Nat) (sizes : Nat → Nat) : PreservesQueues (snapshot source sizes) :=
  fun _ h => ⟨h.distinct,h.fresh⟩

theorem rootCode_queues (sizes : Nat → Nat) (code : HybridCompactChainControl.RootCode) :
    PreservesQueues (rootCode sizes code) := by
  apply queues_bind _ _ (queues_allocate _)
  intro out
  apply queues_bind _ _ (queues_allocate _)
  intro unused
  apply queues_bind _ _ (queues_snapshot _ _)
  intro input
  apply queues_bind _ _ (queues_of_resources _ (counted_resources _ _ _ _ _ _ _ _ _))
  intro _
  exact queues_bind _ _ (tailCode_queues _ _ _) (fun _ => queues_pure _)

/-- The compact root, all following stages, and private snapshot allocation
refine the existing control IR. The projection removes only IDs reserved for
compiler-private memory, not any source array. -/
theorem rootCode_correct (sizes : Nat → Nat) (code : HybridCompactChainControl.RootCode)
    (b : Build) (p : Payload) (inputs : 2 ≤ b.wires.size)
    (known : hasSendBounds (.compact code) = true)
    (covered : CoversQueues cap (rootCode sizes code b).2)
    (senderSafe : ∀ a ∈ allCommandArrays code.sender.body, a < b.nextArray)
    (tailSafe : ∀ a ∈ tailArrays code.tail, a < b.nextArray)
    (hx : p.wires 0 = x) (hy : p.wires 1 = y) :
    ∃ r, (rootCode sizes code b).1.Eval cap p r ∧
      r.map (fun q => trimState b.nextArray q.data) = (code.eval x y p.data).map (trimState b.nextArray) := by
  let budget := max (sizes code.output) (code.sender.count*(sendBound code.sender.body).getD 0)
  let b1 := b.allocateQueue budget
  let b2 := b1.allocateQueue 0
  let b3 := b2.allocateSnapshot code.inputArray sizes
  have knownPair : (sendBound code.sender.body).isSome = true ∧ tailHasSendBounds code.tail = true := by
    simpa only [hasSendBounds,Bool.and_eq_true] using known
  cases hb : sendBound code.sender.body with
  | none => simp [hb] at knownPair
  | some bound =>
    have ec := extends_counted code.sender.start code.sender.stride code.sender.count
      (code.sender.initial.map fromMemoryLoad) (code.sender.refill.map fromMemoryLoad) code.sender.body
      b.nextArray b1.nextQueue b.nextQueue b3
    have frame := counted_frame code.sender.start code.sender.stride code.sender.count
      (code.sender.initial.map fromMemoryLoad) (code.sender.refill.map fromMemoryLoad) code.sender.body
      b.nextArray b1.nextQueue b.nextQueue b3 inputs
    change CoversQueues cap (let (_,b4) := (counted code.sender.start code.sender.stride code.sender.count
      (code.sender.initial.map fromMemoryLoad) (code.sender.refill.map fromMemoryLoad) code.sender.body
      b.nextArray b1.nextQueue b.nextQueue b3); (tailCode sizes b.nextQueue code.tail b4).2) at covered
    change ∃ r, (let (body,b4) := (counted code.sender.start code.sender.stride code.sender.count
      (code.sender.initial.map fromMemoryLoad) (code.sender.refill.map fromMemoryLoad) code.sender.body
      b.nextArray b1.nextQueue b.nextQueue b3);
      let (tail,_) := tailCode sizes b.nextQueue code.tail b4;
      Schedule.seq (.step (.erase code.output)) (.seq (.step (.snapshot b.nextArray code.inputArray))
        (.seq (.step (.clear b.nextQueue)) (.seq body (.seq (.step (.erase code.output)) tail))))).Eval cap p r ∧
      r.map (fun q => trimState b.nextArray q.data) = _
    generalize hc : counted code.sender.start code.sender.stride code.sender.count
      (code.sender.initial.map fromMemoryLoad) (code.sender.refill.map fromMemoryLoad) code.sender.body
      b.nextArray b1.nextQueue b.nextQueue b3 = pair at *
    obtain ⟨bodyCode,b4⟩ := pair
    dsimp only at ec frame covered ⊢
    have et := tailCode_extension sizes b.nextQueue code.tail b4
    have allocated := (covered.before et).before ec
    have capacity : code.sender.count*bound ≤ cap b.nextQueue := by
      have hh := allocated b.nextQueue budget (by simp [b3,b2,b1,Build.allocateSnapshot,Build.allocateQueue])
      dsimp only [budget] at hh
      simp only [hb,Option.getD_some] at hh
      omega
    have readonly : b.nextArray ∉ commandWrites code.sender.body := by
      intro h
      have := senderSafe _ (commandWrites_mem _ h)
      omega
    let p0 := (p.erase code.output).snapshot b.nextArray code.inputArray
    let p1 := p0.clear b.nextQueue
    obtain ⟨r,hr,ho⟩ := producer_static_correct (input:=b.nextArray) (qi:=b1.nextQueue) (qo:=b.nextQueue)
      (cap:=cap) code.sender b3 p1 inputs (by dsimp [b1,Build.allocateQueue]; omega)
      (by simp [p1,Payload.clear]) readonly hx hy hb capacity
    dsimp only [StateT.run] at hr
    rw [hc] at hr
    dsimp only at hr
    have inputEq : arrayInput (p1.data.arrays b.nextArray) = arrayInput ((p.erase code.output).data.arrays code.inputArray) := by
      simp [p1,p0,Payload.clear,Payload.snapshot]
    have projected := congrArg (Option.map (fun result : State × List Int × List Int => (result.1,result.2.2))) ho
    have sourceResult : r.map (observe b.nextQueue) = code.sender.eval
        (arrayInput ((p.erase code.output).data.arrays code.inputArray)) x y p0.data := by
      rw [inputEq] at projected
      simpa [Option.map_map,Function.comp_def,observeBlock,observe,p1,Payload.clear] using projected
    have begin : (Schedule.seq (.step (.erase code.output))
        (.seq (.step (.snapshot b.nextArray code.inputArray)) (.step (.clear b.nextQueue)))).Eval cap p (some p1) :=
      .seq (erase_eval p code.output) (.seq (snapshot_eval (p.erase code.output) b.nextArray code.inputArray) (clear_eval p0 b.nextQueue))
    cases r with
    | none =>
      refine ⟨none,.seq (erase_eval p code.output) (.seq (snapshot_eval (p.erase code.output) b.nextArray code.inputArray)
        (.seq (clear_eval p0 b.nextQueue) (.seq_error hr))),?_⟩
      have eq := root_snapshot_correct (x:=x) (y:=y) code p senderSafe tailSafe
      rw [rootContinuation,← sourceResult] at eq
      exact eq
    | some q =>
      have stable := bodyCode.preserves_below hr frame rfl
      have qx : (q.erase code.output).wires 0 = x := (stable 0 (by dsimp [b3,b2,b1,Build.allocateQueue,Build.allocateSnapshot]; omega)).symm.trans hx
      have qy : (q.erase code.output).wires 1 = y := (stable 1 (by dsimp [b3,b2,b1,Build.allocateQueue,Build.allocateSnapshot]; omega)).symm.trans hy
      have fresh : b.nextQueue < b4.nextQueue := by
        have hh := ec.nextQueue
        dsimp only [b3,b2,b1,Build.allocateSnapshot,Build.allocateQueue] at hh
        omega
      obtain ⟨final,hfinal,ofinal⟩ := tailCode_correct sizes b.nextQueue code.tail b4 (q.erase code.output)
        (Nat.le_trans inputs ec.wires) fresh knownPair.2 covered qx qy
      refine ⟨final,.seq (erase_eval p code.output) (.seq (snapshot_eval (p.erase code.output) b.nextArray code.inputArray)
        (.seq (clear_eval p0 b.nextQueue) (.seq hr (.seq (erase_eval q code.output) hfinal)))),?_⟩
      have full : final.map Payload.data = rootContinuation code
          (arrayInput ((p.erase code.output).data.arrays code.inputArray)) x y p0.data := by
        unfold rootContinuation
        rw [← sourceResult]
        exact ofinal
      have trimmed := congrArg (Option.map (trimState b.nextArray)) full
      rw [Option.map_map] at trimmed
      exact trimmed.trans (root_snapshot_correct code p senderSafe tailSafe)

end IRComparison.Circuit
