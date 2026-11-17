import IRComparison.Circuit.QueueTable
import IRComparison.Circuit.PayloadOperations
import IRComparison.Circuit.StaticCapacity
import IRComparison.Circuit.BudgetCheck

namespace IRComparison.Circuit

/-- Sequential composition of an arbitrary number of compact FIFO stages.
Fresh queue allocation, static capacity, and the captured BV32 inputs are
tracked across every boundary, including errors. -/
theorem tailCode_correct (sizes : Nat → Nat) (incoming : Nat) (code : HybridCompactChainControl.Code)
    (b : Build) (p : Payload) (inputs : 2 ≤ b.wires.size) (fresh : incoming < b.nextQueue)
    (known : tailHasSendBounds code = true)
    (covered : CoversQueues cap (tailCode sizes incoming code b).2)
    (hx : p.wires 0 = x) (hy : p.wires 1 = y) :
    ∃ r, (tailCode sizes incoming code b).1.Eval cap p r ∧
      r.map Payload.data = code.eval x y p.data (p.queues incoming) := by
  induction code generalizing incoming b p with
  | finish receiver =>
    let b1 := b.allocateQueue 0
    let p1 := p.clear b.nextQueue
    have distinct : incoming ≠ b.nextQueue := by omega
    obtain ⟨r,hr,ho⟩ := receiver_correct (input:=0) (cap:=cap) receiver b1 p1 inputs distinct
      (by simp [p1,Payload.clear]) hx hy
    refine ⟨r,?_,?_⟩
    · change (Schedule.seq (.step (.clear b.nextQueue))
        (counted receiver.start receiver.stride receiver.count (receiver.initial.map fromFIFOLoad)
          (receiver.refill.map fromFIFOLoad) receiver.body.target 0 incoming b.nextQueue b1).1).Eval cap p r
      exact .seq (clear_eval p b.nextQueue) hr
    · have projected := congrArg (Option.map (fun result : State × List Int × List Int => result.1)) ho
      simpa [Option.map_map,Function.comp_def,observeBlock,p1,Payload.clear,distinct,HybridCompactChainControl.Code.eval] using projected
  | stage a sender rest ih =>
    let budget := max (sizes a) (sender.count*(sendBound sender.body).getD 0)
    let b1 := b.allocateQueue budget
    have knownPair : (sendBound sender.body).isSome = true ∧ tailHasSendBounds rest = true := by simpa only [tailHasSendBounds,Bool.and_eq_true] using known
    cases hb : sendBound sender.body with
    | none => simp [hb] at knownPair
    | some bound =>
      have ec := extends_counted sender.start sender.stride sender.count (sender.initial.map fromFIFOLoad)
        (sender.refill.map fromFIFOLoad) sender.body 0 incoming b.nextQueue b1
      have frame := counted_frame sender.start sender.stride sender.count (sender.initial.map fromFIFOLoad)
        (sender.refill.map fromFIFOLoad) sender.body 0 incoming b.nextQueue b1 inputs
      change CoversQueues cap (let (_,b2) := (counted sender.start sender.stride sender.count (sender.initial.map fromFIFOLoad)
        (sender.refill.map fromFIFOLoad) sender.body 0 incoming b.nextQueue b1);
        (tailCode sizes b.nextQueue rest b2).2) at covered
      change ∃ r, (let (body,b2) := (counted sender.start sender.stride sender.count (sender.initial.map fromFIFOLoad)
        (sender.refill.map fromFIFOLoad) sender.body 0 incoming b.nextQueue b1);
        let (tail,_) := tailCode sizes b.nextQueue rest b2;
        Schedule.seq (.step (.erase a)) (.seq (.step (.clear b.nextQueue))
          (.seq body (.seq (.step (.erase a)) tail)))).Eval cap p r ∧ r.map Payload.data = _
      generalize hc : counted sender.start sender.stride sender.count (sender.initial.map fromFIFOLoad)
        (sender.refill.map fromFIFOLoad) sender.body 0 incoming b.nextQueue b1 = pair at *
      obtain ⟨bodyCode,b2⟩ := pair
      dsimp only at ec frame covered ⊢
      have et := tailCode_extension sizes b.nextQueue rest b2
      have allocated := (covered.before et).before ec
      have capacity : sender.count*bound ≤ cap b.nextQueue := by
        have hh := allocated.allocated
        dsimp only [budget] at hh
        simp only [hb,Option.getD_some] at hh
        omega
      let p1 := (p.erase a).clear b.nextQueue
      obtain ⟨r,hr,ho⟩ := duplex_static_correct (input:=0) (cap:=cap) (qi:=incoming) (qo:=b.nextQueue) sender b1 p1 inputs
        (by omega) (by simp [p1,Payload.clear]) hx hy hb capacity
      dsimp only [StateT.run] at hr
      rw [hc] at hr
      dsimp only at hr
      have boundary : p1.data = StreamConsumer.erase a p.data ∧ p1.queues incoming = p.queues incoming := by
        simp [p1,Payload.erase,Payload.clear,show incoming ≠ b.nextQueue from by omega]
      cases r with
      | none =>
        have fail : HybridCompactDuplexControl.evalFull sender x y p1.data (p1.queues incoming) = none := ho.symm
        have sourceFail := HybridCompactDuplexControl.evalFull_correct (x:=x) (y:=y) (s:=p1.data) (qi:=p1.queues incoming) sender
        rw [fail] at sourceFail
        refine ⟨none,.seq (erase_eval p a) (.seq (clear_eval (p.erase a) b.nextQueue) (.seq_error hr)),?_⟩
        simp [HybridCompactChainControl.Code.eval,← boundary.1,← boundary.2,← sourceFail]
      | some q =>
        have result : HybridCompactDuplexControl.evalFull sender x y p1.data (p1.queues incoming) =
          some (q.data,q.queues incoming,q.queues b.nextQueue) := ho.symm
        have sourceResult := HybridCompactDuplexControl.evalFull_correct (x:=x) (y:=y) (s:=p1.data) (qi:=p1.queues incoming) sender
        rw [result] at sourceResult
        have stable := bodyCode.preserves_below hr frame rfl
        have qx : (q.erase a).wires 0 = x := (stable 0 (by dsimp [b1,Build.allocateQueue]; omega)).symm.trans hx
        have qy : (q.erase a).wires 1 = y := (stable 1 (by dsimp [b1,Build.allocateQueue]; omega)).symm.trans hy
        have freshNext : b.nextQueue < b2.nextQueue := by
          have hh := ec.nextQueue
          dsimp only [b1,Build.allocateQueue] at hh
          omega
        obtain ⟨final,hfinal,ofinal⟩ := ih b.nextQueue b2 (q.erase a) (Nat.le_trans inputs ec.wires)
          freshNext knownPair.2 covered qx qy
        refine ⟨final,.seq (erase_eval p a) (.seq (clear_eval (p.erase a) b.nextQueue)
          (.seq hr (.seq (erase_eval q a) hfinal))),?_⟩
        simpa [HybridCompactChainControl.Code.eval,← boundary.1,← boundary.2,← sourceResult,Payload.erase] using ofinal

/-- The capacity premise above is supplied by the actual allocated table;
no user-provided FIFO-size assumption remains for a well-formed builder. -/
theorem tailCode_finishes (sizes : Nat → Nat) (incoming : Nat) (code : HybridCompactChainControl.Code)
    (b : Build) (p : Payload) (inputs : 2 ≤ b.wires.size) (fresh : incoming < b.nextQueue)
    (queues : QueueWellFormed b) (known : tailHasSendBounds code = true)
    (hx : p.wires 0 = x) (hy : p.wires 1 = y) :
    let generated := tailCode sizes incoming code b
    ∃ cycles, ((generated.1.assemble generated.2.queues).run cycles (p.at 1)).result =
      some (code.eval x y p.data (p.queues incoming)) := by
  have finalQueues := tailCode_queues sizes incoming code b queues
  obtain ⟨r,hr,ho⟩ := tailCode_correct sizes incoming code b p inputs fresh known
    (finalQueues.covers (tailCode sizes incoming code b).1) hx hy
  obtain ⟨cycles,hcycles⟩ := Schedule.assemble_finishes _ p hr
  exact ⟨cycles,by rw [hcycles,ho]⟩

end IRComparison.Circuit
