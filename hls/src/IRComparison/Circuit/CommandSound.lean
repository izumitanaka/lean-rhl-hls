import IRComparison.Circuit.Counter

namespace IRComparison.Circuit

/-- Correctness of the actual command compiler, including fresh temporaries,
lexical captures, dynamic counted loops, and finite FIFO failure. -/
theorem command_correct (c : HybridIR.Cmd) (b : Build) (i : Expr) (ls : List Expr)
    (p : Payload) (iv xv yv : Int) (lvs : List Int)
    (ctx : Context b.wires.size i ls p iv xv yv lvs) :
    ∃ result, ((command i ls output c).run b).1.Eval cap p result ∧
      result.map (observe output) = bounded (cap output) iv xv yv c p.data (p.queues output) lvs := by
  induction c generalizing b i ls p iv xv yv lvs with
  | skip => exact ⟨some p,.skip,rfl⟩
  | assign r e =>
    refine ⟨_,Schedule.Eval.step,?_⟩
    simp only [Action.eval,Action.node,execute,Payload.at,ctx.read e,bounded]
    cases e.eval iv xv yv p.data lvs [] <;> rfl
  | store a j e =>
    refine ⟨_,Schedule.Eval.step,?_⟩
    simp only [Action.eval,Action.node,execute,Payload.at,ctx.read j,ctx.read e,bounded]
    cases j.eval iv xv yv p.data lvs [] with
    | none => rfl
    | some k => cases e.eval iv xv yv p.data lvs [] with
      | none => rfl
      | some v => simp only [bind,Option.bind]; cases p.data.write a k v <;> rfl
  | send e =>
    refine ⟨_,Schedule.Eval.step,?_⟩
    simp only [Action.eval,Action.node,execute,Payload.at,ctx.read e,bounded]
    cases e.eval iv xv yv p.data lvs [] with
    | none => rfl
    | some v => simp only [bind,Option.bind]; split <;> simp [Runtime.payload,Runtime.setQueue,observe]
  | letValue e c ih =>
    let expr := read i (.wire 0) (.wire 1) ls [] e
    let b1 := b.addWire (b.exprRange expr)
    change ∃ result, (Schedule.seq (.step (.wire b.wires.size expr)) (command i (.wire b.wires.size::ls) output c b1).1).Eval cap p result ∧ _
    cases he : e.eval iv xv yv p.data lvs [] with
    | none =>
      have hfail : (Action.wire b.wires.size expr).eval cap p = none := by
        simp [Action.eval,Action.node,execute,Payload.at,expr,ctx.read e,he]
      refine ⟨none,.seq_error ?_,by simp [bounded,he]⟩
      rw [← hfail]; exact .step
    | some v =>
      have hctx : Context b1.wires.size i (.wire b.wires.size::ls) (p.setWire b.wires.size v) iv xv yv (v::lvs) := by
        simpa [b1,Build.addWire] using (ctx.bind (v:=v))
      obtain ⟨r,hr,ho⟩ := ih b1 i (.wire b.wires.size::ls) (p.setWire b.wires.size v) iv xv yv (v::lvs) hctx
      refine ⟨r,.seq (setWire_eval ((ctx.read e).trans he)) hr,?_⟩
      simpa [bounded,he,Payload.setWire] using ho
  | seq a c ia ib =>
    dsimp only [command,bind,pure,StateT.bind,StateT.pure,StateT.run]
    obtain ⟨r,hr,ho⟩ := ia b i ls p iv xv yv lvs ctx
    have frame := command_frame a i ls output b
    dsimp only [StateT.run] at hr frame
    generalize ha : command i ls output a b = pair at *
    obtain ⟨first,b1⟩ := pair
    dsimp only
    cases r with
    | none => exact ⟨none,.seq_error hr,by simp only [bounded,← ho]; rfl⟩
    | some q =>
      have below := first.preserves_below hr frame.2 rfl
      have ctx' := (ctx.preserve below).weaken frame.1
      obtain ⟨r',hr',ho'⟩ := ib b1 i ls q iv xv yv lvs ctx'
      refine ⟨r',.seq hr hr',?_⟩
      simpa only [bounded,← ho,Option.map_some,observe,bind,Option.bind] using ho'
  | branch e a c ia ib =>
    dsimp only [command,bind,pure,StateT.bind,StateT.pure,StateT.run]
    have frame := command_frame a i ls output b
    dsimp only [StateT.run] at frame
    generalize ha : command i ls output a b = pair at *
    obtain ⟨yes,b1⟩ := pair
    dsimp only
    cases he : e.eval iv xv yv p.data lvs [] with
    | none => exact ⟨none,.branch_error ((ctx.read e).trans he),by simp [bounded,he]⟩
    | some v =>
      by_cases hv : v = 0
      · subst v
        obtain ⟨r,hr,ho⟩ := ib b1 i ls p iv xv yv lvs (ctx.weaken frame.1)
        exact ⟨r,.branch_no ((ctx.read e).trans he) hr,by simpa [bounded,he] using ho⟩
      · obtain ⟨r,hr,ho⟩ := ia b i ls p iv xv yv lvs ctx
        dsimp only [StateT.run] at hr
        rw [ha] at hr
        exact ⟨r,.branch_yes ((ctx.read e).trans he) hv hr,by simpa [bounded,he,hv] using ho⟩
  | «repeat» n c ih =>
    let k := b.wires.size
    let b1 := b.addWire ⟨0,n⟩
    let body := (command i ls output c b1).1
    have size : b1.wires.size = k+1 := by simp [b1,k,Build.addWire]
    have frame : body.above (k+1) := by simpa [body,StateT.run,size] using (command_frame c i ls output b1).2
    let P := fun q => Context k i ls q iv xv yv lvs
    have hinc : ∀ q v, P q → P (q.setWire k v) := fun q v h => h.preserve q.setWire_below
    have hb : ∀ (j : Nat) q, P q → q.wires k = (j : Int) →
        ∃ result, body.Eval cap q result ∧ result.map (observe output) =
          bounded (cap output) iv xv yv c q.data (q.queues output) lvs ∧ LoopResult P k j result := by
      intro j q hq hk
      have hctx : Context b1.wires.size i ls q iv xv yv lvs := hq.weaken (by omega)
      obtain ⟨r,hr,ho⟩ := ih b1 i ls q iv xv yv lvs hctx
      refine ⟨r,hr,ho,?_⟩
      intro t ht
      have hw := body.preserves_below hr frame ht
      exact ⟨hq.preserve (hw.mono (by omega)),(hw k (by omega)).symm.trans hk⟩
    obtain ⟨r,hr,ho,_⟩ := counter_iterations (body:=body) (counter:=k) (stop:=n) (limit:=.lit n) (P:=P)
      (f:=fun _ s => bounded (cap output) iv xv yv c s.1 s.2 lvs)
      (fun _ _ => rfl) hinc hb n 0 (by omega) (p.setWire k 0) (hinc p 0 ctx) (by simp [Payload.setWire])
    refine ⟨r,.seq (setWire_eval (e:=.lit 0) rfl) hr,?_⟩
    simpa [bounded,List.range_eq_range',setWire_observe] using ho
  | forRange e c ih =>
    let expr := Expr.natIndex (read i (.wire 0) (.wire 1) ls [] e)
    let slot := b.wires.size
    let b1 := b.addWire (b.exprRange expr)
    let k := b1.wires.size
    let b2 := b1.addWire (b1.exprRange expr)
    let body := (command i (.wire k::ls) output c b2).1
    have size1 : k = slot+1 := by simp [k,b1,slot,Build.addWire]
    have size2 : b2.wires.size = k+1 := by simp [b2,k,Build.addWire]
    have frame : body.above (k+1) := by simpa [body,StateT.run,size2] using (command_frame c i (.wire k::ls) output b2).2
    change ∃ result, (Schedule.seq (.step (.wire slot expr)) (counterLoop k (.wire slot) body)).Eval cap p result ∧ _
    cases he : e.eval iv xv yv p.data lvs [] with
    | none =>
      have hfail : (Action.wire slot expr).eval cap p = none := by
        simp [Action.eval,Action.node,execute,Payload.at,expr,Expr.eval,ctx.read e,he]
      refine ⟨none,.seq_error ?_,by simp [bounded,he]⟩
      rw [← hfail]; exact .step
    | some n =>
      let P := fun q : Payload => Context slot i ls q iv xv yv lvs ∧ q.wires slot = (n.toNat : Int)
      have hinc : ∀ q v, P q → P (q.setWire k v) := by
        intro q v hq
        refine ⟨hq.1.preserve ((q.setWire_below (n:=k) (v:=v)).mono (by omega)),?_⟩
        simpa [Payload.setWire,show slot ≠ k from by omega] using hq.2
      have hb : ∀ (j : Nat) q, P q → q.wires k = (j : Int) →
          ∃ result, body.Eval cap q result ∧ result.map (observe output) =
            bounded (cap output) iv xv yv c q.data (q.queues output) ((j:Int)::lvs) ∧ LoopResult P k j result := by
        intro j q hq hk
        have hctx : Context b2.wires.size i (.wire k::ls) q iv xv yv ((j:Int)::lvs) := by
          have old := hq.1.weaken (show slot ≤ b2.wires.size from by omega)
          refine ⟨old.inputs,old.indexScope,?_,old.index,old.left,old.right,?_⟩
          · intro ex hex
            rcases List.mem_cons.mp hex with rfl | hex
            · exact .wire (by omega)
            · exact old.localsScope ex hex
          · exact matches_cons old.locals (congrArg some hk)
        obtain ⟨r,hr,ho⟩ := ih b2 i (.wire k::ls) q iv xv yv ((j:Int)::lvs) hctx
        refine ⟨r,hr,ho,?_⟩
        intro t ht
        have hw := body.preserves_below hr frame ht
        exact ⟨⟨hq.1.preserve (hw.mono (by omega)),(hw slot (by omega)).symm.trans hq.2⟩,
          (hw k (by omega)).symm.trans hk⟩
      let q := p.setWire slot (n.toNat : Int)
      have hq : P q := ⟨ctx.preserve p.setWire_below,by simp [q,Payload.setWire]⟩
      obtain ⟨r,hr,ho,_⟩ := counter_iterations (body:=body) (counter:=k) (stop:=n.toNat) (limit:=.wire slot) (P:=P)
        (f:=fun j s => bounded (cap output) iv xv yv c s.1 s.2 ((j:Int)::lvs))
        (fun q hq => congrArg some hq.2) hinc hb n.toNat 0 (by omega)
        (q.setWire k 0) (hinc q 0 hq) (by simp [Payload.setWire])
      have capture : (Schedule.step (.wire slot expr)).Eval cap p (some q) := by
        apply setWire_eval
        simp [expr,Expr.eval,ctx.read e,he]
      refine ⟨r,.seq capture (.seq (setWire_eval (e:=.lit 0) rfl) hr),?_⟩
      simpa [bounded,he,List.range_eq_range',setWire_observe,q,Payload.setWire,observe] using ho

end IRComparison.Circuit
