import IRComparison.Circuit.ChannelFrame

namespace IRComparison.Circuit.ChannelLower
open HybridIR

def setQueue (p : Payload) (a : Nat) (q : List Int) : Payload :=
  {p with queues := fun k => if k = a then q else p.queues k}

theorem view_setQueue (bank : Buffers) :
    bank.view (setQueue p a q) = (bank.view p).setQueue a q := rfl

/-- Correctness of the actual named-body lowerer, not an interpreter used in
place of it. FIFO capacity errors are explicit at this layer. -/
theorem lower_correct (c : ChannelCmd) (bank : Buffers) (b : Build) (i : Expr) (ls : List Expr)
    (fits : bufferCount c ≤ bank.count)
    (p : Payload) (iv xv yv : Int) (lvs : List Int)
    (ctx : Context bank b.wires.size i ls p iv xv yv lvs) :
    ∃ result, (lower bank i ls c b).1.Eval cap p result ∧
      result.map bank.view = bounded cap iv xv yv c (bank.view p) lvs := by
  induction c generalizing b i ls p iv xv yv lvs with
  | skip => exact ⟨some p,.skip,rfl⟩
  | assign r e =>
    refine ⟨_,Schedule.Eval.step,?_⟩
    simp only [Action.eval,Action.node,execute,expressionEvaluation_original,Payload.at,ctx.read e,bounded,Buffers.view]
    cases e.eval iv xv yv p.data lvs [] <;> rfl
  | store a j e =>
    refine ⟨_,Schedule.Eval.step,?_⟩
    simp only [Action.eval,Action.node,execute,expressionEvaluation_original,Payload.at,ctx.read j,ctx.read e,bounded,Buffers.view]
    cases j.eval iv xv yv p.data lvs [] with
    | none => rfl
    | some k => cases e.eval iv xv yv p.data lvs [] with
      | none => rfl
      | some v => simp only [bind,Option.bind]; cases p.data.write a k v <;> rfl
  | send a e =>
    refine ⟨_,Schedule.Eval.step,?_⟩
    simp only [Action.eval,Action.node,execute,expressionEvaluation_original,Payload.at,ctx.read e,bounded,Buffers.view]
    cases e.eval iv xv yv p.data lvs [] with
    | none => rfl
    | some v => simp only [bind,Option.bind]; split <;> rfl
  | hold slot e =>
    have hs : slot < bank.count := by change slot+1 ≤ _ at fits; omega
    cases he : e.eval iv xv yv p.data lvs [] with
    | none =>
      have hf : (Action.wire (bank.value slot) (read i (.wire 0) (.wire 1) ls [] e)).eval cap p = none := by
        simp [Action.eval,Action.node,execute,expressionEvaluation_original,Payload.at,ctx.read e,he]
      refine ⟨none,.seq_error ?_,by simp [bounded,Buffers.view,he]⟩
      rw [← hf]; exact .step
    | some v =>
      refine ⟨_,.seq (setWire_eval ((ctx.read e).trans he)) (setWire_eval (e:=.lit 1) rfl),?_⟩
      simp only [bounded,show (bank.view p).data = p.data from rfl,he,bind,Option.bind,Option.map_some]
      exact congrArg some (bank.view_set p slot hs)
  | receive a slot =>
    have hs : slot < bank.count := by change slot+1 ≤ _ at fits; omega
    cases hq : p.queues a with
    | nil =>
      have hf : (Action.receive a (bank.value slot)).eval cap p = none := by
        simp [Action.eval,Action.node,execute,expressionEvaluation_original,Payload.at,hq]
      refine ⟨none,.seq_error ?_,by simp [bounded,ChannelState.receive,Buffers.view,hq]⟩
      rw [← hf]; exact .step
    | cons v rest =>
      let q := (setQueue p a rest).setWire (bank.value slot) v
      have hr : (Schedule.step (.receive a (bank.value slot))).Eval cap p (some q) := by
        have hh : (Action.receive a (bank.value slot)).eval cap p = some q := by
          simp [Action.eval,Action.node,execute,expressionEvaluation_original,Payload.at,hq,q,setQueue,Runtime.payload,Runtime.setQueue,Runtime.setWire,Payload.setWire]
        rw [← hh]; exact .step
      refine ⟨_,.seq hr (setWire_eval (e:=.lit 1) rfl),?_⟩
      simp only [Option.map_some,bounded,ChannelState.receive,show (bank.view p).queues = p.queues from rfl,hq]
      exact congrArg some ((bank.view_set (setQueue p a rest) slot hs).trans (congrArg (fun t => t.setBuffer slot v) (view_setQueue bank)))
  | letValue e c ih =>
    let expr := read i (.wire 0) (.wire 1) ls [] e
    let b1 := b.addWire (b.exprRange expr)
    change ∃ result, (Schedule.seq (.step (.wire b.wires.size expr)) (lower bank i (.wire b.wires.size::ls) c b1).1).Eval cap p result ∧ _
    cases he : e.eval iv xv yv p.data lvs [] with
    | none =>
      have hf : (Action.wire b.wires.size expr).eval cap p = none := by simp [Action.eval,Action.node,execute,expressionEvaluation_original,Payload.at,expr,ctx.read e,he]
      refine ⟨none,.seq_error ?_,by simp [bounded,Buffers.view,he]⟩
      rw [← hf]; exact .step
    | some v =>
      have hctx : Context bank b1.wires.size i (.wire b.wires.size::ls) (p.setWire b.wires.size v) iv xv yv (v::lvs) := by
        simpa [b1,Build.addWire] using ctx.bind (v:=v)
      obtain ⟨r,hr,ho⟩ := ih b1 i (.wire b.wires.size::ls) fits (p.setWire b.wires.size v) iv xv yv (v::lvs) hctx
      refine ⟨r,.seq (setWire_eval ((ctx.read e).trans he)) hr,?_⟩
      simpa only [bounded,show (bank.view p).data = p.data from rfl,he,bind,Option.bind,bank.view_fresh p ctx.floor] using ho
  | letBuffer slot c ih =>
    let b1 := b.addWire wordRange
    have fit : bufferCount c ≤ bank.count := Nat.le_trans (Nat.le_max_right _ _) fits
    change ∃ result, (Schedule.seq (.step (.wire b.wires.size (bank.read slot))) (lower bank i (.wire b.wires.size::ls) c b1).1).Eval cap p result ∧ _
    cases he : (bank.view p).buffers slot with
    | none =>
      have hf : (Action.wire b.wires.size (bank.read slot)).eval cap p = none := by simp [Action.eval,Action.node,execute,expressionEvaluation_original,Payload.at,bank.read_correct p,he]
      refine ⟨none,.seq_error ?_,by simp [bounded,he]⟩
      rw [← hf]; exact .step
    | some v =>
      have hctx : Context bank b1.wires.size i (.wire b.wires.size::ls) (p.setWire b.wires.size v) iv xv yv (v::lvs) := by
        simpa [b1,Build.addWire] using ctx.bind (v:=v)
      obtain ⟨r,hr,ho⟩ := ih b1 i (.wire b.wires.size::ls) fit (p.setWire b.wires.size v) iv xv yv (v::lvs) hctx
      refine ⟨r,.seq (setWire_eval ((bank.read_correct p).trans he)) hr,?_⟩
      simpa only [bounded,he,bind,Option.bind,bank.view_fresh p ctx.floor] using ho
  | seq a c ia ib =>
    have fa : bufferCount a ≤ bank.count := Nat.le_trans (Nat.le_max_left _ _) fits
    have fc : bufferCount c ≤ bank.count := Nat.le_trans (Nat.le_max_right _ _) fits
    dsimp only [lower,bind,pure,StateT.bind,StateT.pure]
    obtain ⟨r,hr,ho⟩ := ia b i ls fa p iv xv yv lvs ctx
    have hf := lower_frame a bank b i ls fa
    generalize ha : lower bank i ls a b = pair at *
    obtain ⟨first,b1⟩ := pair
    dsimp only
    cases r with
    | none => exact ⟨none,.seq_error hr,by simp only [bounded,← ho]; rfl⟩
    | some q =>
      have hctx := (ctx.preserve (schedule_frame hr hf.2 rfl)).weaken hf.1
      obtain ⟨result,he,hs⟩ := ib b1 i ls fc q iv xv yv lvs hctx
      exact ⟨result,.seq hr he,by simpa only [bounded,← ho,Option.map_some,bind,Option.bind] using hs⟩
  | branch e a c ia ib =>
    have fa : bufferCount a ≤ bank.count := Nat.le_trans (Nat.le_max_left _ _) fits
    have fc : bufferCount c ≤ bank.count := Nat.le_trans (Nat.le_max_right _ _) fits
    dsimp only [lower,bind,pure,StateT.bind,StateT.pure]
    have hf := lower_frame a bank b i ls fa
    generalize ha : lower bank i ls a b = pair at *
    obtain ⟨yes,b1⟩ := pair
    dsimp only
    cases he : e.eval iv xv yv p.data lvs [] with
    | none => exact ⟨none,.branch_error ((ctx.read e).trans he),by simp [bounded,Buffers.view,he]⟩
    | some v =>
      by_cases hv : v = 0
      · subst v
        obtain ⟨r,hr,ho⟩ := ib b1 i ls fc p iv xv yv lvs (ctx.weaken hf.1)
        exact ⟨r,.branch_no ((ctx.read e).trans he) hr,by simpa [bounded,Buffers.view,he] using ho⟩
      · obtain ⟨r,hr,ho⟩ := ia b i ls fa p iv xv yv lvs ctx
        rw [ha] at hr
        exact ⟨r,.branch_yes ((ctx.read e).trans he) hv hr,by simpa [bounded,Buffers.view,he,hv] using ho⟩
  | «repeat» n c ih =>
    let k := b.wires.size
    let b1 := b.addWire ⟨0,n⟩
    let body := (lower bank i ls c b1).1
    have size : b1.wires.size = k+1 := by simp [b1,k,Build.addWire]
    have framed : frame bank (k+1) body := by simpa [body,size] using (lower_frame c bank b1 i ls fits).2
    let P := fun q => Context bank k i ls q iv xv yv lvs
    have hinc : ∀ q v, P q → P (q.setWire k v) := fun q v h => h.setFresh (Nat.le_refl _)
    have hb : ∀ (j : Nat) q, P q → q.wires k = (j:Int) →
        ∃ result, body.Eval cap q result ∧ result.map bank.view =
          bounded cap iv xv yv c (bank.view q) lvs ∧ LoopResult P k j result := by
      intro j q hq hk
      obtain ⟨r,hr,ho⟩ := ih b1 i ls fits q iv xv yv lvs (hq.weaken (by omega))
      refine ⟨r,hr,ho,?_⟩
      intro t ht
      have hw := schedule_frame hr framed ht
      exact ⟨hq.preserve (fun slot hs => hw slot ⟨by have := hs.1; omega,hs.2⟩),
        (hw k ⟨by omega,Or.inr hq.floor⟩).symm.trans hk⟩
    obtain ⟨r,hr,ho,_⟩ := counter_iterations_by (view:=bank.view) (body:=body) (counter:=k) (stop:=n) (limit:=.lit n) (P:=P)
      (f:=fun _ s => bounded cap iv xv yv c s lvs)
      (fun q v => bank.view_fresh q ctx.floor) (fun _ _ => rfl) hinc hb n 0 (by omega)
      (p.setWire k 0) (hinc p 0 ctx) (by simp [Payload.setWire])
    refine ⟨r,.seq (setWire_eval (e:=.lit 0) rfl) hr,?_⟩
    simpa only [bounded,List.range_eq_range',bank.view_fresh p (slot:=k) ctx.floor] using ho
  | forRange e c ih =>
    let expr := Expr.natIndex (read i (.wire 0) (.wire 1) ls [] e)
    let slot := b.wires.size
    let b1 := b.addWire (b.exprRange expr)
    let k := b1.wires.size
    let b2 := b1.addWire (b1.exprRange expr)
    let body := (lower bank i (.wire k::ls) c b2).1
    have size1 : k = slot+1 := by simp [k,b1,slot,Build.addWire]
    have size2 : b2.wires.size = k+1 := by simp [b2,k,Build.addWire]
    have framed : frame bank (k+1) body := by simpa [body,size2] using (lower_frame c bank b2 i (.wire k::ls) fits).2
    change ∃ result, (Schedule.seq (.step (.wire slot expr)) (counterLoop k (.wire slot) body)).Eval cap p result ∧ _
    cases he : e.eval iv xv yv p.data lvs [] with
    | none =>
      have hf : (Action.wire slot expr).eval cap p = none := by simp [Action.eval,Action.node,execute,expressionEvaluation_original,Payload.at,expr,Expr.eval,ctx.read e,he]
      refine ⟨none,.seq_error ?_,by simp [bounded,Buffers.view,he]⟩
      rw [← hf]; exact .step
    | some n =>
      let P := fun q : Payload => Context bank slot i ls q iv xv yv lvs ∧ q.wires slot = (n.toNat:Int)
      have floor : bank.stop ≤ k := by have := ctx.floor; dsimp [slot] at *; omega
      have hinc : ∀ q v, P q → P (q.setWire k v) := by
        intro q v hq
        refine ⟨hq.1.setFresh (by omega),?_⟩
        simpa [Payload.setWire,show slot ≠ k from by omega] using hq.2
      have hb : ∀ (j : Nat) q, P q → q.wires k = (j:Int) →
          ∃ result, body.Eval cap q result ∧ result.map bank.view =
            bounded cap iv xv yv c (bank.view q) ((j:Int)::lvs) ∧ LoopResult P k j result := by
        intro j q hq hk
        have hctx : Context bank b2.wires.size i (.wire k::ls) q iv xv yv ((j:Int)::lvs) := by
          have old := hq.1.weaken (show slot ≤ b2.wires.size from by omega)
          refine ⟨old.inputs,old.floor,old.indexScope,?_,old.index,old.left,old.right,?_⟩
          · intro ex hex
            rcases List.mem_cons.mp hex with rfl | hex
            · exact .wire ⟨by omega,Or.inr floor⟩
            · exact old.localsScope ex hex
          · exact matches_cons old.locals (congrArg some hk)
        obtain ⟨r,hr,ho⟩ := ih b2 i (.wire k::ls) fits q iv xv yv ((j:Int)::lvs) hctx
        refine ⟨r,hr,ho,?_⟩
        intro t ht
        have hw := schedule_frame hr framed ht
        exact ⟨⟨hq.1.preserve (fun v hv => hw v ⟨by have := hv.1; omega,hv.2⟩),
          (hw slot ⟨by omega,Or.inr hq.1.floor⟩).symm.trans hq.2⟩,
          (hw k ⟨by omega,Or.inr floor⟩).symm.trans hk⟩
      let q := p.setWire slot (n.toNat:Int)
      have hq : P q := ⟨ctx.setFresh (Nat.le_refl _),by simp [q,Payload.setWire]⟩
      obtain ⟨r,hr,ho,_⟩ := counter_iterations_by (view:=bank.view) (body:=body) (counter:=k) (stop:=n.toNat) (limit:=.wire slot) (P:=P)
        (f:=fun j s => bounded cap iv xv yv c s ((j:Int)::lvs))
        (fun q v => bank.view_fresh q floor) (fun q hq => congrArg some hq.2) hinc hb n.toNat 0 (by omega)
        (q.setWire k 0) (hinc q 0 hq) (by simp [Payload.setWire])
      have capture : (Schedule.step (.wire slot expr)).Eval cap p (some q) := by
        apply setWire_eval; simp [expr,Expr.eval,ctx.read e,he]
      refine ⟨r,.seq capture (.seq (setWire_eval (e:=.lit 0) rfl) hr),?_⟩
      simpa only [bounded,show (bank.view p).data = p.data from rfl,he,bind,Option.bind,List.range_eq_range',
        bank.view_fresh q floor,q,bank.view_fresh p (slot:=slot) ctx.floor] using ho

end IRComparison.Circuit.ChannelLower
