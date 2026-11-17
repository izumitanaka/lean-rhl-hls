import IRComparison.Circuit.CountedParts

namespace IRComparison.Circuit

theorem Schedule.Eval.remove_skip_middle
    (h : (Schedule.seq a (.seq .skip b)).Eval cap p r) : (Schedule.seq a b).Eval cap p r := by
  cases h with
  | seq_error h => exact .seq_error h
  | seq ha hb =>
    cases hb with
    | seq_error hs => cases hs
    | seq hs hb => cases hs; exact .seq ha hb

def CountedLayout.saved (c : CountedLayout) (initialSize refillSize j : Nat) : List Nat :=
  if j = 0 then [] else c.held.take (if j = 1 then initialSize else refillSize)

def CountedLayout.view (c : CountedLayout) (initialSize refillSize qi qo j : Nat) (p : Payload) :=
  roundView qi qo (c.saved initialSize refillSize j) p

def countedStep (capacity input : Nat) (start stride x y : Int) (initial refill : List Load)
    (body : HybridIR.Cmd) (j : Nat) (state : State × List Int × List Int × List Int) :=
  bufferStep capacity (arrayInput (state.1.arrays input)) (start+(j:Int)*stride) x y
    (if j = 0 then initial else refill) body state

theorem CountedParts.round_frame (h : CountedParts c start stride initial refill body input qi qo) :
    (c.round refill.length).above (c.counter+1) := by
  exact ⟨⟨⟨c.laterLoads.above_mono h.later.frame h.laterBound,
    c.firstRefill.above_mono h.firstRefill.frame h.refillBound⟩,
    ⟨h.move.frame,c.laterBody.above_mono h.laterBody.frame h.laterBodyBound⟩⟩,
    ⟨c.firstLoads.above_mono h.first.frame h.firstBound,
    c.firstBody.above_mono h.firstBody.frame h.firstBodyBound⟩⟩

theorem CountedParts.round_correct (h : CountedParts c start stride initial refill body input qi qo)
    (distinct : qi ≠ qo) (p : Payload) (j : Nat) (hk : p.wires c.counter = (j:Int))
    (hx : p.wires 0 = x) (hy : p.wires 1 = y) :
    ∃ r, (c.round refill.length).Eval cap p r ∧
      r.map (c.view initial.length refill.length qi qo (j+1)) =
        countedStep (cap qo) input start stride x y initial refill body j
          (c.view initial.length refill.length qi qo j p) := by
  have scopeOK : Static (c.counter+1) (c.index start stride) :=
    .bin .lit (.bin (.wire (by omega)) .lit)
  have hi : (c.index start stride).eval p.data p.wires = some (start+(j:Int)*stride) := by
    simp [CountedLayout.index,Expr.eval,Bin.eval,hk]
  have inputs : 2 ≤ c.counter+1 := by have := h.inputs; omega
  cases j with
  | zero =>
    obtain ⟨r,hr,ho⟩ := IRComparison.Circuit.round_correct (cap:=cap) h.first
      (MoveSpec.identity (low:=c.counter+1) (c.held.take initial.length)) h.firstBody
      inputs h.firstBound scopeOK distinct p hi hx hy matches_nil
    refine ⟨r,.branch_no (by simp [Expr.eval,hk]) hr.remove_skip_middle,?_⟩
    simpa [CountedLayout.view,CountedLayout.saved,countedStep,roundView] using ho
  | succ n =>
    cases n with
    | zero =>
      obtain ⟨r,hr,ho⟩ := IRComparison.Circuit.round_correct (cap:=cap) h.firstRefill h.move h.laterBody
        inputs h.refillBound scopeOK distinct p hi hx hy (matches_wires _)
      have outer : (Expr.wire c.counter).eval p.data p.wires = some 1 := by simp [Expr.eval,hk]
      have inner : (Expr.bin .sub (.wire c.counter) (.lit 1)).eval p.data p.wires = some 0 := by
        simp [Expr.eval,Bin.eval,hk]
      refine ⟨r,.branch_yes outer (by decide) ?_,?_⟩
      · cases hr with
        | seq_error hl => exact .seq_error (.branch_no inner hl)
        | seq hl hb => exact .seq (.branch_no inner hl) hb
      · simpa [CountedLayout.view,CountedLayout.saved,countedStep,roundView] using ho
    | succ n =>
      obtain ⟨r,hr,ho⟩ := IRComparison.Circuit.round_correct (cap:=cap) h.later h.move h.laterBody
        inputs h.laterBound scopeOK distinct p hi hx hy (matches_wires _)
      have outer : (Expr.wire c.counter).eval p.data p.wires = some ((n+2:Nat):Int) := by simpa [Expr.eval] using congrArg some hk
      have inner : (Expr.bin .sub (.wire c.counter) (.lit 1)).eval p.data p.wires = some ((n+1:Nat):Int) := by
        simp [Expr.eval,Bin.eval,hk]
      refine ⟨r,.branch_yes outer (by omega) ?_,?_⟩
      · cases hr with
        | seq_error hl => exact .seq_error (.branch_yes inner (by omega) hl)
        | seq hl hb => exact .seq (.branch_yes inner (by omega) hl) hb
      · simpa [CountedLayout.view,CountedLayout.saved,countedStep,roundView] using ho

end IRComparison.Circuit
