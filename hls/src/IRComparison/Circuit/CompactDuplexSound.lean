import IRComparison.Circuit.WindowIteration

namespace IRComparison.Circuit

theorem duplex_loop_iteration (code : HybridCompactDuplex.Code) (n k : Nat)
    (old : List Int) (s : State) (qi qo : List Int) :
    iterationLoop (fifoLoader code.start code.stride code.initial code.refill)
      (fun j s q vs => code.body.eval (code.start+(j:Int)*code.stride) x y s q vs) n k old s qi qo =
      code.loop x y n k old s qi qo := by
  induction n generalizing k old s qi qo with
  | zero => rfl
  | succ n ih =>
    rw [iterationLoop,HybridCompactDuplex.Code.loop]
    simp only [HybridSymbolicLoop.index]
    cases hb : code.body.eval (code.start+(k:Int)*code.stride) x y s qo old with
    | none => rfl
    | some pair =>
      obtain ⟨t,out⟩ := pair
      change (match n with
        | 0 => some (t,qi,out)
        | m+1 => (fifoLoader code.start code.stride code.initial code.refill (k+1) old qi).bind
          (fun (vs,rest) => iterationLoop _ _ (m+1) (k+1) vs t rest out)) = _
      cases n with
      | zero => rfl
      | succ m =>
        simp only [fifoLoader,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte]
        cases WindowFIFO.execute (fun _ => none) old (CompactRouting.instantiate (code.start+((k+1:Nat):Int)*code.stride) code.refill) qi with
        | none => rfl
        | some pair => obtain ⟨vs,rest⟩ := pair; exact ih (k+1) vs t rest out

theorem duplex_eval_iteration (code : HybridCompactDuplex.Code) (s : State) (qi : List Int) :
    iterationEval (fifoLoader code.start code.stride code.initial code.refill)
      (fun j s q vs => code.body.eval (code.start+(j:Int)*code.stride) x y s q vs) code.count s qi [] =
      HybridCompactDuplexControl.evalFull code x y s qi := by
  cases hc : code.count with
  | zero => simp [iterationEval,HybridCompactDuplexControl.evalFull,hc]
  | succ n =>
    simp only [iterationEval,HybridCompactDuplexControl.evalFull,hc,fifoLoader,↓reduceIte,
      Int.natCast_zero,Int.zero_mul,Int.add_zero]
    cases WindowFIFO.execute (fun _ => none) [] (CompactRouting.instantiate code.start code.initial) qi with
    | none => rfl
    | some pair => obtain ⟨vs,rest⟩ := pair; exact duplex_loop_iteration code (n+1) 0 vs s rest []

theorem duplex_sourceFold (code : HybridCompactDuplex.Code) (s : State) (qi : List Int) :
    ((List.range' 0 code.count).foldlM
      (fun st j => sourceCountedStep input code.start code.stride x y (code.initial.map fromFIFOLoad)
        (code.refill.map fromFIFOLoad) code.body j st) (s,[],qi,[])).map (fun (t,_,rest,out) => (t,rest,out)) =
      HybridCompactDuplexControl.evalFull code x y s qi := by
  simp only [sourceCountedStep_fifo]
  rw [← iterationEval_fold]
  exact duplex_eval_iteration code s qi

theorem duplex_bounded_eq (code : HybridCompactDuplex.Code) (s : State) (qi : List Int)
    (fits : ∀ t rest out, HybridCompactDuplexControl.evalFull code x y s qi = some (t,rest,out) → out.length ≤ capacity) :
    boundedCounted capacity input code.start code.stride code.count (code.initial.map fromFIFOLoad)
      (code.refill.map fromFIFOLoad) code.body x y s qi [] = HybridCompactDuplexControl.evalFull code x y s qi := by
  unfold boundedCounted
  rw [countedFold_eq]
  · exact duplex_sourceFold code s qi
  · intro result hr
    have he := duplex_sourceFold (input:=input) (x:=x) (y:=y) code s qi
    rw [hr] at he
    exact fits _ _ _ he.symm

/-- The real compact duplex controller reaches exactly the old control IR's
result, provided the final output fits its allocated finite FIFO. -/
theorem duplex_correct (code : HybridCompactDuplex.Code) (b : Build) (p : Payload)
    (inputs : 2 ≤ b.wires.size) (distinct : qi ≠ qo) (empty : p.queues qo = [])
    (hx : p.wires 0 = x) (hy : p.wires 1 = y)
    (fits : ∀ t rest out, HybridCompactDuplexControl.evalFull code x y p.data (p.queues qi) = some (t,rest,out) → out.length ≤ cap qo) :
    ∃ r, ((counted code.start code.stride code.count (code.initial.map fromFIFOLoad)
      (code.refill.map fromFIFOLoad) code.body input qi qo).run b).1.Eval cap p r ∧
      r.map (observeBlock qi qo) = HybridCompactDuplexControl.evalFull code x y p.data (p.queues qi) := by
  obtain ⟨r,hr,ho⟩ := counted_correct code.start code.stride code.count (code.initial.map fromFIFOLoad)
    (code.refill.map fromFIFOLoad) code.body input qi qo b p inputs distinct hx hy
  refine ⟨r,hr,?_⟩
  rw [empty,duplex_bounded_eq code p.data (p.queues qi) fits] at ho
  exact ho

end IRComparison.Circuit
