import IRComparison.Circuit.FrozenWindow

namespace IRComparison.Circuit

theorem producer_loop_iteration (code : HybridSymbolicProducerLoop.Code) (n k : Nat)
    (old : List Int) (s : State) (qi qo : List Int) :
    iterationLoop (frozenLoader input code.start code.stride (code.initial.map fromMemoryLoad) (code.refill.map fromMemoryLoad))
      (fun j s q vs => code.body.eval (code.start+(j:Int)*code.stride) x y s q vs) n k old s qi qo =
      (code.loop input x y n k old s qo).map (fun (t,out) => (t,qi,out)) := by
  induction n generalizing k old s qi qo with
  | zero => rfl
  | succ n ih =>
    rw [iterationLoop,HybridSymbolicProducerLoop.Code.loop]
    simp only [HybridSymbolicLoop.index]
    cases hb : code.body.eval (code.start+(k:Int)*code.stride) x y s qo old with
    | none => rfl
    | some pair =>
      obtain ⟨t,out⟩ := pair
      simp only [bind,Option.bind]
      cases n with
      | zero => rfl
      | succ m =>
        simp only [frozenLoader_memory,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte]
        cases hl : SymbolicWindowSchedule.execute input (code.start+((k+1:Nat):Int)*code.stride) old code.refill with
        | none => rfl
        | some vs => exact ih (k+1) vs t qi out

theorem producer_eval_iteration (code : HybridSymbolicProducerLoop.Code) (s : State) (qi : List Int) :
    iterationEval (frozenLoader input code.start code.stride (code.initial.map fromMemoryLoad) (code.refill.map fromMemoryLoad))
      (fun j s q vs => code.body.eval (code.start+(j:Int)*code.stride) x y s q vs) code.count s qi [] =
      (code.eval input x y s).map (fun (t,out) => (t,qi,out)) := by
  cases hc : code.count with
  | zero => simp [iterationEval,HybridSymbolicProducerLoop.Code.eval,hc]
  | succ n =>
    simp only [iterationEval,HybridSymbolicProducerLoop.Code.eval,hc,frozenLoader_memory,↓reduceIte,
      Int.natCast_zero,Int.zero_mul,Int.add_zero]
    cases SymbolicWindowSchedule.execute input code.start [] code.initial with
    | none => rfl
    | some vs => exact producer_loop_iteration code (n+1) 0 vs s qi []

theorem producer_sourceFold (code : HybridSymbolicProducerLoop.Code) (s : State) (qi : List Int)
    (readonly : input ∉ commandWrites code.body) :
    ((List.range' 0 code.count).foldlM
      (fun st j => sourceCountedStep input code.start code.stride x y (code.initial.map fromMemoryLoad)
        (code.refill.map fromMemoryLoad) code.body j st) (s,[],qi,[])).map (fun (t,_,rest,out) => (t,rest,out)) =
      (code.eval (arrayInput (s.arrays input)) x y s).map (fun (t,out) => (t,qi,out)) := by
  rw [sourceCountedFold_frozen _ _ readonly rfl,← iterationEval_fold]
  exact producer_eval_iteration code s qi

theorem producer_bounded_eq (code : HybridSymbolicProducerLoop.Code) (s : State) (qi : List Int)
    (readonly : input ∉ commandWrites code.body)
    (fits : ∀ t out, code.eval (arrayInput (s.arrays input)) x y s = some (t,out) → out.length ≤ capacity) :
    boundedCounted capacity input code.start code.stride code.count (code.initial.map fromMemoryLoad)
      (code.refill.map fromMemoryLoad) code.body x y s qi [] =
      (code.eval (arrayInput (s.arrays input)) x y s).map (fun (t,out) => (t,qi,out)) := by
  unfold boundedCounted
  rw [countedFold_eq]
  · exact producer_sourceFold code s qi readonly
  · intro result hr
    have he := producer_sourceFold (input:=input) (x:=x) (y:=y) code s qi readonly
    rw [hr] at he
    cases hs : code.eval (arrayInput (s.arrays input)) x y s with
    | none => simp [hs] at he
    | some pair =>
      obtain ⟨t,out⟩ := pair
      simp only [hs,Option.map_some,Option.some.injEq,Prod.mk.injEq] at he
      rw [he.2.2]
      exact fits t out hs

/-- Producer lowering reads from its frozen snapshot. The source array itself
may be updated by the program; only the fresh snapshot must remain read-only. -/
theorem producer_correct (code : HybridSymbolicProducerLoop.Code) (b : Build) (p : Payload)
    (inputs : 2 ≤ b.wires.size) (distinct : qi ≠ qo) (empty : p.queues qo = [])
    (readonly : input ∉ commandWrites code.body) (hx : p.wires 0 = x) (hy : p.wires 1 = y)
    (fits : ∀ t out, code.eval (arrayInput (p.data.arrays input)) x y p.data = some (t,out) → out.length ≤ cap qo) :
    ∃ r, ((counted code.start code.stride code.count (code.initial.map fromMemoryLoad)
      (code.refill.map fromMemoryLoad) code.body input qi qo).run b).1.Eval cap p r ∧
      r.map (observeBlock qi qo) =
        (code.eval (arrayInput (p.data.arrays input)) x y p.data).map (fun (t,out) => (t,p.queues qi,out)) := by
  obtain ⟨r,hr,ho⟩ := counted_correct code.start code.stride code.count (code.initial.map fromMemoryLoad)
    (code.refill.map fromMemoryLoad) code.body input qi qo b p inputs distinct hx hy
  refine ⟨r,hr,?_⟩
  rw [empty,producer_bounded_eq code p.data (p.queues qi) readonly fits] at ho
  exact ho

end IRComparison.Circuit
