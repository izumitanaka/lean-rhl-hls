import IRComparison.Circuit.StaticCapacity
import IRComparison.Circuit.RegionsSound
import IRComparison.Hybrid.HybridSymbolicGlobal

/-! A proof-only finite execution reference. The hardware generator never
constructs this list: it emits one counted loop. This reference lets us reuse
the existing instruction/queue composition proof without a second semantics. -/
namespace IRComparison.Circuit
open HybridSymbolicGlobal

def referenceBlocks (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) : List HybridIR.Block :=
  (List.range count).map fun (j : Nat) =>
    ⟨start+(j:Int)*stride,((if j = 0 then initial else refill).map (Load.at (start+(j:Int)*stride))),body⟩

theorem blocks_iteration (indices : List Nat) (index : Nat → Int)
    (items : Nat → List WindowFIFO.Load) (body : HybridIR.Cmd) (s : State) (old qi qo : List Int) :
    HybridIR.blocksEval input x y (indices.map (fun j => ⟨index j,items j,body⟩)) old s qi qo =
      (indices.foldlM (fun (st : WindowState) j => do
        let (t,vs,rest,out) := st
        let (values,remaining) ← WindowFIFO.execute input vs (items j) rest
        let (u,output) ← body.eval (index j) x y t out values
        pure (u,values,remaining,output)) (s,old,qi,qo)).map (fun (st : WindowState) => (st.1,st.2.2)) := by
  induction indices generalizing s old qi qo with
  | nil => rfl
  | cons j js ih =>
    simp only [List.map_cons,HybridIR.blocksEval,List.foldlM_cons]
    cases hl : WindowFIFO.execute input old (items j) qi with
    | none => rfl
    | some pair =>
      obtain ⟨vs,rest⟩ := pair
      simp only [bind,Option.bind]
      cases hb : body.eval (index j) x y s qo vs with
      | none => rfl
      | some pair => obtain ⟨t,out⟩ := pair; exact ih t vs rest out

theorem reference_eval (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) :
    HybridIR.blocksEval input x y (referenceBlocks start stride count initial refill body) [] s qi qo =
      iterationEval (frozenLoader input start stride initial refill)
        (fun j s q vs => body.eval (start+(j:Int)*stride) x y s q vs) count s qi qo := by
  rw [referenceBlocks,blocks_iteration,iterationEval_fold]
  simp only [List.range_eq_range',iterationStep,frozenLoader]

def symbolicReference (c : Instruction) : HybridIR.Instruction :=
  let body := symbolicBody c
  ⟨symbolicInput c,symbolicMode c,symbolicOutput c,
    referenceBlocks body.start body.stride body.count (symbolicInitial c) (symbolicRefill c) body.body⟩



theorem frozen_fifo (initial refill : List CompactRouting.Load) :
    frozenLoader input start stride (initial.map fromFIFOLoad) (refill.map fromFIFOLoad) =
      fifoLoader start stride initial refill := by
  funext j old q
  simp only [frozenLoader,fifoLoader]
  by_cases h : j = 0 <;> simp only [h,↓reduceIte,fifoLoads_at,HybridCompactFIFO.execute_input (other:=fun _ => none)]

theorem symbolicReference_correct (c : Instruction) :
    (symbolicReference c).eval x y s qs = c.eval x y s qs := by
  cases c with
  | memory a code =>
    simp only [symbolicReference,symbolicBody,symbolicInput,symbolicMode,symbolicOutput,
      symbolicInitial,symbolicRefill,HybridIR.Instruction.eval,GlobalPipeline.InputMode.eval,Bool.false_eq_true,↓reduceIte,bind,Option.bind,reference_eval]
    have h := producer_eval_iteration (input:=arrayInput (s.arrays a)) (x:=x) (y:=y) (HybridRegions.Region.mk a code).producer s []
    rw [HybridRegions.producer_eval] at h
    dsimp only [HybridRegions.Region.producer] at h ⊢
    rw [h]
    simp only [Instruction.eval,HybridRegions.Region.producer,Option.map_map,Function.comp_def]
    cases code.eval (arrayInput (s.arrays a)) x y s <;> rfl
  | producer a b code =>
    simp only [symbolicReference,symbolicBody,symbolicInput,symbolicMode,symbolicOutput,
      symbolicInitial,symbolicRefill,HybridIR.Instruction.eval,GlobalPipeline.InputMode.eval,Bool.false_eq_true,↓reduceIte,bind,Option.bind,reference_eval]
    rw [producer_eval_iteration code]
    simp only [Instruction.eval]
    cases code.eval (arrayInput (s.arrays a)) x y (StreamConsumer.erase b s) <;> rfl
  | receiver a code =>
    simp only [symbolicReference,symbolicBody,symbolicInput,symbolicMode,symbolicOutput,symbolicInitial,symbolicRefill,
      HybridIR.Instruction.eval,GlobalPipeline.InputMode.eval,bind,Option.bind,reference_eval,frozen_fifo]
    have h := duplex_eval_iteration (x:=x) (y:=y) (receiverDuplex code) s (qs a)
    dsimp only [receiverDuplex] at h
    have hr := receiver_eval_duplex (x:=x) (y:=y) code s (qs a)
    dsimp only [receiverDuplex] at hr
    rw [h,hr]
    simp only [Instruction.eval]
    cases code.eval x y s (qs a) <;> rfl
  | duplex a b code =>
    simp only [symbolicReference,symbolicBody,symbolicInput,symbolicMode,symbolicOutput,symbolicInitial,symbolicRefill,
      HybridIR.Instruction.eval,GlobalPipeline.InputMode.eval,bind,Option.bind,reference_eval,frozen_fifo]
    rw [duplex_eval_iteration]
    have h := HybridCompactDuplexControl.evalFull_correct (x:=x) (y:=y) (s:=StreamConsumer.erase b s) (qi:=qs a) code
    rw [Instruction.eval,← h,Option.map_map]
    cases HybridCompactDuplexControl.evalFull code x y (StreamConsumer.erase b s) (qs a) <;> rfl

theorem symbolicReference_execute (cs : List Instruction) :
    HybridIR.execute x y (cs.map symbolicReference) s qs = HybridSymbolicGlobal.execute x y cs s qs := by
  induction cs generalizing s qs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons,HybridIR.execute,HybridSymbolicGlobal.execute,symbolicReference_correct]
    cases c.eval x y s qs with
    | none => rfl
    | some pair => exact ih



theorem counted_full_reference (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) (b : Build) (p : Payload)
    (inputs : 2 ≤ b.wires.size) (distinct : qi ≠ qo) (empty : p.queues qo = [])
    (readonly : input ∉ commandWrites body) (hx : p.wires 0 = x) (hy : p.wires 1 = y)
    (known : sendBound body = some bound) (capacity : count*bound ≤ cap qo) :
    ∃ r, (counted start stride count initial refill body input qi qo b).1.Eval cap p r ∧
      r.map (fun q => (q.data,q.queues)) =
        (HybridIR.blocksEval (arrayInput (p.data.arrays input)) x y
          (referenceBlocks start stride count initial refill body) [] p.data (p.queues qi) []).map
          (fun (t,rest,out) => (t,GlobalPipeline.put (GlobalPipeline.put p.queues qi rest) qo out)) := by
  obtain ⟨r,hr,ho⟩ := counted_correct start stride count initial refill body input qi qo b p inputs distinct hx hy
  rw [empty,boundedCounted,countedFold_eq] at ho
  · rw [sourceCountedFold_frozen _ _ readonly rfl,← iterationEval_fold,← reference_eval] at ho
    refine ⟨r,hr,?_⟩
    rw [← ho,Option.map_map]
    cases r with
    | none => rfl
    | some q =>
      simp only [Option.map_some,observeBlock,Function.comp_def]
      congr 2
      funext n
      by_cases hout : n = qo
      · subst n; simp [GlobalPipeline.put]
      · by_cases hin : n = qi
        · subst n; simp [GlobalPipeline.put,distinct]
        · have frame := counted_noQueue start stride count initial refill body input qi qo b inputs (Ne.symm hin) (Ne.symm hout)
          have same := (counted start stride count initial refill body input qi qo b).1.preserves_queue hr frame rfl
          simpa [GlobalPipeline.put,hout,hin] using same
  · intro result he
    have h := countedFold_sendBound known (List.range' 0 count) (p.data,[],p.queues qi,[]) result he
    simp only [List.length_nil,List.length_range',Nat.zero_add] at h
    exact Nat.le_trans h capacity

theorem reference_budget (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (known : sendBound body = some bound) :
    blocksBudget (referenceBlocks start stride count initial refill body) = some (count*bound) := by
  have helper : ∀ (js : List Nat), blocksBudget (js.map (fun (j : Nat) =>
      HybridIR.Block.mk (start+(j:Int)*stride)
        ((if j = 0 then initial else refill).map (Load.at (start+(j:Int)*stride))) body)) = some (js.length*bound) := by
    intro js
    induction js with
    | nil => simp [blocksBudget]
    | cons j js ih => simp [List.map_cons,blocksBudget,known,ih,Nat.add_mul,Nat.add_comm]
  simpa only [referenceBlocks,List.length_range] using helper (List.range count)

end IRComparison.Circuit
