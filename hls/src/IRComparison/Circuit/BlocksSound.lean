import IRComparison.Circuit.LoadsSound
import IRComparison.Circuit.QueueFrame
import IRComparison.Circuit.ArrayFrame
import IRComparison.Circuit.Allocate

namespace IRComparison.Circuit

def boundedBlocks (capacity : Nat) (input : Input) (x y : Int) :
    List HybridIR.Block → List Int → State → List Int → List Int → Option (State × List Int × List Int)
  | [],_,s,qi,qo => some (s,qi,qo)
  | b::bs,old,s,qi,qo => do
      let (vs,rest) ← WindowFIFO.execute input old b.loads qi
      let (t,out) ← bounded capacity b.index x y b.body s qo vs
      boundedBlocks capacity input x y bs vs t rest out

def observeBlock (qi qo : Nat) (p : Payload) := (p.data,p.queues qi,p.queues qo)

/-- General correctness of the expanded block-sequence compiler. The frozen
input array is read-only; the input and output queues are distinct resources. -/
theorem blocks_correct (input qi qo : Nat) (old : List Expr) (bs : List HybridIR.Block)
    (b : Build) (p : Payload) (x y : Int) (values : List Int)
    (distinct : qi ≠ qo) (inputs : 2 ≤ b.wires.size)
    (readonly : ∀ block ∈ bs, input ∉ commandWrites block.body)
    (scopeOK : ∀ e ∈ old, Static b.wires.size e) (hm : Matches p.data p.wires old values)
    (hx : p.wires 0 = x) (hy : p.wires 1 = y) :
    ∃ result, ((blocks input qi qo old bs).run b).1.Eval cap p result ∧
      result.map (observeBlock qi qo) =
        boundedBlocks (cap qo) (arrayInput (p.data.arrays input)) x y bs values p.data (p.queues qi) (p.queues qo) := by
  induction bs generalizing b p old values with
  | nil => exact ⟨some p,.skip,rfl⟩
  | cons block bs ih =>
    have alloc := newSlots_shape block.loads.length b
    dsimp only [blocks,bind,pure,StateT.bind,StateT.pure,StateT.run]
    dsimp only [StateT.run] at alloc
    generalize ha : newSlots block.loads.length b = allocation at *
    obtain ⟨slots,b1⟩ := allocation
    dsimp only at alloc
    dsimp only
    have slotLength : block.loads.length = slots.length := by rw [alloc.1,List.length_range']
    have slotOrder : slots.Pairwise (· < ·) := by rw [alloc.1]; exact List.pairwise_lt_range'
    have slotBounds : ∀ n ∈ slots, b.wires.size ≤ n ∧ n < b1.wires.size := by
      intro n hn
      rw [alloc.1,List.mem_range'_1] at hn
      simpa [alloc.2] using hn
    have allocationGrows : b.wires.size ≤ b1.wires.size := by have := alloc.2; omega
    obtain ⟨loaded,hload,oload⟩ := expandedLoads_correct (cap:=cap) input qi old block.loads slots b1 p b.wires.size values
      slotLength slotOrder slotBounds allocationGrows scopeOK hm
    have loadFrame := expandedLoads_frame input qi old block.loads slots b1 b.wires.size
      allocationGrows (fun n hn => (slotBounds n hn).1) slotLength
    dsimp only [StateT.run] at hload loadFrame
    generalize hlc : expandedLoads input qi old block.loads slots b1 = loadPair at *
    obtain ⟨loadCode,b2⟩ := loadPair
    dsimp only
    cases hl : WindowFIFO.execute (arrayInput (p.data.arrays input)) values block.loads (p.queues qi) with
    | none =>
      have rr : loaded = none := by
        cases loaded with
        | none => rfl
        | some q => simp only [hl,Option.map_some,Option.map_none,Option.some_ne_none] at oload
      subst loaded
      exact ⟨none,.seq_error hload,by simp [boundedBlocks,hl]⟩
    | some pair =>
      obtain ⟨vs,rest⟩ := pair
      cases loaded with
      | none => simp [hl] at oload
      | some q =>
        have lobs : q.data = p.data ∧ slots.map q.wires = vs ∧ q.queues qi = rest := by
          simpa [hl,observeLoads] using oload
        have wiresLoad := loadCode.preserves_below hload loadFrame.2 rfl
        have keepOutput := expandedLoads_noQueue input qi old block.loads slots b1 distinct
        dsimp only [StateT.run] at keepOutput
        rw [hlc] at keepOutput
        have qout : q.queues qo = p.queues qo := loadCode.preserves_queue hload keepOutput rfl
        have bodyCtx : Context b2.wires.size (.lit block.index) (slots.map Expr.wire) q block.index x y vs := by
          refine ⟨Nat.le_trans inputs (Nat.le_trans allocationGrows loadFrame.1),.lit,?_,rfl,?_,?_,?_⟩
          · intro e he
            obtain ⟨n,hn,rfl⟩ := List.mem_map.mp he
            exact .wire (Nat.lt_of_lt_of_le (slotBounds n hn).2 loadFrame.1)
          · exact (wiresLoad 0 (by omega)).symm.trans hx
          · exact (wiresLoad 1 (by omega)).symm.trans hy
          · simpa [lobs.2.1] using (matches_wires (s:=q.data) (w:=q.wires) slots)
        obtain ⟨computed,hbody,obody⟩ := command_correct (output:=qo) (cap:=cap) block.body b2 (.lit block.index) (slots.map Expr.wire) q block.index x y vs bodyCtx
        have bodyFrame := command_frame block.body (.lit block.index) (slots.map Expr.wire) qo b2
        have bodyQueue := command_noQueue block.body b2 (.lit block.index) (slots.map Expr.wire) (Ne.symm distinct)
        dsimp only [StateT.run] at hbody bodyFrame bodyQueue
        generalize hbc : command (.lit block.index) (slots.map Expr.wire) qo block.body b2 = bodyPair at *
        obtain ⟨bodyCode,b3⟩ := bodyPair
        dsimp only
        cases computed with
        | none =>
          have failure : bounded (cap qo) block.index x y block.body p.data (p.queues qo) vs = none := by
            simpa [lobs.1,qout] using obody.symm
          exact ⟨none,.seq hload (.seq_error hbody),by simp [boundedBlocks,hl,failure]⟩
        | some t =>
          have bodyResult : bounded (cap qo) block.index x y block.body p.data (p.queues qo) vs = some (t.data,t.queues qo) := by
            simpa [observe,lobs.1,qout] using obody.symm
          have inputArray := bounded_array_frame block.body (readonly block (by simp)) bodyResult
          have qin : t.queues qi = rest := (bodyCode.preserves_queue hbody bodyQueue rfl).trans lobs.2.2
          have wiresBody := bodyCode.preserves_below hbody bodyFrame.2 rfl
          have newScope : ∀ e ∈ slots.map Expr.wire, Static b3.wires.size e := by
            intro e he
            obtain ⟨n,hn,rfl⟩ := List.mem_map.mp he
            exact .wire (Nat.lt_of_lt_of_le (slotBounds n hn).2 (Nat.le_trans loadFrame.1 bodyFrame.1))
          have newMatches : Matches t.data t.wires (slots.map Expr.wire) vs := by
            intro n
            exact ((lookup_static bodyCtx.localsScope).stable wiresBody).symm.trans (bodyCtx.locals n)
          have tx : t.wires 0 = x := (wiresBody 0 (by have := bodyCtx.inputs; omega)).symm.trans bodyCtx.left
          have ty : t.wires 1 = y := (wiresBody 1 (by have := bodyCtx.inputs; omega)).symm.trans bodyCtx.right
          obtain ⟨result,htail,otail⟩ := ih (slots.map Expr.wire) b3 t vs
            (Nat.le_trans bodyCtx.inputs bodyFrame.1) (fun bl hbl => readonly bl (by simp [hbl])) newScope newMatches tx ty
          refine ⟨result,.seq hload (.seq hbody htail),?_⟩
          simpa [boundedBlocks,hl,bodyResult,inputArray,qin] using otail

theorem boundedBlocks_complete (bs : List HybridIR.Block)
    (he : HybridIR.blocksEval input x y bs old s qi qo = some (t,rest,out)) :
    qo.length ≤ out.length ∧ (out.length ≤ capacity →
      boundedBlocks capacity input x y bs old s qi qo = some (t,rest,out)) := by
  induction bs generalizing old s qi qo with
  | nil => cases he; exact ⟨Nat.le_refl _,fun _ => rfl⟩
  | cons b bs ih =>
    cases hl : WindowFIFO.execute input old b.loads qi <;> simp [HybridIR.blocksEval,hl] at he
    next loaded =>
      obtain ⟨vs,remaining⟩ := loaded
      cases hb : b.body.eval b.index x y s qo vs <;> simp [hb] at he
      next result =>
        obtain ⟨u,qu⟩ := result
        have tail := ih he
        have head := bounded_complete (capacity:=capacity) b.body s qo vs u qu hb
        refine ⟨Nat.le_trans head.1 tail.1,fun bound => ?_⟩
        simp only [boundedBlocks,hl,bind,Option.bind,head.2 (Nat.le_trans tail.1 bound)]
        exact tail.2 bound

theorem boundedBlocks_refines (bs : List HybridIR.Block)
    (he : boundedBlocks capacity input x y bs old s qi qo = some (t,rest,out)) :
    HybridIR.blocksEval input x y bs old s qi qo = some (t,rest,out) := by
  induction bs generalizing old s qi qo with
  | nil => exact he
  | cons b bs ih =>
    cases hl : WindowFIFO.execute input old b.loads qi <;> simp [boundedBlocks,hl] at he
    next loaded =>
      obtain ⟨vs,remaining⟩ := loaded
      cases hb : bounded capacity b.index x y b.body s qo vs <;> simp [hb] at he
      next result =>
        obtain ⟨u,qu⟩ := result
        simp only [HybridIR.blocksEval,hl,bind,Option.bind,bounded_refines b.body s qo vs u qu hb]
        exact ih he

theorem boundedBlocks_eq (bs : List HybridIR.Block)
    (fits : ∀ t rest out, HybridIR.blocksEval input x y bs old s qi qo = some (t,rest,out) → out.length ≤ capacity) :
    boundedBlocks capacity input x y bs old s qi qo = HybridIR.blocksEval input x y bs old s qi qo := by
  cases hs : HybridIR.blocksEval input x y bs old s qi qo with
  | none =>
    cases ht : boundedBlocks capacity input x y bs old s qi qo with
    | none => rfl
    | some result =>
      obtain ⟨t,rest,out⟩ := result
      have he := boundedBlocks_refines bs ht
      rw [hs] at he
      cases he
  | some result =>
    obtain ⟨t,rest,out⟩ := result
    exact (boundedBlocks_complete bs hs).2 (fits t rest out hs)

end IRComparison.Circuit
