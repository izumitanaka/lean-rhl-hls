import IRComparison.Circuit.SendBound
import IRComparison.Circuit.CompactProducerSound
import IRComparison.Circuit.CompactReceiverSound

namespace IRComparison.Circuit

theorem sendBound_memory (c : HybridIR.MemoryCmd) : sendBound c.target = some 0 := by
  induction c with
  | skip | assign | store => rfl
  | letValue e b ih => exact ih
  | seq a b ia ib | branch e a b ia ib => simp [HybridIR.MemoryCmd.target,sendBound,ia,ib]
  | «repeat» n b ih => simp [HybridIR.MemoryCmd.target,sendBound,ih]
  | forRange e b ih => simp [HybridIR.MemoryCmd.target,sendBound,ih]

theorem blocksBudget_sound (blocks : List HybridIR.Block) (hb : blocksBudget blocks = some budget)
    (he : HybridIR.blocksEval input x y blocks old s qi qo = some (t,rest,out)) :
    out.length ≤ qo.length+budget := by
  induction blocks generalizing budget old s qi qo with
  | nil => cases he; simp [blocksBudget] at hb; subst budget; omega
  | cons block blocks ih =>
    cases bf : sendBound block.body <;> simp [blocksBudget,bf] at hb
    next first =>
      cases bt : blocksBudget blocks <;> simp [bt] at hb
      next tail =>
        subst budget
        cases hl : WindowFIFO.execute input old block.loads qi <;> simp [HybridIR.blocksEval,hl] at he
        next loaded =>
          obtain ⟨values,remaining⟩ := loaded
          cases hc : block.body.eval block.index x y s qo values <;> simp [hc] at he
          next computed =>
            obtain ⟨u,qu⟩ := computed
            have head := sendBound_sound block.body bf hc
            have rest := ih bt he
            dsimp only at head rest
            omega

theorem duplex_sendBound (code : HybridCompactDuplex.Code) (hb : sendBound code.body = some bound)
    (he : HybridCompactDuplexControl.evalFull code x y s qi = some (t,rest,out)) :
    out.length ≤ code.count*bound := by
  have eq := duplex_sourceFold (input:=0) (x:=x) (y:=y) code s qi
  cases hf : (List.range' 0 code.count).foldlM (fun st j => sourceCountedStep 0 code.start code.stride x y
      (code.initial.map fromFIFOLoad) (code.refill.map fromFIFOLoad) code.body j st) (s,[],qi,[]) with
  | none => simp [hf,he] at eq
  | some result =>
    have hbound := countedFold_sendBound hb (List.range' 0 code.count) (s,[],qi,[]) result hf
    simp only [hf,he,Option.map_some,Option.some.injEq,Prod.mk.injEq] at eq
    simpa [eq.2.2] using hbound

theorem producer_sendBound (code : HybridSymbolicProducerLoop.Code) (hb : sendBound code.body = some bound)
    (readonly : input ∉ commandWrites code.body)
    (he : code.eval (arrayInput (s.arrays input)) x y s = some (t,out)) : out.length ≤ code.count*bound := by
  have eq := producer_sourceFold (input:=input) (x:=x) (y:=y) code s [] readonly
  cases hf : (List.range' 0 code.count).foldlM (fun st j => sourceCountedStep input code.start code.stride x y
      (code.initial.map fromMemoryLoad) (code.refill.map fromMemoryLoad) code.body j st) (s,[],[],[]) with
  | none => simp [hf,he] at eq
  | some result =>
    have hbound := countedFold_sendBound hb (List.range' 0 code.count) (s,[],[],[]) result hf
    simp only [hf,he,Option.map_some,Option.some.injEq,Prod.mk.injEq] at eq
    simpa [eq.2.2] using hbound

/-- Capacity follows from the compiler's static send budget, independently of
data values and of the old logical array/FIFO correspondence. -/
theorem duplex_static_correct (code : HybridCompactDuplex.Code) (b : Build) (p : Payload)
    (inputs : 2 ≤ b.wires.size) (distinct : qi ≠ qo) (empty : p.queues qo = [])
    (hx : p.wires 0 = x) (hy : p.wires 1 = y)
    (known : sendBound code.body = some bound) (capacity : code.count*bound ≤ cap qo) :
    ∃ r, ((counted code.start code.stride code.count (code.initial.map fromFIFOLoad)
      (code.refill.map fromFIFOLoad) code.body input qi qo).run b).1.Eval cap p r ∧
      r.map (observeBlock qi qo) = HybridCompactDuplexControl.evalFull code x y p.data (p.queues qi) :=
  duplex_correct code b p inputs distinct empty hx hy (fun _ _ _ he => Nat.le_trans (duplex_sendBound code known he) capacity)

theorem producer_static_correct (code : HybridSymbolicProducerLoop.Code) (b : Build) (p : Payload)
    (inputs : 2 ≤ b.wires.size) (distinct : qi ≠ qo) (empty : p.queues qo = [])
    (readonly : input ∉ commandWrites code.body) (hx : p.wires 0 = x) (hy : p.wires 1 = y)
    (known : sendBound code.body = some bound) (capacity : code.count*bound ≤ cap qo) :
    ∃ r, ((counted code.start code.stride code.count (code.initial.map fromMemoryLoad)
      (code.refill.map fromMemoryLoad) code.body input qi qo).run b).1.Eval cap p r ∧
      r.map (observeBlock qi qo) =
        (code.eval (arrayInput (p.data.arrays input)) x y p.data).map (fun (t,out) => (t,p.queues qi,out)) :=
  producer_correct code b p inputs distinct empty readonly hx hy (fun _ _ he =>
    Nat.le_trans (producer_sendBound code known readonly he) capacity)

end IRComparison.Circuit
