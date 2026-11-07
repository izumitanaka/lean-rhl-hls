import IRComparison.Circuit.ExpandedFrame

namespace IRComparison.Circuit

/-- Strengthen the block compiler's queue observations to the entire queue
bank. Every unrelated channel is unchanged, which supports non-adjacent and
interleaved stage connections. -/
theorem blocks_full_correct (input qi qo : Nat) (old : List Expr) (bs : List HybridIR.Block)
    (b : Build) (p : Payload) (x y : Int) (values : List Int)
    (distinct : qi ≠ qo) (inputs : 2 ≤ b.wires.size)
    (readonly : ∀ block ∈ bs, input ∉ commandWrites block.body)
    (scopeOK : ∀ e ∈ old, Static b.wires.size e) (hm : Matches p.data p.wires old values)
    (hx : p.wires 0 = x) (hy : p.wires 1 = y)
    (known : blocksBudget bs = some budget) (capacity : (p.queues qo).length+budget ≤ cap qo) :
    ∃ result, (blocks input qi qo old bs b).1.Eval cap p result ∧
      result.map (fun q => (q.data,q.queues)) =
        (HybridIR.blocksEval (arrayInput (p.data.arrays input)) x y bs values p.data (p.queues qi) (p.queues qo)).map
          (fun (t,rest,out) => (t,GlobalPipeline.put (GlobalPipeline.put p.queues qi rest) qo out)) := by
  obtain ⟨r,hr,ho⟩ := blocks_static_correct input qi qo old bs b p x y values distinct inputs readonly scopeOK hm hx hy known capacity
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
      · have frame := blocks_noQueue input qi qo old bs b (Ne.symm hin) (Ne.symm hout)
        have same := (blocks input qi qo old bs b).1.preserves_queue hr frame rfl
        simpa [GlobalPipeline.put,hout,hin] using same

end IRComparison.Circuit
