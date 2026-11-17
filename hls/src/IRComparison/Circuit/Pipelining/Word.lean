import IRComparison.Circuit.Pipelining.Integration
import IRComparison.Circuit.Capacity
import IRComparison.Hybrid.HybridWordGlobal

namespace IRComparison.Circuit.Pipelining

theorem bounded_memory (c : HybridIR.MemoryCmd) (s : State) (q ls : List Int)
    (fits : q.length ≤ capacity) :
    bounded capacity i x y c.target s q ls = (c.eval i x y s ls).map (fun t => (t,q)) := by
  rw [bounded_eq c.target,HybridIR.MemoryCmd.target_correct]
  intro t qs h
  rw [HybridIR.MemoryCmd.target_correct] at h
  cases he : c.eval i x y s ls <;> simp [he] at h
  rcases h with ⟨_,rfl⟩
  exact fits

theorem boundedLoop_word (body : HybridWord.Cmd) (x y : HybridWord.Word) (stride : Int)
    (count : Nat) (start : Int) (s : HybridWord.State) (q : List Int) (fits : q.length ≤ capacity) :
    boundedLoop body.lower.target capacity (HybridWord.encode x) (HybridWord.encode y)
      stride count start (s.encode,q) =
    (HybridWord.iterate body x y stride count start s).map (fun t => (t.encode,q)) := by
  induction count generalizing start s with
  | zero => rfl
  | succ n ih =>
    have lower := HybridWord.Cmd.lower_correct_int (x := x) (y := y) start body s []
    simp only [List.map_nil] at lower
    simp only [boundedLoop,bounded_memory body.lower _ _ _ fits,lower,HybridWord.iterate]
    cases body.eval (BitVec.ofInt 32 start) x y s [] <;> simp [ih]

def wordPayload (s : HybridWord.State) (x y : HybridWord.Word) : Payload :=
  ⟨s.encode,fun n => if n = 0 then HybridWord.encode x else if n = 1 then HybridWord.encode y else 0,
    fun _ => []⟩

def pipelineWord (k : HybridWord.Kernel) (b : Build) (ii : Nat) : Transformed × Build :=
  pipelineCommands k.body.lower.target 0 k.stride k.count k.start b ii

/-- Ordinary Lean kernel → existing BV32/mixed/control code → overlapping
clock schedule. The only source premise is the existing Kernel.correct;
there is no new per-example scheduling proof or trusted SMT answer. -/
theorem pipelineWord_correct (k : HybridWord.Kernel) (b : Build) (hb : 2 ≤ b.wires.size)
    (ii : Nat) (s : HybridWord.State) (x y : HybridWord.Word) :
    ∃ result, (pipelineWord k b ii).1.Eval cap (wordPayload s x y) result ∧
      result.map Payload.data = (k.source x y s).map HybridWord.State.encode := by
  obtain ⟨r,he,ho⟩ := pipelineCommands_correct k.body.lower.target 0 k.stride k.count k.start
    b (wordPayload s x y) hb ii (cap := cap)
  refine ⟨r,he,?_⟩
  have source : boundedLoop k.body.lower.target (cap 0) (HybridWord.encode x) (HybridWord.encode y)
      k.stride k.count k.start (s.encode,[]) =
      (k.source x y s).map (fun t => (t.encode,[])) := by
    rw [boundedLoop_word k.body x y k.stride k.count k.start s [] (by simp),HybridWord.iterate_native]
    rfl
  have ho' : r.map (observe 0) = (k.source x y s).map (fun t => (t.encode,[])) := by
    simpa only [wordPayload,ite_true,ite_false,show ¬ (1:Nat) = 0 from by decide,source] using ho
  have hd := congrArg (Option.map Prod.fst) ho'
  simpa only [Option.map_map,Function.comp_def,observe] using hd

theorem pipelineWord_finishes (k : HybridWord.Kernel) (b : Build) (hb : 2 ≤ b.wires.size)
    (ii : Nat) (s : HybridWord.State) (x y : HybridWord.Word) (capacities : Array (Nat × Nat)) :
    ∃ cycles, (pipelineWord k b ii).1.execute capacities cycles (wordPayload s x y) =
      some ((k.source x y s).map HybridWord.State.encode) := by
  obtain ⟨result,he,ho⟩ := pipelineWord_correct k b hb ii s x y (cap := capacityOf capacities)
  obtain ⟨cycles,hc⟩ := Transformed.finishes _ he
  exact ⟨cycles,by simpa only [ho] using hc⟩

end IRComparison.Circuit.Pipelining
