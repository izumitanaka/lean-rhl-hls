import PaperCore.MemoryCoverage
import PaperCore.LoopAnalysis

namespace PaperCore.MemoryCoverage
open AccessAnalysis
variable {Op : Type} {classify : Op → Option Arithmetic} {meaning : Op → Int → Int → Int}

/-- Every analyzed access of a completed loop establishes a symbolic initialized
span. This is independent of the values stored and the source body computation. -/
theorem loop_covers {trips : Nat} (ops : ArithmeticSound classify meaning)
    (analysis : analyze classify (Env.initial counter) body = .ok summary)
    (knownCounter : summary.env counter = some ⟨1,delta-step⟩)
    (nonzero : delta ≠ 0) (eventMember : event ∈ summary.accesses)
    (endpoint : stop = start+(trips:Int)*delta)
    (run : SourceExec meaning (.loop counter (.num start) stop step body) initial final) :
    Covers final.memory event.array (event.index.eval start) (event.index.scale*delta) trips := by
  induction trips generalizing start initial with
  | zero => intro n hn; omega
  | succ trips ih =>
    have product : ((trips+1:Nat):Int)*delta ≠ 0 := Int.mul_ne_zero (by omega) nonzero
    have notEnd : start ≠ stop := by
      intro same
      rw [same] at endpoint
      apply product
      omega
    cases run with
    | forExit value =>
      simp [Expr.eval] at value
      exact (notEnd value).elim
    | @forLoop k _ _ middle _ next _ _ _ _ value guard bodyRun counterValue rest =>
      simp [Expr.eval] at value
      subst k
      obtain ⟨env,trace⟩ := analyze_sound ops body analysis
        (LoopAnalysis.Env.initial_matches (lookup_put_same ..)) bodyRun
      have counterResult := env counter _ knownCounter
      simp only [Affine.eval,Int.one_mul] at counterResult
      have advance : next + step = start+delta := by
        have same := Option.some.inj (counterValue.symm.trans counterResult)
        omega
      have nextEndpoint : stop = (start+delta)+(trips:Int)*delta := by
        simp only [Int.natCast_add,Int.natCast_one,Int.add_mul,Int.one_mul] at endpoint
        omega
      have rest' := rest
      rw [advance] at rest'
      have tail := ih nextEndpoint rest'
      have current := trace_defines trace (List.mem_map.mpr ⟨event,eventMember,rfl⟩)
      have currentFinal := execution_preserves rest current
      intro n hn
      cases n with
      | zero => simpa [SymbolicAccess.eval] using currentFinal
      | succ n =>
        have point := tail n (by omega)
        simpa [Affine.eval,Int.natCast_add,Int.add_mul,Int.mul_add,Int.add_assoc,
          Int.add_comm,Int.add_left_comm] using point

#print axioms loop_covers
end PaperCore.MemoryCoverage
