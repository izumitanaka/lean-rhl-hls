import IRComparison.Hybrid.HybridWindowTransport
import IRComparison.Memory.AlternativeRouting
namespace IRComparison.HybridRouting
open AlternativeRouting (loads)
structure Blocks (source : List HybridWindowPlan.Block) (before : List (List Int)) where
  code : List HybridWindowTransport.Block
  after : List (List Int)
  correct : ∀ keys ∈ before, ∃ tail ∈ after, HybridWindowTransport.Routes source keys code tail

def compile : (source : List HybridWindowPlan.Block) → (before : List (List Int)) →
    Option (Blocks source before)
  | [],before => some ⟨[],before,by intro keys hk; exact ⟨keys,hk,.nil⟩⟩
  | b::bs,before => do
    let first ← loads b.loads before
    let next ← compile bs first.after
    return ⟨⟨b.index,first.code,b.body⟩::next.code,next.after,by
      intro keys hk
      obtain ⟨middle,hm,hfirst⟩ := first.correct keys hk
      obtain ⟨tail,ht,hnext⟩ := next.correct middle hm
      exact ⟨tail,ht,.cons hfirst hnext⟩⟩

theorem Blocks.eval_correct (p : Blocks source before) (hk : keys ∈ before)
    (hq : CommunicationIR.Corresponds input keys queue) (old : List Int) (s : State) (x y : Int) :
    (HybridWindowTransport.eval input x y p.code old s queue).map Prod.fst =
      HybridWindowPlan.eval input x y source old s := by
  obtain ⟨tail,ht,route⟩ := p.correct keys hk
  exact (route.correct hq old s x y).1

end IRComparison.HybridRouting
