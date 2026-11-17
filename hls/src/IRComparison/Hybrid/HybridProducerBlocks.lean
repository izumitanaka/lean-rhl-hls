import IRComparison.Hybrid.HybridAlternatives
import IRComparison.Hybrid.HybridWindowTransport
import IRComparison.Hybrid.HybridRuntime
import IRComparison.Memory.AlternativeProducerBlocks
namespace IRComparison.HybridProducerBlocks
open StreamState
open HybridIR (Block)
open AlternativeProducerBlocks (Result)
structure Compiled (array size : Nat) (before : List (List Int)) (source : List HybridWindowTransport.Block) where
  code : List Block
  after : List (List Int)
  correct : ∀ keys ∈ before, ∀ input x y old s t qi qo, Related array size keys s t qo →
    Result array size after (HybridWindowTransport.eval input x y source old s qi) (HybridIR.blocksEval input x y code old t qi qo)

def compile (array size : Nat) (before : List (List Int)) :
    (source : List HybridWindowTransport.Block) → Option (Compiled array size before source)
  | [] => some ⟨[],before,by intro keys member input x y old s t qi qo h; exact .some member h⟩
  | b::bs => do
    let cb ← HybridAlternatives.compile b.index array size before b.body
    let tail ← compile array size cb.after bs
    return ⟨⟨b.index,b.loads,cb.code⟩::tail.code,tail.after,by
      intro keys member input x y old s t qi qo h
      simp only [HybridWindowTransport.eval,HybridIR.blocksEval]
      cases hl : WindowFIFO.execute input old b.loads qi with
      | none => exact .none
      | some pair =>
        obtain ⟨vs,rest⟩ := pair
        simp only [bind,Option.bind]
        have hb := cb.correct keys member s t qo x y vs h
        cases hs : b.body.eval b.index x y s vs <;> cases ht : cb.code.eval b.index x y t qo vs <;>
          simp only [hs,ht] at hb
        · exact .none
        · cases hb
        · cases hb
        · rename_i u pair
          obtain ⟨v,out⟩ := pair
          cases hb with
          | some member hr => exact tail.correct _ member input x y vs u v rest out hr⟩

end IRComparison.HybridProducerBlocks
