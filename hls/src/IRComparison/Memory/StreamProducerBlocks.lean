import IRComparison.Memory.StreamConsumer

namespace IRComparison.StreamProducerBlocks
open StreamState

structure Block where
  index : Int
  loads : List WindowFIFO.Load
  body : StreamProducer.Cmd

def eval (input : Input) (x y : Int) : List Block → List Int → State → List Int → List Int → Option (State × List Int × List Int)
  | [],_,s,qi,qo => some (s,qi,qo)
  | b::bs,old,s,qi,qo => do
    let (vs,rest) ← WindowFIFO.execute input old b.loads qi
    let (t,out) ← b.body.eval b.index x y s qo vs
    eval input x y bs vs t rest out

inductive Result (array size : Nat) (keys : List Int) : Option (State × List Int) → Option (State × List Int × List Int) → Prop where
  | none : Result array size keys none none
  | some : Related array size keys s t qo → Result array size keys (some (s,qi)) (some (t,qi,qo))

structure Compiled (array size : Nat) (before : List Int) (source : List WindowTransport.Block) where
  code : List Block
  after : List Int
  correct : ∀ input x y old s t qi qo, Related array size before s t qo →
    Result array size after (WindowTransport.eval input x y source old s qi) (eval input x y code old t qi qo)

def compile (array size : Nat) (before : List Int) :
    (source : List WindowTransport.Block) → Option (Compiled array size before source)
  | [] => some ⟨[],before,by intro input x y old s t qi qo h; exact .some h⟩
  | b::bs => do
    let cb ← StreamProducer.compile b.index array size before b.body
    let tail ← compile array size cb.after bs
    return ⟨⟨b.index,b.loads,cb.code⟩::tail.code,tail.after,by
      intro input x y old s t qi qo h
      simp only [WindowTransport.eval,eval]
      cases hl : WindowFIFO.execute input old b.loads qi with
      | none => exact .none
      | some pair =>
        obtain ⟨vs,rest⟩ := pair
        simp only [bind,Option.bind]
        have hb := cb.correct s t qo x y vs h
        cases hs : b.body.eval b.index x y s vs <;> cases ht : cb.code.eval b.index x y t qo vs <;>
          simp only [hs,ht] at hb
        · exact .none
        · cases hb
        · cases hb
        · rename_i u pair
          obtain ⟨v,out⟩ := pair
          cases hb with
          | some hr => exact tail.correct input x y vs u v rest out hr⟩

end IRComparison.StreamProducerBlocks
