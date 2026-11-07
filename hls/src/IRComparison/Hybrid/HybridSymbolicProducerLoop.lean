import IRComparison.Hybrid.HybridSymbolicProducer
import IRComparison.Hybrid.HybridSymbolicLoop
import IRComparison.Memory.CompactSequence

namespace IRComparison.HybridSymbolicProducerLoop
open AffineAddress StreamState HybridSymbolicLoop
open SymbolicProducer (keys Safe)

structure Code where
  start : Int
  stride : Int
  count : Nat
  initial : List SymbolicWindowSchedule.Load
  refill : List SymbolicWindowSchedule.Load
  body : HybridIR.Cmd

def Code.loop (c : Code) (input : Input) (x y : Int) : Nat → Nat → List Int → State → List Int → Option (State × List Int)
  | 0,_,_,s,q => some (s,q)
  | n+1,k,values,s,q => do
    let (t,qs) ← c.body.eval (index c.start c.stride k) x y s q values
    match n with
    | 0 => some (t,qs)
    | m+1 => do
      let next ← SymbolicWindowSchedule.execute input (index c.start c.stride (k+1)) values c.refill
      c.loop input x y (m+1) (k+1) next t qs

def Code.eval (c : Code) (input : Input) (x y : Int) (s : State) : Option (State × List Int) :=
  match c.count with
  | 0 => some (s,[])
  | n+1 => do
    let vs ← SymbolicWindowSchedule.execute input c.start [] c.initial
    c.loop input x y (n+1) 0 vs s []

structure Plan (array size : Nat) (memory : HybridSymbolicLoop.Code) where
  body : HybridSymbolicProducer.Compiled array size memory.body
  address : Linear
  single : body.writes = [address]
  valid : ∀ k, k < memory.count → Valid body.guards (index memory.start memory.stride k)
  bounded : ∀ k, k < memory.count → 0 ≤ address.eval (index memory.start memory.stride k) ∧
    address.eval (index memory.start memory.stride k) < (size:Int)
  distinct : address.coefficient * memory.stride ≠ 0 ∨ memory.count ≤ 1

def Plan.code (p : Plan array size memory) : Code :=
  ⟨memory.start,memory.stride,memory.count,memory.initial,memory.refill,p.body.code⟩
def Plan.sequence (p : Plan array size memory) : CompactSequence.Seq :=
  ⟨p.address.eval memory.start,p.address.coefficient*memory.stride,memory.count⟩
def Plan.prefixKeys (p : Plan array size memory) (k : Nat) : List Int :=
  PaperCore.IndexSequence.entries p.sequence.first p.sequence.step k

theorem Plan.address_at (p : Plan array size memory) :
    p.address.eval (index memory.start memory.stride k) = p.sequence.first+(k:Int)*p.sequence.step := by
  simp [Linear.eval,index,Plan.sequence,Int.mul_add,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm,Int.add_assoc,Int.add_comm,Int.add_left_comm]

theorem Plan.fresh (p : Plan array size memory) (hk : k < memory.count) :
    p.address.eval (index memory.start memory.stride k) ∉ p.prefixKeys k := by
  intro member
  obtain ⟨j,hj,eq⟩ := (PaperCore.IndexSequence.mem_entries _ _ _ _).mp member
  rw [p.address_at] at eq
  have same : (k:Int)*p.sequence.step = (j:Int)*p.sequence.step := by omega
  rcases p.distinct with nonzero | short
  · have hjk := (Int.mul_eq_mul_right_iff nonzero).mp same
    omega
  · omega

theorem Plan.prefix_next (p : Plan array size memory) :
    p.prefixKeys k ++ SymbolicProducer.keys p.body.writes (index memory.start memory.stride k) = p.prefixKeys (k+1) := by
  simp only [p.single,SymbolicProducer.keys,List.map_cons,List.map_nil,p.address_at,Plan.prefixKeys]
  exact (PaperCore.IndexSequence.append_entries _ _ _).symm

theorem Plan.body_safe (p : Plan array size memory) (hk : k < memory.count) :
    SymbolicProducer.Safe size (p.prefixKeys k) (SymbolicProducer.keys p.body.writes (index memory.start memory.stride k)) := by
  simp only [p.single,SymbolicProducer.keys,List.map_cons,List.map_nil]
  exact .cons (p.bounded k hk).1 (p.bounded k hk).2 (p.fresh hk) .nil

theorem Plan.loop_correct (p : Plan array size memory) (n k : Nat) (bound : k+n ≤ memory.count)
    (values : List Int) (s t : State) (q : List Int) (h : Related array size (p.prefixKeys k) s t q) :
    StreamState.Result array size (p.prefixKeys (k+n))
      (memory.loop input x y n k values s) (p.code.loop input x y n k values t q) := by
  induction n generalizing k values s t q with
  | zero => simpa using StreamState.Result.some h
  | succ n ih =>
    rw [HybridSymbolicLoop.Code.loop,Code.loop]
    dsimp only [Plan.code]
    have hb := p.body.correct (index memory.start memory.stride k) (p.valid k (by omega))
      (p.prefixKeys k) s t q x y values (p.body_safe (by omega)) h
    rw [p.prefix_next] at hb
    cases hs : memory.body.eval (index memory.start memory.stride k) x y s values <;>
      cases ht : p.body.code.eval (index memory.start memory.stride k) x y t q values <;>
      simp only [hs,ht] at hb
    · exact .none
    · cases hb
    · cases hb
    · rename_i u pair
      obtain ⟨v,qs⟩ := pair
      cases hb with
      | some next =>
        cases n with
        | zero => exact .some next
        | succ m =>
          simp only [bind,Option.bind]
          cases hl : SymbolicWindowSchedule.execute input (index memory.start memory.stride (k+1)) values memory.refill with
          | none => exact .none
          | some vs =>
            simpa only [Plan.code,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
              ih (k+1) (by omega) vs u v qs next

theorem Plan.correct (p : Plan array size memory) (s t : State)
    (h : Related array size [] s t []) :
    StreamState.Result array size p.sequence.entries (memory.eval input x y s) (p.code.eval input x y t) := by
  cases hc : memory.count with
  | zero =>
    simpa [HybridSymbolicLoop.Code.eval,Code.eval,Plan.code,Plan.sequence,CompactSequence.Seq.entries,hc,PaperCore.IndexSequence.entries] using StreamState.Result.some h
  | succ n =>
    simp only [HybridSymbolicLoop.Code.eval,Code.eval,Plan.code,hc]
    cases hl : SymbolicWindowSchedule.execute input memory.start [] memory.initial with
    | none => exact .none
    | some vs =>
      have result := p.loop_correct (input:=input) (x:=x) (y:=y) (n+1) 0 (by omega) vs s t [] h
      simpa only [Plan.code,hc,Plan.prefixKeys,Plan.sequence,CompactSequence.Seq.entries,Nat.zero_add,bind,Option.bind] using result

def compile (array size : Nat) (memory : HybridSymbolicLoop.Code) : Option (Plan array size memory) := do
  let body ← HybridSymbolicProducer.compile array size memory.body
  match h : body.writes with
  | [address] =>
    if valid : checkGuards body.guards memory.start memory.stride memory.count = true then
      if bounds : checkGuards [address,⟨-address.coefficient,(size:Int)-1-address.offset⟩] memory.start memory.stride memory.count = true then
        if distinct : address.coefficient * memory.stride ≠ 0 ∨ memory.count ≤ 1 then
          return ⟨body,address,h,by intro k hk; exact checkGuards_sound valid hk,by
            intro k hk
            have hs := checkGuards_sound bounds hk
            have lo := hs address (by simp)
            have hi := hs ⟨-address.coefficient,(size:Int)-1-address.offset⟩ (by simp)
            simp only [Linear.eval,Int.neg_mul,index] at lo hi ⊢
            constructor <;> omega,distinct⟩
        else none
      else none
    else none
  | _ => none

end IRComparison.HybridSymbolicProducerLoop
