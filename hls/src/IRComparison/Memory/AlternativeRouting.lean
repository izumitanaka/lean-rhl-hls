import IRComparison.Memory.WindowTransport

namespace IRComparison.AlternativeRouting

/-- One static destructive-read schedule must work for every incoming FIFO
    invariant. Logical alternatives are erased; the machine has no tags. -/
structure Loads (source : List WindowSchedule.Load) (before : List (List Int)) where
  code : List WindowFIFO.Load
  after : List (List Int)
  correct : ∀ keys ∈ before, ∃ tail ∈ after, WindowFIFO.Routes source keys code tail

def loads (source : List WindowSchedule.Load) :
    (before : List (List Int)) → Option (Loads source before)
  | [] => none
  | keys::rest => do
    let first ← WindowFIFO.route source keys
    match rest with
    | [] => return ⟨first.code,[first.remaining],by
        intro ks member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        subst ks
        exact ⟨first.remaining,by simp,first.correct⟩⟩
    | k::ks =>
      let next ← loads source (k::ks)
      if same : first.code = next.code then
        return ⟨first.code,first.remaining::next.after,by
          intro actual member
          rcases List.mem_cons.mp member with rfl | hm
          · exact ⟨first.remaining,by simp,first.correct⟩
          · obtain ⟨tail,ht,hr⟩ := next.correct actual hm
            exact ⟨tail,List.mem_cons_of_mem _ ht,same ▸ hr⟩⟩
      else none

structure Blocks (source : List NativeWindowPlan.Block) (before : List (List Int)) where
  code : List WindowTransport.Block
  after : List (List Int)
  correct : ∀ keys ∈ before, ∃ tail ∈ after, WindowTransport.Routes source keys code tail

def compile : (source : List NativeWindowPlan.Block) → (before : List (List Int)) →
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
    (WindowTransport.eval input x y p.code old s queue).map Prod.fst =
      NativeWindowPlan.evalI input x y source old s := by
  obtain ⟨tail,ht,route⟩ := p.correct keys hk
  exact (route.correct hq old s x y).1

end IRComparison.AlternativeRouting
