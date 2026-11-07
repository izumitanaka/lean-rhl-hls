import PaperCore.MixedTarget
import PaperCore.DirectBody
import PaperCore.Move

namespace PaperCore.Hybrid
open MixedTarget

/-- Retained arrays agree cell by cell; selected arrays use the existing FIFO
correspondence. The policy is fixed for the entire program. -/
structure Corresponds (ordinary : Var → Prop) (fifo : Array → Prop)
    (source : State Heap) (target : State Storage) (indices : IndexMap) : Prop where
  streams : PaperCore.Corresponds ordinary fifo source ⟨target.regs,target.memory.2⟩ indices
  memory : ∀ a, ¬ fifo a → ∀ i, source.memory.lookup (a,i) = target.memory.1.lookup (a,i)

theorem Corresponds.registers (c : Corresponds ordinary fifo s t is) :
    ∀ x, ordinary x → s.regs.lookup x = t.regs.lookup x := c.streams.registers

theorem Corresponds.eval_eq (c : Corresponds ordinary fifo s t is)
    (meaning : Op → Int → Int → Int) (e : Expr Op) (typed : e.ordinary ordinary) :
    e.eval meaning s.regs = e.eval meaning t.regs := c.streams.eval_eq meaning e typed

theorem Corresponds.setReg (c : Corresponds ordinary fifo s t is) (x : Var) (v : Int) :
    Corresponds ordinary fifo (s.setReg x v) (t.setReg x v) is :=
  ⟨c.streams.setReg x v,c.memory⟩

theorem Corresponds.setBuffer (c : Corresponds ordinary fifo s t is) (fresh : ¬ ordinary x) (v : Int) :
    Corresponds ordinary fifo s (t.setReg x v) is :=
  ⟨c.streams.setBuffer fresh v,c.memory⟩

theorem Corresponds.memory_write (c : Corresponds ordinary fifo s t is) (retained : ¬ fifo a) :
    Corresponds ordinary fifo {s with memory := put s.memory (a,i) v}
      {t with memory := (put t.memory.1 (a,i) v,t.memory.2)} is := by
  constructor
  · constructor
    · exact c.registers
    · intro b hb
      obtain ⟨js,vs,hj,hv,distinct,contents⟩ := c.streams.streams b hb
      refine ⟨js,vs,hj,hv,distinct,contents.congr ?_⟩
      intro j _
      apply lookup_put_other
      intro same
      exact retained ((Prod.mk.inj same).1 ▸ hb)
  · intro b hb j
    by_cases same : (b,j) = (a,i)
    · rw [same,lookup_put_same,lookup_put_same]
    · rw [lookup_put_other _ _ _ _ same,lookup_put_other _ _ _ _ same]
      exact c.memory b hb j

theorem Corresponds.pop (c : Corresponds ordinary fifo s t is) (selected : fifo a)
    (head : is.lookup a = some (i :: tail)) (dest : Var) :
    ∃ value rest, s.memory.lookup (a,i) = some value ∧ t.memory.2.lookup a = some (value :: rest) ∧
      Corresponds ordinary fifo (s.setReg dest value)
        ⟨put t.regs dest value,(t.memory.1,put t.memory.2 a rest)⟩ (put is a tail) := by
  obtain ⟨v,rest,cell,queue,after⟩ := DirectBody.pop_ordinary c.streams selected head dest
  exact ⟨v,rest,cell,queue,after,c.memory⟩

theorem Corresponds.push (c : Corresponds ordinary fifo s t is) (selected : fifo a)
    (witness : is.lookup a = some values) (fresh : i ∉ values)
    (typed : ordinary x) (value : s.regs.lookup x = some v) :
    ∃ out, Step meaning (.stream (.write a x)) t out ∧
      Corresponds ordinary fifo {s with memory := put s.memory (a,i) v} out (put is a (values ++ [i])) := by
  obtain ⟨out,run,after⟩ := DirectBody.push_ordinary c.streams selected witness fresh typed value
  refine ⟨streamState out t.memory.1,?_,after,?_⟩
  · exact Step.stream run
  · intro b hb j
    have different : (b,j) ≠ (a,i) := by
      intro same
      exact hb ((Prod.mk.inj same).1.symm ▸ selected)
    rw [lookup_put_other _ _ _ _ different]
    exact c.memory b hb j

theorem memory_step_iff : Step meaning (.memory command) s t ↔
    MemoryStep meaning command ⟨s.regs,s.memory.1⟩ ⟨t.regs,t.memory.1⟩ ∧ t.memory.2 = s.memory.2 := by
  constructor
  · intro h; cases h with
    | memory h => exact ⟨h,rfl⟩
  · rcases s with ⟨sr,sh,sq⟩
    rcases t with ⟨tr,th,tq⟩
    rintro ⟨h,equal⟩
    dsimp at equal; subst tq
    exact .memory h

theorem stream_step_iff : Step meaning (.stream command) s t ↔
    StreamStep command ⟨s.regs,s.memory.2⟩ ⟨t.regs,t.memory.2⟩ ∧ t.memory.1 = s.memory.1 := by
  constructor
  · intro h; cases h with
    | stream h => exact ⟨h,rfl⟩
  · rcases s with ⟨sr,sh,sq⟩
    rcases t with ⟨tr,th,tq⟩
    rintro ⟨h,equal⟩
    dsimp at equal; subst th
    exact .stream h

/-- Determinism includes both untouched storage components. -/
theorem step_deterministic (first : Step meaning command s t) (second : Step meaning command s u) : t = u := by
  cases command with
  | memory cmd =>
    obtain ⟨h,frame⟩ := memory_step_iff.mp first
    obtain ⟨h',frame'⟩ := memory_step_iff.mp second
    have eq := memoryStep_deterministic h h'
    rcases t with ⟨tr,th,tq⟩; rcases u with ⟨ur,uh,uq⟩
    simp_all
  | stream cmd =>
    obtain ⟨h,frame⟩ := stream_step_iff.mp first
    obtain ⟨h',frame'⟩ := stream_step_iff.mp second
    have eq := streamStep_deterministic h h'
    rcases t with ⟨tr,th,tq⟩; rcases u with ⟨ur,uh,uq⟩
    simp_all

theorem retained_read_forward (c : Corresponds ordinary fifo s t is)
    (retained : ¬ fifo a) (typed : e.ordinary ordinary)
    (run : SourceExec meaning (.action (.read x a e)) s out) :
    ∃ target, Execution meaning (.action (.memory (.read x a e))) t target ∧
      Corresponds ordinary fifo out target is := by
  cases run with
  | action step =>
    cases step with
    | read index cell =>
      refine ⟨t.setReg x _,.action (memory_step_iff.mpr ⟨.read ((c.eval_eq meaning e typed).symm.trans index) ((c.memory a retained _).symm.trans cell),rfl⟩),c.setReg x _⟩

theorem retained_read_backward (c : Corresponds ordinary fifo s t is)
    (retained : ¬ fifo a) (typed : e.ordinary ordinary)
    (run : Execution meaning (.action (.memory (.read x a e))) t out) :
    ∃ source, SourceExec meaning (.action (.read x a e)) s source ∧
      Corresponds ordinary fifo source out is := by
  rcases out with ⟨outRegs,outHeap,outQueues⟩
  cases run with
  | action step =>
    obtain ⟨read,frame⟩ := memory_step_iff.mp step
    cases read with
    | read index cell =>
      refine ⟨s.setReg x _,.action (.read ((c.eval_eq meaning e typed).trans index)
        ((c.memory a retained _).trans cell)),?_⟩
      · dsimp at frame; subst outQueues
        exact c.setReg x _

theorem retained_write_forward (c : Corresponds ordinary fifo s t is)
    (retained : ¬ fifo a) (typed : ordinary x ∧ e.ordinary ordinary)
    (run : SourceExec meaning (.action (.write a e x)) s out) :
    ∃ target, Execution meaning (.action (.memory (.write a e x))) t target ∧
      Corresponds ordinary fifo out target is := by
  cases run with
  | action step =>
    cases step with
    | write index value =>
      refine ⟨{t with memory := (put t.memory.1 (a,_) _,t.memory.2)},
        .action (memory_step_iff.mpr ⟨.write ?_ ?_,rfl⟩),c.memory_write retained⟩
      · exact (c.eval_eq meaning e typed.2).symm.trans index
      · exact (c.registers x typed.1).symm.trans value

theorem retained_write_backward (c : Corresponds ordinary fifo s t is)
    (retained : ¬ fifo a) (typed : ordinary x ∧ e.ordinary ordinary)
    (run : Execution meaning (.action (.memory (.write a e x))) t out) :
    ∃ source, SourceExec meaning (.action (.write a e x)) s source ∧
      Corresponds ordinary fifo source out is := by
  rcases out with ⟨outRegs,outHeap,outQueues⟩
  cases run with
  | action step =>
    obtain ⟨write,frame⟩ := memory_step_iff.mp step
    cases write with
    | write index value =>
      refine ⟨{s with memory := put s.memory (a,_) _},
        .action (.write ((c.eval_eq meaning e typed.2).trans index) ((c.registers x typed.1).trans value)),?_⟩
      · dsimp at frame; subst outQueues
        exact c.memory_write retained

#print axioms Corresponds.memory_write
#print axioms Corresponds.push
end PaperCore.Hybrid
