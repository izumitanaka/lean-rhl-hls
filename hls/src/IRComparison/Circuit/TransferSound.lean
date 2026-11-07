import IRComparison.Circuit.DataSafety

namespace IRComparison.Circuit

theorem transfer_sound (instruction : Node) (hb : RuntimeBound f r) (hc : transfer f instruction = .ok edges)
    (he : execute capacity instruction r = some t) :
    t.done = true ∨ ∃ nextFrame, (t.pc,nextFrame) ∈ edges ∧ RuntimeBound nextFrame t := by
  have hf := Frame.not_empty hb.wires
  unfold transfer at hc
  simp only [hf,Bool.false_eq_true,↓reduceIte] at hc
  cases instruction <;> dsimp only [bind,pure,Except.bind,Except.pure] at hc
  case halt => cases he; exact Or.inl rfl
  case jump next =>
      cases hc; cases he
      exact Or.inr ⟨f,by simp,hb.setPC⟩
  case wire k e next =>
      split at hc
      · rename_i hk
        cases hc
        cases hv : e.eval r.data r.wires with
        | none => simp [execute,hv] at he
        | some v =>
          simp only [execute,hv,bind,Option.bind] at he
          cases he
          exact Or.inr ⟨_,by simp,(hb.setWire hk (range_correct e hb.inputs hv)).setPC⟩
      · cases hc
  case assign reg e next =>
      split at hc
      · rename_i hw
        cases hc
        cases hv : e.eval r.data r.wires with
        | none => simp [execute,hv] at he
        | some v =>
          simp only [execute,hv,bind,Option.bind] at he
          cases he
          exact Or.inr ⟨f,by simp,⟨hb.data.set (isWord_sound hw (range_correct e hb.inputs hv)),hb.wires,hb.queues⟩⟩
      · cases hc
  case store a j e next =>
      split at hc
      · rename_i hw
        cases hc
        cases hj : j.eval r.data r.wires with
        | none => simp [execute,hj] at he
        | some index =>
          cases hv : e.eval r.data r.wires with
          | none => simp [execute,hj,hv] at he
          | some v =>
            cases hs : r.data.write a index v with
            | none => simp [execute,hj,hv,hs] at he
            | some data =>
              simp only [execute,hj,hv,hs,bind,Option.bind] at he
              cases he
              exact Or.inr ⟨f,by simp,⟨hb.data.write (isWord_sound hw (range_correct e hb.inputs hv)) hs,hb.wires,hb.queues⟩⟩
      · cases hc
  case branch c yes no =>
      cases hc
      cases hv : c.eval r.data r.wires with
      | none => simp [execute,hv] at he
      | some v =>
        cases htest : (v != 0) <;> simp only [execute,hv,bind,Option.bind,htest,Bool.false_eq_true,↓reduceIte] at he
        · cases he
          exact Or.inr ⟨_,by simp,⟨hb.data,Frame.refine_sound f hb.inputs hv htest,hb.queues⟩⟩
        · cases he
          exact Or.inr ⟨_,by simp,⟨hb.data,Frame.refine_sound f hb.inputs hv htest,hb.queues⟩⟩
  case snapshot dst src next =>
      cases hc; cases he
      exact Or.inr ⟨f,by simp,⟨hb.data.replace (hb.data.arrays src),hb.wires,hb.queues⟩⟩
  case erase a next =>
      cases hc; cases he
      exact Or.inr ⟨f,by simp,⟨hb.data.replace (by intros; simp_all),hb.wires,hb.queues⟩⟩
  case clear q next =>
      cases hc; cases he
      exact Or.inr ⟨f,by simp,(hb.setQueue (by intros; simp_all)).setPC⟩
  case send q e next =>
      split at hc
      · rename_i hw
        cases hc
        cases hv : e.eval r.data r.wires with
        | none => simp [execute,hv] at he
        | some v =>
          simp only [execute,hv,bind,Option.bind] at he
          split at he
          · cases he
            apply Or.inr
            refine ⟨f,by simp,(hb.setQueue ?_).setPC⟩
            intro u hu
            simp only [List.mem_append,List.mem_singleton] at hu
            rcases hu with old | new
            · exact hb.queues q u old
            · subst u; exact isWord_sound hw (range_correct e hb.inputs hv)
          · cases he
      · cases hc
  case receive q k next =>
      split at hc
      · rename_i hk
        cases hc
        cases hq : r.queues q with
        | nil => simp [execute,hq] at he
        | cons v vs =>
          simp only [execute,hq] at he
          cases he
          have hv := hb.queues q v (by simp [hq])
          have ht := hb.setQueue (q:=q) (vs:=vs) (fun u hu => hb.queues q u (by simp [hq,hu]))
          exact Or.inr ⟨_,by simp,(ht.setWire hk hv).setPC⟩
      · cases hc

end IRComparison.Circuit
