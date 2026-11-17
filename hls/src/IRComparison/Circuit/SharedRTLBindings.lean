import IRComparison.Circuit.SharedRTLSignals

namespace IRComparison.Circuit.Shared.LocalRTL

/-- Invalid values are unconstrained; only the valid bit is observed then. -/
structure SignalModel (signals : Array Int) (cache : Cache) : Prop where
  sizes : signals.size = 2*cache.size
  valid : ∀ n, (signals[2*n+1]?.getD 0 != 0) = (get cache n).isSome
  value : ∀ n v, get cache n = some v → signals[2*n]?.getD 0 = v

@[simp] theorem valueRef_full (r : Runtime) (signals : Array Int) (n : Nat) :
    (valueRef n).eval (fullRuntime r signals) = signals[2*n]?.getD 0 := rfl

@[simp] theorem validRef_full (h : SignalModel signals cache) (r : Runtime) (n : Nat) :
    (validRef n).eval (fullRuntime r signals) = (get cache n).isSome := by
  simp only [validRef,RTL.Validity.eval,RTL.Term.eval,fullRuntime,h.valid]
  cases get cache n <;> rfl

@[simp] theorem fullRuntime_data (r : Runtime) (signals : Array Int) : (fullRuntime r signals).data = r.data := rfl

theorem raw_full_correct {outputBounds : Interval} (n : Shared.Node) (notInput : ∀ e, n ≠ .input e)
    (model : SignalModel signals cache) :
    (RTL.Combinational.mk (raw n).1 (raw n).2 outputBounds).eval (fullRuntime r signals) =
      n.bitRaw wr r.data r.wires cache := by
  cases n with
  | input e => exact False.elim (notInput e rfl)
  | memory a j =>
    cases hj : get cache j with
    | none => simp [raw,RTL.Combinational.eval,RTL.Validity.eval,validRef_full model,hj,Shared.Node.bitRaw,Shared.Node.eval]
    | some index =>
      have hval := model.value j index hj
      by_cases hn : index < 0
      · simp [raw,RTL.Combinational.eval,RTL.Validity.eval,RTL.Term.eval,validRef_full model,
          hj,hval,Shared.Node.bitRaw,Shared.Node.eval,arrayInput,hn,show ¬0 ≤ index from by omega]
      · by_cases hi : index.toNat < (r.data.arrays a).size
        · simp [raw,RTL.Combinational.eval,RTL.Validity.eval,RTL.Term.eval,validRef_full model,
            hj,hval,Shared.Node.bitRaw,Shared.Node.eval,arrayInput,hn,hi,show 0 ≤ index from by omega]
        · simp [raw,RTL.Combinational.eval,RTL.Validity.eval,RTL.Term.eval,validRef_full model,
            hj,hval,Shared.Node.bitRaw,Shared.Node.eval,arrayInput,hn,hi,show 0 ≤ index from by omega]
  | binary op a b =>
    cases ha : get cache a <;> cases hb : get cache b
    all_goals try have hva := model.value _ _ ha
    all_goals try have hvb := model.value _ _ hb
    all_goals simp [raw,RTL.Combinational.eval,RTL.Validity.eval,RTL.Term.eval,validRef_full model,
        Shared.Node.bitRaw, *]
  | wrap32 a | natIndex a =>
    cases ha : get cache a
    all_goals try have hva := model.value _ _ ha
    all_goals simp [raw,RTL.Combinational.eval,RTL.Term.eval,validRef_full model,Shared.Node.bitRaw,Shared.Node.eval, *]
  | seq a b =>
    cases ha : get cache a <;> cases hb : get cache b
    all_goals try have hvb := model.value _ _ hb
    all_goals simp [raw,RTL.Combinational.eval,RTL.Validity.eval,validRef_full model,Shared.Node.bitRaw,Shared.Node.eval, *]
  | select c a b =>
    cases hc : get cache c <;> cases ha : get cache a <;> cases hb : get cache b
    all_goals try have hvc := model.value _ _ hc
    all_goals try have hva := model.value _ _ ha
    all_goals try have hvb := model.value _ _ hb
    all_goals simp [raw,RTL.Combinational.eval,RTL.Validity.eval,RTL.Term.eval,validRef_full model,
        Shared.Node.bitRaw,Shared.Node.eval, *] <;> split <;> simp_all

theorem lower_full_correct (n : Shared.Node) (model : SignalModel signals cache) :
    (if (lower wr rs n).valid r signals then some ((lower wr rs n).value r signals) else none) =
      n.bitEval wr rs r.data r.wires cache := by
  by_cases h : ∃ e, n = .input e
  · obtain ⟨e,rfl⟩ := h
    have he := lower_correct (wr:=wr) (rs:=rs) (r:=r) (cache:=cache) (.input e)
    simpa [lower,Code.value,Code.valid,Code.eval,RTL.Combinational.eval] using he
  · have hn : ∀ e, n ≠ .input e := by simpa using h
    have shape : lower wr rs n = .localNode
        ⟨.resize (signedWidth (n.range wr rs)) (raw n).1,(raw n).2,n.range wr rs⟩ := by
      cases n <;> simp_all [lower]
    rw [shape]
    change (RTL.Combinational.mk (.resize _ (raw n).1) (raw n).2 (n.range wr rs)).eval (fullRuntime r signals) = _
    rw [RTL.Combinational.resize_eval (⟨(raw n).1,(raw n).2,n.range wr rs⟩ : RTL.Combinational),raw_full_correct n hn model]
    rfl

theorem SignalModel.push (model : SignalModel signals cache) (value : Int) (valid : Bool) :
    SignalModel ((signals.push value).push (if valid then 1 else 0))
      (cache.push (if valid then some value else none)) := by
  refine ⟨by simp [model.sizes]; omega,?_,?_⟩
  · intro n
    by_cases hn : n = cache.size
    · have hodd : 2*n+1 ≠ signals.size := by have := model.sizes; omega
      have heq : 2*n+1 = signals.size+1 := by have := model.sizes; omega
      have hs : 2*n+1 = (signals.push value).size := by simp only [Array.size_push]; omega
      rw [hs,Array.getElem?_push_size]
      simp only [get,hn,Array.getElem?_push_size,Option.getD_some]
      cases valid <;> rfl
    · have hodd : 2*n+1 ≠ signals.size := by have := model.sizes; omega
      have hother : 2*n+1 ≠ signals.size+1 := by have := model.sizes; omega
      simpa only [get,Array.getElem?_push,Array.size_push,if_neg hn,if_neg hodd,if_neg hother]
        using model.valid n
  · intro n v hv
    by_cases hn : n = cache.size
    · have heven : 2*n = signals.size := by have := model.sizes; omega
      have hother : 2*n ≠ signals.size+1 := by omega
      simp only [get,Array.getElem?_push,hn,if_pos rfl,Option.getD_some] at hv
      cases valid <;> simp_all [Array.getElem?_push]
    · have heven : 2*n ≠ signals.size := by have := model.sizes; omega
      have hother : 2*n ≠ signals.size+1 := by have := model.sizes; omega
      have old : get cache n = some v := by simpa only [get,Array.getElem?_push,if_neg hn] using hv
      simpa only [Array.getElem?_push,Array.size_push,if_neg heven,if_neg hother] using model.value n v old

theorem fullValues_model (g : Graph) :
    SignalModel (fullValues r (lowerGraph wr g).code) (bitValues wr r.data r.wires g).cache := by
  induction g with
  | nil => exact ⟨rfl,by simp [fullValues,lowerGraph,bitValues,get],by simp [fullValues,lowerGraph,bitValues,get]⟩
  | cons n g ih =>
    have hr := (lowerGraph_correct (r:=r) (wr:=wr) g).1
    have nodeMeaning := lower_full_correct (wr:=wr) (rs:=(lowerGraph wr g).ranges) (r:=r) n ih
    have pushed := ih.push ((lower wr (lowerGraph wr g).ranges n).value r (fullValues r (lowerGraph wr g).code))
      ((lower wr (lowerGraph wr g).ranges n).valid r (fullValues r (lowerGraph wr g).code))
    rw [nodeMeaning] at pushed
    simpa only [fullValues,lowerGraph,bitValues,hr] using pushed

theorem compile_fullEval_correct (p : Shared.Program) (r : Runtime) :
    (compile wr p).fullEval r = p.bitEval wr r.data r.wires := by
  have model := fullValues_model (r:=r) (wr:=wr) p.graph
  unfold compile Program.fullEval Shared.Program.bitEval
  cases h : get (bitValues wr r.data r.wires p.graph).cache p.result with
  | none => simp [model.valid p.result,h]
  | some v => simp [model.valid p.result,h,model.value p.result v h]

end IRComparison.Circuit.Shared.LocalRTL
