import IRComparison.Circuit.Pipelining.Compiler

namespace IRComparison.Circuit.Pipelining

abbrev WireConstants := List (Nat × Option Int)
def constantAt : WireConstants → Nat → Option Int
  | [],_ => none
  | (k,v)::rest,n => if n = k then v else constantAt rest n
def ConstantsMatch (c : WireConstants) (p : Payload) : Prop := ∀ k v, constantAt c k = some v → p.wires k = v
def constantState (c : WireConstants) : Payload :=
  ⟨⟨fun _ => 0,fun _ => #[]⟩,fun k => (constantAt c k).getD 0,fun _ => []⟩

def constantExpr (c : WireConstants) (e : Expr) : Option Int :=
  if (reads e).all (fun cell => match cell with | .wire k => (constantAt c k).isSome | _ => false)
  then e.eval (constantState c).data (constantState c).wires else none

theorem constantExpr_correct (hc : ConstantsMatch c p) (he : constantExpr c e = some v) :
    e.eval p.data p.wires = some v := by
  unfold constantExpr at he
  split at he
  · rename_i known
    rw [expr_agrees e p (constantState c)]
    · exact he
    · intro cell member
      have hm := List.all_eq_true.mp known cell member
      cases cell <;> simp only [Bool.false_eq_true] at hm <;> try contradiction
      rename_i k
      cases hk : constantAt c k <;> simp [hk] at hm
      simp [get,constantState,hk,hc k _ hk]
  · cases he

def updateConstant (c : WireConstants) (k : Nat) (v : Option Int) : WireConstants :=
  (k,v)::c

def actionConstants (c : WireConstants) : Action → WireConstants
  | .wire k e => updateConstant c k (constantExpr c e)
  | .receive _ k => updateConstant c k none
  | _ => c

def specializeAction (c : WireConstants) : Action → Action
  | .wire k e => match constantExpr c e with | some v => .wire k (.lit v) | none => .wire k e
  | a => a

theorem specializeAction_correct (a : Action) (hc : ConstantsMatch c p) :
    (specializeAction c a).eval cap p = a.eval cap p := by
  cases a <;> try rfl
  rename_i k e
  cases he : constantExpr c e with
  | none => simp [specializeAction,he]
  | some v => simp [specializeAction,he,Action.eval,Action.node,execute,Payload.at,Expr.eval,constantExpr_correct hc he]

theorem actionConstants_correct (a : Action) (hc : ConstantsMatch c p)
    (he : a.eval cap p = some q) : ConstantsMatch (actionConstants c a) q := by
  cases a with
  | wire k e =>
    cases hv : e.eval p.data p.wires <;> simp [Action.eval,Action.node,execute,Payload.at,hv] at he
    subst q
    intro n v hn
    by_cases eq : n = k
    · subst n
      have hconst : constantExpr c e = some v := by simpa [actionConstants,updateConstant,constantAt] using hn
      have value := constantExpr_correct hc hconst
      rw [hv] at value; cases value
      simp [Circuit.Runtime.payload,Circuit.Runtime.setWire]
    · have original : constantAt c n = some v := by simpa [actionConstants,updateConstant,constantAt,eq] using hn
      simpa [Circuit.Runtime.payload,Circuit.Runtime.setWire,eq] using hc n v original
  | receive qi k =>
    cases hq : p.queues qi <;> simp [Action.eval,Action.node,execute,Payload.at,hq] at he
    subst q
    intro n v hn
    by_cases eq : n = k
    · simp [actionConstants,updateConstant,constantAt,eq] at hn
    · simpa [Circuit.Runtime.payload,Circuit.Runtime.setWire,Circuit.Runtime.setQueue,eq] using
        hc n v (by simpa [actionConstants,updateConstant,constantAt,eq] using hn)
  | assign k e | send k e =>
    cases hv : e.eval p.data p.wires <;> simp [Action.eval,Action.node,execute,Payload.at,hv] at he
    all_goals first | (subst q; exact hc) | (obtain ⟨_,rfl⟩ := he; exact hc)
  | store a j e =>
    cases hj : j.eval p.data p.wires <;> cases hv : e.eval p.data p.wires <;>
      simp [Action.eval,Action.node,execute,Payload.at,hj,hv] at he
    rename_i index value
    cases hw : p.data.write a index value <;> simp [hw] at he
    subst q; exact hc
  | snapshot | erase | clear => cases he; exact hc

/-- Only generated control determined by literal/wire constants is unfolded.
Unknown branches, data-dependent loops and exhausted budgets return none.
No input array or host parameter is evaluated during compilation. -/
def linearize : Nat → WireConstants → Circuit.Schedule → Option (List Action × WireConstants)
  | 0,_,_ => none
  | _+1,c,.skip => some ([],c)
  | _+1,c,.step a => some ([specializeAction c a],actionConstants c a)
  | fuel+1,c,.seq a b => do
      let (as,c') ← linearize fuel c a
      let (bs,c'') ← linearize fuel c' b
      return (as++bs,c'')
  | fuel+1,c,.branch e a b => do
      let v ← constantExpr c e
      linearize fuel c (if v = 0 then b else a)
  | fuel+1,c,.loop e body => do
      let v ← constantExpr c e
      if v = 0 then return ([],c)
      else
        let (as,c') ← linearize fuel c body
        let (bs,c'') ← linearize fuel c' (.loop e body)
        return (as++bs,c'')

theorem linearize_correct (fuel : Nat) (s : Circuit.Schedule)
    (compiled : linearize fuel c s = some (as,after)) (hc : ConstantsMatch c p)
    (he : s.Eval cap p result) :
    evalList (Action.eval cap) as p = result ∧ ∀ q, result = some q → ConstantsMatch after q := by
  induction fuel generalizing c s as after p result with
  | zero => cases compiled
  | succ fuel ih =>
    cases s with
    | skip => simp [linearize] at compiled; obtain ⟨rfl,rfl⟩ := compiled; cases he; exact ⟨rfl,by intro q h; cases h; exact hc⟩
    | step a =>
      simp [linearize] at compiled; obtain ⟨rfl,rfl⟩ := compiled
      cases he
      refine ⟨by simp [evalList,specializeAction_correct a hc],?_⟩
      exact fun q h => actionConstants_correct a hc h
    | seq a b =>
      cases ha : linearize fuel c a <;> simp [linearize,ha] at compiled
      rename_i first
      cases hb : linearize fuel first.2 b <;> simp [hb] at compiled
      obtain ⟨rfl,rfl⟩ := compiled
      rw [evalList_append]
      cases he with
      | seq_error he =>
        rw [(ih a ha hc he).1]; exact ⟨rfl,by intros; contradiction⟩
      | seq ha' hb' =>
        have first := ih a ha hc ha'
        rw [first.1]
        exact ih b hb (first.2 _ rfl) hb'
    | branch e a b =>
      cases hv : constantExpr c e <;> simp [linearize,hv] at compiled
      rename_i v
      have ev := constantExpr_correct hc hv
      cases he with
      | branch_error h => simp [ev] at h
      | branch_yes h nonzero branch =>
        rw [expressionEvaluation_original,ev] at h; cases h
        simp [nonzero] at compiled
        exact ih a compiled hc branch
      | branch_no h branch =>
        rw [expressionEvaluation_original,ev] at h; cases h
        simp at compiled
        exact ih b compiled hc branch
    | loop e body =>
      cases hv : constantExpr c e <;> simp [linearize,hv] at compiled
      rename_i v
      have ev := constantExpr_correct hc hv
      by_cases zero : v = 0
      · subst v; simp at compiled; obtain ⟨rfl,rfl⟩ := compiled
        cases he with
        | loop_error h => simp [ev] at h
        | loop_stop => exact ⟨rfl,by intro q h; cases h; exact hc⟩
        | loop_body_error h ne _ | loop_next h ne _ _ => rw [expressionEvaluation_original,ev] at h; cases h; contradiction
      · simp [zero] at compiled
        cases ha : linearize fuel c body <;> simp [ha] at compiled
        rename_i first
        cases hb : linearize fuel first.2 (.loop e body) <;> simp [hb] at compiled
        obtain ⟨rfl,rfl⟩ := compiled
        rw [evalList_append]
        cases he with
        | loop_error h => simp [ev] at h
        | loop_stop h => simp [ev,zero] at h
        | loop_body_error _ _ h =>
          rw [(ih body ha hc h).1]; exact ⟨rfl,by intros; contradiction⟩
        | loop_next _ _ hbody htail =>
          have first := ih body ha hc hbody
          rw [first.1]
          exact ih (.loop e body) hb (first.2 _ rfl) htail

end IRComparison.Circuit.Pipelining
