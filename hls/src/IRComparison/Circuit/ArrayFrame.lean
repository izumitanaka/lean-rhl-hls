import IRComparison.Circuit.Capacity

namespace IRComparison.Circuit

def commandWrites : HybridIR.Cmd → List Nat
  | .store a _ _ => [a]
  | .seq a b | .branch _ a b => commandWrites a ++ commandWrites b
  | .letValue _ b | .repeat _ b | .forRange _ b => commandWrites b
  | _ => []

theorem fold_same {f : α → β → Option α} {project : α → γ}
    (h : ∀ s a t, f s a = some t → project t = project s)
    (xs : List β) (he : xs.foldlM f s = some t) : project t = project s := by
  induction xs generalizing s with
  | nil => change some s = some t at he; cases he; rfl
  | cons a xs ih =>
    cases hf : f s a with
    | none => simp [List.foldlM_cons,hf] at he
    | some u =>
      simp only [List.foldlM_cons,hf,bind,Option.bind] at he
      exact (ih he).trans (h s a u hf)

theorem command_array_frame (c : HybridIR.Cmd) (safe : array ∉ commandWrites c)
    (he : c.eval i x y s q ls = some (t,qs)) : t.arrays array = s.arrays array := by
  induction c generalizing s q ls t qs with
  | skip => cases he; rfl
  | assign reg e | send e =>
    cases hv : e.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hv] at he
    obtain ⟨rfl,_⟩ := he
    rfl
  | store a j e =>
    cases hj : j.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hj] at he
    next index =>
      cases hv : e.eval i x y s ls [] <;> simp [hv] at he
      next value =>
        cases write : s.write a index value <;> simp [write] at he
        obtain ⟨rfl,_⟩ := he
        exact GlobalEffects.write_other write (by simpa [commandWrites] using safe)
  | letValue e b ih =>
    cases hv : e.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hv] at he
    exact ih safe he
  | seq a b ia ib =>
    simp only [commandWrites,List.mem_append,not_or] at safe
    cases ha : a.eval i x y s q ls <;> simp [HybridIR.Cmd.eval,ha] at he
    next pair =>
      obtain ⟨u,qu⟩ := pair
      exact (ib safe.2 he).trans (ia safe.1 ha)
  | branch e a b ia ib =>
    simp only [commandWrites,List.mem_append,not_or] at safe
    cases hv : e.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hv] at he
    split at he
    · exact ib safe.2 he
    · exact ia safe.1 he
  | «repeat» n b ih =>
    exact fold_same (project:=fun p : State × List Int => p.1.arrays array)
      (fun s _ t h => ih safe h) (List.range n) he
  | forRange e b ih =>
    cases hv : e.eval i x y s ls [] <;> simp [HybridIR.Cmd.eval,hv] at he
    next n =>
      exact fold_same (project:=fun p : State × List Int => p.1.arrays array)
        (fun s (j:Nat) t h => ih (ls:=(j:Int)::ls) safe h) (List.range n.toNat) he

theorem bounded_array_frame (c : HybridIR.Cmd) (safe : array ∉ commandWrites c)
    (he : bounded capacity i x y c s q ls = some (t,qs)) : t.arrays array = s.arrays array :=
  command_array_frame c safe (bounded_refines c s q ls t qs he)

theorem matches_wires (slots : List Nat) : Matches s w (slots.map Expr.wire) (slots.map w) := by
  intro n
  simp only [lookup,List.getElem?_map]
  cases slots[n]? <;> rfl

end IRComparison.Circuit
