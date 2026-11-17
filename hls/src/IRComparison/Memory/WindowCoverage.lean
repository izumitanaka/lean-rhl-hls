import IRComparison.Memory.WindowSchedule

namespace IRComparison.WindowCoverage

def Covered (input : Input) (size : Nat) := ∀ (j : Int), 0 ≤ j → j < (size:Int) → ∃ v, input j = some v

theorem array_covered (xs : Array Int) : Covered (arrayInput xs) xs.size := by
  intro j lo hi
  have hj : j.toNat < xs.size := by omega
  refine ⟨xs[j.toNat],?_⟩
  simp [arrayInput,show ¬j < 0 by omega,Array.getElem?_eq_getElem hj]

theorem emit_exists (covered : Covered input size)
    (bounds : ∀ j ∈ keys, 0 ≤ j ∧ j < (size:Int)) : ∃ vs, CommunicationIR.emit input keys = some vs := by
  induction keys with
  | nil => exact ⟨[],rfl⟩
  | cons k ks ih =>
    have hk := bounds k (by simp)
    -- Memory-preserving window initialization/refill uses Tr-InsMemBuf,
    -- not the FIFO receive rule. Both readers use the same frozen array;
    -- the enclosing window proof establishes that its contents are framed.
    obtain ⟨out,_,_,hv⟩ := Relational.insertion_succeeds
      (BufferRules.insertMemory_rule (fun (_ : Unit) => input k)
        (fun (_ : Unit) => input k) (fun _ _ => True))
      (s := ()) (t := ()) ⟨trivial,rfl,covered k hk.1 hk.2⟩
    obtain ⟨vs,hvs⟩ := ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj))
    exact ⟨out.2::vs,by simp [CommunicationIR.emit,hv,hvs]⟩


end IRComparison.WindowCoverage
