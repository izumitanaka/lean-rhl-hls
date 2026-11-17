import IRComparison.Core.CommunicationIR
import IRComparison.Core.Relational

namespace IRComparison.BufferRules
open CommunicationIR

/-- A target-only held value and the remaining queue. No peek or valid bit. -/
abbrev Buffer := Int × List Int

def receive : Buffer → Option Buffer
  | (_,[]) => none
  | (_,v::q) => some (v,q)

/-- Tr-InsMemBuf (extension of ESOP for retained memory). The target
keeps its entire state, including memory and queues, and binds the read value.
Read agreement and definedness are separate from the arbitrary relation R;
in particular, a True postcondition cannot justify an invalid prefetch. -/
theorem insertMemory_rule {S T : Type} (sourceRead : S → Option Int)
    (targetRead : T → Option Int) (R : S → T → Prop) :
    Relational.Insertion
      (fun s t => R s t ∧ sourceRead s = targetRead t ∧ ∃ v, targetRead t = some v)
      (fun t => (targetRead t).map (fun v => (t,v)))
      (fun s out => R s out.1 ∧ sourceRead s = some out.2) := by
  intro s t h
  obtain ⟨related,same,v,defined⟩ := h
  simp only [defined,Option.map_some]
  exact .some ⟨related,same.trans defined⟩

/-- Tr-InsRBuf. The nonempty index sequence plus correspondence ensures
that the inserted receive succeeds, independently of any postcondition. -/
theorem insertRead_rule :
    Relational.Insertion (fun (_ : Unit) b => Corresponds input (j::keys) b.2)
      receive (fun _ b => input j = some b.1 ∧ Corresponds input keys b.2) := by
  intro _ b h
  obtain ⟨old,q⟩ := b
  cases h with
  | cons hv ht => exact .some ⟨hv,ht⟩

/-- Tr-InsMove. The source value must exist even when post is True.
The precondition is a semantic weakest precondition, not an SMT assumption. -/
theorem insertMove_rule (post : Unit → Int → Prop) :
    Relational.Insertion
      (fun s (_ : Unit) => ∃ v, value = some v ∧ post s v) (fun _ => value) post := by
  intro s _ h
  obtain ⟨v,hv,hp⟩ := h
  simpa [hv] using Option.Rel.some hp

/-- Tr-ReadMem: once b holds a[j], replacing that read by the binding
preserves its value and definedness. No window-shape assumption. -/
theorem readMem_rule {input : Input} (holds : input j = some b) :
    Relational.Translation (fun (_ : Unit) (_ : Unit) => True)
      (fun _ => input j) (fun _ => some b) Eq := by
  intro _ _ _
  simp only [holds]
  exact .some rfl

def take : Nat → Buffer → Option Buffer
  | 0,b => receive b
  | n+1,b => (receive b).bind (take n)

/-- Repeated Tr-InsRBuf applications, overwriting unused held values.
This is the derived discard-and-receive operation used by the route planner. -/
theorem take_rule (found : keys[n]? = some j) :
    Relational.Insertion (fun (_ : Unit) b => Corresponds input keys b.2)
      (take n) (fun _ b => input j = some b.1 ∧ Corresponds input (keys.drop (n+1)) b.2) := by
  induction n generalizing keys with
  | zero =>
    cases keys with
    | nil => simp at found
    | cons k ks =>
      simp at found
      subst j
      exact insertRead_rule
  | succ n ih =>
    cases keys with
    | nil => simp at found
    | cons k ks =>
      have first : Relational.Insertion
          (fun (_ : Unit) b => Corresponds input (k::ks) b.2)
          receive (fun _ b => Corresponds input ks b.2) :=
        Relational.consequence insertRead_rule (fun _ _ h => h) (fun _ _ h => h.2)
      simpa only [take,List.drop_succ_cons] using
        Relational.insertLeft first (ih (by simpa using found))

/-- Connect the derived rule to the compact executable take operation.
The equation covers empty queues and too-large discards as failures. -/
theorem take_eval (n : Nat) (b : Buffer) :
    take n b = (b.2[n]?).map (fun v => (v,b.2.drop (n+1))) := by
  induction n generalizing b with
  | zero => cases b with | mk v q => cases q <;> rfl
  | succ n ih =>
    obtain ⟨v,q⟩ := b
    cases q with
    | nil => rfl
    | cons a q => simpa [take,receive] using ih (a,q)

end IRComparison.BufferRules
