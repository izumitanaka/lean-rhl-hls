import IRComparison.Hybrid.HybridValues

namespace IRComparison.HybridAddress
open HybridIR

abbrev Known := List (Option Int)
def Matches (known : Known) (temps : List Int) : Prop :=
  ∀ (k : Nat) (v : Int), known[k]? = some (some v) → temps[k]? = some v

theorem matches_cons (h : Matches known temps) (hv : ∀ k, value = some k → actual = k) :
    Matches (value::known) (actual::temps) := by
  intro n v hn
  cases n with
  | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at hn
            simp only [List.getElem?_cons_zero,Option.some.injEq]
            cases value with
            | none => cases hn
            | some z => cases hn; exact hv v rfl
  | succ n => exact h n v (by simpa using hn)

def value (i : Int) (known : Known) : Value → Option Int
  | .lit n => some n
  | .index => some i
  | .temp n => known[n]?.join
  | .natIndex e => return Int.ofNat (← value i known e).toNat
  | .add a b => return (← value i known a)+(← value i known b)
  | .sub a b => return (← value i known a)-(← value i known b)
  | .mul a b => return (← value i known a)*(← value i known b)
  | .div a b => return (← value i known a)/(← value i known b)
  | _ => none

theorem value_correct (e : Value) (h : value i known e = some v) (hm : Matches known temps) :
    e.eval i x y locals temps = some v := by
  induction e generalizing v with
  | lit | index => exact h
  | temp n =>
    cases he : known[n]? with
    | none => simp [value,he] at h
    | some ov => cases ov with
      | none => simp [value,he] at h
      | some z => simp [value,he] at h; subst v; exact hm n z he
  | natIndex e ih =>
    cases he : value i known e <;> simp [value,he] at h
    subst v; simp [Value.eval,ih he]
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb =>
    cases h₁ : value i known a <;> simp [value,h₁] at h
    cases h₂ : value i known b <;> simp [h₂] at h
    subst v; simp [Value.eval,ha h₁,hb h₂]
  | left | right | «local» => simp [value] at h

def read (i : Int) (known : Known) : ReadCode → Option Int
  | .pure v => value i known v
  | .register .. | .memory .. => none
  | .bind first next => do
      let v ← read i known first
      read i (some v::known) next
  | .branch c yes no => do
      if (← value i known c) != 0 then read i known yes else read i known no

theorem read_correct (e : ReadCode) (h : read i known e = some v) (hm : Matches known temps) :
    e.eval i x y s locals temps = some v := by
  induction e generalizing known temps v with
  | pure e => exact value_correct e h hm
  | register | memory => simp [read] at h
  | bind first next hf hn =>
    cases ha : read i known first with
    | none => simp [read,ha] at h
    | some a =>
      simp only [read,ha,bind,Option.bind] at h
      have hea := hf ha hm
      simp only [ReadCode.eval,hea,bind,Option.bind]
      exact hn h (matches_cons hm (by simp))
  | branch c yes no hy hn =>
    cases hc : value i known c with
    | none => simp [read,hc] at h
    | some cvalue =>
      have hec := value_correct c hc hm (x:=x) (y:=y) (locals:=locals)
      simp only [read,hc,bind,Option.bind] at h
      simp only [ReadCode.eval,hec,bind,Option.bind]
      split at h
      · simp_all [hy h hm]
      · simp_all [hn h hm]

/-- Extend known temporaries only by facts proved from the read computation;
    unknown values are allowed and do not restrict accepted source programs. -/
theorem after_read (hm : Matches known temps) (he : e.eval i x y s locals temps = some actual) :
    Matches (read i known e::known) (actual::temps) := by
  intro n v hn
  cases n with
  | zero =>
    simp only [List.getElem?_cons_zero,Option.some.injEq] at hn
    have hv := read_correct e hn hm (x:=x) (y:=y) (s:=s) (locals:=locals)
    rw [he] at hv
    simpa using hv
  | succ n => exact hm n v (by simpa using hn)

end IRComparison.HybridAddress
