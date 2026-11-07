import IRComparison.Hybrid.HybridWindowRead
import IRComparison.Core.AffineAddress

namespace IRComparison.HybridAffine
open HybridIR AffineAddress
/-- Symbolic scalar expressions only; no reconstruction of an imperative body. -/
abbrev Known := List (Option Expr)
def Matches (known : Known) (temps : List Int) (i x y : Int) (s : State) (ls : List Int) :=
  ∀ (n : Nat) (e : Expr), known[n]? = some (some e) → ∃ v, temps[n]? = some v ∧ e.eval i x y s ls = some v

def value (known : Known) : Value → Option Expr
  | .lit n => some (.lit n)
  | .index => some .index
  | .temp n => known[n]?.join
  | .natIndex e => return .natIndex (← value known e)
  | .add a b => return .add (← value known a) (← value known b)
  | .sub a b => return .sub (← value known a) (← value known b)
  | .mul a b => return .mul (← value known a) (← value known b)
  | .div a b => return .div (← value known a) (← value known b)
  | _ => none

theorem value_correct (e : Value) (h : value known e = some v) (hm : Matches known temps i x y s ls) :
    ∃ actual, e.eval i x y ls temps = some actual ∧ v.eval i x y s ls = some actual := by
  induction e generalizing v with
  | lit n => cases h; exact ⟨n,rfl,rfl⟩
  | index => cases h; exact ⟨i,rfl,rfl⟩
  | temp n =>
    cases he : known[n]? with
    | none => simp [value,he] at h
    | some ov => cases ov with
      | none => simp [value,he] at h
      | some z => simp [value,he] at h; subst v; exact hm n z he
  | natIndex e ih =>
    cases he : value known e <;> simp [value,he] at h
    subst v
    obtain ⟨a,ha,hb⟩ := ih he
    exact ⟨Int.ofNat a.toNat,by simp [Value.eval,ha],by simp [Expr.eval,hb]⟩
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb =>
    cases h₁ : value known a <;> simp [value,h₁] at h
    cases h₂ : value known b <;> simp [h₂] at h
    subst v
    obtain ⟨av,he₁,hv₁⟩ := ha h₁
    obtain ⟨bv,he₂,hv₂⟩ := hb h₂
    simp [Value.eval,Expr.eval,he₁,he₂,hv₁,hv₂]
  | left | right | «local» => simp [value] at h

def read (known : Known) : ReadCode → Option Expr
  | .pure v => value known v
  | .bind first next => do
      let v ← read known first
      read (some v::known) next
  | _ => none

theorem matches_cons (hm : Matches known temps i x y s ls)
    (hv : ∀ e, expression = some e → e.eval i x y s ls = some actual) :
    Matches (expression::known) (actual::temps) i x y s ls := by
  intro n e hn
  cases n with
  | zero => exact ⟨actual,rfl,hv e (by simpa using hn)⟩
  | succ n => exact hm n e (by simpa using hn)

theorem read_correct (e : ReadCode) (h : read known e = some v)
    (hm : Matches known temps i x y s ls) :
    ∃ actual, e.eval i x y s ls temps = some actual ∧ v.eval i x y s ls = some actual := by
  induction e generalizing known temps v with
  | pure e => exact value_correct e h hm
  | register | memory | branch => simp [read] at h
  | bind first next hf hn =>
    cases ha : read known first with
    | none => simp [read,ha] at h
    | some a =>
      simp only [read,ha,bind,Option.bind] at h
      obtain ⟨av,hea,hva⟩ := hf ha hm
      obtain ⟨nv,hen,hvn⟩ := hn h (matches_cons hm (by intro e eq; cases eq; exact hva))
      exact ⟨nv,by simpa [ReadCode.eval,hea] using hen,hvn⟩

theorem after_read (hm : Matches known temps i x y s ls)
    (he : e.eval i x y s ls temps = some actual) :
    Matches (read known e::known) (actual::temps) i x y s ls := by
  apply matches_cons hm
  intro expression h
  obtain ⟨v,hv,hx⟩ := read_correct e h hm
  rw [he] at hv
  cases hv
  exact hx

end IRComparison.HybridAffine
