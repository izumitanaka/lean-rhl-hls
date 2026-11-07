import IRComparison.Core.CommunicationIR
import PaperCore.WindowAnalysis

namespace IRComparison.WindowSchedule

/-- Static buffer operations. Copies refer to the previous window, not to an
    associative cache or a runtime valid bit. Addresses are fixed by planning. -/
inductive Load where
  | memory (address : Int)
  | saved (slot : Nat)
  deriving Repr, DecidableEq

def Load.eval (input : Input) (old : List Int) : Load → Option Int
  | .memory a => input a
  | .saved j => old[j]?

def execute (input : Input) (old : List Int) : List Load → Option (List Int)
  | [] => some []
  | x::xs => do return (← x.eval input old) :: (← execute input old xs)

def slot (key : Int) : (keys : List Int) → Option {n : Nat // keys[n]? = some key}
  | [] => none
  | k::ks =>
    if h : key = k then some ⟨0,by simp [h]⟩ else do
      let ⟨n,hn⟩ ← slot key ks
      return ⟨n+1,by simpa using hn⟩

inductive Matches (input : Input) (keys values : List Int) : Prop where
  | intro (same : keys.length = values.length)
      (point : ∀ (n : Nat) key, keys[n]? = some key → ∃ value, values[n]? = some value ∧ input key = some value) :
      Matches input keys values

theorem Matches.nil : Matches input [] [] := ⟨rfl,by simp⟩
theorem Matches.cons (h : input k = some v) (rest : Matches input ks vs) :
    Matches input (k::ks) (v::vs) := by
  obtain ⟨len,point⟩ := rest
  refine ⟨by simp [len],?_⟩
  intro n key found
  cases n with
  | zero => simp at found; subst key; exact ⟨v,rfl,h⟩
  | succ n => simpa using point n key (by simpa using found)

def loads (old : List Int) : List Int → List Load
  | [] => []
  | key::keys =>
    (match slot key old with | some j => .saved j.val | none => .memory key) :: loads old keys

theorem loads_correct (held : Matches input old values) :
    execute input values (loads old keys) = CommunicationIR.emit input keys := by
  induction keys with
  | nil => rfl
  | cons k ks ih =>
    simp only [loads,execute,CommunicationIR.emit]
    cases hs : slot k old with
    | none => simpa [Load.eval,ih]
    | some j =>
      obtain ⟨len,point⟩ := held
      obtain ⟨v,hv,hi⟩ := point j.val k j.property
      simp [Load.eval,hv,hi,ih]

theorem emit_matches (h : CommunicationIR.emit input keys = some values) : Matches input keys values := by
  induction keys generalizing values with
  | nil => simp [CommunicationIR.emit] at h; subst values; exact .nil
  | cons k ks ih =>
    cases hk : input k <;> simp [CommunicationIR.emit,hk] at h
    cases ht : CommunicationIR.emit input ks <;> simp [ht] at h
    subst values
    exact Matches.cons hk (ih ht)

/-- Memory reads physically remaining after reuse; copies do not consume FIFO. -/
def reads : List Load → List Int
  | [] => []
  | .memory a::xs => a::reads xs
  | .saved _::xs => reads xs

/-- The full min/max interval, in movement order. Holes in the original access
    set are included; callers must establish coverage before using this plan. -/
def interval (reverse : Bool) (low high : Int) : List Int :=
  if reverse then ((List.range (high-low+1).toNat).map fun (j : Nat) => high-(j:Int))
  else ((List.range (high-low+1).toNat).map fun (j : Nat) => low+(j:Int))

end IRComparison.WindowSchedule
