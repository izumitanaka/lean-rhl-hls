import IRComparison.Memory.PipelineUse
import IRComparison.Memory.StreamProducerBlocks

namespace IRComparison.StreamChainState
open StreamConsumer StreamState

def eraseMany : List Nat → State → State
  | [],s => s
  | a::as,s => erase a (eraseMany as s)

theorem eraseMany_array (h : a ∉ hidden) : (eraseMany hidden s).arrays a = s.arrays a := by
  induction hidden with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.mem_cons,not_or] at h
    simp [eraseMany,erase,h.1,ih h.2]

theorem erase_commute (a b : Nat) (s : State) : erase a (erase b s) = erase b (erase a s) := by
  cases s
  simp only [erase,State.mk.injEq,true_and]
  funext k
  by_cases ha : k = a <;> by_cases hb : k = b <;> simp [ha,hb]

theorem eraseMany_commute (hidden : List Nat) (a : Nat) (s : State) :
    eraseMany hidden (erase a s) = erase a (eraseMany hidden s) := by
  induction hidden with
  | nil => rfl
  | cons b bs ih => simp only [eraseMany,ih,erase_commute b a]

structure Clear (hidden : List Nat) (code : List WindowTransport.Block) where
  bodies : ∀ a ∈ hidden, PipelineUse.BodiesClear a code

def check (hidden : List Nat) (code : List WindowTransport.Block) : Option (Clear hidden code) := do
  match hidden with
  | [] => return ⟨by intro a ha; exact False.elim (List.not_mem_nil ha)⟩
  | a::as =>
    let first ← PipelineUse.checkBodies a code
    let rest ← check as code
    return ⟨by
      intro b hb
      if same : b = a then exact same ▸ first
      else exact rest.bodies b (by simpa [same] using hb)⟩

theorem Clear.correct (c : Clear hidden code) :
    WindowTransport.eval input x y code old (eraseMany hidden s) q =
      (WindowTransport.eval input x y code old s q).map (fun p => (eraseMany hidden p.1,p.2)) := by
  induction hidden with
  | nil => simp [eraseMany]
  | cons a as ih =>
    rw [eraseMany,← (c.bodies a (by simp)).correct]
    rw [ih ⟨by intro b hb; exact c.bodies b (by simp [hb])⟩]
    simp [Option.map_map,Function.comp_def,eraseMany]

inductive LoadsClosed : List WindowTransport.Block → Type where
  | nil : LoadsClosed []
  | cons : loadsClosed b.loads = true → LoadsClosed bs → LoadsClosed (b::bs)

def checkLoads : (code : List WindowTransport.Block) → Option (LoadsClosed code)
  | [] => some .nil
  | b::bs => do
    if h : loadsClosed b.loads = true then return .cons h (← checkLoads bs) else none

theorem LoadsClosed.correct (h : LoadsClosed code) :
    WindowTransport.eval input x y code old s q = WindowTransport.eval other x y code old s q := by
  induction h generalizing old s q with
  | nil => rfl
  | @cons bs b hb hs ih =>
    simp only [WindowTransport.eval,loads_independent b.loads hb (input:=input) (other:=other)]
    cases WindowFIFO.execute other old b.loads q with
    | none => rfl
    | some pair =>
      obtain ⟨vs,qs⟩ := pair
      simp only [bind,Option.bind]
      cases b.body.eval b.index x y s vs with
      | none => rfl
      | some t => exact ih

end IRComparison.StreamChainState
