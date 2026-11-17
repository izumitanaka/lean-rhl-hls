import IRComparison.Hybrid.HybridUse
import IRComparison.Memory.StreamChainState
namespace IRComparison.HybridClear
open StreamConsumer StreamChainState
structure Clear (hidden : List Nat) (code : List HybridWindowTransport.Block) where
  bodies : ∀ a ∈ hidden, HybridUse.BodiesClear a code

def check (hidden : List Nat) (code : List HybridWindowTransport.Block) : Option (Clear hidden code) := do
  match hidden with
  | [] => return ⟨by intro a ha; exact False.elim (List.not_mem_nil ha)⟩
  | a::as =>
    let first ← HybridUse.checkBodies a code
    let rest ← check as code
    return ⟨by
      intro b hb
      if same : b = a then exact same ▸ first
      else exact rest.bodies b (by simpa [same] using hb)⟩

theorem Clear.correct (c : Clear hidden code) :
    HybridWindowTransport.eval input x y code old (eraseMany hidden s) q =
      (HybridWindowTransport.eval input x y code old s q).map (fun p => (eraseMany hidden p.1,p.2)) := by
  induction hidden with
  | nil => simp [eraseMany]
  | cons a as ih =>
    rw [eraseMany,← (c.bodies a (by simp)).correct]
    rw [ih ⟨by intro b hb; exact c.bodies b (by simp [hb])⟩]
    simp [Option.map_map,Function.comp_def,eraseMany]

inductive LoadsClosed : List HybridWindowTransport.Block → Type where
  | nil : LoadsClosed []
  | cons : loadsClosed b.loads = true → LoadsClosed bs → LoadsClosed (b::bs)

def checkLoads : (code : List HybridWindowTransport.Block) → Option (LoadsClosed code)
  | [] => some .nil
  | b::bs => do
    if h : loadsClosed b.loads = true then return .cons h (← checkLoads bs) else none

theorem LoadsClosed.correct (h : LoadsClosed code) :
    HybridWindowTransport.eval input x y code old s q = HybridWindowTransport.eval other x y code old s q := by
  induction h generalizing old s q with
  | nil => rfl
  | @cons bs b hb hs ih =>
    simp only [HybridWindowTransport.eval,loads_independent b.loads hb (input:=input) (other:=other)]
    cases WindowFIFO.execute other old b.loads q with
    | none => rfl
    | some pair =>
      obtain ⟨vs,qs⟩ := pair
      simp only [bind,Option.bind]
      cases b.body.eval b.index x y s vs with
      | none => rfl
      | some t => exact ih

end IRComparison.HybridClear
