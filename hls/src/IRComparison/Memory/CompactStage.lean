import IRComparison.Memory.CompactDuplex
import IRComparison.Memory.StreamChainState
import IRComparison.Memory.FunctionalSymbolicLoop

namespace IRComparison.CompactStage
open StreamConsumer StreamChainState PipelineShapes

structure Stage where
  array : Nat
  size : Nat
  code : SymbolicWindowLoop.Code
  source : Int → Int → State → Option State
  correct : ∀ s, (s.arrays array).size = size → ∀ x y,
    code.eval (arrayInput (s.arrays array)) x y s = source x y s

def Stage.rebase (p : Stage) (other : Int → Int → State → Option State) (same : ∀ x y s, p.source x y s = other x y s) : Stage :=
  ⟨p.array,p.size,p.code,other,fun s hs x y => (p.correct s hs x y).trans (same x y s)⟩

def imperative (p : SymbolicWindowLoop.Selected size array body start stride count) : Stage :=
  ⟨array,size,p.code,(fun x y s => Source.iterate (fun i => body.eval i x y) stride count start s),
    fun s hs x y => p.correct s hs⟩
def functional (p : FunctionalSymbolicLoop.Selection size array body start stride count) : Stage :=
  ⟨array,size,p.code,(fun x y s => Source.iterate (fun i t => body.eval i x y [t]) stride count start s),p.correct⟩

theorem loop_same (code : SymbolicWindowLoop.Code)
    (h : code.loop input x y n k old s = some t) : Same s t := by
  induction n generalizing k old s with
  | zero => cases h; exact fun _ => rfl
  | succ n ih =>
    rw [SymbolicWindowLoop.Code.loop] at h
    cases hb : code.body.eval (SymbolicWindowLoop.index code.start code.stride k) x y s old <;> simp only [hb,bind,Option.bind] at h
    · cases h
    · rename_i u
      have first := body_same code.body hb
      cases n with
      | zero => cases h; exact first
      | succ m =>
        cases hl : SymbolicWindowSchedule.execute input (SymbolicWindowLoop.index code.start code.stride (k+1)) old code.refill <;>
          simp only [hl,bind,Option.bind] at h
        · cases h
        · have next := ih h; exact fun a => (first a).trans (next a)

theorem code_same (code : SymbolicWindowLoop.Code) (h : code.eval input x y s = some t) : Same s t := by
  unfold SymbolicWindowLoop.Code.eval at h
  cases hc : code.count <;> simp only [hc] at h
  · cases h; exact fun _ => rfl
  · cases hl : SymbolicWindowSchedule.execute input code.start [] code.initial <;> simp only [hl,bind,Option.bind] at h
    · cases h
    · exact loop_same code h

theorem Stage.same (p : Stage) (sized : (s.arrays p.array).size = p.size) (h : p.source x y s = some t) : Same s t :=
  code_same p.code ((p.correct s sized x y).trans h)

theorem loop_erase (checked : Checked array code.body) (n k : Nat) (old : List Int) (s : State) :
    (SymbolicWindowLoop.Code.loop code input x y n k old s).map (erase array) =
      code.loop input x y n k old (erase array s) := by
  induction n generalizing k old s with
  | zero => rfl
  | succ n ih =>
    rw [SymbolicWindowLoop.Code.loop,SymbolicWindowLoop.Code.loop,← checked.correct]
    cases hb : code.body.eval (SymbolicWindowLoop.index code.start code.stride k) x y s old with
    | none => rfl
    | some t =>
      cases n with
      | zero => rfl
      | succ m =>
        simp only [Option.map_some,bind,Option.bind]
        cases SymbolicWindowSchedule.execute input (SymbolicWindowLoop.index code.start code.stride (k+1)) old code.refill with
        | none => rfl
        | some vs => exact ih (k+1) vs t

theorem code_erase (checked : Checked array code.body) (s : State) :
    (SymbolicWindowLoop.Code.eval code input x y s).map (erase array) = code.eval input x y (erase array s) := by
  cases hc : code.count with
  | zero => simp [SymbolicWindowLoop.Code.eval,hc]
  | succ n =>
    simp only [SymbolicWindowLoop.Code.eval,hc]
    cases SymbolicWindowSchedule.execute input code.start [] code.initial with
    | none => rfl
    | some vs => exact loop_erase checked (n+1) 0 vs s

structure Clear (hidden : List Nat) (body : Imperative.Cmd) where
  bodies : ∀ a ∈ hidden, Checked a body

def check (hidden : List Nat) (body : Imperative.Cmd) : Option (Clear hidden body) := do
  match hidden with
  | [] => return ⟨by intro a ha; exact False.elim (List.not_mem_nil ha)⟩
  | a::as =>
    let first ← StreamConsumer.check a body
    let rest ← check as body
    return ⟨by
      intro b hb
      if same : b = a then exact same ▸ first
      else exact rest.bodies b (by simpa [same] using hb)⟩

theorem Clear.correct (c : Clear hidden code.body) :
    SymbolicWindowLoop.Code.eval code input x y (eraseMany hidden s) =
      (code.eval input x y s).map (eraseMany hidden) := by
  induction hidden with
  | nil => simp [eraseMany]
  | cons a as ih =>
    rw [eraseMany,← code_erase (c.bodies a (by simp))]
    rw [ih ⟨by intro b hb; exact c.bodies b (by simp [hb])⟩]
    simp only [Option.map_map,Function.comp_def,eraseMany]

def source (x y : Int) : List Stage → State → Option State
  | [],s => some s
  | p::ps,s => do source x y ps (← p.source x y s)

end IRComparison.CompactStage
