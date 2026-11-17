import IRComparison.Hybrid.HybridShapes
import IRComparison.Hybrid.HybridSafety

namespace IRComparison.HybridUse
open HybridStage HybridSafety
open StreamConsumer (erase)

inductive BodiesClear (array : Nat) : List HybridWindowTransport.Block → Type where
  | nil : BodiesClear array []
  | cons : Checked array b.body → BodiesClear array bs → BodiesClear array (b::bs)

def checkBodies (array : Nat) : (bs : List HybridWindowTransport.Block) → Option (BodiesClear array bs)
  | [] => some .nil
  | b::bs => do return .cons (← check array b.body) (← checkBodies array bs)

theorem BodiesClear.correct (h : BodiesClear array bs) :
    (HybridWindowTransport.eval input x y bs old s q).map (fun p => (erase array p.1,p.2)) =
      HybridWindowTransport.eval input x y bs old (erase array s) q := by
  induction h generalizing old s q with
  | nil => rfl
  | @cons bs b body tail ih =>
    simp only [HybridWindowTransport.eval]
    cases hl : WindowFIFO.execute input old b.loads q with
    | none => rfl
    | some pair =>
      obtain ⟨vs,qs⟩ := pair
      simp only [bind,Option.bind,← body.correct b.index x y s vs]
      cases hb : b.body.eval b.index x y s vs with
      | none => rfl
      | some t => exact ih

structure StageClear (array : Nat) (p : Stage) where
  different : p.array ≠ array
  bodies : BodiesClear array p.code

def checkStage (array : Nat) (p : Stage) : Option (StageClear array p) := do
  if h : p.array ≠ array then return ⟨h,← checkBodies array p.code⟩ else none

theorem StageClear.ready (h : StageClear array p) (r : p.Ready s) : p.Ready (erase array s) := by
  simpa [Stage.Ready,erase,h.different] using r

theorem StageClear.source (h : StageClear array p) (r : p.Ready s) :
    p.source x y (erase array s) = (p.source x y s).map (erase array) := by
  obtain ⟨q,hq,hc⟩ := p.queue_ready s r
  have sameArray : (erase array s).arrays p.array = s.arrays p.array := by simp [erase,h.different]
  have eq₁ := p.correct s r.1 x y q hc
  have eq₂ := p.correct (erase array s) (h.ready r).1 x y q (by simpa only [sameArray] using hc)
  rw [← eq₂,← eq₁]
  simp only [sameArray,← h.bodies.correct,Option.map_map,Function.comp_def]

inductive Clear (array : Nat) : List Stage → Type where
  | nil : Clear array []
  | cons : StageClear array p → Clear array ps → Clear array (p::ps)

def checkTail (array : Nat) : (ps : List Stage) → Option (Clear array ps)
  | [] => some .nil
  | p::ps => do return .cons (← checkStage array p) (← checkTail array ps)

theorem Clear.ready (h : Clear array ps) (r : Ready x y ps s) : Ready x y ps (erase array s) := by
  induction h generalizing s with
  | nil => trivial
  | @cons p ps hp ht ih =>
    refine ⟨hp.ready r.1,?_⟩
    intro t hr
    rw [hp.source r.1] at hr
    cases he : p.source x y s with
    | none => simp [he] at hr
    | some u =>
      simp [he] at hr
      subst t
      exact ih (r.2 u he)

theorem Clear.source (h : Clear array ps) (r : Ready x y ps s) :
    source x y ps (erase array s) = (source x y ps s).map (erase array) := by
  induction h generalizing s with
  | nil => rfl
  | @cons p ps hp ht ih =>
    simp only [HybridStage.source,hp.source r.1]
    cases he : p.source x y s with
    | none => rfl
    | some u => exact ih (r.2 u he)


end IRComparison.HybridUse
