import IRComparison.Memory.PipelineUse
import IRComparison.Memory.AlternativeStageFusion

namespace IRComparison.AutoPipeline
open WindowPipeline PipelineShapes PipelineUse StreamConsumer

def cleared (sizes : Nat → Nat) (array : Nat) : Nat → Nat := fun a => if a = array then 0 else sizes a

theorem layout_erase (h : Layout sizes s) : Layout (cleared sizes array) (erase array s) := by
  intro a
  by_cases ha : a = array <;> simp [erase,cleared,ha,h a]

inductive Reason where
  | globalPolicyUnavailable
  | lastStage
  | publicArray (array : Nat)
  | layoutMismatch (array : Nat)
  | noProducerTrace (array : Nat)
  | suffixNotProvedUnused (array : Nat)
  | pairNotSupported (array : Nat)
  | selected (array : Nat)
  deriving Repr, DecidableEq

/-- Greedy disjoint adjacent pairs, with no bound on the pipeline length.
    Every erased channel is absent from the public output and from the suffix. -/
inductive Plan (outputs : List Nat) : (Nat → Nat) → List Stage → Type where
  | nil : Plan outputs sizes []
  | keep (p : Stage) (reason : Reason) (tail : Plan outputs sizes ps) : Plan outputs sizes (p::ps)
  | fuse (p c : Stage) (hidden : c.array ∉ outputs) (sizeOK : c.size = sizes c.array)
      (pair : StreamFusion.Plan p c c.array c.size) (unused : Clear c.array ps)
      (tail : Plan outputs (cleared sizes c.array) ps) : Plan outputs sizes (p::c::ps)

  | alternatives (p c : Stage) (hidden : c.array ∉ outputs) (sizeOK : c.size = sizes c.array)
      (pair : AlternativeStageFusion.Plan p c) (unused : Clear c.array ps)
      (tail : Plan outputs (cleared sizes c.array) ps) : Plan outputs sizes (p::c::ps)

def compile (outputs : List Nat) (sizes : Nat → Nat) : (ps : List Stage) → Plan outputs sizes ps
  | [] => .nil
  | [p] => .keep p .lastStage .nil
  | p::c::ps =>
    let fallback := fun reason => Plan.keep p reason (compile outputs sizes (c::ps))
    if hidden : c.array ∉ outputs then
      if sizeOK : c.size = sizes c.array then
        if c.producer.isEmpty then fallback (.noProducerTrace c.array) else
        match checkTail c.array ps with
        | none => fallback (.suffixNotProvedUnused c.array)
        | some unused => match StreamFusion.compile p c c.array c.size with
          | none => match AlternativeStageFusion.compile p c with
            | none => fallback (.pairNotSupported c.array)
            | some pair => .alternatives p c hidden sizeOK pair unused (compile outputs (cleared sizes c.array) ps)
          | some pair => .fuse p c hidden sizeOK pair unused (compile outputs (cleared sizes c.array) ps)
      else fallback (.layoutMismatch c.array)
    else fallback (.publicArray c.array)

def Plan.eval (p : Plan outputs sizes ps) (x y : Int) (s : State) : Option State :=
  match p with
  | .nil => some s
  | .keep first _ tail => do tail.eval x y (← first.eval x y s)
  | .fuse _ _ _ _ pair _ tail => do tail.eval x y (← pair.eval x y s)
  | .alternatives _ _ _ _ pair _ tail => do tail.eval x y (← pair.eval x y s)

/-- Positions and inferred channel IDs make decisions reviewable. -/
def Plan.channels : Plan outputs sizes ps → List (Nat × Nat)
  | .nil => []
  | .keep _ _ tail => tail.channels.map (fun (position,array) => (position+1,array))
  | .fuse _ c _ _ _ _ tail | .alternatives _ c _ _ _ _ tail => (0,c.array)::tail.channels.map (fun (position,array) => (position+2,array))

def Plan.decisions : Plan outputs sizes ps → List (Nat × Reason)
  | .nil => []
  | .keep _ reason tail => (0,reason)::tail.decisions.map (fun (i,r) => (i+1,r))
  | .fuse _ c _ _ _ _ tail | .alternatives _ c _ _ _ _ tail => (0,.selected c.array)::tail.decisions.map (fun (i,r) => (i+2,r))

theorem Plan.correct (plan : Plan outputs sizes ps) (s : State)
    (layout : Layout sizes s) (ready : Ready x y ps s) :
    (plan.eval x y s).map (observe outputs) = (source x y ps s).map (observe outputs) := by
  induction plan generalizing s with
  | nil => rfl
  | @keep sizes ps p reason tail ih =>
    simp only [Plan.eval,source,p.eval_correct s ready.1 x y]
    cases hp : p.source x y s with
    | none => rfl
    | some u => exact ih u (layout.after (stage_same p ready.1 hp)) (ready.2 u hp)
  | @fuse sizes ps p c hidden sizeOK pair unused tail ih =>
    have sized : (s.arrays c.array).size = c.size := (layout c.array).trans sizeOK.symm
    simp only [Plan.eval,pair.correct s ready.1 sized x y,source]
    cases hp : p.source x y s with
    | none => rfl
    | some u =>
      simp only [bind,Option.bind]
      have ru := ready.2 u hp
      have lu := layout.after (stage_same p ready.1 hp)
      cases hc : c.source x y u with
      | none => rfl
      | some v =>
        have rv := ru.2 v hc
        have lv := lu.after (stage_same c ru.1 hc)
        have result := ih (erase c.array v) (layout_erase lv) (unused.ready rv)
        simpa only [unused.source rv,Option.map_map,Function.comp_def,observe_erase hidden] using result
  | @alternatives sizes ps p c hidden sizeOK pair unused tail ih =>
    have sized : (s.arrays c.array).size = c.size := (layout c.array).trans sizeOK.symm
    simp only [Plan.eval,pair.correct s ready.1 sized x y,source]
    cases hp : p.source x y s with
    | none => rfl
    | some u =>
      simp only [bind,Option.bind]
      have ru := ready.2 u hp
      have lu := layout.after (stage_same p ready.1 hp)
      cases hc : c.source x y u with
      | none => rfl
      | some v =>
        have rv := ru.2 v hc
        have lv := lu.after (stage_same c ru.1 hc)
        have result := ih (erase c.array v) (layout_erase lv) (unused.ready rv)
        simpa only [unused.source rv,Option.map_map,Function.comp_def,observe_erase hidden] using result

theorem compile_correct (outputs : List Nat) (sizes : Nat → Nat) (ps : List Stage)
    (s : State) (layout : Layout sizes s) (ready : Ready x y ps s) :
    ((compile outputs sizes ps).eval x y s).map (observe outputs) =
      (source x y ps s).map (observe outputs) :=
  (compile outputs sizes ps).correct s layout ready

end IRComparison.AutoPipeline
