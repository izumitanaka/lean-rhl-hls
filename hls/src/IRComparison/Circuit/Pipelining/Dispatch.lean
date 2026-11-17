import IRComparison.Circuit.SharedCompiler

namespace IRComparison.Circuit.Pipelining

/-- All alternatives retain the successful compiler/emitter equations.
Fallback preserves the SAME memory-optimization plan; it does not quietly
discard buffer insertion or restore eliminated arrays. The rolled fallback
also retains the named-communication lowerer used by the structured route. -/
inductive Integrated (p : HybridWord.Plan outputs sizes ks) (layout : Array (Nat × Nat)) (fuel : Nat) where
  | pipelined (built : WordCircuit) (verified : compileOptimizedScheduled p layout fuel = .ok built)
  | structured (built : Shared.StructuredCircuit) (verified : Shared.compileStructured p layout = .ok built)
  | sequential (built : Circuit.Checked) (text : String)
      (compiled : Circuit.compile layout (HybridUnifiedPipeline.lower p) CountedBackend.named.build = .ok built)
      (emitted : built.emit outputs = .ok text) (reason : String)

/-- Expansion is opt-in. The rolled route retains runtime loops and performs
checked boundary overlap where possible; it does not enumerate iterations.
`fuel` only applies to the explicit static-expansion attempt. -/
inductive LoopStrategy where
  | rolled
  | staticExpansion
  deriving Repr, DecidableEq

private def integrateRolled (p : HybridWord.Plan outputs sizes ks)
    (layout : Array (Nat × Nat)) (fuel : Nat) (prior : String := "") :
    Except String (Integrated p layout fuel) :=
  match structured : Shared.compileStructured p layout with
  | .ok built => .ok (.structured built structured)
  | .error structuredReason =>
    let reason := s!"{prior}structured: {structuredReason}"
    match compiled : Circuit.compile layout (HybridUnifiedPipeline.lower p) CountedBackend.named.build with
    | .error why => .error why
    | .ok built => match emitted : built.emit outputs with
      | .error why => .error why
      | .ok text => .ok (.sequential built text compiled emitted reason)

def integrate (p : HybridWord.Plan outputs sizes ks) (layout : Array (Nat × Nat))
    (fuel : Nat := 4096) (strategy : LoopStrategy := .rolled) :
    Except String (Integrated p layout fuel) :=
  match strategy with
  | .rolled => integrateRolled p layout fuel
  | .staticExpansion =>
    match checked : compileOptimizedScheduled p layout fuel with
    | .ok built => .ok (.pipelined built checked)
    | .error why => integrateRolled p layout fuel s!"static: {why}; "

/-- Optimized scheduling may decline; the SAME memory plan always has the
provided certified sequential realization. No scheduling restriction is added. -/
theorem integrate_total (p : HybridWord.Plan outputs sizes ks) (layout : Array (Nat × Nat))
    (fuel : Nat) (strategy : LoopStrategy)
    (fallback : ∃ built text,
      Circuit.compile layout (HybridUnifiedPipeline.lower p) CountedBackend.named.build = .ok built ∧
      built.emit outputs = .ok text) :
    ∃ result, integrate p layout fuel strategy = .ok result := by
  obtain ⟨built,text,compiled,emitted⟩ := fallback
  have rolled (prior : String) : ∃ result, integrateRolled p layout fuel prior = .ok result := by
    unfold integrateRolled
    split
    · exact ⟨_,rfl⟩
    · dsimp only
      split
      · rename_i why rejected
        rw [compiled] at rejected
        contradiction
      · rename_i checked accepted
        have same : checked = built := Except.ok.inj (accepted.symm.trans compiled)
        subst checked
        split
        · rename_i why rejected
          rw [emitted] at rejected
          contradiction
        · exact ⟨_,rfl⟩
  cases strategy with
  | rolled => exact rolled ""
  | staticExpansion =>
    simp only [integrate]
    split
    · exact ⟨_,rfl⟩
    · exact rolled _

def Integrated.text : Integrated p layout fuel → String
  | .pipelined built _ => built.module.text
  | .structured built _ => built.module.text
  | .sequential _ text _ _ _ => text

def Integrated.isPipelined : Integrated p layout fuel → Bool
  | .pipelined .. | .structured .. => true
  | .sequential .. => false

def Integrated.fallbackReason : Integrated p layout fuel → Option String
  | .pipelined .. | .structured .. => none
  | .sequential _ _ _ _ reason => some reason

/-- Scheduling mode, separate from a claim of overlapping loop iterations. -/
def Integrated.route : Integrated p layout fuel → String
  | .pipelined .. => "static"
  | .structured .. => "structured"
  | .sequential .. => "sequential"

end IRComparison.Circuit.Pipelining
