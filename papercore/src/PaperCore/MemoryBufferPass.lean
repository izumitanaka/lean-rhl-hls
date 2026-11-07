import PaperCore.MemoryWindowProgram
import PaperCore.MemoryFacts

namespace PaperCore.MemoryBufferPass
open AccessAnalysis SourcePass MemoryWindowPlan

structure Result (classify : Op → Option Arithmetic) (variables : List Var)
    (known : List MemoryFacts.Span) (source : Source Op) where
  code : Source Op
  notes : List String
  forward : ∀ meaning, ArithmeticSound classify meaning → ∀ {left right final},
    Agrees (fun x => x ∈ variables) left right → MemoryFacts.Holds known left.memory →
    SourceExec meaning source left final →
    ∃ out, SourceExec meaning code right out ∧ Agrees (fun x => x ∈ variables) final out
  backward : ∀ meaning, ArithmeticSound classify meaning → ∀ {left right out},
    Agrees (fun x => x ∈ variables) left right → MemoryFacts.Holds known left.memory →
    SourceExec meaning code right out →
    ∃ final, SourceExec meaning source left final ∧ Agrees (fun x => x ∈ variables) final out

variable {Op : Type} {classify : Op → Option Arithmetic} {variables : List Var}
  {known : List MemoryFacts.Span} {source : Source Op}

def retain (source : Source Op) (typed : BufferView.Typed (fun x => x ∈ variables) source)
    (reason : String) : Result classify variables known source where
  code := source
  notes := if reason = "" then [] else [reason]
  forward := fun _ _ _ _ _ agrees _ run => execute_frame run typed agrees
  backward := by
    intro meaning ops left right out agrees _ run
    obtain ⟨final,executed,after⟩ := execute_frame run typed agrees.symm
    exact ⟨final,executed,after.symm⟩

def after (known : List MemoryFacts.Span) (facts : MemoryFacts.Result classify source) := known ++ facts.facts

theorem after_holds (knownAt : MemoryFacts.Holds known initial.memory)
    (facts : MemoryFacts.Result classify source) (ops : ArithmeticSound classify meaning)
    (run : SourceExec meaning source initial final) : MemoryFacts.Holds (after known facts) final.memory := by
  intro span member
  rcases List.mem_append.mp member with old | new
  · exact MemoryFacts.preserved run knownAt span old
  · exact facts.sound meaning ops run span new

def sequence (first : Result classify variables known a)
    (facts : MemoryFacts.Result classify a)
    (second : Result classify variables (after known facts) b) : Result classify variables known (.seq a b) where
  code := .seq first.code second.code
  notes := first.notes ++ second.notes
  forward := by
    intro meaning ops left right final agrees knownAt run
    cases run with
    | seq ha hb =>
      obtain ⟨mid,firstRun,midAgrees⟩ := first.forward meaning ops agrees knownAt ha
      obtain ⟨out,secondRun,endAgrees⟩ := second.forward meaning ops midAgrees (after_holds knownAt facts ops ha) hb
      exact ⟨out,.seq firstRun secondRun,endAgrees⟩
  backward := by
    intro meaning ops left right out agrees knownAt run
    cases run with
    | seq ha hb =>
      obtain ⟨mid,firstRun,midAgrees⟩ := first.backward meaning ops agrees knownAt ha
      obtain ⟨final,secondRun,endAgrees⟩ := second.backward meaning ops midAgrees (after_holds knownAt facts ops firstRun) hb
      exact ⟨final,.seq firstRun secondRun,endAgrees⟩

def branch (condition : Var) (typed : condition ∈ variables)
    (yes : Result classify variables known a) (no : Result classify variables known b) :
    Result classify variables known (.branch condition a b) where
  code := .branch condition yes.code no.code
  notes := yes.notes ++ no.notes
  forward := by
    intro meaning ops left right final agrees knownAt run
    cases run with
    | ifTrue value nonzero body =>
      obtain ⟨out,executed,after⟩ := yes.forward meaning ops agrees knownAt body
      exact ⟨out,.ifTrue ((agrees.registers _ typed).symm.trans value) nonzero executed,after⟩
    | ifFalse value body =>
      obtain ⟨out,executed,after⟩ := no.forward meaning ops agrees knownAt body
      exact ⟨out,.ifFalse ((agrees.registers _ typed).symm.trans value) executed,after⟩
  backward := by
    intro meaning ops left right out agrees knownAt run
    cases run with
    | ifTrue value nonzero body =>
      obtain ⟨final,executed,after⟩ := yes.backward meaning ops agrees knownAt body
      exact ⟨final,.ifTrue ((agrees.registers _ typed).trans value) nonzero executed,after⟩
    | ifFalse value body =>
      obtain ⟨final,executed,after⟩ := no.backward meaning ops agrees knownAt body
      exact ⟨final,.ifFalse ((agrees.registers _ typed).trans value) executed,after⟩

def kernel (inside : Result classify variables known body) : Result classify variables known (.kernel body) where
  code := .kernel inside.code
  notes := inside.notes
  forward := by
    intro meaning ops left right final agrees knownAt run
    cases run with
    | kernel body =>
      obtain ⟨out,executed,after⟩ := inside.forward meaning ops agrees knownAt body
      exact ⟨out,.kernel executed,after⟩
  backward := by
    intro meaning ops left right out agrees knownAt run
    cases run with
    | kernel body =>
      obtain ⟨final,executed,after⟩ := inside.backward meaning ops agrees knownAt body
      exact ⟨final,.kernel executed,after⟩

def needed (p : Candidate classify source) : MemoryFacts.Span :=
  ⟨p.input,p.base p.start,OrientedWindow.direction p.reverse,
    if p.start = p.stop then 0 else p.overlap+p.trips*p.reload⟩

def window (p : Candidate classify source)
    (typed : BufferView.Typed (fun x => x ∈ variables) source)
    (included : ∀ x ∈ variables, x ∈ p.variables)
    (coverage : MemoryFacts.Certificate known (needed p)) : Result classify variables known source where
  code := p.code
  notes := ["memory-window-inserted:" ++ p.input]
  forward := by
    intro meaning ops left right final agrees knownAt run
    obtain ⟨sourceOut,original,frame⟩ := execute_frame run typed agrees
    have covered : p.covered right.memory := by
      rw [← agrees.memory]
      exact coverage.sound _ knownAt
    obtain ⟨out,executed,after⟩ := p.program_forward ops covered original
    exact ⟨out,executed,frame.trans ⟨fun x hx => after.registers x (included x hx),after.memory⟩⟩
  backward := by
    intro meaning ops left right out agrees knownAt run
    have covered : p.covered right.memory := by
      rw [← agrees.memory]
      exact coverage.sound _ knownAt
    obtain ⟨sourceOut,original,after⟩ := p.program_backward ops covered run
    obtain ⟨final,executed,frame⟩ := execute_frame original typed agrees.symm
    exact ⟨final,executed,frame.symm.trans ⟨fun x hx => after.registers x (included x hx),after.memory⟩⟩

def prepare (classify : Op → Option Arithmetic) (add mul : Op) (variables : List Var)
    (known : List MemoryFacts.Span) : (source : Source Op) →
    BufferView.Typed (fun x => x ∈ variables) source → Result classify variables known source
  | .seq a b,typed =>
    let facts := MemoryFacts.infer classify a
    sequence (prepare classify add mul variables known a typed.1) facts
      (prepare classify add mul variables (after known facts) b typed.2)
  | .branch condition a b,typed => branch condition typed.1
      (prepare classify add mul variables known a typed.2.1) (prepare classify add mul variables known b typed.2.2)
  | .kernel body,typed => kernel (prepare classify add mul variables known body typed)
  | .assign x e,typed => retain (.assign x e) typed ""
  | .action action,typed => retain (.action action) typed ""
  | source,typed =>
    match MemoryWindowPlan.prepare classify add mul variables source with
    | .error reason => retain source typed reason
    | .ok p =>
      if names : variables.all (fun x => decide (x ∈ p.variables)) = true then
        match MemoryFacts.certify known (needed p) with
        | none => retain source typed ("memory-window-prefetch-not-proved:" ++ p.input)
        | some coverage => window p typed
            (fun x hx => by simpa using List.all_eq_true.mp names x hx) coverage
      else retain source typed "memory-window-unprotected-variable"

structure Artifact (classify : Op → Option Arithmetic) (source : Source Op) where
  pass : SourcePass.Prepared classify source
  notes : List String

def compile (classify : Op → Option Arithmetic) (add mul : Op) (source : Source Op) : Artifact classify source :=
  let variables := BufferNames.sourceVars source
  let result := prepare classify add mul variables [] source (BufferNames.source_typed source (by intros; assumption))
  if names : variables.all (fun x => decide (x ∈ BufferNames.sourceVars result.code)) = true then
    ⟨⟨result.code,(fun x hx => by simpa using List.all_eq_true.mp names x hx),by
      intro meaning ops
      constructor
      · intro initial final run
        exact result.forward meaning ops (Agrees.refl initial) (by intro span member; simp at member) run
      · intro initial out run
        exact result.backward meaning ops (Agrees.refl initial) (by intro span member; simp at member) run⟩,result.notes⟩
  else ⟨SourcePass.identity classify source,["memory-window-output-variable-coverage-fallback"]⟩

#print axioms compile
end PaperCore.MemoryBufferPass
