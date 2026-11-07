import PaperCore.BufferMemory

namespace PaperCore.MemoryBufferBody
open AccessAnalysis BufferView

/-- Unlike MixedBody, writes remain array writes. Storage selection belongs to
another pass. A successful body substitution preserves the complete state. -/
def Valid (meaning : Op → Int → Int → Int) (slots : Slots) (counter : Int)
    (env after : Env) (source transformed : Source Op) : Prop :=
  ∀ initial final, env.Matches initial.regs counter → View slots counter initial.memory initial.regs →
    (SourceExec meaning source initial final ↔ SourceExec meaning transformed initial final) ∧
    (SourceExec meaning source initial final →
      after.Matches final.regs counter ∧ View slots counter final.memory final.regs)

structure Prepared (classify : Op → Option Arithmetic) (slots : Slots) (input : Array)
    (env : Env) (source : Source Op) where
  code : Source Op
  after : Env
  correct : ∀ meaning, ArithmeticSound classify meaning → ∀ ordinary,
    Fresh slots ordinary → Typed ordinary source → BufferMemory.SlotsFor slots input →
    ∀ counter, Valid meaning slots counter env after source code

variable {Op : Type} {classify : Op → Option Arithmetic} {meaning : Op → Int → Int → Int}

private theorem assign_valid (ops : ArithmeticSound classify meaning)
    (fresh : Fresh slots ordinary) (typed : Typed ordinary (.assign x e : Source Op)) :
    Valid meaning slots counter env (env.set x (infer classify env e)) (.assign x e) (.assign x e) := by
  intro initial final agrees view
  refine ⟨Iff.rfl,?_⟩
  intro run
  cases run with
  | assign value => exact ⟨assign_env ops agrees value,view_set fresh view typed.1⟩

private theorem read_valid (ops : ArithmeticSound classify meaning)
    (fresh : Fresh slots ordinary) (typed : Typed ordinary (.action (.read x a e) : Source Op))
    (inferred : infer classify env e = some index) (found : slots a index = some buffer) :
    Valid meaning slots counter env (env.set x none) (.action (.read x a e)) (.assign x (.var buffer)) := by
  intro initial final agrees view
  obtain ⟨value,cell,held⟩ := view a index buffer found
  have address := infer_sound ops agrees inferred
  have original : SourceExec meaning (.action (.read x a e)) initial (initial.setReg x value) :=
    .action (.read address cell)
  have replaced : SourceExec meaning (.assign x (.var buffer)) initial (initial.setReg x value) :=
    .assign held
  constructor
  · constructor
    · intro run
      have same := memoryAction_unique run original
      subst final
      exact replaced
    · intro run
      cases run with
      | assign assigned =>
        have same := Option.some.inj (assigned.symm.trans held)
        subst_vars
        exact original
  · intro run
    have same := memoryAction_unique run original
    subst final
    exact ⟨Env.matches_forget agrees value,view_set fresh view typed.1⟩

private theorem write_valid (only : BufferMemory.SlotsFor slots input) (other : a ≠ input) :
    Valid meaning slots counter env env (.action (.write a e x)) (.action (.write a e x)) := by
  intro initial final agrees view
  refine ⟨Iff.rfl,?_⟩
  intro run
  cases run with
  | action step =>
    cases step with
    | write index value => exact ⟨agrees,BufferMemory.view_write only other view⟩

private theorem seq_valid
    (left : Valid meaning slots counter env mid a ta)
    (right : Valid meaning slots counter mid finalEnv b tb) :
    Valid meaning slots counter env finalEnv (.seq a b) (.seq ta tb) := by
  intro initial final agrees view
  constructor
  · constructor
    · intro run
      cases run with
      | seq first second =>
        obtain ⟨eqFirst,postFirst⟩ := left _ _ agrees view
        obtain ⟨midEnv,midView⟩ := postFirst first
        exact .seq (eqFirst.mp first) ((right _ _ midEnv midView).1.mp second)
    · intro run
      cases run with
      | seq first second =>
        obtain ⟨eqFirst,postFirst⟩ := left _ _ agrees view
        have original := eqFirst.mpr first
        obtain ⟨midEnv,midView⟩ := postFirst original
        exact .seq original ((right _ _ midEnv midView).1.mpr second)
  · intro run
    cases run with
    | seq first second =>
      obtain ⟨midEnv,midView⟩ := (left _ _ agrees view).2 first
      exact (right _ _ midEnv midView).2 second

private theorem branch_valid
    (yes : Valid meaning slots counter env leftEnv a ta)
    (no : Valid meaning slots counter env rightEnv b tb) :
    Valid meaning slots counter env (leftEnv.merge rightEnv) (.branch c a b) (.branch c ta tb) := by
  intro initial final agrees view
  constructor
  · constructor
    · intro run
      cases run with
      | ifTrue condition nonzero body => exact .ifTrue condition nonzero ((yes _ _ agrees view).1.mp body)
      | ifFalse condition body => exact .ifFalse condition ((no _ _ agrees view).1.mp body)
    · intro run
      cases run with
      | ifTrue condition nonzero body => exact .ifTrue condition nonzero ((yes _ _ agrees view).1.mpr body)
      | ifFalse condition body => exact .ifFalse condition ((no _ _ agrees view).1.mpr body)
  · intro run
    cases run with
    | ifTrue condition nonzero body =>
      obtain ⟨env,held⟩ := (yes _ _ agrees view).2 body
      exact ⟨Env.merge_left env,held⟩
    | ifFalse condition body =>
      obtain ⟨env,held⟩ := (no _ _ agrees view).2 body
      exact ⟨Env.merge_right env,held⟩

/-- Affine access inference is used only for selecting a buffer slot. Writes to
other arrays stay unchanged, even when their indices cannot be inferred. -/
def prepare (classify : Op → Option Arithmetic) (slots : Slots) (input : Array) (env : Env)
    (source : Source Op) : Except String (Prepared classify slots input env source) :=
  match source with
  | .assign x e => .ok ⟨.assign x e,env.set x (infer classify env e),
      fun _ ops _ fresh typed _ _ => assign_valid ops fresh typed⟩
  | .action (.read x a e) =>
    match hi : infer classify env e with
    | none => .error ("memory-buffer-unknown-read-index:" ++ a)
    | some index => match hs : slots a index with
      | none => .error ("memory-buffer-no-slot:" ++ a)
      | some buffer => .ok ⟨.assign x (.var buffer),env.set x none,
          fun _ ops _ fresh typed _ _ => read_valid ops fresh typed hi hs⟩
  | .action (.write a e x) =>
    if other : a = input then .error "memory-buffer-write-to-buffered-input"
    else .ok ⟨.action (.write a e x),env,
      fun _ _ _ _ _ only _ => write_valid only other⟩
  | .seq a b => do
    let first ← prepare classify slots input env a
    let second ← prepare classify slots input first.after b
    return ⟨.seq first.code second.code,second.after,fun meaning ops ordinary fresh typed only counter =>
      seq_valid (first.correct meaning ops ordinary fresh typed.1 only counter)
        (second.correct meaning ops ordinary fresh typed.2 only counter)⟩
  | .branch c a b => do
    let yes ← prepare classify slots input env a
    let no ← prepare classify slots input env b
    return ⟨.branch c yes.code no.code,yes.after.merge no.after,
      fun meaning ops ordinary fresh typed only counter =>
        branch_valid (yes.correct meaning ops ordinary fresh typed.2.1 only counter)
          (no.correct meaning ops ordinary fresh typed.2.2 only counter)⟩
  | .loop .. => .error "memory-buffer-nested-loop-not-yet-supported"
  | .kernel .. => .error "memory-buffer-kernel-in-body-not-yet-supported"

#print axioms prepare
end PaperCore.MemoryBufferBody
