import PaperCore.Language

namespace PaperCore

structure State (Memory : Type) where
  regs : Registers
  memory : Memory
  deriving Repr, DecidableEq

def State.setReg (s : State M) (x : Var) (v : Int) : State M :=
  {s with regs := put s.regs x v}

inductive MemoryStep (meaning : Op → Int → Int → Int) :
    MemoryAction Op → State Heap → State Heap → Prop where
  | read (index : e.eval meaning s.regs = some i)
      (cell : s.memory.lookup (a,i) = some v) :
      MemoryStep meaning (.read x a e) s (s.setReg x v)
  | write (index : e.eval meaning s.regs = some i)
      (value : s.regs.lookup x = some v) :
      MemoryStep meaning (.write a e x) s {s with memory := put s.memory (a,i) v}

/-- Exactly one element is removed/added. No cache, Ratio or phase flag. -/
inductive StreamStep : StreamAction → State Streams → State Streams → Prop where
  | read (queue : s.memory.lookup a = some (v :: tail)) :
      StreamStep (.read x a) s
        {regs := put s.regs x v, memory := put s.memory a tail}
  | write (queue : s.memory.lookup a = some values)
      (value : s.regs.lookup x = some v) :
      StreamStep (.write a x) s {s with memory := put s.memory a (values ++ [v])}

/-- fig-lang3.tex, with the two memory rules supplied separately. Loop
    continuation uses the counter AFTER the body, including body updates.
    The literal initializer below represents evaluation of x+n in R-ForLoop;
    it avoids enlarging the grammar to allow nested expressions or literals
    as operands of `bin`. No fuel or traversal-counter restriction occurs. -/
inductive Exec (meaning : Op → Int → Int → Int)
    (action : Action → State M → State M → Prop) :
    Stmt Op Action → State M → State M → Prop where
  | action (h : action cmd s t) : Exec meaning action (.action cmd) s t
  | assign (value : e.eval meaning s.regs = some v) :
      Exec meaning action (.assign x e) s (s.setReg x v)
  | seq (first : Exec meaning action a s mid) (second : Exec meaning action b mid t) :
      Exec meaning action (.seq a b) s t
  | ifTrue (condition : s.regs.lookup x = some v) (nonzero : v ≠ 0)
      (body : Exec meaning action yes s t) : Exec meaning action (.branch x yes no) s t
  | ifFalse (condition : s.regs.lookup x = some 0)
      (body : Exec meaning action no s t) : Exec meaning action (.branch x yes no) s t
  | forExit (value : e.eval meaning s.regs = some stop) :
      Exec meaning action (.loop x e stop step body) s (s.setReg x stop)
  | forLoop (value : e.eval meaning s.regs = some k) (notAtEnd : k ≠ stop)
      (bodyRun : Exec meaning action body (s.setReg x k) mid)
      (counter : mid.regs.lookup x = some next)
      (rest : Exec meaning action (.loop x (.num (next + step)) stop step body) mid t) :
      Exec meaning action (.loop x e stop step body) s t
  | kernel (body : Exec meaning action code s t) : Exec meaning action (.kernel code) s t

abbrev SourceExec (meaning : Op → Int → Int → Int) := Exec meaning (MemoryStep meaning)
abbrev TargetExec (meaning : Op → Int → Int → Int) := Exec meaning StreamStep

theorem stream_read_empty (s : State Streams) (a x : String)
    (empty : s.memory.lookup a = some []) :
    ¬ ∃ t, StreamStep (.read x a) s t := by
  rintro ⟨t,h⟩
  cases h with
  | read queue => simp [empty] at queue

theorem memory_read_missing (meaning : Op → Int → Int → Int)
    (s : State Heap) (a x : String) (i : Int)
    (missing : s.memory.lookup (a,i) = none) :
    ¬ ∃ t, MemoryStep meaning (.read x a (.num i)) s t := by
  rintro ⟨t,h⟩
  cases h with
  | read index cell =>
    simp [Expr.eval] at index
    subst_vars
    simp_all

#print axioms stream_read_empty
#print axioms memory_read_missing
end PaperCore
