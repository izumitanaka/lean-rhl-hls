import Std

/- The displayed core grammar in lang2.tex. This module intentionally does
   not import Compat or any experimental language. Op and its mathematical
   interpretation are parameters, as OP is in the paper. -/
namespace PaperCore

abbrev Var := String
abbrev Array := String
abbrev Registers := List (Var × Int)
abbrev Heap := List ((Array × Int) × Int)
abbrev Streams := List (Array × List Int)

def put [BEq K] (entries : List (K × V)) (key : K) (value : V) : List (K × V) :=
  (key,value) :: entries.filter (fun entry => !(entry.1 == key))

inductive Expr (Op : Type) where
  | num (value : Int)
  | var (name : Var)
  | bin (op : Op) (left right : Var)
  deriving Repr, DecidableEq

def Expr.eval (meaning : Op → Int → Int → Int) (regs : Registers) : Expr Op → Option Int
  | .num n => some n
  | .var x => regs.lookup x
  | .bin op x y => do return meaning op (← regs.lookup x) (← regs.lookup y)

inductive MemoryAction (Op : Type) where
  | read (dest : Var) (array : Array) (index : Expr Op)
  | write (array : Array) (index : Expr Op) (value : Var)
  deriving Repr, DecidableEq

inductive StreamAction where
  | read (dest : Var) (array : Array)
  | write (array : Array) (value : Var)
  deriving Repr, DecidableEq

/-- Action separates the source's two array commands from the target's two
    FIFO commands. It does not introduce any extra program operation. -/
inductive Stmt (Op Action : Type) where
  | action (command : Action)
  | assign (dest : Var) (value : Expr Op)
  | seq (first second : Stmt Op Action)
  | branch (condition : Var) (yes no : Stmt Op Action)
  | loop (counter : Var) (start : Expr Op) (stop step : Int) (body : Stmt Op Action)
  | kernel (body : Stmt Op Action)
  deriving Repr, DecidableEq

abbrev Source (Op : Type) := Stmt Op (MemoryAction Op)
abbrev Target (Op : Type) := Stmt Op StreamAction

def Stmt.kernelFree : Stmt Op Action → Bool
  | .kernel _ => false
  | .seq a b | .branch _ a b => a.kernelFree && b.kernelFree
  | .loop _ _ _ _ body => body.kernelFree
  | _ => true

def Stmt.wellFormed : Stmt Op Action → Bool
  | .kernel body => body.kernelFree
  | .seq a b | .branch _ a b => a.wellFormed && b.wellFormed
  | .loop _ _ _ _ body => body.wellFormed
  | _ => true

/-- Non-nesting of kernel blocks is the paper's explicit syntax condition. -/
abbrev Program (Op Action : Type) := {s : Stmt Op Action // s.wellFormed = true}

end PaperCore
