import PaperCore.Correspondence

namespace PaperCore.AccessAnalysis

structure Affine where
  scale : Int
  offset : Int
  deriving Repr, DecidableEq

def Affine.eval (a : Affine) (counter : Int) := a.scale * counter + a.offset

def Affine.add (a b : Affine) : Affine := ⟨a.scale+b.scale,a.offset+b.offset⟩
def Affine.sub (a b : Affine) : Affine := ⟨a.scale-b.scale,a.offset-b.offset⟩

/-- Multiplication remains affine when at least one operand is constant. -/
def Affine.mul (a b : Affine) : Option Affine :=
  if a.scale = 0 then some ⟨a.offset*b.scale,a.offset*b.offset⟩
  else if b.scale = 0 then some ⟨a.scale*b.offset,a.offset*b.offset⟩
  else none

theorem Affine.mul_sound {a b c : Affine} (success : a.mul b = some c) :
    c.eval counter = a.eval counter * b.eval counter := by
  unfold Affine.mul at success
  split at success
  · rename_i zero
    simp at success; subst c
    simp [Affine.eval,zero,Int.mul_add,Int.mul_assoc]
  · split at success
    · rename_i nonzero zero
      simp at success; subst c
      simp [Affine.eval,zero,Int.add_mul,Int.mul_add,Int.mul_assoc,Int.mul_comm,Int.mul_left_comm]
    · simp at success

inductive Arithmetic where
  | add | sub | mul
  deriving Repr, DecidableEq

def Arithmetic.eval : Arithmetic → Int → Int → Int
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

/-- Only the arithmetic adapter needs to know the source OP interpretation.
    Unsupported operators return none; they are never treated as addition. -/
def ArithmeticSound (classify : Op → Option Arithmetic) (meaning : Op → Int → Int → Int) : Prop :=
  ∀ op kind, classify op = some kind → ∀ x y, meaning op x y = kind.eval x y

abbrev Env := Var → Option Affine

def Env.set (env : Env) (name : Var) (value : Option Affine) : Env :=
  fun x => if x = name then value else env x

def Env.merge (left right : Env) : Env := fun x =>
  match left x,right x with
  | some a,some b => if a = b then some a else none
  | _,_ => none

def Env.initial (counter : Var) : Env := fun x => if x = counter then some ⟨1,0⟩ else none

def Env.Matches (env : Env) (regs : Registers) (counter : Int) : Prop :=
  ∀ x a, env x = some a → regs.lookup x = some (a.eval counter)

def infer (classify : Op → Option Arithmetic) (env : Env) : Expr Op → Option Affine
  | .num n => some ⟨0,n⟩
  | .var x => env x
  | .bin op x y => do
    let kind ← classify op
    let left ← env x
    let right ← env y
    match kind with
    | .add => return left.add right
    | .sub => return left.sub right
    | .mul => left.mul right

theorem infer_sound (ops : ArithmeticSound classify meaning)
    (agrees : env.Matches regs counter) (success : infer classify env expr = some result) :
    expr.eval meaning regs = some (result.eval counter) := by
  cases expr with
  | num n => simp [infer] at success; subst result; simp [Expr.eval,Affine.eval]
  | var x => exact agrees x result success
  | bin op x y =>
    cases hc : classify op with
    | none => simp [infer,hc] at success
    | some kind =>
      cases hx : env x with
      | none => simp [infer,hc,hx] at success
      | some left =>
        cases hy : env y with
        | none => simp [infer,hc,hx,hy] at success
        | some right =>
          have rx := agrees x left hx
          have ry := agrees y right hy
          cases kind with
          | add =>
            simp [infer,hc,hx,hy] at success; subst result
            simp [Expr.eval,rx,ry,ops op _ hc,Arithmetic.eval,Affine.add,Affine.eval,Int.add_mul]
            omega
          | sub =>
            simp [infer,hc,hx,hy] at success; subst result
            simp [Expr.eval,rx,ry,ops op _ hc,Arithmetic.eval,Affine.sub,Affine.eval,Int.sub_mul]
            omega
          | mul =>
            simp [infer,hc,hx,hy] at success
            have same := Affine.mul_sound (counter := counter) success
            simpa [Expr.eval,rx,ry,ops op _ hc,Arithmetic.eval] using congrArg some same.symm

theorem Env.matches_set {env : Env} {value : Affine} (agrees : env.Matches regs counter) :
    (env.set name (some value)).Matches (put regs name (value.eval counter)) counter := by
  intro x a known
  by_cases eq : x = name
  · subst x; simp [Env.set] at known; subst a; exact lookup_put_same ..
  · simp [Env.set,eq] at known
    rw [lookup_put_other _ _ _ _ eq]
    exact agrees x a known

theorem Env.matches_forget {env : Env} (agrees : env.Matches regs counter) (value : Int) :
    (env.set name none).Matches (put regs name value) counter := by
  intro x a known
  by_cases eq : x = name
  · subst x; simp [Env.set] at known
  · simp [Env.set,eq] at known
    rw [lookup_put_other _ _ _ _ eq]
    exact agrees x a known

theorem Env.merge_left {left right : Env} (agrees : left.Matches regs counter) :
    (left.merge right).Matches regs counter := by
  intro x a known
  cases hl : left x <;> cases hr : right x <;> simp [Env.merge,hl,hr] at known
  exact agrees x a (hl.trans (congrArg some known.2))

theorem Env.merge_right {left right : Env} (agrees : right.Matches regs counter) :
    (left.merge right).Matches regs counter := by
  intro x a known
  cases hl : left x <;> cases hr : right x <;> simp [Env.merge,hl,hr] at known
  exact agrees x a (hr.trans (congrArg some (known.1.symm.trans known.2)))

inductive Direction where
  | read | write
  deriving Repr, DecidableEq

structure Access where
  direction : Direction
  array : Array
  index : Int
  deriving Repr, DecidableEq

structure SymbolicAccess where
  direction : Direction
  array : Array
  index : Affine
  deriving Repr, DecidableEq

def SymbolicAccess.eval (counter : Int) (a : SymbolicAccess) : Access :=
  ⟨a.direction,a.array,a.index.eval counter⟩

structure Summary where
  env : Env
  accesses : List SymbolicAccess

/-- Straight-line body analysis. Unknown scalar results are forgotten, not
    guessed. The whole source language remains unchanged. Unsupported body
    control or index expressions are explicitly reported to the caller. -/
def analyze (classify : Op → Option Arithmetic) (env : Env) : Source Op → Except String Summary
  | .assign x e => .ok ⟨env.set x (infer classify env e),[]⟩
  | .action (.read x a e) =>
    match infer classify env e with
    | none => .error ("unknown-read-index:" ++ a)
    | some index => .ok ⟨env.set x none,[⟨.read,a,index⟩]⟩
  | .action (.write a e _) =>
    match infer classify env e with
    | none => .error ("unknown-write-index:" ++ a)
    | some index => .ok ⟨env,[⟨.write,a,index⟩]⟩
  | .seq a b =>
    match analyze classify env a with
    | .error err => .error err
    | .ok first =>
      match analyze classify first.env b with
      | .error err => .error err
      | .ok second => .ok ⟨second.env,first.accesses ++ second.accesses⟩
  | .branch _ a b =>
    match analyze classify env a,analyze classify env b with
    | .ok first,.ok second =>
      if first.accesses = second.accesses then .ok ⟨first.env.merge second.env,first.accesses⟩
      else .error "branch-dependent-access-sequence-not-yet-supported"
    | .error reason,_ | _,.error reason => .error reason
  | .loop .. => .error "nested-body-loop-not-yet-supported"
  | .kernel .. => .error "body-kernel-not-yet-supported"

/-- An observation of existing source executions, not a replacement source
    semantics: primitive steps are the original MemoryStep/SourceExec. -/
inductive AccessTrace (meaning : Op → Int → Int → Int) :
    Source Op → State Heap → State Heap → List Access → Prop where
  | assign (run : SourceExec meaning (.assign x e) s t) :
      AccessTrace meaning (.assign x e) s t []
  | read (run : MemoryStep meaning (.read x a e) s t)
      (index : e.eval meaning s.regs = some i) :
      AccessTrace meaning (.action (.read x a e)) s t [⟨.read,a,i⟩]
  | write (run : MemoryStep meaning (.write a e x) s t)
      (index : e.eval meaning s.regs = some i) :
      AccessTrace meaning (.action (.write a e x)) s t [⟨.write,a,i⟩]
  | seq (first : AccessTrace meaning a s mid left) (second : AccessTrace meaning b mid t right) :
      AccessTrace meaning (.seq a b) s t (left ++ right)
  | branchTrue (condition : s.regs.lookup x = some value) (nonzero : value ≠ 0)
      (body : AccessTrace meaning yes s t events) : AccessTrace meaning (.branch x yes no) s t events
  | branchFalse (condition : s.regs.lookup x = some 0)
      (body : AccessTrace meaning no s t events) : AccessTrace meaning (.branch x yes no) s t events

theorem analyze_sound {Op : Type} {meaning : Op → Int → Int → Int}
    {classify : Op → Option Arithmetic} (ops : ArithmeticSound classify meaning) (code : Source Op)
    (success : analyze classify env code = .ok summary)
    (agrees : env.Matches s.regs counter) (run : SourceExec meaning code s t) :
    summary.env.Matches t.regs counter ∧
      AccessTrace meaning code s t (summary.accesses.map (SymbolicAccess.eval counter)) := by
  induction code generalizing env summary s t with
  | assign x e =>
    simp [analyze] at success
    subst summary
    cases run with
    | assign value =>
      refine ⟨?_,.assign (.assign value)⟩
      cases inferred : infer classify env e with
      | none =>
        simp only [inferred]
        exact Env.matches_forget agrees _
      | some a =>
        have actual := infer_sound ops agrees inferred
        have same := Option.some.inj (value.symm.trans actual)
        subst_vars
        simpa [inferred] using Env.matches_set agrees (name := x) (value := a)
  | action cmd =>
    cases cmd with
    | read x a e =>
      cases inferred : infer classify env e with
      | none => simp [analyze,inferred] at success
      | some index =>
        simp [analyze,inferred] at success
        subst summary
        have actual := infer_sound ops agrees inferred
        cases run with
        | action step =>
          refine ⟨?_,.read step actual⟩
          cases step
          exact Env.matches_forget agrees _
    | write a e x =>
      cases inferred : infer classify env e with
      | none => simp [analyze,inferred] at success
      | some index =>
        simp [analyze,inferred] at success
        subst summary
        have actual := infer_sound ops agrees inferred
        cases run with
        | action step =>
          refine ⟨?_,.write step actual⟩
          cases step
          exact agrees
  | seq a b ia ib =>
    cases ha : analyze classify env a with
    | error err => simp [analyze,ha,Except.bind,Except.map] at success
    | ok first =>
      cases hb : analyze classify first.env b with
      | error err => simp [analyze,ha,hb,Except.bind,Except.map] at success
      | ok second =>
        simp [analyze,ha,hb,Except.bind,Except.map] at success
        subst summary
        cases run with
        | seq left right =>
          obtain ⟨ma,ta⟩ := ia ha agrees left
          obtain ⟨mb,tb⟩ := ib hb ma right
          exact ⟨mb,by simpa only [List.map_append] using AccessTrace.seq ta tb⟩
  | branch c yes no iy ino =>
    cases hy : analyze classify env yes with
    | error reason => simp [analyze,hy] at success
    | ok first =>
      cases hn : analyze classify env no with
      | error reason => simp [analyze,hy,hn] at success
      | ok second =>
        by_cases same : first.accesses = second.accesses
        · simp [analyze,hy,hn,same] at success; subst summary
          cases run with
          | ifTrue condition nonzero bodyRun =>
            obtain ⟨envAfter,trace⟩ := iy hy agrees bodyRun
            exact ⟨Env.merge_left envAfter,by simpa only [same] using AccessTrace.branchTrue condition nonzero trace⟩
          | ifFalse condition bodyRun =>
            obtain ⟨envAfter,trace⟩ := ino hn agrees bodyRun
            exact ⟨Env.merge_right envAfter,by simpa only [same] using AccessTrace.branchFalse condition trace⟩
        · simp [analyze,hy,hn,same] at success
  | loop x start stop step body ih => simp [analyze] at success
  | kernel body ih => simp [analyze] at success

#print axioms infer_sound
#print axioms analyze_sound
end PaperCore.AccessAnalysis
