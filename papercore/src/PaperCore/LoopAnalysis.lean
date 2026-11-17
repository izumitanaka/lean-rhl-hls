import PaperCore.AccessAnalysis

namespace PaperCore.LoopAnalysis
open AccessAnalysis

/-- Root-first paths: child 0 is the first/yes/body node; child 1 is the
    second/no node. -/
def child (code : Source Op) (index : Nat) : Option (Source Op) :=
  match code,index with
  | .seq a _,0 | .branch _ a _,0 | .loop _ _ _ _ a,0 | .kernel a,0 => some a
  | .seq _ b,1 | .branch _ _ b,1 => some b
  | _,_ => none

def atPath (code : Source Op) : List Nat → Option (Source Op)
  | [] => some code
  | k :: rest => do atPath (← child code k) rest

structure Site (Op : Type) where
  path : List Nat
  original : Source Op
  deriving Repr

def under (index : Nat) (site : Site Op) : Site Op :=
  ⟨index :: site.path,site.original⟩

def sites : Source Op → List (Site Op)
  | code@(.loop _ _ _ _ body) => ⟨[],code⟩ :: (sites body).map (under 0)
  | .seq a b | .branch _ a b => (sites a).map (under 0) ++ (sites b).map (under 1)
  | .kernel body => (sites body).map (under 0)
  | _ => []

theorem under_faithful (parent : Source Op) (selected : child parent k = some body)
    (exactChild : ∀ site ∈ sites body, atPath body site.path = some site.original)
    (member : site ∈ (sites body).map (under k)) :
    atPath parent site.path = some site.original := by
  obtain ⟨inner,belongs,rfl⟩ := List.mem_map.mp member
  simpa [under,atPath,selected] using exactChild inner belongs

theorem sites_faithful (code : Source Op) :
    ∀ site ∈ sites code, atPath code site.path = some site.original := by
  induction code with
  | action cmd => simp [sites]
  | assign x e => simp [sites]
  | seq a b ia ib =>
    intro site member
    rcases List.mem_append.mp member with left | right
    · exact under_faithful _ rfl ia left
    · exact under_faithful _ rfl ib right
  | branch c a b ia ib =>
    intro site member
    rcases List.mem_append.mp member with left | right
    · exact under_faithful _ rfl ia left
    · exact under_faithful _ rfl ib right
  | loop x start stop step body ih =>
    intro site member
    rcases List.mem_cons.mp member with root | nested
    · subst site; rfl
    · exact under_faithful _ rfl ih nested
  | kernel body ih =>
    intro site member
    exact under_faithful _ rfl ih member

structure Info (Op : Type) where
  counter : Var
  start : Expr Op
  stop : Int
  step : Int
  accesses : List SymbolicAccess
  counterAfter : Option Affine
  deriving Repr

/-- The AST itself provides the loop and its body. The analyzer does not
    construct or compare against CertifiedScan/CertifiedSlidingPair examples. -/
def inspect (classify : Op → Option Arithmetic) (code : Source Op) : Except String (Info Op) :=
  match code with
  | .loop counter start stop step body =>
    match analyze classify (Env.initial counter) body with
    | .error reason => .error reason
    | .ok summary => .ok ⟨counter,start,stop,step,summary.accesses,summary.env counter⟩
  | _ => .error "site-is-not-a-loop"

structure Report (Op : Type) where
  site : Site Op
  result : Except String (Info Op)
  deriving Repr

def inspectAll (classify : Op → Option Arithmetic) (source : Source Op) : List (Report Op) :=
  (sites source).map (fun site => ⟨site,inspect classify site.original⟩)

theorem reports_faithful (member : report ∈ inspectAll classify source) :
    atPath source report.site.path = some report.site.original := by
  obtain ⟨site,belongs,rfl⟩ := List.mem_map.mp member
  exact sites_faithful source site belongs

theorem Env.initial_matches (counterValue : regs.lookup counter = some k) :
    (Env.initial counter).Matches regs k := by
  intro x a known
  by_cases eq : x = counter
  · subst x; simp [Env.initial] at known; subst a; simpa [Affine.eval] using counterValue
  · simp [Env.initial,eq] at known

/-- On any actual body execution, all reported accesses are exactly the
    runtime accesses, with their actual order, arrays and indices. In
    particular a counter assignment changes later inferred indices. -/
theorem inspect_sound {Op : Type} {classify : Op → Option Arithmetic}
    {meaning : Op → Int → Int → Int} {info : Info Op} {body : Source Op} {start : Expr Op}
    (ops : ArithmeticSound classify meaning)
    (success : inspect classify (.loop counter start stop step body) = .ok info)
    (counterValue : s.regs.lookup counter = some k)
    (run : SourceExec meaning body s t) :
    AccessTrace meaning body s t (info.accesses.map (SymbolicAccess.eval k)) ∧
      (∀ a, info.counterAfter = some a → t.regs.lookup counter = some (a.eval k)) := by
  cases analyzed : analyze classify (Env.initial counter) body with
  | error reason => simp [inspect,analyzed] at success
  | ok summary =>
    simp [inspect,analyzed] at success
    subst info
    obtain ⟨after,trace⟩ := analyze_sound ops body analyzed (Env.initial_matches counterValue) run
    exact ⟨trace,fun a known => after counter a known⟩

#print axioms sites_faithful
#print axioms reports_faithful
#print axioms inspect_sound
end PaperCore.LoopAnalysis
