import IRComparison.Core.ControlIR
import IRComparison.Core.ProgramLowering

namespace IRComparison.ProgramControlIR

/-- Private loop inputs; separate from all source-visible registers/arrays. -/
structure Frame where
  index : Int
  left : Int
  right : Int
  deriving Repr

def initial : Frame := ⟨0,0,0⟩

inductive Instr where
  | setFrame (frame : Frame)
  | readLeft (offset : Int)
  | readRight (offset : Int)
  | retain
  | advance (stride : Int)
  | body (code : List ControlIR.Instr)
  | repeat (count : Nat) (code : List Instr)
  | testReg (reg : Nat) (yes no : List Instr)
  deriving Repr

inductive Config where
  | running (pending : List Instr) (state : State) (frame : Frame)
  | inBody (pending : List Instr) (frame : Frame) (body : ControlIR.Config)
  | stopped (result : Option State)

/-- Body execution takes one existing controller step, never a whole-body eval.
    Input reads, retention, and advancing the index are separate transitions. -/
def step (input : Input) : Config → Config
  | .stopped r => .stopped r
  | .running [] s _ => .stopped (some s)
  | .running (.setFrame f :: rest) s _ => .running rest s f
  | .running (.readLeft o :: rest) s f =>
    match input (f.index+o) with
    | none => .stopped none
    | some x => .running rest s { f with left := x }
  | .running (.readRight o :: rest) s f =>
    match input (f.index+o) with
    | none => .stopped none
    | some y => .running rest s { f with right := y }
  | .running (.retain :: rest) s f => .running rest s { f with left := f.right }
  | .running (.advance d :: rest) s f => .running rest s { f with index := f.index+d }
  | .running (.body b :: rest) s f => .inBody rest f (.running b s [])
  | .running (.repeat 0 _ :: rest) s f => .running rest s f
  | .running (.repeat (n+1) b :: rest) s f => .running (b ++ .repeat n b :: rest) s f
  | .running (.testReg r a b :: rest) s f =>
    .running ((if s.regs r != 0 then a else b) ++ rest) s f
  | .inBody _ _ (.stopped none) => .stopped none
  | .inBody rest f (.stopped (some s)) => .running rest s f
  | .inBody rest f c@(.inSnapshots ..) => .inBody rest f (ControlIR.step f.index f.left f.right c)
  | .inBody rest f c@(.running ..) => .inBody rest f (ControlIR.step f.index f.left f.right c)

def readIteration (d l r : Int) (b : List ControlIR.Instr) : List Instr :=
  [.readLeft l,.readRight r,.body b,.advance d]
def bufferedIteration (d o : Int) (b : List ControlIR.Instr) : List Instr :=
  [.readRight (d+o),.body b,.retain,.advance d]
def loopCode (i d : Int) (n : Nat) (l r : Int) (b : List ControlIR.Instr) : List Instr :=
  [.setFrame ⟨i,0,0⟩,.repeat n (readIteration d l r b)]
def bufferedCode (i d : Int) (n : Nat) (o : Int) (b : List ControlIR.Instr) : List Instr :=
  match n with
  | 0 => []
  | n+1 => [.setFrame ⟨i,0,0⟩,.readLeft o,.repeat (n+1) (bufferedIteration d o b)]

def lower : Imperative.Program → List Instr
  | .loop i d n l r b => loopCode i d n l r (ControlIR.lower b)
  | .buffered i d n o b => bufferedCode i d n o (ControlIR.lower b)
  | .effect b => [.setFrame initial,.body (ControlIR.lower b)]
  | .seq a b => lower a ++ lower b
  | .branch r a b => [.testReg r (lower a) (lower b)]

def resume (result : Option State) (rest : List Instr) (frame : Frame) : Config :=
  match result with
  | none => .stopped none
  | some s => .running rest s frame

inductive Reaches (input : Input) : Config → Config → Prop where
  | refl (c) : Reaches input c c
  | next {a b} : Reaches input (step input a) b → Reaches input a b

theorem Reaches.trans (h : Reaches input a b) (g : Reaches input b c) : Reaches input a c := by
  induction h with
  | refl => exact g
  | next _ ih => exact .next (ih g)

/-- Lift every body transition, including nested loops, into the outer control. -/
theorem lift_steps (f : Frame) (rest : List Instr)
    (h : ControlIR.Reaches f.index f.left f.right a b) :
    Reaches input (.inBody rest f a) (.inBody rest f b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih =>
    cases a with
    | running => exact .next ih
    | inSnapshots => exact .next ih
    | stopped r => simpa only [ControlIR.step] using ih

theorem lift_body (f : Frame) (rest : List Instr)
    (h : ControlIR.Reaches f.index f.left f.right a (.stopped result)) :
    Reaches input (.inBody rest f a) (resume result rest f) := by
  apply (lift_steps f rest h).trans
  cases result <;> exact .next (.refl _)

theorem body_correct (b : Imperative.Cmd) (f : Frame) (s : State) (rest : List Instr) :
    Reaches input (.running (.body (ControlIR.lower b) :: rest) s f)
      (resume (b.eval f.index f.left f.right s) rest f) := by
  apply Reaches.next
  apply lift_body
  have h := ControlIR.lower_correct b f.index f.left f.right s [] []
  simp only [List.append_nil] at h
  apply h.trans
  cases b.eval f.index f.left f.right s [] <;> simp [ControlIR.resume]
  · exact .refl _
  · exact .next (.refl _)

def BodyCorrect (input : Input) (code : List ControlIR.Instr) (meaning : Step State) : Prop :=
  ∀ (f : Frame) (s : State) (rest : List Instr),
    Reaches input (.running (.body code::rest) s f)
      (resume (meaning f.index f.left f.right s) rest f)

theorem readRepeat_generic (input : Input) (code : List ControlIR.Instr) (meaning : Step State)
    (bodyProof : BodyCorrect input code meaning) (d l r : Int)
    (n : Nat) (f : Frame) (s : State) (rest : List Instr) :
    ∃ finalFrame, Reaches input
      (.running (.repeat n (readIteration d l r code) :: rest) s f)
      (resume (readLoop input meaning d l r n f.index s) rest finalFrame) := by
  induction n generalizing f s with
  | zero => exact ⟨f,.next (.refl _)⟩
  | succ n ih =>
    cases hx : input (f.index+l) with
    | none =>
      refine ⟨f,.next (.next ?_)⟩
      simp [step,readIteration,hx,readLoop,resume]
      exact .refl _
    | some x =>
      cases hy : input (f.index+r) with
      | none =>
        refine ⟨f,.next (.next (.next ?_))⟩
        simp [step,readIteration,hx,hy,readLoop,resume]
        exact .refl _
      | some y =>
        have first := bodyProof ⟨f.index,x,y⟩ s
          (.advance d :: .repeat n (readIteration d l r code) :: rest)
        cases hb : meaning f.index x y s with
        | none =>
          refine ⟨f,.next (.next (.next ?_))⟩
          simpa [step,readIteration,hx,hy,readLoop,hb,resume] using first
        | some t =>
          obtain ⟨g,hg⟩ := ih ⟨f.index+d,x,y⟩ t
          refine ⟨g,.next (.next (.next ?_))⟩
          simp only [step,readIteration,List.cons_append,List.nil_append,hx,hy]
          apply first.trans
          simpa [hb,resume,readLoop,hx,hy,step] using Reaches.next hg

theorem bufferedRepeat_generic (input : Input) (code : List ControlIR.Instr) (meaning : Step State)
    (bodyProof : BodyCorrect input code meaning) (d o : Int)
    (n : Nat) (f : Frame) (s : State) (rest : List Instr) :
    ∃ finalFrame, Reaches input
      (.running (.repeat n (bufferedIteration d o code) :: rest) s f)
      (resume ((Imperative.bufferedLoop (fun j => input (j+o)) meaning
        d n f.index ⟨s,f.left⟩).map Imperative.Machine.data) rest finalFrame) := by
  induction n generalizing f s with
  | zero => exact ⟨f,.next (.refl _)⟩
  | succ n ih =>
    cases hr : input (f.index+(d+o)) with
    | none =>
      refine ⟨f,.next (.next ?_)⟩
      simp [step,bufferedIteration,hr,Imperative.bufferedLoop,Int.add_assoc,resume]
      exact .refl _
    | some y =>
      have first := bodyProof ⟨f.index,f.left,y⟩ s
        (.retain :: .advance d :: .repeat n (bufferedIteration d o code) :: rest)
      cases hb : meaning f.index f.left y s with
      | none =>
        refine ⟨f,.next (.next ?_)⟩
        simpa [step,bufferedIteration,hr,Imperative.bufferedLoop,Int.add_assoc,hb,resume] using first
      | some t =>
        obtain ⟨g,hg⟩ := ih ⟨f.index+d,y,y⟩ t
        refine ⟨g,.next (.next ?_)⟩
        simp only [step,bufferedIteration,List.cons_append,List.nil_append,hr]
        apply first.trans
        simpa [hb,resume,Imperative.bufferedLoop,Int.add_assoc,hr,step] using
          (Reaches.next (Reaches.next hg))

theorem readRepeat_correct (input : Input) (b : Imperative.Cmd) (d l r : Int)
    (n : Nat) (f : Frame) (s : State) (rest : List Instr) :
    ∃ finalFrame, Reaches input
      (.running (.repeat n (readIteration d l r (ControlIR.lower b)) :: rest) s f)
      (resume (readLoop input (fun i x y => b.eval i x y) d l r n f.index s) rest finalFrame) :=
  readRepeat_generic input (ControlIR.lower b) (fun i x y => b.eval i x y)
    (body_correct b) d l r n f s rest

theorem bufferedRepeat_correct (input : Input) (b : Imperative.Cmd) (d o : Int)
    (n : Nat) (f : Frame) (s : State) (rest : List Instr) :
    ∃ finalFrame, Reaches input
      (.running (.repeat n (bufferedIteration d o (ControlIR.lower b)) :: rest) s f)
      (resume ((Imperative.bufferedLoop (fun j => input (j+o)) (fun i x y => b.eval i x y)
        d n f.index ⟨s,f.left⟩).map Imperative.Machine.data) rest finalFrame) :=
  bufferedRepeat_generic input (ControlIR.lower b) (fun i x y => b.eval i x y)
    (body_correct b) d o n f s rest

/-- Whole-program lowering, including sequential composition and branches.
    Private frames may change; source-visible state and failure are preserved. -/
theorem lower_correct (p : Imperative.Program) (input : Input) (s : State)
    (f : Frame) (rest : List Instr) :
    ∃ finalFrame, Reaches input (.running (lower p ++ rest) s f)
      (resume (p.eval input s) rest finalFrame) := by
  induction p generalizing s f rest with
  | loop i d n l r b =>
    obtain ⟨g,hg⟩ := readRepeat_correct input b d l r n ⟨i,0,0⟩ s rest
    exact ⟨g,.next hg⟩
  | buffered i d n o b =>
    cases n with
    | zero => exact ⟨f,.refl _⟩
    | succ n =>
      cases hr : input (i+o) with
      | none =>
        refine ⟨f,.next (.next ?_)⟩
        simp [lower,bufferedCode,step,hr,Imperative.Program.eval,Imperative.runBuffered,resume]
        exact .refl _
      | some x =>
        obtain ⟨g,hg⟩ := bufferedRepeat_correct input b d o (n+1) ⟨i,x,0⟩ s rest
        refine ⟨g,.next (.next ?_)⟩
        simpa [lower,bufferedCode,step,hr,Imperative.Program.eval,Imperative.runBuffered,resume] using hg
  | effect b => exact ⟨initial,.next (body_correct b initial s rest)⟩
  | seq a b ha hb =>
    obtain ⟨g,hg⟩ := ha s f (lower b ++ rest)
    cases h : a.eval input s with
    | none =>
      refine ⟨g,?_⟩
      simpa [lower,List.append_assoc,Imperative.Program.eval,h,resume] using hg
    | some t =>
      obtain ⟨j,hj⟩ := hb t g rest
      refine ⟨j,?_⟩
      simp only [lower,List.append_assoc,Imperative.Program.eval,h,Option.bind_some]
      apply hg.trans
      simpa [h,resume] using hj
  | branch r a b ha hb =>
    by_cases hz : s.regs r = 0
    · obtain ⟨g,hg⟩ := hb s f rest
      refine ⟨g,.next ?_⟩
      simpa [lower,step,Imperative.Program.eval,hz] using hg
    · obtain ⟨g,hg⟩ := ha s f rest
      refine ⟨g,.next ?_⟩
      simpa [lower,step,Imperative.Program.eval,hz] using hg

def run (input : Input) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run input n (step input c)

theorem Reaches.finite (h : Reaches input a b) : ∃ n, run input n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem lower_finishes (p : Imperative.Program) (input : Input) (s : State) (f : Frame) :
    ∃ n, run input n (.running (lower p) s f) = .stopped (p.eval input s) := by
  obtain ⟨g,hg⟩ := lower_correct p input s f []
  simp only [List.append_nil] at hg
  apply Reaches.finite
  apply hg.trans
  cases p.eval input s <;> simp [resume]
  · exact .refl _
  · exact .next (.refl _)

def lowerFunctional (p : Functional.Program) : Option (List Instr) :=
  (ProgramLowering.lower p).map lower

theorem lowerFunctional_finishes (p : Functional.Program) (code : List Instr)
    (h : lowerFunctional p = some code) (input : Input) (s : State) (f : Frame) :
    ∃ n, run input n (.running code s f) = .stopped (p.eval input s) := by
  cases hp : ProgramLowering.lower p <;> simp [lowerFunctional,hp] at h
  subst code
  rw [← ProgramLowering.lower_correct p _ hp input s]
  exact lower_finishes _ input s f

theorem run_add (input : Input) (n m : Nat) (c : Config) :
    run input (n+m) c = run input m (run input n c) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih => simpa [run,Nat.succ_add] using ih (step input c)

@[simp] theorem run_stopped (input : Input) (n : Nat) (r : Option State) :
    run input n (.stopped r) = .stopped r := by
  induction n <;> simp_all [run,step]

theorem result_unique (ha : run input n c = .stopped a)
    (hb : run input m c = .stopped b) : a = b := by
  have h : run input (n+m) c = .stopped a := by rw [run_add,ha,run_stopped]
  have g : run input (n+m) c = .stopped b := by rw [Nat.add_comm,run_add,hb,run_stopped]
  rw [h] at g
  exact Config.stopped.inj g

theorem optimized_finishes (p : Imperative.Program) (input : Input) (s : State) :
    ∃ n, run input n (.running (lower (Imperative.transform p)) s initial) =
      .stopped (p.eval input s) := by
  simpa only [Imperative.transform_correct] using lower_finishes (Imperative.transform p) input s initial

theorem optimized_result_correct (p : Imperative.Program) (input : Input) (s : State)
    (h : run input fuel (.running (lower (Imperative.transform p)) s initial) = .stopped result) :
    result = p.eval input s := by
  obtain ⟨n,hn⟩ := optimized_finishes p input s
  exact result_unique h hn

theorem optimizedFunctional_finishes (p : Functional.Program) (code : List Instr)
    (h : lowerFunctional (Functional.transform p) = some code) (input : Input) (s : State) :
    ∃ n, run input n (.running code s initial) = .stopped (p.eval input s) := by
  simpa only [Functional.transform_correct] using
    lowerFunctional_finishes (Functional.transform p) code h input s initial

theorem optimizedFunctional_result_correct (p : Functional.Program) (code : List Instr)
    (lowered : lowerFunctional (Functional.transform p) = some code) (input : Input) (s : State)
    (h : run input fuel (.running code s initial) = .stopped result) :
    result = p.eval input s := by
  obtain ⟨n,hn⟩ := optimizedFunctional_finishes p code lowered input s
  exact result_unique h hn

/-- The common emitted schedule after the existing overlap decision. -/
def optimizedLoopCode (i d : Int) (n : Nat) (l r : Int) (body : List ControlIR.Instr) : List Instr :=
  if r = l+d then bufferedCode i d n l body else loopCode i d n l r body

theorem lower_optimizedLoop (b : Imperative.Cmd) (i d : Int) (n : Nat) (l r : Int) :
    lower (Imperative.transform (.loop i d n l r b)) =
      optimizedLoopCode i d n l r (ControlIR.lower b) := by
  by_cases h : r = l+d <;> simp [Imperative.transform,optimizedLoopCode,h,lower]

theorem lowerFunctional_optimizedLoop (b : Functional.Term) (body : List ControlIR.Instr)
    (h : ControlIR.lowerFunctional b = some body) (i d : Int) (n : Nat) (l r : Int) :
    lowerFunctional (Functional.transform (.loop i d n l r b)) =
      some (optimizedLoopCode i d n l r body) := by
  cases hb : StateLowering.lower b <;> simp [ControlIR.lowerFunctional,hb] at h
  subst body
  by_cases overlap : r = l+d <;>
    simp [lowerFunctional,Functional.transform,overlap,ProgramLowering.lower,hb,lower,optimizedLoopCode]

end IRComparison.ProgramControlIR
