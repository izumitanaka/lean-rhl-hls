import IRComparison.Core.SnapshotIR

namespace IRComparison.SnapshotControlIR
open SnapshotIR

inductive Continuation where
  | next (code : Code) (states : List State) (locals : List Int)
  | again (captured indexed : Bool) (body next : Code) (states : List State) (locals : List Int)
      (index remaining : Nat)

inductive Config where
  | running (code : Code) (states : List State) (locals : List Int) (stack : List Continuation)
  | iterating (captured indexed : Bool) (body next : Code) (states : List State) (locals : List Int)
      (index remaining : Nat) (current : State) (stack : List Continuation)
  | returning (result : Option State) (stack : List Continuation)
  | stopped (result : Option State)

def iterationLocals (indexed : Bool) (k : Nat) (ls : List Int) :=
  if indexed then Int.ofNat k :: ls else ls

/-- Each transition performs a read/copy/update or changes control. It never
    executes an entire source body through its semantic evaluator. -/
def step (i x y : Int) : Config → Config
  | .stopped r => .stopped r
  | .returning r [] => .stopped r
  | .returning none (_::ks) => .returning none ks
  | .returning (some s) (.next b ss ls::ks) => .running b (s::ss) ls ks
  | .returning (some s) (.again cap idx b next ss ls k n::ks) => .iterating cap idx b next ss ls k n s ks
  | .iterating _ _ _ next ss ls _ 0 s ks => .running next (s::ss) ls ks
  | .iterating cap idx b next ss ls k (n+1) s ks =>
    .running b (s :: if cap then ss else []) (iterationLocals idx k ls) (.again cap idx b next ss ls (k+1) n::ks)
  | .running (.yield v) ss _ ks => .returning ss[v]? ks
  | .running (.capture v e next) ss ls ks =>
    match ss[v]? >>= fun s => e.eval i x y s ls with
    | none => .returning none ks
    | some a => .running next ss (a::ls) ks
  | .running (.copy v next) ss ls ks =>
    match ss[v]? with
    | none => .returning none ks
    | some s => .running next (s::ss) ls ks
  | .running (.assign r e next) (s::ss) ls ks =>
    match e.eval i x y s ls with
    | none => .returning none ks
    | some a => .running next (s.set r a::ss) ls ks
  | .running (.assign ..) [] _ ks => .returning none ks
  | .running (.store a j e next) (s::ss) ls ks =>
    match (do s.write a (← j.eval i x y s ls) (← e.eval i x y s ls)) with
    | none => .returning none ks
    | some t => .running next (t::ss) ls ks
  | .running (.store ..) [] _ ks => .returning none ks
  | .running (.branch v e a b) ss ls ks =>
    match ss[v]? >>= fun s => e.eval i x y s ls with
    | none => .returning none ks
    | some c => .running (if c != 0 then a else b) ss ls ks
  | .running (.bind b next) ss ls ks => .running b ss ls (.next next ss ls::ks)
  | .running (.call v b next) ss ls ks =>
    match ss[v]? with
    | none => .returning none ks
    | some s => .running b [s] ls (.next next ss ls::ks)
  | .running (.repeat v n b next) ss ls ks =>
    match ss[v]? with
    | none => .returning none ks
    | some s => .iterating false false b next ss ls 0 n s ks
  | .running (.forRange v e b next) ss ls ks =>
    match ss[v]? with
    | none => .returning none ks
    | some s => match e.eval i x y s ls with
      | none => .returning none ks
      | some n => .iterating false true b next ss ls 0 n.toNat s ks
  | .running (.forRangeCaptured v e b next) ss ls ks =>
    match ss[v]? with
    | none => .returning none ks
    | some s => match e.eval i x y s ls with
      | none => .returning none ks
      | some n => .iterating true true b next ss ls 0 n.toNat s ks

inductive Reaches (i x y : Int) : Config → Config → Prop where
  | refl (c) : Reaches i x y c c
  | next {a b} : Reaches i x y (step i x y a) b → Reaches i x y a b

theorem Reaches.trans (h : Reaches i x y a b) (g : Reaches i x y b c) : Reaches i x y a c := by
  induction h with
  | refl => exact g
  | next _ ih => exact .next (ih g)

def Correct (code : Code) (i x y : Int) : Prop := ∀ ss ls ks,
  Reaches i x y (.running code ss ls ks) (.returning (code.eval i x y ss ls) ks)

theorem iterate_correct (b next : Code) (hb : Correct b i x y) (hn : Correct next i x y)
    (captured indexed : Bool) (n k : Nat) (s : State) (ss : List State) (ls : List Int) (ks : List Continuation) :
    Reaches i x y (.iterating captured indexed b next ss ls k n s ks)
      (.returning (do
        let t ← (List.range' k n).foldlM (fun t j => b.eval i x y (t :: if captured then ss else []) (iterationLocals indexed j ls)) s
        next.eval i x y (t::ss) ls) ks) := by
  induction n generalizing k s with
  | zero => exact .next (hn _ _ _)
  | succ n ih =>
    apply Reaches.next
    apply (hb (s :: if captured then ss else []) (iterationLocals indexed k ls) (.again captured indexed b next ss ls (k+1) n::ks)).trans
    simp only [List.range',List.foldlM_cons]
    cases h : b.eval i x y (s :: if captured then ss else []) (iterationLocals indexed k ls) <;> simp only [h,bind,Option.bind]
    · exact .next (.refl _)
    · exact .next (ih (k+1) _)

theorem lower_correct (code : Code) (i x y : Int) : Correct code i x y := by
  induction code with
  | yield v => intro ss ls ks; exact .next (.refl _)
  | capture v e b ih =>
    intro ss ls ks
    apply Reaches.next
    cases hs : ss[v]? <;> simp [step,Code.eval,hs]
    · exact .refl _
    · cases he : e.eval i x y _ ls <;> simp [he]
      · exact .refl _
      · exact ih _ _ _
  | copy v b ih =>
    intro ss ls ks
    apply Reaches.next
    cases hs : ss[v]? <;> simp [step,Code.eval,hs]
    · exact .refl _
    · exact ih _ _ _
  | assign r e b ih =>
    intro ss ls ks
    apply Reaches.next
    cases ss with
    | nil => exact .refl _
    | cons s ss =>
      cases he : e.eval i x y s ls <;> simp [step,Code.eval,he]
      · exact .refl _
      · exact ih _ _ _
  | store a j e b ih =>
    intro ss ls ks
    apply Reaches.next
    cases ss with
    | nil => exact .refl _
    | cons s ss =>
      cases hj : j.eval i x y s ls <;> simp [step,Code.eval,hj]
      · exact .refl _
      · cases he : e.eval i x y s ls <;> simp [he]
        · exact .refl _
        · cases hw : s.write a _ _ <;> simp [hw]
          · exact .refl _
          · exact ih _ _ _
  | branch v e a b iha ihb =>
    intro ss ls ks
    apply Reaches.next
    cases hs : ss[v]? <;> simp [step,Code.eval,hs]
    · exact .refl _
    · cases he : e.eval i x y _ ls <;> simp [he]
      · exact .refl _
      · split
        · exact ihb _ _ _
        · exact iha _ _ _
  | bind b next ihb ihn =>
    intro ss ls ks
    apply Reaches.next
    apply (ihb ss ls (.next next ss ls::ks)).trans
    cases hb : b.eval i x y ss ls <;> simp [Code.eval,hb]
    · exact .next (.refl _)
    · exact .next (ihn _ _ _)
  | call v b next ihb ihn =>
    intro ss ls ks
    apply Reaches.next
    cases hs : ss[v]? <;> simp [step,Code.eval,hs]
    · exact .refl _
    · apply (ihb [_] ls (.next next ss ls::ks)).trans
      cases hb : b.eval i x y [_] ls <;> simp [hb]
      · exact .next (.refl _)
      · exact .next (ihn _ _ _)
  | «repeat» v n b next ihb ihn =>
    intro ss ls ks
    apply Reaches.next
    cases hs : ss[v]? <;> simp [step,Code.eval,hs]
    · exact .refl _
    · simpa only [iterationLocals, Bool.false_eq_true, ↓reduceIte,List.range_eq_range'] using
        iterate_correct b next ihb ihn false false n 0 _ ss ls ks
  | forRange v e b next ihb ihn =>
    intro ss ls ks
    apply Reaches.next
    cases hs : ss[v]? <;> simp [step,Code.eval,hs]
    · exact .refl _
    · cases he : e.eval i x y _ ls <;> simp [he]
      · exact .refl _
      · simpa only [iterationLocals,↓reduceIte,List.range_eq_range'] using
          iterate_correct b next ihb ihn false true _ 0 _ ss ls ks
  | forRangeCaptured v e b next ihb ihn =>
    intro ss ls ks
    apply Reaches.next
    cases hs : ss[v]? <;> simp [step,Code.eval,hs]
    · exact .refl _
    · cases he : e.eval i x y _ ls <;> simp [he]
      · exact .refl _
      · simpa only [iterationLocals,↓reduceIte,List.range_eq_range'] using
          iterate_correct b next ihb ihn true true _ 0 _ ss ls ks

def run (i x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run i x y n (step i x y c)

theorem Reaches.finite (h : Reaches i x y a b) : ∃ n, run i x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem lower_finishes (code : Code) (i x y : Int) (ss : List State) (ls : List Int) :
    ∃ n, run i x y n (.running code ss ls []) = .stopped (code.eval i x y ss ls) := by
  exact (Reaches.trans (lower_correct code i x y ss ls []) (.next (.refl _))).finite

theorem functional_finishes (body : Functional.Term) (i x y : Int) (ss : List State) (ls : List Int) :
    ∃ n, run i x y n (.running (SnapshotIR.lower body) ss ls []) = .stopped (body.eval i x y ss ls) := by
  simpa only [SnapshotIR.lower_correct] using lower_finishes (SnapshotIR.lower body) i x y ss ls

end IRComparison.SnapshotControlIR
