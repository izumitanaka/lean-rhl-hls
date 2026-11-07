import PaperCore.WindowTrim
import PaperCore.OrientedWindow
import PaperCore.MemoryCoverage

namespace PaperCore.MemoryWindowSchedule

/-- Proof-level sequences of existing commands; no skip is added to Source. -/
inductive Runs (meaning : Op → Int → Int → Int) : List (Source Op) → State Heap → State Heap → Prop where
  | nil : Runs meaning [] state state
  | cons : SourceExec meaning command initial middle → Runs meaning commands middle final →
      Runs meaning (command :: commands) initial final

def prepend (commands : List (Source Op)) (body : Source Op) : Source Op := commands.foldr Stmt.seq body

theorem prepend_exec : SourceExec meaning (prepend commands body) initial final ↔
    ∃ middle, Runs meaning commands initial middle ∧ SourceExec meaning body middle final := by
  induction commands generalizing initial with
  | nil =>
    constructor
    · intro run; exact ⟨initial,.nil,run⟩
    · rintro ⟨middle,steps,run⟩; cases steps; exact run
  | cons command rest ih =>
    constructor
    · intro run
      cases run with
      | seq first remaining =>
        obtain ⟨middle,steps,bodyRun⟩ := ih.mp remaining
        exact ⟨middle,.cons first steps,bodyRun⟩
    · rintro ⟨middle,steps,bodyRun⟩
      cases steps with
      | cons first rest => exact .seq first (ih.mpr ⟨middle,rest,bodyRun⟩)

/-- Cursor and increment are fresh scalar variables. Reads remain memory reads. -/
def loads (add : Op) (array : Array) (cursor increment : Var) : List Var → List (Source Op)
  | [] => []
  | buffer :: rest => .action (.read buffer array (.var cursor)) ::
      .assign cursor (.bin add cursor increment) :: loads add array cursor increment rest

def copies : List Var → List (Source Op)
  | [] | [_] => []
  | a :: b :: rest => .assign a (.var b) :: copies (b :: rest)

def shifts : Nat → List Var → List (Source Op)
  | 0,_ => []
  | n+1,buffers => copies buffers ++ shifts n buffers.dropLast

theorem loads_frame (run : Runs meaning (loads add array cursor increment buffers) initial final)
    (notBuffer : x ∉ buffers) (notCursor : x ≠ cursor) :
    final.regs.lookup x = initial.regs.lookup x := by
  induction buffers generalizing initial with
  | nil => cases run; rfl
  | cons buffer rest ih =>
    cases run with
    | cons first remaining =>
      cases first with
      | action step =>
        cases step with
        | read address cell =>
          cases remaining with
          | cons advance tail =>
            cases advance with
            | assign value =>
              rw [ih tail (fun h => notBuffer (List.mem_cons_of_mem _ h))]
              simp only [State.setReg,lookup_put_other _ _ _ _ notCursor,
                lookup_put_other _ _ _ _ (show x ≠ buffer from fun h => notBuffer (by simp [h]))]

theorem loads_memory (run : Runs meaning (loads add array cursor increment buffers) initial final) :
    final.memory = initial.memory := by
  induction buffers generalizing initial with
  | nil => cases run; rfl
  | cons buffer rest ih =>
    cases run with
    | cons first remaining =>
      cases first with
      | action step =>
        cases step with
        | read address cell =>
          cases remaining with
          | cons advance tail =>
            cases advance with
            | assign value => simpa only [State.setReg] using ih tail

/-- Every cell of the contiguous range, including access gaps, must be defined. -/
theorem loads_exists (buffers : List Var)
    (addMeaning : ∀ x y, meaning add x y = x+y)
    (cursorValue : initial.regs.lookup cursor = some first)
    (incrementValue : initial.regs.lookup increment = some stride)
    (different : cursor ≠ increment)
    (cursorFresh : cursor ∉ buffers) (incrementFresh : increment ∉ buffers)
    (distinct : buffers.Nodup)
    (coverage : MemoryCoverage.Covers initial.memory array first stride buffers.length) :
    ∃ final, Runs meaning (loads add array cursor increment buffers) initial final ∧
      final.regs.lookup cursor = some (first+(buffers.length:Int)*stride) ∧
      OrientedWindow.Held stride initial.memory final.regs array first buffers := by
  induction buffers generalizing initial first with
  | nil => exact ⟨initial,.nil,by simpa using cursorValue,True.intro⟩
  | cons buffer rest ih =>
    obtain ⟨value,cell⟩ := coverage 0 (by simp)
    simp only [Int.natCast_zero,Int.zero_mul,Int.add_zero] at cell
    have cb : cursor ≠ buffer := fun h => cursorFresh (by simp [h])
    have ib : increment ≠ buffer := fun h => incrementFresh (by simp [h])
    let loaded := initial.setReg buffer value
    let advanced := loaded.setReg cursor (first+stride)
    have cv : loaded.regs.lookup cursor = some first := by
      simpa [loaded,State.setReg,lookup_put_other _ _ _ _ cb] using cursorValue
    have iv : loaded.regs.lookup increment = some stride := by
      simpa [loaded,State.setReg,lookup_put_other _ _ _ _ ib] using incrementValue
    have advance : SourceExec meaning (.assign cursor (.bin add cursor increment)) loaded advanced :=
      .assign (by simp [Expr.eval,cv,iv,addMeaning])
    have incAfter : advanced.regs.lookup increment = some stride := by
      simpa [advanced,State.setReg,lookup_put_other _ _ _ _ different.symm] using iv
    have restCoverage : MemoryCoverage.Covers advanced.memory array (first+stride) stride rest.length := by
      intro n hn
      have point := coverage (n+1) (by simp; omega)
      simpa [advanced,loaded,State.setReg,Int.natCast_add,Int.add_mul,Int.add_assoc,
        Int.add_comm,Int.add_left_comm] using point
    obtain ⟨final,tail,endCursor,held⟩ := ih (initial := advanced) (first := first+stride)
      (lookup_put_same ..) incAfter
      (fun h => cursorFresh (List.mem_cons_of_mem _ h))
      (fun h => incrementFresh (List.mem_cons_of_mem _ h))
      (List.nodup_cons.mp distinct).2 restCoverage
    have kept : final.regs.lookup buffer = some value := by
      rw [loads_frame tail (List.nodup_cons.mp distinct).1 cb.symm]
      simp [advanced,loaded,State.setReg,lookup_put_other _ _ _ _ cb.symm]
    refine ⟨final,.cons (.action (.read cursorValue cell)) (.cons advance tail),?_,value,cell,kept,held⟩
    simpa [Int.natCast_add,Int.add_mul,Int.add_assoc,Int.add_comm,Int.add_left_comm] using endCursor

theorem Runs.append (first : Runs meaning a initial middle) (second : Runs meaning b middle final) :
    Runs meaning (a ++ b) initial final := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head (ih second)

theorem copies_frame (run : Runs meaning (copies buffers) initial final) (fresh : x ∉ buffers) :
    final.regs.lookup x = initial.regs.lookup x := by
  induction buffers generalizing initial with
  | nil => cases run; rfl
  | cons b rest ih =>
    cases rest with
    | nil => cases run; rfl
    | cons c rest =>
      cases run with
      | cons first later =>
        cases first with
        | assign value =>
          rw [ih later (fun h => fresh (List.mem_cons_of_mem _ h))]
          exact lookup_put_other _ _ _ _ (fun h => fresh (by simp [h]))

theorem copies_memory (run : Runs meaning (copies buffers) initial final) :
    final.memory = initial.memory := by
  induction buffers generalizing initial with
  | nil => cases run; rfl
  | cons b rest ih =>
    cases rest with
    | nil => cases run; rfl
    | cons c rest =>
      cases run with
      | cons first later =>
        cases first with
        | assign value => simpa only [State.setReg] using ih later

theorem copies_exists (buffers : List Var) (distinct : buffers.Nodup)
    (held : OrientedWindow.Held stride initial.memory initial.regs array first buffers) :
    ∃ final, Runs meaning (copies buffers) initial final ∧
      OrientedWindow.Held stride initial.memory final.regs array (first+stride) buffers.dropLast := by
  induction buffers generalizing initial first with
  | nil => exact ⟨initial,.nil,True.intro⟩
  | cons b rest ih =>
    cases rest with
    | nil => exact ⟨initial,.nil,True.intro⟩
    | cons c rest =>
      obtain ⟨old,oldCell,oldReg,value,cell,reg,heldRest⟩ := held
      have notTail := (List.nodup_cons.mp distinct).1
      have midHeld : OrientedWindow.Held stride (initial.setReg b value).memory
          (initial.setReg b value).regs array (first+stride) (c :: rest) :=
        OrientedWindow.Held.set_other ⟨value,cell,reg,heldRest⟩ notTail
      obtain ⟨final,later,heldOut⟩ := ih (List.nodup_cons.mp distinct).2 midHeld
      have kept : final.regs.lookup b = some value := by
        rw [copies_frame later notTail]
        exact lookup_put_same ..
      exact ⟨final,.cons (.assign reg) later,value,cell,kept,heldOut⟩

theorem shifts_exists (count : Nat) (buffers : List Var) (distinct : buffers.Nodup)
    (held : OrientedWindow.Held stride initial.memory initial.regs array first buffers) :
    ∃ final, Runs meaning (shifts count buffers) initial final ∧
      final.memory = initial.memory ∧
      OrientedWindow.Held stride initial.memory final.regs array (first+(count:Int)*stride)
        (WindowStrideShifts.trim count buffers) := by
  induction count generalizing buffers initial first with
  | zero => exact ⟨initial,.nil,rfl,by simpa [WindowStrideShifts.trim] using held⟩
  | succ n ih =>
    obtain ⟨middle,one,heldMiddle⟩ := copies_exists buffers distinct held (meaning := meaning)
    have mem := copies_memory one
    have middleHeld : OrientedWindow.Held stride middle.memory middle.regs array (first+stride) buffers.dropLast := by
      simpa only [mem] using heldMiddle
    obtain ⟨final,remaining,finalMemory,heldFinal⟩ := ih buffers.dropLast
      ((List.dropLast_sublist buffers).nodup distinct) middleHeld
    refine ⟨final,one.append remaining,finalMemory.trans mem,?_⟩
    simpa [mem,WindowStrideShifts.trim,Int.natCast_add,Int.add_mul,Int.add_assoc,
      Int.add_comm,Int.add_left_comm] using heldFinal

/-- Complete a window without overwriting its retained retained. -/
theorem refill_exists (retained refill : List Var)
    (addMeaning : ∀ x y, meaning add x y = x+y)
    (cursorValue : initial.regs.lookup cursor = some (first+(retained.length:Int)*stride))
    (incrementValue : initial.regs.lookup increment = some stride)
    (different : cursor ≠ increment)
    (cursorFresh : cursor ∉ retained ++ refill) (incrementFresh : increment ∉ retained ++ refill)
    (distinct : (retained ++ refill).Nodup)
    (held : OrientedWindow.Held stride initial.memory initial.regs array first retained)
    (coverage : MemoryCoverage.Covers initial.memory array (first+(retained.length:Int)*stride) stride refill.length) :
    ∃ final, Runs meaning (loads add array cursor increment refill) initial final ∧
      OrientedWindow.Held stride initial.memory final.regs array first (retained ++ refill) := by
  obtain ⟨final,run,_,refillHeld⟩ := loads_exists refill addMeaning cursorValue incrementValue different
    (fun h => cursorFresh (List.mem_append_right _ h))
    (fun h => incrementFresh (List.mem_append_right _ h))
    (List.nodup_append.mp distinct).2.1 coverage
  refine ⟨final,run,OrientedWindow.Held.append.mpr ⟨held.congr_regs ?_,refillHeld⟩⟩
  intro b hb
  apply loads_frame run
  · intro hr
    exact (List.nodup_append.mp distinct).2.2 b hb b hr rfl
  · intro same
    subst b
    exact cursorFresh (List.mem_append_left _ hb)

/-- Recompute the cursor from the current loop counter, so downstream affine
analysis can establish its value independently at every iteration. -/
def address (add mul : Op) (counter cursor increment : Var) (scale offset stride : Int) : List (Source Op) :=
  [.assign cursor (.num scale),.assign cursor (.bin mul cursor counter),
   .assign increment (.num offset),.assign cursor (.bin add cursor increment),
   .assign increment (.num stride)]

theorem address_exists
    (addMeaning : ∀ x y, meaning add x y = x+y)
    (mulMeaning : ∀ x y, meaning mul x y = x*y)
    (value : initial.regs.lookup counter = some k)
    (counterCursor : counter ≠ cursor) (different : cursor ≠ increment) :
    ∃ final, Runs meaning (address add mul counter cursor increment scale offset stride) initial final ∧
      final.regs.lookup cursor = some (scale*k+offset) ∧
      final.regs.lookup increment = some stride ∧ final.memory = initial.memory := by
  let s1 := initial.setReg cursor scale
  let s2 := s1.setReg cursor (scale*k)
  let s3 := s2.setReg increment offset
  let s4 := s3.setReg cursor (scale*k+offset)
  let s5 := s4.setReg increment stride
  have v1 : s1.regs.lookup cursor = some scale := lookup_put_same ..
  have v2 : s1.regs.lookup counter = some k := by
    simpa [s1,State.setReg,lookup_put_other _ _ _ _ counterCursor] using value
  have v3 : s3.regs.lookup cursor = some (scale*k) := by
    simp [s3,s2,State.setReg,lookup_put_other _ _ _ _ different]
  have v4 : s3.regs.lookup increment = some offset := lookup_put_same ..
  refine ⟨s5,.cons (.assign rfl) (.cons (.assign ?_) (.cons (.assign rfl)
    (.cons (.assign ?_) (.cons (.assign rfl) .nil)))),?_,lookup_put_same ..,rfl⟩
  · change (Expr.bin mul cursor counter).eval meaning s1.regs = _
    simp [Expr.eval,v1,v2,mulMeaning]
  · change (Expr.bin add cursor increment).eval meaning s3.regs = _
    simp [Expr.eval,v3,v4,addMeaning]
  · simp [s5,s4,State.setReg,lookup_put_other _ _ _ _ different]

/-- Append existing source commands after a body without introducing skip. -/
def appendTo (body : Source Op) (commands : List (Source Op)) : Source Op :=
  match commands with
  | [] => body
  | command :: rest => appendTo (.seq body command) rest

theorem appendTo_exec : SourceExec meaning (appendTo body commands) initial final ↔
    ∃ middle, SourceExec meaning body initial middle ∧ Runs meaning commands middle final := by
  induction commands generalizing body initial with
  | nil =>
    constructor
    · intro run; exact ⟨final,run,.nil⟩
    · rintro ⟨middle,run,rest⟩; cases rest; exact run
  | cons command rest ih =>
    constructor
    · intro run
      obtain ⟨middle,combined,remaining⟩ := ih.mp run
      cases combined with
      | seq first next => exact ⟨_,first,.cons next remaining⟩
    · rintro ⟨middle,first,remaining⟩
      cases remaining with
      | cons next rest => exact ih.mpr ⟨_,.seq first next,rest⟩

def Flat : Source Op → Prop
  | .action _ | .assign _ _ => True
  | _ => False

theorem flat_unique (flat : Flat command)
    (first : SourceExec meaning command initial left) (second : SourceExec meaning command initial right) :
    left = right := by
  cases command with
  | action _ => exact memoryAction_unique first second
  | assign _ _ => exact assign_unique first second
  | seq a b => cases flat
  | branch x a b => cases flat
  | loop x start stop step body => cases flat
  | kernel body => cases flat

theorem Runs.deterministic (first : Runs meaning commands initial left)
    (second : Runs meaning commands initial right) (flat : ∀ c ∈ commands, Flat c) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons otherHead otherTail =>
      have same := flat_unique (flat _ (by simp)) head otherHead
      subst_vars
      exact ih otherTail (fun c hc => flat c (List.mem_cons_of_mem _ hc))

theorem loads_flat : ∀ c ∈ loads add array cursor increment buffers, Flat c := by
  induction buffers with
  | nil => simp [loads]
  | cons b rest ih => simpa [loads,Flat] using ih

theorem copies_flat : ∀ c ∈ copies (Op := Op) buffers, Flat c := by
  induction buffers with
  | nil => simp [copies]
  | cons b rest ih =>
    cases rest with
    | nil => simp [copies]
    | cons c rest => simpa [copies,Flat] using ih

theorem shifts_flat : ∀ c ∈ shifts (Op := Op) count buffers, Flat c := by
  induction count generalizing buffers with
  | zero => simp [shifts]
  | succ n ih =>
    intro c hc
    rcases List.mem_append.mp hc with first | rest
    · exact copies_flat c first
    · exact ih c rest

theorem address_flat : ∀ c ∈ address add mul counter cursor increment scale offset stride, Flat c := by
  simp [address,Flat]

theorem Runs.append_iff : Runs meaning (a ++ b) initial final ↔
    ∃ middle, Runs meaning a initial middle ∧ Runs meaning b middle final := by
  induction a generalizing initial with
  | nil =>
    constructor
    · intro run; exact ⟨initial,.nil,run⟩
    · rintro ⟨middle,first,rest⟩; cases first; exact rest
  | cons c cs ih =>
    constructor
    · intro run
      cases run with
      | cons first remaining =>
        obtain ⟨middle,left,right⟩ := ih.mp remaining
        exact ⟨middle,.cons first left,right⟩
    · rintro ⟨middle,first,rest⟩
      cases first with
      | cons head tail => exact .cons head (ih.mpr ⟨middle,tail,rest⟩)

theorem shifts_frame (run : Runs meaning (shifts count buffers) initial final)
    (fresh : x ∉ buffers) : final.regs.lookup x = initial.regs.lookup x := by
  induction count generalizing buffers initial with
  | zero => cases run; rfl
  | succ n ih =>
    obtain ⟨middle,first,rest⟩ := Runs.append_iff.mp run
    exact (ih rest (fun h => fresh ((List.dropLast_sublist buffers).subset h))).trans
      (copies_frame first fresh)

theorem shifts_memory (run : Runs meaning (shifts count buffers) initial final) :
    final.memory = initial.memory := by
  induction count generalizing buffers initial with
  | zero => cases run; rfl
  | succ n ih =>
    obtain ⟨middle,first,rest⟩ := Runs.append_iff.mp run
    exact (ih rest).trans (copies_memory first)

theorem address_frame (run : Runs meaning (address add mul counter cursor increment scale offset stride) initial final)
    (notCursor : x ≠ cursor) (notIncrement : x ≠ increment) :
    final.regs.lookup x = initial.regs.lookup x ∧ final.memory = initial.memory := by
  cases run with
  | cons first rest =>
    cases first with
    | assign v1 =>
      cases rest with
      | cons second rest =>
        cases second with
        | assign v2 =>
          cases rest with
          | cons third rest =>
            cases third with
            | assign v3 =>
              cases rest with
              | cons fourth rest =>
                cases fourth with
                | assign v4 =>
                  cases rest with
                  | cons fifth rest =>
                    cases fifth with
                    | assign v5 =>
                      cases rest
                      simp only [State.setReg,lookup_put_other _ _ _ _ notCursor,
                        lookup_put_other _ _ _ _ notIncrement,and_self]

/-- Initial window addresses are compile-time constants; exposing them directly
also lets the FIFO pass analyze each preload without scalar constant propagation. -/
def literalLoads (array : Array) (first stride : Int) : List Var → List (Source Op)
  | [] => []
  | b :: rest => .action (.read b array (.num first)) :: literalLoads array (first+stride) stride rest

theorem literalLoads_frame (run : Runs meaning (literalLoads array first stride buffers) initial final)
    (fresh : x ∉ buffers) : final.regs.lookup x = initial.regs.lookup x ∧ final.memory = initial.memory := by
  induction buffers generalizing initial first with
  | nil => cases run; exact ⟨rfl,rfl⟩
  | cons b rest ih =>
    cases run with
    | cons read remaining =>
      cases read with
      | action step =>
        cases step with
        | read address cell =>
          obtain ⟨regs,mem⟩ := ih remaining (fun h => fresh (List.mem_cons_of_mem _ h))
          exact ⟨regs.trans (lookup_put_other _ _ _ _ (fun same => fresh (by simp [same]))),mem⟩

theorem literalLoads_exists (buffers : List Var) (distinct : buffers.Nodup)
    (coverage : MemoryCoverage.Covers initial.memory array first stride buffers.length) :
    ∃ final, Runs meaning (literalLoads array first stride buffers) initial final ∧
      final.memory = initial.memory ∧ OrientedWindow.Held stride final.memory final.regs array first buffers := by
  induction buffers generalizing initial first with
  | nil => exact ⟨initial,.nil,rfl,True.intro⟩
  | cons b rest ih =>
    obtain ⟨value,cell⟩ := coverage 0 (by simp)
    simp only [Int.natCast_zero,Int.zero_mul,Int.add_zero] at cell
    have restCoverage : MemoryCoverage.Covers (initial.setReg b value).memory array (first+stride) stride rest.length := by
      have tail := coverage.subrange (offset := 1) (length := rest.length) (by simp; omega)
      simpa [State.setReg] using tail
    obtain ⟨final,tail,mem,held⟩ := ih (List.nodup_cons.mp distinct).2 restCoverage
    have reg : final.regs.lookup b = some value := by
      rw [(literalLoads_frame tail (List.nodup_cons.mp distinct).1).1]
      exact lookup_put_same ..
    exact ⟨final,.cons (.action (.read rfl cell)) tail,mem,value,by simpa only [mem] using cell,reg,held⟩

theorem literalLoads_flat : ∀ c ∈ literalLoads (Op := Op) array first stride buffers, Flat c := by
  induction buffers generalizing first with
  | nil => simp [literalLoads]
  | cons b rest ih => simpa [literalLoads,Flat] using ih (first := first+stride)

#print axioms loads_exists
#print axioms shifts_exists
#print axioms refill_exists
#print axioms address_exists
#print axioms Runs.deterministic
end PaperCore.MemoryWindowSchedule
