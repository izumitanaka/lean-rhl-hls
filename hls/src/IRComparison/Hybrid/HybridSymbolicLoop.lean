import IRComparison.Memory.SymbolicWindowSchedule
import IRComparison.Hybrid.HybridSymbolicBody

namespace IRComparison.HybridSymbolicLoop
open WindowSchedule AffineAddress SymbolicWindowExpr SymbolicWindowSchedule HybridIR

/-- Executable counted loop: one body, one initial prelude, one refill prelude.
    Neither construction nor code size enumerates the source iterations. -/
structure Code where
  start : Int
  stride : Int
  count : Nat
  initial : List SymbolicWindowSchedule.Load
  refill : List SymbolicWindowSchedule.Load
  body : MemoryCmd

def index (start stride : Int) (k : Nat) := start+(k:Int)*stride

theorem index_next : index start stride (k+1) = index start stride k + stride := by
  simp [index,Int.add_mul]; omega

def Code.loop (c : Code) (input : Input) (x y : Int) : Nat → Nat → List Int → State → Option State
  | 0,_,_,s => some s
  | n+1,k,values,s => do
    let t ← c.body.eval (index c.start c.stride k) x y s values
    match n with
    | 0 => some t
    | m+1 => do
      let next ← SymbolicWindowSchedule.execute input (index c.start c.stride (k+1)) values c.refill
      c.loop input x y (m+1) (k+1) next t

def Code.eval (c : Code) (input : Input) (x y : Int) (s : State) : Option State :=
  match c.count with
  | 0 => some s
  | n+1 => do
    let initial ← SymbolicWindowSchedule.execute input c.start [] c.initial
    c.loop input x y (n+1) 0 initial s

structure Plan (size array : Nat) (source : MemoryCmd) (start stride : Int) (count : Nat) where
  coefficient : Int
  offsets : List Int
  buffered : Bool
  body : HybridSymbolicBody.Compiled array 0 coefficient offsets source
  safe : checkGuards (body.guards++coverageGuards size coefficient offsets) start stride count = true

def Plan.code (p : Plan size array source start stride count) : Code :=
  ⟨start,stride,count,initial p.coefficient p.offsets,
    refill p.coefficient (p.coefficient*stride) p.offsets p.offsets,p.body.code⟩

theorem Plan.valid (p : Plan size array source start stride count) (hk : k < count) :
    Valid p.body.guards (index start stride k) ∧
    ∀ j ∈ keys p.coefficient p.offsets (index start stride k), 0 ≤ j ∧ j < (size:Int) := by
  obtain ⟨body,bounds⟩ := valid_append.mp (checkGuards_sound p.safe hk)
  exact ⟨body,coverage_sound bounds⟩

/-- Logical state relation: the target's saved values correspond to the
source array at the current iteration. No new runtime state is introduced. -/
def Plan.Held (p : Plan size array source start stride count) (data : Array Int)
    (k : Nat) (s : State) (t : List Int × State) : Prop :=
  s = t.2 ∧ s.arrays array = data ∧
    Matches (arrayInput data) (keys p.coefficient p.offsets (index start stride k)) t.1

def Plan.bodyStep (p : Plan size array source start stride count) (x y : Int)
    (k : Nat) (t : List Int × State) : Option (List Int × State) :=
  (p.code.body.eval (index start stride k) x y t.2 t.1).map (fun s => (t.1,s))

def Plan.refillStep (p : Plan size array source start stride count) (data : Array Int)
    (k : Nat) (t : List Int × State) : Option (List Int × State) :=
  (SymbolicWindowSchedule.execute (arrayInput data) (index start stride (k+1)) t.1
    p.code.refill).map (fun values => (values,t.2))

/-- Tr-ReadMem lifted through the body, preserving the read-only array and
all held values until the subsequent refill insertion. -/
theorem Plan.body_rule (p : Plan size array source start stride count) (hk : k < count) :
    Relational.Translation (p.Held data k)
      (fun s => source.eval (index start stride k) x y s [])
      (p.bodyStep x y k) (p.Held data k) := by
  intro s t h
  obtain ⟨same,frozen,held⟩ := h
  subst s
  have eq := p.body.correct (index start stride k) (p.valid hk).1 data t.1 [] t.2 x y frozen held rfl
  simp only [List.nil_append] at eq
  unfold Plan.bodyStep
  change Option.Rel _ _ ((p.body.code.eval _ _ _ _ _).map _)
  rw [eq]
  change Option.Rel (p.Held data k) (source.eval (index start stride k) x y t.2 [])
    ((source.eval (index start stride k) x y t.2 []).map (fun s => (t.1,s)))
  cases hs : source.eval (index start stride k) x y t.2 [] with
  | none => exact .none
  | some out => exact .some ⟨rfl,(p.body.frame _ _ _ _ _ _ hs).trans frozen,held⟩

/-- Tr-InsMemBuf / Tr-InsMove: refill succeeds and establishes the next
iteration's relation. It is inserted only when another iteration exists. -/
theorem Plan.refill_rule (p : Plan size array source start stride count)
    (sized : data.size = size) (hk : k+1 < count) :
    Relational.Insertion (p.Held data k) (p.refillStep data k) (p.Held data (k+1)) := by
  intro s t h
  have coverage : WindowCoverage.Covered (arrayInput data) size := sized ▸ WindowCoverage.array_covered data
  obtain ⟨values,hvalues⟩ := WindowCoverage.emit_exists coverage (p.valid hk).2
  have reload : SymbolicWindowSchedule.execute (arrayInput data) (index start stride (k+1)) t.1
      p.code.refill = some values := by
    change SymbolicWindowSchedule.execute _ _ _ (refill _ _ _ _) = _
    rw [index_next,refill_correct h.2.2]
    simpa only [index_next] using hvalues
  unfold Plan.refillStep
  rw [reload]
  exact .some ⟨h.1,h.2.1,emit_matches hvalues⟩

private theorem source_iterations {source : MemoryCmd} {start stride x y : Int} {s : State} (n k : Nat) :
    Relational.iterate (fun k => source.eval (index start stride k) x y) n k s =
      Source.iterate (fun i => source.eval i x y) stride n (index start stride k) s := by
  induction n generalizing k s with
  | zero => rfl
  | succ n ih =>
    simp only [Relational.iterate,Source.iterate]
    cases source.eval (index start stride k) x y s with
    | none => rfl
    | some t => simpa only [Option.bind_some,index_next] using ih (k+1) (s:=t)

/-- Tr-For derived from body translation and target-only refill insertion.
The original loop evaluator is supplied to the shared rule unchanged. -/
theorem Plan.loop_rule (p : Plan size array source start stride count)
    (sized : data.size = size) (n k : Nat) (bound : k+n < count) :
    Relational.Translation (p.Held data k)
      (fun s => Source.iterate (fun i => source.eval i x y) stride (n+1) (index start stride k) s)
      (fun t => p.code.loop (arrayInput data) x y (n+1) k t.1 t.2) Eq := by
  have h := Relational.for_with_refill_rule
    (fun k hk => p.body_rule (x:=x) (y:=y) (data:=data) (k:=k) hk)
    (fun k hk => p.refill_rule (k:=k) sized hk)
    (fun _ s t ht => Option.Rel.some ht.1)
    (run:=fun n k t => p.code.loop (arrayInput data) x y n k t.1 t.2)
    (finish:=fun t => some t.2) (R:=Eq) (fun n k t => by
      dsimp only
      rw [Code.loop]
      dsimp only [Plan.bodyStep,Plan.refillStep,Plan.code]
      cases p.body.code.eval (index start stride k) x y t.2 t.1 with
      | none => rfl
      | some out => cases n <;> simp [Option.bind_map,Function.comp_def]) n k bound
  intro s t ht
  have result := h s t ht
  simpa only [source_iterations] using result

theorem Plan.loop_correct (p : Plan size array source start stride count) (remaining k : Nat)
    (range : k+remaining ≤ count) (data : Array Int) (sized : data.size = size) (s : State)
    (frozen : s.arrays array = data) (held : Matches (arrayInput data) (keys p.coefficient p.offsets (index start stride k)) values) :
    p.code.loop (arrayInput data) x y remaining k values s =
      Source.iterate (fun i => source.eval i x y) stride remaining (index start stride k) s := by
  cases remaining with
  | zero => rfl
  | succ n =>
    have h := p.loop_rule (x:=x) (y:=y) sized n k (by omega) s (values,s) ⟨rfl,frozen,held⟩
    exact (Relational.result_eq h).symm

/-- Initial memory loads are an insertion, with their success proved from
coverage. A zero-trip loop bypasses this rule entirely. -/
theorem Plan.initial_rule (p : Plan size array source start stride count)
    (sized : data.size = size) (nonempty : 0 < count) :
    Relational.Insertion (fun s t => s = t ∧ s.arrays array = data)
      (fun t => (SymbolicWindowSchedule.execute (arrayInput data) start [] p.code.initial).map
        (fun values => (values,t))) (p.Held data 0) := by
  intro s t h
  have coverage : WindowCoverage.Covered (arrayInput data) size := sized ▸ WindowCoverage.array_covered data
  obtain ⟨values,hvalues⟩ := WindowCoverage.emit_exists coverage (p.valid nonempty).2
  have load : SymbolicWindowSchedule.execute (arrayInput data) start [] p.code.initial = some values := by
    rw [show p.code.initial = initial p.coefficient p.offsets from rfl,initial_correct]
    simpa only [index,Int.natCast_zero,Int.zero_mul,Int.add_zero] using hvalues
  rw [load]
  exact .some ⟨h.1,h.2,emit_matches hvalues⟩

theorem Plan.correct (p : Plan size array source start stride count) (s : State)
    (sized : (s.arrays array).size = size) :
    p.code.eval (arrayInput (s.arrays array)) x y s =
      Source.iterate (fun i => source.eval i x y) stride count start s := by
  cases count with
  | zero => rfl
  | succ n =>
    have h := Relational.insertLeft (p.initial_rule sized (by omega))
      (p.loop_rule (x:=x) (y:=y) sized n 0 (by omega)) s s ⟨rfl,rfl⟩
    simp only [index,Int.natCast_zero,Int.zero_mul,Int.add_zero] at h
    simpa only [Code.eval,Plan.code,Option.bind_map] using (Relational.result_eq h).symm

/-- Overlap of actual accesses, independent of trip-count enumeration. -/
def reuse (offsets : List Int) (delta : Int) (count : Nat) : Bool :=
  offsets.eraseDups.length != offsets.length ||
  (count > 1 && offsets.any (fun a => offsets.any fun b =>
    if delta = 0 then a == b else (a-b)%delta == 0 && 0 < (a-b)/delta && (a-b)/delta < (count:Int)))

def compile (size array : Nat) (source : MemoryCmd) (start stride : Int) (count : Nat) :
    Option (Plan size array source start stride count) := do
  let accessed ← HybridSymbolicBody.accesses array source
  let first ← accessed.head?
  let offsets := accessed.map Linear.offset
  let buffered := reuse offsets (first.coefficient*stride) count
  let window ← (if buffered then (PaperCore.WindowAnalysis.bounds offsets).map
      (fun (low,high) => WindowSchedule.interval (first.coefficient*stride < 0) low high)
    else some offsets)
  let body ← HybridSymbolicBody.compile array 0 first.coefficient window source
  if safe : checkGuards (body.guards++coverageGuards size first.coefficient window) start stride count = true then
    return ⟨first.coefficient,window,buffered,body,safe⟩
  else none

def direct (body : MemoryCmd) (start stride : Int) (count : Nat) : Code :=
  ⟨start,stride,count,[],[],body⟩

theorem direct_loop_correct (body : MemoryCmd) (n k : Nat) (s : State) :
    (direct body start stride count).loop input x y n k [] s =
      Source.iterate (fun i => body.eval i x y) stride n (index start stride k) s := by
  induction n generalizing k s with
  | zero => rfl
  | succ n ih =>
    rw [Code.loop,Source.iterate]
    dsimp only [direct]
    cases hb : body.eval (index start stride k) x y s [] with
    | none => rfl
    | some t =>
      cases n with
      | zero => rfl
      | succ m => simpa only [bind,Option.bind,SymbolicWindowSchedule.execute,index_next,direct] using ih (k+1) t

theorem direct_correct (body : MemoryCmd) (s : State) :
    (direct body start stride count).eval input x y s =
      Source.iterate (fun i => body.eval i x y) stride count start s := by
  cases count with
  | zero => rfl
  | succ n =>
    simpa only [Code.eval,direct,SymbolicWindowSchedule.execute,bind,Option.bind,index,Int.natCast_zero,Int.zero_mul,Int.add_zero] using
      direct_loop_correct (input:=input) (x:=x) (y:=y) (count:=n+1) (start:=start) (stride:=stride) body (n+1) 0 s

inductive Selected (size array : Nat) (source : MemoryCmd) (start stride : Int) (count : Nat) where
  | original
  | optimized (plan : Plan size array source start stride count)

def select (size array : Nat) (source : MemoryCmd) (start stride : Int) (count : Nat) :
    Selected size array source start stride count :=
  match compile size array source start stride count with
  | none => .original
  | some p => .optimized p

def Selected.code : Selected size array source start stride count → Code
  | .original => direct source start stride count
  | .optimized p => p.code

theorem Selected.correct (p : Selected size array source start stride count) (s : State)
    (sized : (s.arrays array).size = size) :
    p.code.eval (arrayInput (s.arrays array)) x y s =
      Source.iterate (fun i => source.eval i x y) stride count start s := by
  cases p with
  | original => exact direct_correct source s
  | optimized p => exact p.correct s sized

end IRComparison.HybridSymbolicLoop
