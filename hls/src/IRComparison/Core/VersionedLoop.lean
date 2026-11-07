import IRComparison.Memory.SymbolicWindowSchedule
import IRComparison.Core.VersionedWindow

namespace IRComparison.VersionedLoop
open WindowSchedule AffineAddress SymbolicWindowExpr SymbolicWindowSchedule HybridIR

/-- Executable counted loop: one body, one initial prelude, one refill prelude.
    Neither construction nor code size enumerates the source iterations. -/
structure Code where
  start : Int
  stride : Int
  count : Nat
  initial : List SymbolicWindowSchedule.Load
  refill : List SymbolicWindowSchedule.Load
  body : VersionedWindow.Body

def index (start stride : Int) (k : Nat) := start+(k:Int)*stride

theorem index_next : index start stride (k+1) = index start stride k + stride := by
  simp [index,Int.add_mul]; omega

def Code.loop (c : Code) (input : Input) (x y : Int) : Nat → Nat → List Int → State → Option State
  | 0,_,_,s => some s
  | n+1,k,values,s => do
    let t ← VersionedWindow.run c.body (index c.start c.stride k) x y s values
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

structure Plan (size array : Nat) (source : VersionedWindow.Body) (start stride : Int) (count : Nat) where
  coefficient : Int
  offsets : List Int
  buffered : Bool
  body : VersionedWindow.Compiled array 0 coefficient offsets source
  safe : checkGuards (body.guards++coverageGuards size coefficient offsets) start stride count = true

def Plan.code (p : Plan size array source start stride count) : Code :=
  ⟨start,stride,count,initial p.coefficient p.offsets,
    refill p.coefficient (p.coefficient*stride) p.offsets p.offsets,p.body.code⟩

theorem Plan.valid (p : Plan size array source start stride count) (hk : k < count) :
    Valid p.body.guards (index start stride k) ∧
    ∀ j ∈ keys p.coefficient p.offsets (index start stride k), 0 ≤ j ∧ j < (size:Int) := by
  obtain ⟨body,bounds⟩ := valid_append.mp (checkGuards_sound p.safe hk)
  exact ⟨body,coverage_sound bounds⟩

theorem Plan.loop_correct (p : Plan size array source start stride count) (remaining k : Nat)
    (range : k+remaining ≤ count) (data : Array Int) (sized : data.size = size) (s : State)
    (frozen : s.arrays array = data) (held : Matches (arrayInput data) (keys p.coefficient p.offsets (index start stride k)) values) :
    p.code.loop (arrayInput data) x y remaining k values s =
      Source.iterate (fun i => VersionedWindow.run source i x y) stride remaining (index start stride k) s := by
  induction remaining generalizing k s values with
  | zero => rfl
  | succ n ih =>
    have good := p.valid (k:=k) (by omega)
    have bodyEq := p.body.correct (index start stride k) good.1 data values [] s x y frozen held rfl
    rw [Code.loop,Source.iterate]
    dsimp only [Plan.code]
    simp only [List.nil_append] at bodyEq
    rw [bodyEq]
    cases hb : VersionedWindow.run source (index start stride k) x y s [] with
    | none => rfl
    | some t =>
      have frozenNext := (p.body.frame _ _ _ _ _ _ hb).trans frozen
      cases n with
      | zero => rfl
      | succ m =>
        have goodNext := p.valid (k:=k+1) (by omega)
        have coverage : WindowCoverage.Covered (arrayInput data) size := sized ▸ WindowCoverage.array_covered data
        obtain ⟨vs,hvs⟩ := WindowCoverage.emit_exists coverage goodNext.2
        have reload : SymbolicWindowSchedule.execute (arrayInput data) (index start stride (k+1)) values
            (refill p.coefficient (p.coefficient*stride) p.offsets p.offsets) = some vs := by
          rw [index_next,refill_correct held]
          simpa only [index_next] using hvs
        simp only [bind,Option.bind,reload]
        simpa only [Plan.code,index_next] using ih (k+1) (by omega) t frozenNext (emit_matches hvs)

theorem Plan.correct (p : Plan size array source start stride count) (s : State)
    (sized : (s.arrays array).size = size) :
    p.code.eval (arrayInput (s.arrays array)) x y s =
      Source.iterate (fun i => VersionedWindow.run source i x y) stride count start s := by
  cases count with
  | zero => simp [Code.eval,Plan.code,Source.iterate]
  | succ n =>
    have good := p.valid (k:=0) (by omega)
    have coverage : WindowCoverage.Covered (arrayInput (s.arrays array)) size := sized ▸ WindowCoverage.array_covered _
    obtain ⟨vs,hvs⟩ := WindowCoverage.emit_exists coverage good.2
    simp only [index,Int.natCast_zero,Int.zero_mul,Int.add_zero] at hvs
    simp only [Code.eval,Plan.code,initial_correct,hvs,bind,Option.bind]
    simpa only [Plan.code,index,Int.natCast_zero,Int.zero_mul,Int.add_zero] using
      p.loop_correct (x:=x) (y:=y) (n+1) 0 (by omega) _ sized s rfl (by simpa [index] using emit_matches hvs)

/-- Overlap of actual accesses, independent of trip-count enumeration. -/
def reuse (offsets : List Int) (delta : Int) (count : Nat) : Bool :=
  offsets.eraseDups.length != offsets.length ||
  (count > 1 && offsets.any (fun a => offsets.any fun b =>
    if delta = 0 then a == b else (a-b)%delta == 0 && 0 < (a-b)/delta && (a-b)/delta < (count:Int)))

def compile (size array : Nat) (source : VersionedWindow.Body) (start stride : Int) (count : Nat) :
    Option (Plan size array source start stride count) := do
  let accessed ← VersionedWindow.accesses array source
  let first ← accessed.head?
  let offsets := accessed.map Linear.offset
  let buffered := reuse offsets (first.coefficient*stride) count
  let window ← (if buffered then (PaperCore.WindowAnalysis.bounds offsets).map
      (fun (low,high) => WindowSchedule.interval (first.coefficient*stride < 0) low high)
    else some offsets)
  let body ← VersionedWindow.compile array 0 first.coefficient window source
  if safe : checkGuards (body.guards++coverageGuards size first.coefficient window) start stride count = true then
    return ⟨first.coefficient,window,buffered,body,safe⟩
  else none

def direct (body : VersionedWindow.Body) (start stride : Int) (count : Nat) : Code :=
  ⟨start,stride,count,[],[],body⟩

theorem direct_loop_correct (body : VersionedWindow.Body) (n k : Nat) (s : State) :
    (direct body start stride count).loop input x y n k [] s =
      Source.iterate (fun i => VersionedWindow.run body i x y) stride n (index start stride k) s := by
  induction n generalizing k s with
  | zero => rfl
  | succ n ih =>
    rw [Code.loop,Source.iterate]
    dsimp only [direct]
    cases hb : VersionedWindow.run body (index start stride k) x y s [] with
    | none => rfl
    | some t =>
      cases n with
      | zero => rfl
      | succ m => simpa only [bind,Option.bind,SymbolicWindowSchedule.execute,index_next,direct] using ih (k+1) t

theorem direct_correct (body : VersionedWindow.Body) (s : State) :
    (direct body start stride count).eval input x y s =
      Source.iterate (fun i => VersionedWindow.run body i x y) stride count start s := by
  cases count with
  | zero => rfl
  | succ n =>
    simpa only [Code.eval,direct,SymbolicWindowSchedule.execute,bind,Option.bind,index,Int.natCast_zero,Int.zero_mul,Int.add_zero] using
      direct_loop_correct (input:=input) (x:=x) (y:=y) (count:=n+1) (start:=start) (stride:=stride) body (n+1) 0 s

inductive Selected (size array : Nat) (source : VersionedWindow.Body) (start stride : Int) (count : Nat) where
  | original
  | optimized (plan : Plan size array source start stride count)

def select (size array : Nat) (source : VersionedWindow.Body) (start stride : Int) (count : Nat) :
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
      Source.iterate (fun i => VersionedWindow.run source i x y) stride count start s := by
  cases p with
  | original => exact direct_correct source s
  | optimized p => exact p.correct s sized

end IRComparison.VersionedLoop
