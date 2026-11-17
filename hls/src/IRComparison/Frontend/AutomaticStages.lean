import IRComparison.Frontend.HLSGeneration
import IRComparison.Frontend.FixedLowering

/-! Extract source-ordered stages from a whole fixed-array computation.
Loops are represented by a body and range, never enumerated during extraction.
A lexical/control boundary that is not split remains an ordinary memory stage. -/
namespace IRComparison.AutomaticStages
open HybridWord CertifiedHLS

/-- Remove the selected lexical loop binder, using the stage counter instead.
The old administrative counter is zero in a whole-function entry. -/
def indexExpr (depth : Nat) : HybridWord.Expr → HybridWord.Expr
  | .index => .lit 0
  | .local n => if n < depth then .local n else if n = depth then .index else .local (n-1)
  | .add a b => .add (indexExpr depth a) (indexExpr depth b)
  | .sub a b => .sub (indexExpr depth a) (indexExpr depth b)
  | .mul a b => .mul (indexExpr depth a) (indexExpr depth b)
  | .div a b => .div (indexExpr depth a) (indexExpr depth b)
  | .read a j => .read a (indexExpr depth j)
  | .select c a b => .select (indexExpr depth c) (indexExpr depth a) (indexExpr depth b)
  | e => e

private theorem indexLocal (bound suffix : List Word) (i x y : Word) (s : HybridWord.State) (n : Nat) :
    (indexExpr bound.length (.local n)).eval i x y s (bound++suffix) =
      (bound++i::suffix)[n]? := by
  induction bound generalizing n with
  | nil => cases n <;> simp [indexExpr,HybridWord.Expr.eval]
  | cons a rest ih =>
    cases n with
    | zero => simp [indexExpr,HybridWord.Expr.eval]
    | succ n =>
      by_cases lt : n < rest.length
      · simpa [indexExpr,HybridWord.Expr.eval,lt,Nat.succ_lt_succ_iff] using ih n
      · by_cases eq : n = rest.length
        · simp [indexExpr,HybridWord.Expr.eval,lt,eq]
        · have positive : 0 < n := by omega
          cases n with
          | zero => omega
          | succ m => simpa [indexExpr,HybridWord.Expr.eval,lt,eq,Nat.succ_lt_succ_iff] using ih (m+1)

theorem indexExpr_correct (e : HybridWord.Expr) (bound suffix : List Word)
    (i x y : Word) (s : HybridWord.State) :
    (indexExpr bound.length e).eval i x y s (bound++suffix) =
      e.eval 0 x y s (bound++i::suffix) := by
  induction e with
  | «local» n => exact indexLocal bound suffix i x y s n
  | _ => simp_all [indexExpr,HybridWord.Expr.eval]

private theorem fold_congr (f g : HybridWord.State → α → Option HybridWord.State)
    (same : ∀ s a, f s a = g s a) (xs : List α) (s : HybridWord.State) :
    xs.foldlM f s = xs.foldlM g s := by
  have : f = g := funext fun s => funext fun a => same s a
  rw [this]

def indexBody (depth : Nat) : HybridWord.Cmd → HybridWord.Cmd
  | .assign r e => .assign r (indexExpr depth e)
  | .store a j e => .store a (indexExpr depth j) (indexExpr depth e)
  | .letValue e b => .letValue (indexExpr depth e) (indexBody (depth+1) b)
  | .seq a b => .seq (indexBody depth a) (indexBody depth b)
  | .branch c a b => .branch (indexExpr depth c) (indexBody depth a) (indexBody depth b)
  | .repeat n b => .repeat n (indexBody depth b)
  | .forRange e b => .forRange (indexExpr depth e) (indexBody (depth+1) b)
  | .forStatic a b d c => .forStatic a b d (indexBody (depth+1) c)
  | c => c

theorem indexBody_correct (c : HybridWord.Cmd) (bound suffix : List Word)
    (i x y : Word) (s : HybridWord.State) :
    (indexBody bound.length c).eval i x y s (bound++suffix) =
      c.eval 0 x y s (bound++i::suffix) := by
  induction c generalizing bound s with
  | skip | copy => rfl
  | assign | store => simp [indexBody,HybridWord.Cmd.eval,indexExpr_correct]
  | seq a b ha hb => simp [indexBody,HybridWord.Cmd.eval,ha,hb]
  | branch e a b ha hb => simp [indexBody,HybridWord.Cmd.eval,indexExpr_correct,ha,hb]
  | letValue e b ih =>
    simp only [indexBody,HybridWord.Cmd.eval,indexExpr_correct]
    cases e.eval 0 x y s (bound++i::suffix) with
    | none => rfl
    | some v => simpa using ih (v::bound) s
  | «repeat» n b ih =>
    exact fold_congr _ _ (fun t _ => ih bound t) _ s
  | forStatic a b d c ih =>
    exact fold_congr _ _ (fun t k => by simpa using ih (k::bound) t) _ s
  | forRange e b ih =>
    simp only [indexBody,HybridWord.Cmd.eval,indexExpr_correct]
    cases e.eval 0 x y s (bound++i::suffix) with
    | none => rfl
    | some n =>
      exact fold_congr _ _ (fun t k => by simpa using ih (BitVec.ofNat 32 k::bound) t) _ s

structure Piece where
  body : HybridWord.Cmd
  start : Int := 0
  stride : Int := 1
  count : Nat := 1

def Piece.run (p : Piece) (s : HybridWord.State) : Option HybridWord.State :=
  HybridWord.runSource (fun i x y t => p.body.eval i x y t []) 0 0 p.stride p.count p.start s

def pieces : HybridWord.Cmd → List Piece
  | .skip => []
  | .seq a b => pieces a ++ pieces b
  | .forStatic a b d c => [⟨indexBody 0 c,a,d,rangeCount a b d⟩]
  | .forRange (.lit n) c => [⟨indexBody 0 c,0,1,n.toNat⟩]
  | c => [⟨c,0,1,1⟩]

def run : List Piece → HybridWord.State → Option HybridWord.State
  | [],s => some s
  | p::ps,s => (p.run s).bind (run ps)

theorem run_append (as bs : List Piece) (s : HybridWord.State) :
    run (as++bs) s = (run as s).bind (run bs) := by
  induction as generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.cons_append,run]
    cases a.run s <;> simp_all

private theorem runSource_range (f : Word → Word → Word → HybridWord.State → Option HybridWord.State)
    (n : Nat) (start stride : Int) (s : HybridWord.State) :
    HybridWord.runSource f 0 0 stride n start s =
      (List.range n).foldlM (fun t (k : Nat) => f (BitVec.ofInt 32 (start+(k:Int)*stride)) 0 0 t) s := by
  induction n generalizing start s with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.foldlM_cons]
    simp only [HybridWord.runSource,Int.natCast_zero,Int.zero_mul,Int.add_zero]
    cases f (BitVec.ofInt 32 start) 0 0 s with
    | none => rfl
    | some t =>
      simp only [ih,List.foldlM_map]
      apply fold_congr
      intro u k
      have addr : start+stride+(k:Int)*stride = start+((k+1:Nat):Int)*stride := by
        simp [Int.natCast_add,Int.add_mul,Int.add_assoc,Int.add_comm,Int.add_left_comm]
      rw [addr]

private theorem option_right (o : Option α) : o.bind (fun x => some x) = o := by
  cases o <;> rfl

theorem pieces_correct (c : HybridWord.Cmd) (s : HybridWord.State) :
    run (pieces c) s = c.eval 0 0 0 s [] := by
  induction c generalizing s with
  | skip => rfl
  | seq a b ha hb =>
    simp only [pieces,run_append,HybridWord.Cmd.eval,ha]
    cases a.eval 0 0 0 s [] <;> simp_all
  | forStatic a b d c ih =>
    simp only [pieces,run,Piece.run,option_right,runSource_range,HybridWord.Cmd.eval,range,List.foldlM_map]
    apply fold_congr
    intro t k
    simpa using indexBody_correct c [] [] (BitVec.ofInt 32 (a+(k:Int)*d)) 0 0 t
  | forRange e c ih =>
    cases e <;> try { simp [pieces,run,Piece.run,HybridWord.runSource]; done }
    rename_i n
    simp only [pieces,run,Piece.run,option_right,runSource_range,HybridWord.Cmd.eval,HybridWord.Expr.eval,
      Int.zero_add,Int.mul_one]
    dsimp only [bind,Option.bind]
    apply fold_congr
    intro t k
    simpa using indexBody_correct c [] [] (BitVec.ofNat 32 k) 0 0 t
  | assign | store | letValue | branch | «repeat» | copy => simp [pieces,run,Piece.run,HybridWord.runSource]

theorem indexExpr_declared (e : HybridWord.Expr) (depth : Nat) :
    FixedMemory.exprDeclared ds (indexExpr depth e) = FixedMemory.exprDeclared ds e := by
  induction e <;> simp_all [indexExpr,FixedMemory.exprDeclared]
  split
  · rfl
  · split <;> rfl

theorem indexBody_declared (c : HybridWord.Cmd) (depth : Nat) :
    FixedMemory.declared ds (indexBody depth c) = FixedMemory.declared ds c := by
  induction c generalizing depth <;> simp_all [indexBody,FixedMemory.declared,indexExpr_declared]

theorem pieces_declared (c : HybridWord.Cmd) (h : FixedMemory.declared ds c = true)
    (p : Piece) (member : p ∈ pieces c) : FixedMemory.declared ds p.body = true := by
  induction c with
  | skip => simp [pieces] at member
  | seq a b ha hb =>
    simp only [pieces,List.mem_append] at member
    have both : FixedMemory.declared ds a = true ∧ FixedMemory.declared ds b = true := by
      simpa [FixedMemory.declared,Bool.and_eq_true] using h
    exact member.elim (ha both.1) (hb both.2)
  | forStatic a b d c ih =>
    simp only [pieces,List.mem_singleton] at member
    subst p
    simpa [indexBody_declared] using h
  | forRange e c ih =>
    cases e <;> simp only [pieces,List.mem_singleton] at member <;> subst p
    · simpa [indexBody_declared,FixedMemory.declared,FixedMemory.exprDeclared] using h
    all_goals exact h
  | _ =>
    simp only [pieces,List.mem_singleton] at member
    subst p
    exact h

/-- Deterministic read-only input candidate; eligibility remains the optimizer's
job. No array IDs, trip counts, or stencil shapes are hard-coded. -/
def candidate (p : Piece) (a : Nat) : Bool :=
  !(HybridEffects.writes p.body.lower).contains a &&
    match HybridSymbolicBody.accesses a p.body.lower with
    | some addresses => !addresses.isEmpty
    | none => false

def Piece.input (p : Piece) (ds : FixedMemory.Declarations) (anchor : Nat)
    (preferred : List Nat := []) : Nat :=
  match ds.toList.find? (fun d => preferred.contains d.1 && candidate p d.1) with
  | some d => d.1
  | none => match ds.toList.find? (fun d => candidate p d.1) with
    | some d => d.1
    | none => anchor

theorem Piece.input_declared (p : Piece) (ds : FixedMemory.Declarations) (anchor : Nat)
    (preferred : List Nat) :
    p.input ds anchor preferred = anchor ∨ ∃ n, (p.input ds anchor preferred,n) ∈ ds.toList := by
  unfold Piece.input
  cases priority : ds.toList.find? (fun d => preferred.contains d.1 && candidate p d.1) with
  | some d => exact Or.inr ⟨d.2,List.mem_of_find?_eq_some priority⟩
  | none =>
    cases found : ds.toList.find? (fun d => candidate p d.1) with
    | none => exact Or.inl rfl
    | some d => exact Or.inr ⟨d.2,List.mem_of_find?_eq_some found⟩

def Piece.stage (p : Piece) (ds : FixedMemory.Declarations) (anchor : Nat)
    (preferred : List Nat := []) : CertifiedHLS.Stage :=
  let a := p.input ds anchor preferred
  ⟨(fun i x y s => p.body.eval i x y s []),FixedMemory.sizes ds a,
    a,p.start,p.stride,p.count,(fun _ => [])⟩

def entry (ds : FixedMemory.Declarations) (anchor : Nat) (preferred : List Nat) :
    (ps : List Piece) → CertifiedHLS.Entry (ps.map (fun p => p.stage ds anchor preferred))
  | [] => .nil
  | p::ps => .cons ⟨p.body,by intros; rfl⟩ (entry ds anchor preferred ps)

theorem source_eq (ds : FixedMemory.Declarations) (anchor : Nat) (preferred : List Nat) (ps : List Piece)
    (s : HybridWord.State) :
    CertifiedHLS.runSource (ps.map (fun p => p.stage ds anchor preferred)) 0 0 s = run ps s := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    change (p.run s).bind _ = (p.run s).bind _
    cases p.run s <;> simp_all

theorem entry_closed {layout : Array (Nat × Nat)} {preferred : List Nat} (ps : List Piece)
    (declared : ∀ p ∈ ps, FixedMemory.declared ds p.body = true)
    (anchorLive : ∃ n, (anchor,n) ∈ layout.toList)
    (included : ∀ a n, (a,n) ∈ ds.toList → (a,n) ∈ layout.toList) :
    ∀ k ∈ (entry ds anchor preferred ps).kernels,
      (∃ n, (k.array,n) ∈ layout.toList) ∧
      k.body.lower.target.ArraysWithin (fun a => ∃ n, (a,n) ∈ layout.toList) := by
  induction ps with
  | nil => simp [entry,CertifiedHLS.Entry.kernels]
  | cons p ps ih =>
    intro k hk
    simp only [entry,CertifiedHLS.Entry.kernels,List.mem_cons] at hk
    rcases hk with rfl | rest
    · constructor
      · change ∃ n, (p.input ds anchor preferred,n) ∈ layout.toList
        rcases p.input_declared ds anchor preferred with same | ⟨n,mem⟩
        · simpa [same] using anchorLive
        · exact ⟨n,included _ _ mem⟩
      · apply (Circuit.commandArrays_closed p.body.lower.target).mpr
        intro a ha
        have all := FixedMemory.lower_declared p.body (declared p (by simp))
        have found := List.all_eq_true.mp all a ha
        cases h : FixedMemory.lookup ds a with
        | none => simp [h] at found
        | some n => exact ⟨n,included _ _ (FixedMemory.lookup_mem h)⟩
    · exact ih (fun p hp => declared p (by simp [hp])) k rest

end IRComparison.AutomaticStages
