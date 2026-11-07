import IRComparison.Hybrid.HybridCommands

namespace IRComparison.HybridCommandControl
open HybridIR

/-- Explicit continuation and lexical locals for the send-capable controller.
    One step evaluates an expression or enters a structured command. -/
inductive Config where
  | running (pending : List (Cmd × List Int)) (state : State) (queue : List Int)
  | stopped (result : Option (State × List Int))

def step (i x y : Int) : Config → Config
  | .stopped r => .stopped r
  | .running [] s q => .stopped (some (s,q))
  | .running ((.skip,_)::rest) s q => .running rest s q
  | .running ((.assign r e,ls)::rest) s q =>
    match e.eval i x y s ls [] with
    | none => .stopped none
    | some v => .running rest (s.set r v) q
  | .running ((.store a j e,ls)::rest) s q =>
    match (do s.write a (← j.eval i x y s ls []) (← e.eval i x y s ls [])) with
    | none => .stopped none
    | some t => .running rest t q
  | .running ((.send e,ls)::rest) s q =>
    match e.eval i x y s ls [] with
    | none => .stopped none
    | some v => .running rest s (q++[v])
  | .running ((.letValue e b,ls)::rest) s q =>
    match e.eval i x y s ls [] with
    | none => .stopped none
    | some v => .running ((b,v::ls)::rest) s q
  | .running ((.seq a b,ls)::rest) s q => .running ((a,ls)::(b,ls)::rest) s q
  | .running ((.branch e a b,ls)::rest) s q =>
    match e.eval i x y s ls [] with
    | none => .stopped none
    | some v => .running (((if v != 0 then a else b),ls)::rest) s q
  | .running ((.repeat n b,ls)::rest) s q =>
      .running (((List.range n).map (fun _ => (b,ls))) ++ rest) s q
  | .running ((.forRange e b,ls)::rest) s q =>
      match e.eval i x y s ls [] with
      | none => .stopped none
      | some n => .running (((List.range n.toNat).map (fun k => (b,Int.ofNat k::ls))) ++ rest) s q

def resume (r : Option (State × List Int)) (rest : List (Cmd × List Int)) : Config :=
  match r with
  | none => .stopped none
  | some (s,q) => .running rest s q

inductive Reaches (i x y : Int) : Config → Config → Prop where
  | refl (a) : Reaches i x y a a
  | next : Reaches i x y (step i x y a) b → Reaches i x y a b

theorem Reaches.trans (h : Reaches i x y a b) (k : Reaches i x y b c) : Reaches i x y a c := by
  induction h with
  | refl => exact k
  | next _ ih => exact .next (ih k)

theorem frames_correct (items : List α) (frame : α → Cmd × List Int)
    (h : ∀ a s q rest, Reaches i x y (.running (frame a::rest) s q)
      (resume ((frame a).1.eval i x y s q (frame a).2) rest)) (s : State) (q : List Int)
    (rest : List (Cmd × List Int)) :
    Reaches i x y (.running (items.map frame ++ rest) s q)
      (resume (items.foldlM (fun (s,q) a => (frame a).1.eval i x y s q (frame a).2) (s,q)) rest) := by
  induction items generalizing s q with
  | nil => exact .refl _
  | cons a as ih =>
    apply (h a s q (as.map frame ++ rest)).trans
    cases he : (frame a).1.eval i x y s q (frame a).2 with
    | none => simp [resume,List.foldlM_cons,he]; exact .refl _
    | some pair =>
      obtain ⟨t,qs⟩ := pair
      simpa [resume,List.foldlM_cons,he] using ih t qs

theorem correct (b : Cmd) (s : State) (q ls : List Int) (rest : List (Cmd × List Int)) :
    Reaches i x y (.running ((b,ls)::rest) s q) (resume (b.eval i x y s q ls) rest) := by
  induction b generalizing s q ls rest with
  | skip => exact .next (.refl _)
  | assign r e =>
    apply Reaches.next
    cases he : e.eval i x y s ls [] <;> simp [step,Cmd.eval,he,resume] <;> exact .refl _
  | send e =>
    apply Reaches.next
    cases he : e.eval i x y s ls [] <;> simp [step,Cmd.eval,he,resume] <;> exact .refl _
  | store a j e =>
    apply Reaches.next
    cases hj : j.eval i x y s ls [] with
    | none => simp [step,Cmd.eval,hj,resume]; exact .refl _
    | some index =>
      cases he : e.eval i x y s ls [] with
      | none => simp [step,Cmd.eval,hj,he,resume]; exact .refl _
      | some v =>
        cases hw : s.write a index v <;> simp [step,Cmd.eval,hj,he,hw,resume] <;> exact .refl _
  | letValue e b ih =>
    apply Reaches.next
    cases he : e.eval i x y s ls [] with
    | none => simp [step,Cmd.eval,he,resume]; exact .refl _
    | some v => simpa [step,Cmd.eval,he] using ih s q (v::ls) rest
  | seq a b ia ib =>
    apply Reaches.next
    apply (ia s q ls ((b,ls)::rest)).trans
    cases ha : a.eval i x y s q ls with
    | none => simp [resume,Cmd.eval,ha]; exact .refl _
    | some pair =>
      obtain ⟨t,qs⟩ := pair
      simpa [resume,Cmd.eval,ha] using ib t qs ls rest
  | branch e a b ia ib =>
    apply Reaches.next
    cases he : e.eval i x y s ls [] with
    | none => simp [step,Cmd.eval,he,resume]; exact .refl _
    | some v =>
      by_cases hv : v = 0
      · simpa [step,Cmd.eval,he,hv] using ib s q ls rest
      · simpa [step,Cmd.eval,he,hv] using ia s q ls rest
  | «repeat» n b ih =>
    apply Reaches.next
    have h := frames_correct (i:=i) (x:=x) (y:=y) (List.range n) (fun _ => (b,ls))
      (fun _ s q rest => ih s q ls rest) s q rest
    simpa [step,Cmd.eval] using h
  | forRange e b ih =>
    apply Reaches.next
    cases he : e.eval i x y s ls [] with
    | none => simp [step,Cmd.eval,he,resume]; exact .refl _
    | some n =>
      simpa [step,Cmd.eval,he] using
        frames_correct (i:=i) (x:=x) (y:=y) (List.range n.toNat) (fun k => (b,Int.ofNat k::ls))
          (fun k s q rest => ih s q (Int.ofNat k::ls) rest) s q rest

def run (i x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run i x y n (step i x y c)

theorem Reaches.finite (h : Reaches i x y a b) : ∃ n, run i x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem finishes (b : Cmd) (s : State) (q ls : List Int) :
    ∃ n, run i x y n (.running [(b,ls)] s q) = .stopped (b.eval i x y s q ls) := by
  have h := correct (i:=i) (x:=x) (y:=y) b s q ls []
  apply Reaches.finite
  apply h.trans
  cases b.eval i x y s q ls with
  | none => exact .refl _
  | some p => obtain ⟨t,qs⟩ := p; exact .next (.refl _)

end IRComparison.HybridCommandControl
