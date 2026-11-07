import IRComparison.Memory.WindowTransport

namespace IRComparison.WindowControl

structure Block where
  index : Int
  loads : List WindowFIFO.Load
  body : List ControlIR.Instr

def lower (blocks : List WindowTransport.Block) : List Block :=
  blocks.map (fun b => ⟨b.index,b.loads,ControlIR.lower b.body⟩)

inductive Config where
  | start (blocks : List Block) (old : List Int) (state : State) (queue : List Int)
  | loading (index : Int) (pending : List WindowFIFO.Load) (old collected : List Int)
      (state : State) (queue : List Int) (body : List ControlIR.Instr) (rest : List Block)
  | body (index : Int) (rest : List Block) (values queue : List Int) (control : ControlIR.Config)
  | stopped (result : Option State) (queue : List Int)

def step (input : Input) (x y : Int) : Config → Config
  | .stopped r q => .stopped r q
  | .start [] _ s q => .stopped (some s) q
  | .start (b::rest) old s q => .loading b.index b.loads old [] s q b.body rest
  | .loading i [] _ vs s q body rest => .body i rest vs q (.running body s vs)
  | .loading i (.memory a::ls) old vs s q body rest =>
      match input a with
      | none => .stopped none q
      | some v => .loading i ls old (vs++[v]) s q body rest
  | .loading i (.saved j::ls) old vs s q body rest =>
      match old[j]? with
      | none => .stopped none q
      | some v => .loading i ls old (vs++[v]) s q body rest
  | .loading _ (.take _::_) _ _ _ [] _ _ => .stopped none []
  | .loading i (.take 0::ls) old vs s (v::q) body rest => .loading i ls old (vs++[v]) s q body rest
  | .loading i (.take (n+1)::ls) old vs s (_::q) body rest => .loading i (.take n::ls) old vs s q body rest
  | .body _ _ _ q (.stopped none) => .stopped none q
  | .body _ rest vs q (.stopped (some s)) => .start rest vs s q
  | .body i rest vs q c@(.running ..) => .body i rest vs q (ControlIR.step i x y c)
  | .body i rest vs q c@(.inSnapshots ..) => .body i rest vs q (ControlIR.step i x y c)

inductive Reaches (input : Input) (x y : Int) : Config → Config → Prop where
  | refl (c) : Reaches input x y c c
  | next {a b} : Reaches input x y (step input x y a) b → Reaches input x y a b

theorem Reaches.trans (h : Reaches input x y a b) (g : Reaches input x y b c) : Reaches input x y a c := by
  induction h with
  | refl => exact g
  | next _ ih => exact .next (ih g)

/-- Every discarded token is a distinct controller transition. -/
theorem take_reduce (n : Nat) (q : List Int) :
    (∃ v tail, q[n]? = some v ∧ tail = q.drop (n+1) ∧
      Reaches input x y (.loading i (.take n::ls) old vs s q body rest)
        (.loading i ls old (vs++[v]) s tail body rest)) ∨
    (q[n]? = none ∧ ∃ tail, Reaches input x y (.loading i (.take n::ls) old vs s q body rest) (.stopped none tail)) := by
  induction n generalizing q with
  | zero =>
    cases q with
    | nil => exact .inr ⟨rfl,[],.next (.refl _)⟩
    | cons v q => exact .inl ⟨v,q,rfl,rfl,.next (.refl _)⟩
  | succ n ih =>
    cases q with
    | nil => exact .inr ⟨rfl,[],.next (.refl _)⟩
    | cons a q =>
      rcases ih q with ⟨v,tail,hv,ht,run⟩ | ⟨hn,tail,run⟩
      · exact .inl ⟨v,tail,by simpa using hv,by simpa using ht,.next run⟩
      · exact .inr ⟨by simpa using hn,tail,.next run⟩

def loadEnd (result : Option (List Int × List Int)) (i : Int) (vs : List Int)
    (s : State) (body : List ControlIR.Instr) (rest : List Block) (errorQueue : List Int) : Config :=
  match result with
  | none => .stopped none errorQueue
  | some (new,q) => .body i rest (vs++new) q (.running body s (vs++new))

theorem loads_correct (pending : List WindowFIFO.Load) (old vs : List Int) (q : List Int) :
    ∃ errorQueue, Reaches input x y (.loading i pending old vs s q body rest)
      (loadEnd (WindowFIFO.execute input old pending q) i vs s body rest errorQueue) := by
  induction pending generalizing vs q with
  | nil => exact ⟨q,by simpa [loadEnd,WindowFIFO.execute] using (Reaches.next (Reaches.refl (.body i rest vs q (.running body s vs))))⟩
  | cons l ls ih =>
    have advance : ∀ v tail,
        Reaches input x y (.loading i (l::ls) old vs s q body rest) (.loading i ls old (vs++[v]) s tail body rest) →
        l.eval input old q = some (v,tail) →
        ∃ errorQueue, Reaches input x y (.loading i (l::ls) old vs s q body rest)
          (loadEnd (WindowFIFO.execute input old (l::ls) q) i vs s body rest errorQueue) := by
      intro v tail run hv
      obtain ⟨failed,after⟩ := ih (vs++[v]) tail
      refine ⟨failed,run.trans ?_⟩
      cases he : WindowFIFO.execute input old ls tail <;>
        simpa [WindowFIFO.execute,hv,he,loadEnd,List.append_assoc] using after
    cases l with
    | memory a =>
      cases h : input a with
      | none => exact ⟨q,by
          simp only [WindowFIFO.execute,WindowFIFO.Load.eval,h,bind,Option.bind,loadEnd]
          apply Reaches.next
          simpa [step,h] using (Reaches.refl (.stopped none q))⟩
      | some v => exact advance v q (by
          apply Reaches.next
          simpa [step,h] using (Reaches.refl (.loading i ls old (vs++[v]) s q body rest))) (by simp [WindowFIFO.Load.eval,h])
    | saved j =>
      cases h : old[j]? with
      | none => exact ⟨q,by
          simp only [WindowFIFO.execute,WindowFIFO.Load.eval,h,bind,Option.bind,loadEnd]
          apply Reaches.next
          simpa [step,h] using (Reaches.refl (.stopped none q))⟩
      | some v => exact advance v q (by
          apply Reaches.next
          simpa [step,h] using (Reaches.refl (.loading i ls old (vs++[v]) s q body rest))) (by simp [WindowFIFO.Load.eval,h])
    | take n =>
      rcases take_reduce (input:=input) (x:=x) (y:=y) (i:=i) (ls:=ls) (old:=old) (vs:=vs) (s:=s) (body:=body) (rest:=rest) n q with
        ⟨v,tail,hv,ht,run⟩ | ⟨hn,tail,run⟩
      · exact advance v tail run (by simp [WindowFIFO.Load.eval,hv,ht])
      · exact ⟨tail,by simpa [WindowFIFO.execute,WindowFIFO.Load.eval,hn,loadEnd] using run⟩

theorem lift_body (h : ControlIR.Reaches i x y a b) :
    Reaches input x y (.body i rest vs q a) (.body i rest vs q b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih =>
    cases a with
    | running => exact .next ih
    | inSnapshots => exact .next ih
    | stopped r => simpa [ControlIR.step] using ih

def resultEnd (result : Option (State × List Int)) (errorQueue : List Int) : Config :=
  match result with
  | none => .stopped none errorQueue
  | some (s,q) => .stopped (some s) q

theorem lower_correct (blocks : List WindowTransport.Block) (old : List Int) (s : State) (q : List Int) :
    ∃ errorQueue, Reaches input x y (.start (lower blocks) old s q)
      (resultEnd (WindowTransport.eval input x y blocks old s q) errorQueue) := by
  induction blocks generalizing old s q with
  | nil => exact ⟨q,.next (.refl _)⟩
  | cons b rest ih =>
    obtain ⟨errorQueue,loaded⟩ := loads_correct (input:=input) (x:=x) (y:=y) (i:=b.index) (s:=s)
      (body:=ControlIR.lower b.body) (rest:=lower rest) b.loads old [] q
    cases he : WindowFIFO.execute input old b.loads q with
    | none =>
      refine ⟨errorQueue,Reaches.next ?_⟩
      simpa [loadEnd,WindowTransport.eval,he,resultEnd] using loaded
    | some pair =>
      obtain ⟨vs,tail⟩ := pair
      simp only [loadEnd,he,List.nil_append] at loaded
      have bodyRun := ControlIR.lower_correct b.body b.index x y s vs []
      simp only [List.append_nil] at bodyRun
      have finished : ControlIR.Reaches b.index x y (.running (ControlIR.lower b.body) s vs)
          (.stopped (b.body.eval b.index x y s vs)) := by
        apply bodyRun.trans
        cases b.body.eval b.index x y s vs <;> simp [ControlIR.resume]
        · exact .refl _
        · exact .next (.refl _)
      have bodyReached := loaded.trans (lift_body finished)
      cases hb : b.body.eval b.index x y s vs with
      | none =>
        refine ⟨tail,Reaches.next (bodyReached.trans ?_)⟩
        simp only [WindowTransport.eval,he,hb,bind,Option.bind,resultEnd]
        exact .next (.refl _)
      | some t =>
        obtain ⟨failed,run⟩ := ih vs t tail
        refine ⟨failed,Reaches.next (bodyReached.trans ?_)⟩
        simpa [WindowTransport.eval,he,hb,resultEnd,step] using (Reaches.next run)

def run (input : Input) (x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run input x y n (step input x y c)

theorem Reaches.finite (h : Reaches input x y a b) : ∃ n, run input x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem lower_finishes (blocks : List WindowTransport.Block) (old : List Int) (s : State) (q : List Int) :
    ∃ n errorQueue, run input x y n (.start (lower blocks) old s q) =
      resultEnd (WindowTransport.eval input x y blocks old s q) errorQueue := by
  obtain ⟨failed,run⟩ := lower_correct (input:=input) (x:=x) (y:=y) blocks old s q
  obtain ⟨n,hn⟩ := run.finite
  exact ⟨n,failed,hn⟩

theorem selected_finishes (selected : WindowTransport.Selected size array body stride count start producer)
    (s : State) (sized : (s.arrays array).size = size) (x y : Int) (values : List Int)
    (contract : selected.Contract (s.arrays array) values) :
    ∃ steps remaining, run (arrayInput (s.arrays array)) x y steps (.start (lower selected.code) [] s values) =
      .stopped (Source.iterate (fun j => body.eval j x y) stride count start s) remaining := by
  obtain ⟨steps,errorQueue,run⟩ := lower_finishes (input:=arrayInput (s.arrays array)) (x:=x) (y:=y) selected.code [] s values
  have same := (selected.code_correct (s.arrays array) x y s values).trans (selected.correct s sized x y values contract)
  cases he : WindowTransport.eval (arrayInput (s.arrays array)) x y selected.code [] s values with
  | none =>
    simp only [he,Option.map_none] at same
    exact ⟨steps,errorQueue,by simpa [he,resultEnd,← same] using run⟩
  | some pair =>
    obtain ⟨t,tail⟩ := pair
    simp only [he,Option.map_some] at same
    exact ⟨steps,tail,by simpa [he,resultEnd,← same] using run⟩

end IRComparison.WindowControl
