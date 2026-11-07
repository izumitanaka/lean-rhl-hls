import IRComparison.Circuit.CompactLoadsSound
import IRComparison.Circuit.CopiesSound
import IRComparison.Circuit.QueueFrame
import IRComparison.Circuit.ArrayFrame

namespace IRComparison.Circuit

/-- Contracts of compiler-produced fragments. These package the existing
general compiler theorems; they do not accept a per-example equivalence test. -/
structure BodySpec (code : Schedule) (i : Expr) (locals : List Expr) (src : HybridIR.Cmd) (output : Nat) where
  bound : Nat
  inputs : 2 ≤ bound
  indexScope : Static bound i
  localsScope : ∀ e ∈ locals, Static bound e
  frame : code.above bound
  queueFrame : ∀ q, output ≠ q → code.noQueue q
  correct : ∀ cap p iv x y vs,
    i.eval p.data p.wires = some iv → p.wires 0 = x → p.wires 1 = y → Matches p.data p.wires locals vs →
    ∃ r, code.Eval cap p r ∧ r.map (observe output) = bounded (cap output) iv x y src p.data (p.queues output) vs

def BodySpec.ofCommand (b : Build) (i : Expr) (locals : List Expr) (src : HybridIR.Cmd) (output : Nat)
    (inputs : 2 ≤ b.wires.size) (indexScope : Static b.wires.size i)
    (localsScope : ∀ e ∈ locals, Static b.wires.size e) : BodySpec (command i locals output src b).1 i locals src output :=
  ⟨b.wires.size,inputs,indexScope,localsScope,(command_frame src i locals output b).2,
    fun q h => command_noQueue src b i locals h,
    fun cap p iv x y vs hi hx hy hm => command_correct src b i locals p iv x y vs ⟨inputs,indexScope,localsScope,hi,hx,hy,hm⟩⟩

structure WindowSpec (code : Schedule) (i : Expr) (input qi : Nat) (old : List Expr) (items : List Load) (slots : List Nat) where
  bound : Nat
  frame : code.above bound
  queueFrame : ∀ q, qi ≠ q → code.noQueue q
  correct : ∀ cap p iv vs, i.eval p.data p.wires = some iv → Matches p.data p.wires old vs →
    ∃ r, code.Eval cap p r ∧ r.map (observeLoads qi slots) =
      (WindowFIFO.execute (arrayInput (p.data.arrays input)) vs (items.map (Load.at iv)) (p.queues qi)).map
        (fun (values,rest) => (p.data,values,rest))

theorem compactLoads_noQueue (i : Expr) (input qi : Nat) (old : List Expr) (items : List Load)
    (slots : List Nat) (b : Build) (h : qi ≠ protectedQueue) :
    ((loads i input qi old items slots).run b).1.noQueue protectedQueue := by
  induction items generalizing slots b with
  | nil => trivial
  | cons l ls ih =>
    cases slots with
    | nil => trivial
    | cons slot slots =>
      cases l with
      | memory | saved => exact ⟨True.intro,ih slots b⟩
      | take n =>
        dsimp only [loads,compactLoadOne,bind,pure,StateT.bind,StateT.pure,StateT.run]
        have hh := take_noQueue b qi slot (linear i n) h
        dsimp only [StateT.run] at hh
        generalize he : take qi slot (linear i n) b = pair at *
        obtain ⟨first,b1⟩ := pair
        exact ⟨hh,ih slots b1⟩

def WindowSpec.ofLoads (i : Expr) (input qi : Nat) (old : List Expr) (items : List Load)
    (slots : List Nat) (b : Build) (low : Nat)
    (lengths : items.length = slots.length) (ordered : slots.Pairwise (· < ·))
    (bounds : ∀ n ∈ slots, low ≤ n ∧ n < b.wires.size) (lowBound : low ≤ b.wires.size)
    (oldScope : ∀ e ∈ old, Static low e) (indexScope : Static low i) :
    WindowSpec (loads i input qi old items slots b).1 i input qi old items slots :=
  ⟨low,(compactLoads_frame i input qi old items slots b low lowBound (fun n hn => (bounds n hn).1) lengths).2,
    fun q h => compactLoads_noQueue i input qi old items slots b h,
    fun cap p iv vs hi hm => compactLoads_correct i input qi old items slots b p low vs lengths ordered bounds lowBound oldScope hm indexScope hi⟩

structure MoveSpec (code : Schedule) (dest source : List Nat) (low : Nat) : Prop where
  frame : code.above low
  correct : ∀ cap p, ∃ q, code.Eval cap p (some q) ∧ Copied p q dest source

def MoveSpec.identity (slots : List Nat) : MoveSpec .skip slots slots low :=
  ⟨True.intro,fun _ p => ⟨p,.skip,⟨rfl,rfl,rfl,fun _ _ => rfl⟩⟩⟩

def MoveSpec.ofCopies (dest source : List Nat) (lengths : dest.length = source.length) (unique : dest.Nodup)
    (disjoint : ∀ d ∈ dest, ∀ s ∈ source, d ≠ s) (bound : ∀ n ∈ dest, low ≤ n) :
    MoveSpec (copies dest source) dest source low :=
  ⟨copies_frame dest source bound,fun _ p => copies_correct dest source p lengths unique disjoint⟩

def roundView (qi qo : Nat) (dest : List Nat) (p : Payload) : State × List Int × List Int × List Int :=
  (p.data,dest.map p.wires,p.queues qi,p.queues qo)

def bufferStep (capacity : Nat) (input : Input) (i x y : Int) (items : List Load) (body : HybridIR.Cmd)
    (state : State × List Int × List Int × List Int) : Option (State × List Int × List Int × List Int) := do
  let (s,old,qi,qo) := state
  let (values,rest) ← WindowFIFO.execute input old (items.map (Load.at i)) qi
  let (t,out) ← bounded capacity i x y body s qo values
  return (t,values,rest,out)

/-- Connect a whole refill, optional scratch-to-buffer copy, and compiled body.
The same lemma covers both the initial and steady-state rounds. -/
theorem round_correct
    (ws : WindowSpec loadCode i input qi old items slots)
    (ms : MoveSpec moveCode dest slots low)
    (bs : BodySpec bodyCode i (dest.map Expr.wire) body qo)
    (inputs : 2 ≤ low) (lw : low ≤ ws.bound) (indexScope : Static low i)
    (distinct : qi ≠ qo) (p : Payload) (hi : i.eval p.data p.wires = some iv)
    (hx : p.wires 0 = x) (hy : p.wires 1 = y) (hm : Matches p.data p.wires old values) :
    ∃ result, (Schedule.seq loadCode (.seq moveCode bodyCode)).Eval cap p result ∧
      result.map (roundView qi qo dest) =
        bufferStep (cap qo) (arrayInput (p.data.arrays input)) iv x y items body
          (p.data,values,p.queues qi,p.queues qo) := by
  obtain ⟨r,hr,ho⟩ := ws.correct cap p iv values hi hm
  cases hl : WindowFIFO.execute (arrayInput (p.data.arrays input)) values (items.map (Load.at iv)) (p.queues qi) with
  | none =>
    have rn : r = none := by cases r with
      | none => rfl
      | some q => simp only [hl,Option.map_some,Option.map_none,Option.some_ne_none] at ho
    subst r
    exact ⟨none,.seq_error hr,by simp [bufferStep,hl]⟩
  | some pair =>
    obtain ⟨vs,rest⟩ := pair
    cases r with
    | none => simp [hl] at ho
    | some q =>
      have obs : q.data = p.data ∧ slots.map q.wires = vs ∧ q.queues qi = rest := by simpa [hl,observeLoads] using ho
      have qoSame := loadCode.preserves_queue hr (ws.queueFrame qo distinct) rfl
      have below := (loadCode.preserves_below hr ws.frame rfl).mono lw
      obtain ⟨u,hu,copy⟩ := ms.correct cap q
      have belowMove := moveCode.preserves_below hu ms.frame rfl
      have stable := below.trans belowMove
      have hi' : i.eval u.data u.wires = some iv := (indexScope.stable stable).symm.trans hi
      have hx' := (stable 0 (by omega)).symm.trans hx
      have hy' := (stable 1 (by omega)).symm.trans hy
      have valuesSame : dest.map u.wires = vs := copy.values.trans obs.2.1
      have hm' : Matches u.data u.wires (dest.map Expr.wire) vs := by
        simpa [valuesSame] using matches_wires (s:=u.data) (w:=u.wires) dest
      obtain ⟨r',hr',ho'⟩ := bs.correct cap u iv x y vs hi' hx' hy' hm'
      refine ⟨r',.seq hr (.seq hu hr'),?_⟩
      cases r' with
      | none =>
        have fail : bounded (cap qo) iv x y body p.data (p.queues qo) vs = none := by
          simpa [copy.data,copy.queues,obs.1,qoSame] using ho'.symm
        simp [bufferStep,hl,fail]
      | some t =>
        have result : bounded (cap qo) iv x y body p.data (p.queues qo) vs = some (t.data,t.queues qo) := by
          simpa [observe,copy.data,copy.queues,obs.1,qoSame] using ho'.symm
        have keepInput : t.queues qi = rest := by
          simpa [copy.queues,obs.2.2] using bodyCode.preserves_queue hr' (bs.queueFrame qi (Ne.symm distinct)) rfl
        have hw := bodyCode.preserves_below hr' bs.frame rfl
        have keepValues : dest.map t.wires = vs := by
          rw [← valuesSame]
          apply List.map_congr_left
          intro n hn
          have hs := bs.localsScope (.wire n) (List.mem_map.mpr ⟨n,hn,rfl⟩)
          cases hs with
          | wire hlt => exact (hw n hlt).symm
        simp [bufferStep,hl,result,roundView,keepValues,keepInput]

end IRComparison.Circuit
