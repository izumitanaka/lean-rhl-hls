import IRComparison.Hybrid.ChannelCommandBridge
import IRComparison.Circuit.SymbolicReference

namespace IRComparison.Circuit.ChannelCounted
open HybridIR ChannelWindow

def load : Circuit.Load → ChannelWindow.Load
  | .memory a => .memory a
  | .saved n => .saved n
  | .take d => .take d

theorem load_at (l : Circuit.Load) : (load l).at i = l.at i := by cases l <;> rfl

def oldWidth (initial refill : List Circuit.Load) (k : Nat) :=
  if k = 0 then 0 else if k = 1 then initial.length else refill.length

def items (initial refill : List Circuit.Load) (k : Nat) := if k = 0 then initial else refill

def piece (input qi qo width : Nat) (ls : List Circuit.Load) (body : Cmd) : ChannelCmd :=
  .seq
    (ChannelBuffers.capture ((List.range width).map (0+·))
      (ChannelWindow.loads input qi 0 width 2 (.local width) (ls.map load)))
    (ChannelBuffers.capture ((List.range ls.length).map (0+·))
      (ChannelCommandBridge.command qo ls.length 2 body))

def round (input qi qo : Nat) (start stride : Int) (initial refill : List Circuit.Load) (body : Cmd) : ChannelCmd :=
  .letValue (.pure (.add (.lit start) (.mul (.local 0) (.lit stride))))
    (.branch (.pure (.local 1))
      (.branch (.pure (.sub (.local 1) (.lit 1)))
        (piece input qi qo refill.length refill body)
        (piece input qi qo initial.length refill body))
      (piece input qi qo 0 initial body))

def command (input qi qo : Nat) (start stride : Int) (count : Nat)
    (initial refill : List Circuit.Load) (body : Cmd) : ChannelCmd :=
  .forRange (.pure (.lit count)) (round input qi qo start stride initial refill body)

def update (s : ChannelState) (qi qo : Nat) (w : WindowState) : ChannelState :=
  ChannelCommandBridge.replace (ChannelWindow.put (s.setQueue qi w.2.2.1) 0 w.2.1) qo (w.1,w.2.2.2)

theorem update_data : (update s qi qo w).data = w.1 := rfl

theorem update_input (distinct : qi ≠ qo) : (update s qi qo w).queues qi = w.2.2.1 := by
  simp [update,ChannelCommandBridge.replace,ChannelState.setQueue,distinct]

theorem update_output : (update s qi qo w).queues qo = w.2.2.2 := by
  simp [update,ChannelCommandBridge.replace,ChannelState.setQueue]

theorem update_held : Held (update s qi qo w) 0 w.2.1 :=
  ChannelWindow.put_held _

theorem piece_correct (held : Held s 0 old) (size : old.length = width) (distinct : qi ≠ qo) :
    (piece input qi qo width ls body).eval outer x y s [i,k] =
      (do
        let (values,rest) ← WindowFIFO.execute (arrayInput (s.data.arrays input)) old (ls.map (Circuit.Load.at i)) (s.queues qi)
        let (t,out) ← body.eval i x y s.data (s.queues qo) values
        return (t,values,rest,out)).map (update s qi qo) := by
  unfold piece
  rw [ChannelCmd.eval]
  have capture := capture_held held (i:=outer) (x:=x) (y:=y) (ls:=[i,k]) (c:=ChannelWindow.loads input qi 0 width 2 (.local width) (ls.map load))
  rw [← size] at capture ⊢
  rw [capture,loads_correct (ls.map load) (array:=input) (channel:=qi) (base:=0) (width:=old.length) (padding:=2) (index:=.local old.length) (outer:=outer) (x:=x) (y:=y) (s:=s) (i:=i) (old:=old) (extra:=[i,k]) rfl rfl (by
    simp [Value.eval])]
  simp only [List.map_map]
  have atEq : ChannelWindow.Load.at i ∘ load = Circuit.Load.at i := funext load_at
  rw [atEq]
  cases hl : WindowFIFO.execute (arrayInput (s.data.arrays input)) old (ls.map (Circuit.Load.at i)) (s.queues qi) with
  | none => rfl
  | some pair =>
    obtain ⟨vs,rest⟩ := pair
    have len : vs.length = ls.length := by
      have h := execute_length _ hl
      simpa using h
    simp only [Option.map_some,bind,Option.bind]
    have captured := capture_held (put_held (s:=s.setQueue qi rest) (base:=0) vs) (i:=outer) (x:=x) (y:=y) (ls:=[i,k])
      (c:=ChannelCommandBridge.command qo ls.length 2 body)
    rw [← len] at captured ⊢
    rw [captured,ChannelCommandBridge.command_correct body (output:=qo) (width:=vs.length) (padding:=2) (ls:=vs) (extra:=[i,k]) (outer:=outer) (x:=x) (y:=y) (s:=put (s.setQueue qi rest) 0 vs) rfl rfl (by rfl : [i,k][0]? = some i)]
    simp only [put_data,put_queues,ChannelState.setQueue,if_neg (Ne.symm distinct)]
    cases body.eval i x y s.data (s.queues qo) vs <;> rfl

theorem round_correct (held : Held s 0 old) (size : old.length = oldWidth initial refill k)
    (distinct : qi ≠ qo) :
    (round input qi qo start stride initial refill body).eval outer x y s [(k:Int)] =
      (sourceCountedStep input start stride x y initial refill body k (s.data,old,s.queues qi,s.queues qo)).map
        (update s qi qo) := by
  simp only [round,ChannelCmd.eval,ReadCode.eval,bind,Option.bind,Value.eval,
    List.getElem?_cons_succ,List.getElem?_cons_zero]
  have step := fun width ls (h : old.length = width) =>
    piece_correct (input:=input) (qi:=qi) (qo:=qo) (ls:=ls) (body:=body)
      (outer:=outer) (x:=x) (y:=y) (i:=start+(k:Int)*stride) (k:=(k:Int)) held h distinct
  by_cases hz : k = 0
  · subst k
    simp only [oldWidth,ite_true] at size
    simp only [Int.natCast_zero,Int.zero_mul,Int.add_zero,bne_self_eq_false,Bool.false_eq_true,ite_false]
    simpa only [sourceCountedStep,ite_true,Nat.zero_eq,Int.natCast_zero,Int.zero_mul,Int.add_zero,Option.map_eq_map,Option.bind_map,Option.map_bind,Option.map_some] using step 0 initial size
  · have ki : (k:Int) ≠ 0 := by omega
    simp only [ki,bne_iff_ne,ne_eq,not_false_eq_true,ite_true]
    by_cases ho : k = 1
    · have one : (k:Int)-1 = 0 := by omega
      simp only [one,not_true_eq_false,ite_false]
      have hs : old.length = initial.length := by simpa [oldWidth,hz,ho] using size
      simpa only [sourceCountedStep,hz,ite_false,Option.map_eq_map,Option.bind_map,Option.map_bind,Option.map_some] using step initial.length refill hs
    · have nonone : (k:Int)-1 ≠ 0 := by omega
      simp only [nonone,not_false_eq_true,ite_true]
      have hs : old.length = refill.length := by simpa [oldWidth,hz,ho] using size
      simpa only [sourceCountedStep,hz,ite_false,Option.map_eq_map,Option.bind_map,Option.map_bind,Option.map_some] using step refill.length refill hs

def Related (original : Nat → List Int) (qi qo : Nat) (initial refill : List Circuit.Load)
    (k : Nat) (w : WindowState) (s : ChannelState) : Prop :=
  s.data = w.1 ∧
  s.queues = GlobalPipeline.put (GlobalPipeline.put original qi w.2.2.1) qo w.2.2.2 ∧
  Held s 0 w.2.1 ∧ w.2.1.length = oldWidth initial refill k

theorem step_length (h : sourceCountedStep input start stride x y initial refill body k w = some next) :
    next.2.1.length = oldWidth initial refill (k+1) := by
  obtain ⟨s,old,qi,qo⟩ := w
  unfold sourceCountedStep at h
  cases hl : WindowFIFO.execute (arrayInput (s.arrays input)) old
      ((if k = 0 then initial else refill).map (Circuit.Load.at (start+(k:Int)*stride))) qi with
  | none => simp [hl] at h
  | some pair =>
    obtain ⟨vs,rest⟩ := pair
    cases hb : body.eval (start+(k:Int)*stride) x y s qo vs with
    | none => simp [hl,hb] at h
    | some pair =>
      obtain ⟨t,out⟩ := pair
      simp only [hl,hb,bind,Option.bind,pure,Option.some.injEq] at h
      subst next
      have len := execute_length _ hl
      by_cases hz : k = 0 <;> simp_all [oldWidth]

theorem update_related (h : Related original qi qo initial refill k w s)
    (len : next.2.1.length = oldWidth initial refill (k+1)) (distinct : qi ≠ qo) :
    Related original qi qo initial refill (k+1) next (update s qi qo next) := by
  refine ⟨rfl,?_,update_held,len⟩
  simp only [update,ChannelCommandBridge.replace,ChannelState.setQueue,put_queues,h.2.1,GlobalPipeline.put]
  funext a
  by_cases ha : a = qo <;> by_cases hb : a = qi <;> simp_all [GlobalPipeline.put]

theorem fold_correct (n k : Nat) (h : Related original qi qo initial refill k w s) (distinct : qi ≠ qo) :
    Option.Rel (Related original qi qo initial refill (k+n))
      ((List.range' k n).foldlM (fun st (j:Nat) => sourceCountedStep input start stride x y initial refill body j st) w)
      ((List.range' k n).foldlM (fun st (j:Nat) => (round input qi qo start stride initial refill body).eval outer x y st [(j:Int)]) s) := by
  induction n generalizing k w s with
  | zero => simpa using Option.Rel.some h
  | succ n ih =>
    rw [List.range'_succ,List.foldlM_cons,List.foldlM_cons,round_correct h.2.2.1 h.2.2.2 distinct]
    have qiEq : s.queues qi = w.2.2.1 := by simp [h.2.1,GlobalPipeline.put,distinct]
    have qoEq : s.queues qo = w.2.2.2 := by simp [h.2.1,GlobalPipeline.put]
    rw [h.1,qiEq,qoEq]
    cases hs : sourceCountedStep input start stride x y initial refill body k w with
    | none => exact .none
    | some next =>
      simp only [Option.map_some,bind,Option.bind]
      have rel := update_related h (step_length hs) distinct
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (k+1) rel

theorem command_correct (distinct : qi ≠ qo) :
    ((command input qi qo start stride count initial refill body).eval outer x y s []).map
      (fun t => (t.data,t.queues)) =
    ((List.range' 0 count).foldlM (fun st (j:Nat) => sourceCountedStep input start stride x y initial refill body j st)
      (s.data,[],s.queues qi,s.queues qo)).map
      (fun w => (w.1,GlobalPipeline.put (GlobalPipeline.put s.queues qi w.2.2.1) qo w.2.2.2)) := by
  have initialRel : Related s.queues qi qo initial refill 0 (s.data,[],s.queues qi,s.queues qo) s := by
    refine ⟨rfl,?_,?_,rfl⟩
    · funext a; simp [GlobalPipeline.put]; split <;> simp_all
    · intro slot hs; simp at hs
  have h := fold_correct (outer:=outer) (input:=input) (start:=start) (stride:=stride) (x:=x) (y:=y) (body:=body) count 0 initialRel distinct
  simp only [command,ChannelCmd.eval,ReadCode.eval,Value.eval,bind,Option.bind,Int.toNat_natCast,List.range_eq_range']
  cases hs : (List.range' 0 count).foldlM (fun st (j:Nat) => sourceCountedStep input start stride x y initial refill body j st)
      (s.data,[],s.queues qi,s.queues qo) <;>
    cases ht : (List.range' 0 count).foldlM (fun st (j:Nat) => (round input qi qo start stride initial refill body).eval outer x y st [(j:Int)]) s <;>
    simp only [hs,ht] at h
  · rfl
  · cases h
  · cases h
  · cases h with
    | some rel => simp only [Option.map_some]; exact congrArg some (Prod.ext rel.1 rel.2.1)

end IRComparison.Circuit.ChannelCounted
