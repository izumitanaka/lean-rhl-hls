import IRComparison.Hybrid.ChannelScope
import IRComparison.Hybrid.ChannelWindowLoads

namespace IRComparison.ChannelCommandBridge
open HybridIR

/-- Name the existing output stream and relocate the task index. This pass
changes neither source syntax nor the already selected communication policy. -/
def command (output width padding : Nat) : Cmd → ChannelCmd
  | .skip => .skip
  | .assign r e => .assign r (ChannelScope.read width padding e)
  | .store a j e => .store a (ChannelScope.read width padding j) (ChannelScope.read width padding e)
  | .send e => .send output (ChannelScope.read width padding e)
  | .letValue e b => .letValue (ChannelScope.read width padding e) (command output (width+1) padding b)
  | .seq a b => .seq (command output width padding a) (command output width padding b)
  | .branch e a b => .branch (ChannelScope.read width padding e) (command output width padding a) (command output width padding b)
  | .repeat n b => .repeat n (command output width padding b)
  | .forRange e b => .forRange (ChannelScope.read width padding e) (command output (width+1) padding b)

def replace (s : ChannelState) (output : Nat) (p : State × List Int) : ChannelState :=
  ({s with data := p.1}).setQueue output p.2

@[simp] theorem replace_same (s : ChannelState) : replace s output (s.data,s.queues output) = s :=
  ChannelWindow.queue_self s
@[simp] theorem replace_replace (s : ChannelState) :
    replace (replace s output a) output b = replace s output b := by
  simp only [replace,ChannelState.setQueue]
  congr 1
  funext k
  split <;> simp_all
@[simp] theorem replace_data : (replace s output p).data = p.1 := rfl
@[simp] theorem replace_queue : (replace s output p).queues output = p.2 := by simp [replace,ChannelState.setQueue]
@[simp] theorem replace_buffers : (replace s output p).buffers = s.buffers := rfl

theorem fold_replace (f : State × List Int → α → Option (State × List Int))
    (g : ChannelState → α → Option ChannelState)
    (h : ∀ s a, g s a = (f (s.data,s.queues output) a).map (replace s output))
    (items : List α) :
    items.foldlM g s = (items.foldlM f (s.data,s.queues output)).map (replace s output) := by
  induction items generalizing s with
  | nil => simp
  | cons a as ih =>
    rw [List.foldlM_cons,List.foldlM_cons,h]
    cases he : f (s.data,s.queues output) a with
    | none => rfl
    | some pair =>
      simp only [Option.map_some,bind,Option.bind,ih,replace_data,replace_queue]
      congr 1
      funext result
      exact replace_replace s

theorem command_correct (c : Cmd) (size : ls.length = width) (extraSize : extra.length = padding)
    (index : extra[0]? = some i) :
    (command output width padding c).eval outer x y s (ls++extra) =
      (c.eval i x y s.data (s.queues output) ls).map (replace s output) := by
  induction c generalizing s ls width with
  | skip => simp [command,ChannelCmd.eval,Cmd.eval]
  | assign r e =>
    simp only [command,ChannelCmd.eval,Cmd.eval,ChannelScope.read_correct e size extraSize index]
    cases e.eval i x y s.data ls [] <;> simp [replace,ChannelWindow.queue_self]
  | store a j e =>
    simp only [command,ChannelCmd.eval,Cmd.eval,ChannelScope.read_correct j size extraSize index,ChannelScope.read_correct e size extraSize index]
    cases j.eval i x y s.data ls [] with
    | none => rfl
    | some k =>
      cases e.eval i x y s.data ls [] with
      | none => rfl
      | some v =>
        simp only [bind,Option.bind]
        cases s.data.write a k v <;> simp [replace,ChannelWindow.queue_self]
  | send e =>
    simp only [command,ChannelCmd.eval,Cmd.eval,ChannelScope.read_correct e size extraSize index]
    cases e.eval i x y s.data ls [] <;> rfl
  | letValue e c ih =>
    simp only [command,ChannelCmd.eval,Cmd.eval,ChannelScope.read_correct e size extraSize index]
    cases e.eval i x y s.data ls [] with
    | none => rfl
    | some v => simpa only [bind,Option.bind,List.cons_append] using ih (ls:=v::ls) (by simp [size])
  | seq a b ia ib =>
    simp only [command,ChannelCmd.eval,Cmd.eval,ia size]
    cases a.eval i x y s.data (s.queues output) ls with
    | none => rfl
    | some pair =>
      simp only [Option.map_some,bind,Option.bind,ib size,replace_data,replace_queue]
      congr 1
      funext result
      exact replace_replace s
  | branch e a b ia ib =>
    simp only [command,ChannelCmd.eval,Cmd.eval,ChannelScope.read_correct e size extraSize index]
    cases e.eval i x y s.data ls [] with
    | none => rfl
    | some v => simp only [bind,Option.bind]; split <;> simp_all
  | «repeat» n c ih =>
    exact fold_replace (fun p (_:Nat) => c.eval i x y p.1 p.2 ls) _ (fun s _ => ih (s:=s) size) _
  | forRange e c ih =>
    simp only [command,ChannelCmd.eval,Cmd.eval,ChannelScope.read_correct e size extraSize index]
    cases e.eval i x y s.data ls [] with
    | none => rfl
    | some n =>
      exact fold_replace (fun p (k:Nat) => c.eval i x y p.1 p.2 ((k:Int)::ls)) _
        (fun s k => by simpa only [List.cons_append] using ih (s:=s) (ls:=(k:Int)::ls) (by simp [size])) _

end IRComparison.ChannelCommandBridge
