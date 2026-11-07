import IRComparison.Circuit.QueueTable
import IRComparison.Circuit.StaticCapacity

namespace IRComparison.Circuit

theorem loadOne_resources (input qi : Nat) (old : List Expr) (slot : Nat) (l : WindowFIFO.Load) :
    PreservesResources (loadOne input qi old slot l) := by
  cases l with
  | memory | saved => exact resources_pure _
  | take => exact take_resources _ _ _

theorem expandedLoads_resources (input qi : Nat) (old : List Expr) (items : List WindowFIFO.Load) (slots : List Nat) :
    PreservesResources (expandedLoads input qi old items slots) := by
  induction items generalizing slots with
  | nil => exact resources_pure _
  | cons l ls ih =>
    cases slots with
    | nil => exact resources_pure _
    | cons n ns =>
      exact resources_bind _ _ (loadOne_resources _ _ _ _ _)
        (fun _ => resources_bind _ _ (ih ns) (fun _ => resources_pure _))

theorem blocks_resources (input qi qo : Nat) (old : List Expr) (bs : List HybridIR.Block) :
    PreservesResources (blocks input qi qo old bs) := by
  induction bs generalizing old with
  | nil => exact resources_pure _
  | cons bl bs ih =>
    apply resources_bind _ _ (newSlots_resources _)
    intro slots
    apply resources_bind _ _ (expandedLoads_resources _ _ _ _ _)
    intro _
    apply resources_bind _ _ (command_resources _ _ _ _)
    intro _
    exact resources_bind _ _ (ih (slots.map Expr.wire)) (fun _ => resources_pure _)

theorem blocks_noQueue (input qi qo : Nat) (old : List Expr) (bs : List HybridIR.Block) (b : Build)
    (hin : qi ≠ protectedQueue) (hout : qo ≠ protectedQueue) :
    (blocks input qi qo old bs b).1.noQueue protectedQueue := by
  induction bs generalizing b old with
  | nil => trivial
  | cons bl bs ih =>
    dsimp only [blocks,bind,pure,StateT.bind,StateT.pure]
    generalize ha : newSlots bl.loads.length b = pair
    obtain ⟨slots,b1⟩ := pair
    dsimp only
    have hl := expandedLoads_noQueue input qi old bl.loads slots b1 hin
    dsimp only [StateT.run] at hl
    generalize hc : expandedLoads input qi old bl.loads slots b1 = pair at *
    obtain ⟨loadCode,b2⟩ := pair
    dsimp only
    have hb := command_noQueue bl.body b2 (.lit bl.index) (slots.map Expr.wire) hout
    dsimp only [StateT.run] at hb
    generalize hbcode : command (.lit bl.index) (slots.map Expr.wire) qo bl.body b2 = pair at *
    obtain ⟨bodyCode,b3⟩ := pair
    exact ⟨hl,hb,ih (slots.map Expr.wire) b3⟩

theorem blocks_frame (input qi qo : Nat) (old : List Expr) (bs : List HybridIR.Block) (b : Build) :
    b.wires.size ≤ (blocks input qi qo old bs b).2.wires.size ∧
      (blocks input qi qo old bs b).1.above b.wires.size := by
  induction bs generalizing old b with
  | nil => exact ⟨Nat.le_refl _,True.intro⟩
  | cons bl bs ih =>
    have alloc := newSlots_shape bl.loads.length b
    dsimp only [StateT.run] at alloc
    dsimp only [blocks,bind,pure,StateT.bind,StateT.pure]
    generalize ha : newSlots bl.loads.length b = pair at *
    obtain ⟨slots,b1⟩ := pair
    dsimp only at alloc ⊢
    have len : bl.loads.length = slots.length := by simp [alloc.1]
    have grow : b.wires.size ≤ b1.wires.size := by have := alloc.2; omega
    have slotBound : ∀ n ∈ slots, b.wires.size ≤ n := by
      intro n hn; rw [alloc.1,List.mem_range'_1] at hn; exact hn.1
    have loadFrame := expandedLoads_frame input qi old bl.loads slots b1 b.wires.size grow slotBound len
    dsimp only [StateT.run] at loadFrame
    generalize hc : expandedLoads input qi old bl.loads slots b1 = pair at *
    obtain ⟨loadCode,b2⟩ := pair
    dsimp only at loadFrame ⊢
    have bodyFrame := command_frame bl.body (.lit bl.index) (slots.map Expr.wire) qo b2
    dsimp only [StateT.run] at bodyFrame
    generalize hb : command (.lit bl.index) (slots.map Expr.wire) qo bl.body b2 = pair at *
    obtain ⟨bodyCode,b3⟩ := pair
    dsimp only at bodyFrame ⊢
    have tailFrame := ih (slots.map Expr.wire) b3
    generalize ht : blocks input qi qo (slots.map Expr.wire) bs b3 = pair at *
    obtain ⟨tailCode,b4⟩ := pair
    have g2 := Nat.le_trans grow loadFrame.1
    have g3 := Nat.le_trans g2 bodyFrame.1
    exact ⟨Nat.le_trans g3 tailFrame.1,loadFrame.2,
      bodyCode.above_mono bodyFrame.2 g2,tailCode.above_mono tailFrame.2 g3⟩

theorem blocks_static_correct (input qi qo : Nat) (old : List Expr) (bs : List HybridIR.Block)
    (b : Build) (p : Payload) (x y : Int) (values : List Int)
    (distinct : qi ≠ qo) (inputs : 2 ≤ b.wires.size)
    (readonly : ∀ block ∈ bs, input ∉ commandWrites block.body)
    (scopeOK : ∀ e ∈ old, Static b.wires.size e) (hm : Matches p.data p.wires old values)
    (hx : p.wires 0 = x) (hy : p.wires 1 = y)
    (known : blocksBudget bs = some budget) (capacity : (p.queues qo).length+budget ≤ cap qo) :
    ∃ result, (blocks input qi qo old bs b).1.Eval cap p result ∧
      result.map (observeBlock qi qo) =
        HybridIR.blocksEval (arrayInput (p.data.arrays input)) x y bs values p.data (p.queues qi) (p.queues qo) := by
  obtain ⟨r,hr,ho⟩ := blocks_correct input qi qo old bs b p x y values distinct inputs readonly scopeOK hm hx hy
  refine ⟨r,hr,?_⟩
  rw [boundedBlocks_eq] at ho
  · exact ho
  · intro t rest out he
    exact Nat.le_trans (blocksBudget_sound bs known he) capacity

theorem extends_blocks (input qi qo : Nat) (old : List Expr) (bs : List HybridIR.Block) :
    ExtendsBuild (blocks input qi qo old bs) := by
  intro b
  have hr := blocks_resources input qi qo old bs b
  have hq := congrArg (fun r => r.2.1) hr
  have hn := congrArg (fun r => r.2.2.2) hr
  dsimp only [Build.resources] at hq hn
  refine ⟨(blocks_frame input qi qo old bs b).1,?_,?_⟩
  · intro pair hp; rw [hq]; exact hp
  · rw [hn]; exact Nat.le_refl _

end IRComparison.Circuit
