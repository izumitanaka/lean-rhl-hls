import IRComparison.Circuit.ChannelLower

/-! Shared induction over the executable buildelaws. Different allocation
properties supply only the primitive effects and the counted-body contract. -/
namespace IRComparison.Circuit.BuildInvariant

def Preserves (P : Build → Prop) (action : Builder α) : Prop :=
  ∀ b, P b → P (action b).2

theorem pure_preserves (v : α) : Preserves P (pure v) := fun _ h => h

theorem bind_preserves {action : Builder α} {nextAction : α → Builder β}
    (first : Preserves P action) (rest : ∀ v, Preserves P (nextAction v)) :
    Preserves P (action >>= nextAction) :=
  fun b h => rest (action b).1 (action b).2 (first b h)

structure Rules (P : Build → Prop) : Prop where
  fresh : ∀ r, Preserves P (Circuit.fresh r)
  queue : ∀ n, Preserves P (Circuit.queue n)
  snapshot : ∀ a sizes, Preserves P (Circuit.snapshot a sizes)

namespace Rules
variable {P : Build → Prop} (laws : Rules P)
include laws

theorem freshFor (e : Expr) : Preserves P (Circuit.freshFor e) :=
  fun b h => laws.fresh (b.exprRange e) b h

omit laws in
theorem bounds (e : Expr) : Preserves P (Circuit.bounds e) := fun _ h => h

theorem command (c : HybridIR.Cmd) (i : Expr) (locals : List Expr) (output : Nat) :
    Preserves P (Circuit.command i locals output c) := by
  induction c generalizing i locals with
  | skip | assign | store | send => exact pure_preserves _
  | letValue e b ih =>
    exact bind_preserves (laws.freshFor _) (fun n => bind_preserves (ih i (.wire n::locals)) (fun _ => pure_preserves _))
  | seq a b ia ib | branch e a b ia ib =>
    exact bind_preserves (ia i locals) (fun _ => bind_preserves (ib i locals) (fun _ => pure_preserves _))
  | «repeat» n b ih =>
    exact bind_preserves (laws.fresh _) (fun _ => bind_preserves (ih i locals) (fun _ => pure_preserves _))
  | forRange e b ih =>
    exact bind_preserves (laws.freshFor _) (fun _ => bind_preserves (bounds _) (fun _ =>
      bind_preserves (laws.fresh _) (fun k => bind_preserves (ih i (.wire k::locals)) (fun _ => pure_preserves _))))

theorem newSlots (n : Nat) : Preserves P (Circuit.newSlots n) := by
  induction n with
  | zero => exact pure_preserves _
  | succ n ih => exact bind_preserves (laws.fresh _) (fun _ => bind_preserves ih (fun _ => pure_preserves _))

theorem take (q slot : Nat) (e : Expr) : Preserves P (Circuit.take q slot e) :=
  bind_preserves (laws.freshFor _) (fun _ => bind_preserves (bounds _) (fun _ =>
    bind_preserves (laws.fresh _) (fun _ => bind_preserves (laws.fresh _) (fun _ => pure_preserves _))))

theorem compactLoadOne (i : Expr) (input qi : Nat) (old : List Expr) (slot : Nat) (l : Load) :
    Preserves P (Circuit.compactLoadOne i input qi old slot l) := by
  cases l with
  | memory | saved => exact pure_preserves _
  | take => exact laws.take _ _ _

theorem loads (i : Expr) (input qi : Nat) (old : List Expr) (ls : List Load) (slots : List Nat) :
    Preserves P (Circuit.loads i input qi old ls slots) := by
  induction ls generalizing slots with
  | nil => exact pure_preserves _
  | cons l ls ih =>
    cases slots with
    | nil => exact pure_preserves _
    | cons n ns =>
      exact bind_preserves (laws.compactLoadOne _ _ _ _ _ _) (fun _ => bind_preserves (ih ns) (fun _ => pure_preserves _))

theorem prepareCounted (start stride count initial refill body input qi qo) :
    Preserves P (Circuit.prepareCounted start stride count initial refill body input qi qo) := by
  apply bind_preserves (laws.fresh _); intro k
  apply bind_preserves (laws.newSlots _); intro held
  apply bind_preserves (laws.newSlots _); intro scratch
  apply bind_preserves (laws.loads _ _ _ _ _ _); intro _
  apply bind_preserves (laws.command _ _ _ _); intro _
  apply bind_preserves (laws.loads _ _ _ _ _ _); intro _
  apply bind_preserves (laws.loads _ _ _ _ _ _); intro _
  exact bind_preserves (laws.command _ _ _ _) (fun _ => pure_preserves _)

theorem counted (start stride count initial refill body input qi qo) :
    Preserves P (Circuit.counted start stride count initial refill body input qi qo) := by
  intro b hb
  by_cases hz : count = 0
  · simpa only [Circuit.counted,hz,↓reduceIte,pure,StateT.pure] using hb
  · have h := laws.prepareCounted start stride count initial refill body input qi qo b hb
    simpa only [Circuit.counted,hz,↓reduceIte,bind,StateT.bind,pure,StateT.pure] using h

theorem expandedLoads (input qi : Nat) (old : List Expr) (items : List WindowFIFO.Load) (slots : List Nat) :
    Preserves P (Circuit.expandedLoads input qi old items slots) := by
  induction items generalizing slots with
  | nil => exact pure_preserves _
  | cons l ls ih =>
    cases slots with
    | nil => exact pure_preserves _
    | cons n ns =>
      apply bind_preserves
      · cases l with
        | memory | saved => exact pure_preserves _
        | take => exact laws.take _ _ _
      · intro _; exact bind_preserves (ih ns) (fun _ => pure_preserves _)

theorem blocks (input qi qo : Nat) (old : List Expr) (bs : List HybridIR.Block) :
    Preserves P (Circuit.blocks input qi qo old bs) := by
  induction bs generalizing old with
  | nil => exact pure_preserves _
  | cons bl bs ih =>
    apply bind_preserves (laws.newSlots _); intro slots
    apply bind_preserves (laws.expandedLoads _ _ _ _ _); intro _
    apply bind_preserves (laws.command _ _ _ _); intro _
    exact bind_preserves (ih (slots.map Expr.wire)) (fun _ => pure_preserves _)

theorem channelLower (c : HybridIR.ChannelCmd) (bank : ChannelLower.Buffers) (i : Expr) (ls : List Expr) :
    Preserves P (ChannelLower.lower bank i ls c) := by
  induction c generalizing ls with
  | skip | assign | store | send | hold | receive => exact pure_preserves _
  | letValue e c ih =>
    exact bind_preserves (laws.freshFor _) (fun n => bind_preserves (ih (.wire n::ls)) (fun _ => pure_preserves _))
  | letBuffer n c ih =>
    exact bind_preserves (laws.fresh _) (fun n => bind_preserves (ih (.wire n::ls)) (fun _ => pure_preserves _))
  | seq a b ia ib | branch e a b ia ib =>
    exact bind_preserves (ia ls) (fun _ => bind_preserves (ib ls) (fun _ => pure_preserves _))
  | «repeat» n c ih =>
    exact bind_preserves (laws.fresh _) (fun _ => bind_preserves (ih ls) (fun _ => pure_preserves _))
  | forRange e c ih =>
    exact bind_preserves (laws.freshFor _) (fun _ => bind_preserves (bounds _) (fun _ =>
      bind_preserves (laws.fresh _) (fun k => bind_preserves (ih (.wire k::ls)) (fun _ => pure_preserves _))))

theorem chooseInput (channels : Nat → Nat) (mode : GlobalPipeline.InputMode) :
    Preserves P (chooseInputQueue channels mode) := by
  cases mode with
  | channel => exact pure_preserves _
  | memory => exact laws.queue _

theorem chooseOutput (channels : Nat → Nat) (budget : Nat) (output : Option Nat) :
    Preserves P (chooseOutputQueue channels budget output) := by
  cases output with
  | some => exact pure_preserves _
  | none => exact laws.queue _

theorem channels (capacity : Nat → Nat) (ids : List Nat) :
    Preserves P (allocateChannels capacity ids) := by
  induction ids with
  | nil => exact pure_preserves _
  | cons a ids ih =>
    exact bind_preserves (laws.queue _) (fun _ => bind_preserves ih (fun _ => pure_preserves _))

theorem prepareInstruction (sizes channels : Nat → Nat) (c : HybridIR.Instruction) :
    Preserves P (prepareInstruction sizes channels c) := by
  apply bind_preserves (laws.snapshot _ _)
  intro input
  apply bind_preserves (laws.chooseInput _ _)
  intro qi
  apply bind_preserves (laws.chooseOutput _ _ _)
  intro qo
  exact bind_preserves (laws.blocks input qi qo [] c.blocks) (fun _ => pure_preserves _)

theorem instruction (sizes channels : Nat → Nat) (c : HybridIR.Instruction) :
    Preserves P (instruction sizes channels c) :=
  bind_preserves (laws.prepareInstruction _ _ _) (fun _ => pure_preserves _)

theorem instructions (sizes channels : Nat → Nat) (cs : List HybridIR.Instruction) :
    Preserves P (instructions sizes channels cs) := by
  induction cs with
  | nil => exact pure_preserves _
  | cons c cs ih =>
    exact bind_preserves (laws.instruction _ _ _) (fun _ => bind_preserves ih (fun _ => pure_preserves _))

theorem tail (sizes : Nat → Nat) (incoming : Nat) (code : HybridCompactChainControl.Code) :
    Preserves P (tailCode sizes incoming code) := by
  induction code generalizing incoming with
  | finish r =>
    exact bind_preserves (laws.queue _) (fun _ =>
      bind_preserves (laws.counted _ _ _ _ _ _ _ _ _) (fun _ => pure_preserves _))
  | stage a s rest ih =>
    exact bind_preserves (laws.queue _) (fun out =>
      bind_preserves (laws.counted _ _ _ _ _ _ _ _ _) (fun _ =>
        bind_preserves (ih out) (fun _ => pure_preserves _)))

theorem root (sizes : Nat → Nat) (r : HybridCompactChainControl.RootCode) :
    Preserves P (rootCode sizes r) :=
  bind_preserves (laws.queue _) (fun _ =>
    bind_preserves (laws.queue _) (fun _ =>
      bind_preserves (laws.snapshot _ _) (fun _ =>
        bind_preserves (laws.counted _ _ _ _ _ _ _ _ _) (fun _ =>
          bind_preserves (laws.tail _ _ _) (fun _ => pure_preserves _)))))

theorem region (sizes : Nat → Nat) (r : HybridRegions.Region) :
    Preserves P (regionCode sizes r) :=
  bind_preserves (laws.queue _) (fun _ =>
    bind_preserves (laws.queue _) (fun _ =>
      bind_preserves (laws.snapshot _ _) (fun _ =>
        bind_preserves (laws.counted _ _ _ _ _ _ _ _ _) (fun _ => pure_preserves _))))

theorem regions (sizes : Nat → Nat) (rs : List HybridRegions.Region) :
    Preserves P (regionsCode sizes rs) := by
  induction rs with
  | nil => exact pure_preserves _
  | cons r rs ih =>
    exact bind_preserves (laws.region _ _) (fun _ => bind_preserves ih (fun _ => pure_preserves _))

theorem prepareSymbolic (backend : CountedBuilder)
    (bodyPreserves : ∀ start stride count initial refill body input qi qo,
      Preserves P (backend start stride count initial refill body input qi qo)) (sizes channels : Nat → Nat)
    (c : HybridSymbolicGlobal.Instruction) : Preserves P (prepareSymbolicWith backend sizes channels c) :=
  bind_preserves (laws.snapshot _ _) (fun _ =>
    bind_preserves (laws.chooseInput _ _) (fun _ =>
      bind_preserves (laws.chooseOutput _ _ _) (fun _ =>
        bind_preserves (bodyPreserves _ _ _ _ _ _ _ _ _) (fun _ => pure_preserves _))))

theorem symbolicInstruction (backend : CountedBuilder)
    (bodyPreserves : ∀ start stride count initial refill body input qi qo,
      Preserves P (backend start stride count initial refill body input qi qo)) (sizes channels : Nat → Nat)
    (c : HybridSymbolicGlobal.Instruction) : Preserves P (symbolicInstructionWith backend sizes channels c) :=
  bind_preserves (laws.prepareSymbolic backend bodyPreserves _ _ _) (fun _ => pure_preserves _)

theorem symbolicInstructions (backend : CountedBuilder)
    (bodyPreserves : ∀ start stride count initial refill body input qi qo,
      Preserves P (backend start stride count initial refill body input qi qo)) (sizes channels : Nat → Nat)
    (cs : List HybridSymbolicGlobal.Instruction) : Preserves P (symbolicInstructionsWith backend sizes channels cs) := by
  induction cs with
  | nil => exact pure_preserves _
  | cons c cs ih =>
    exact bind_preserves (laws.symbolicInstruction backend bodyPreserves _ _ _) (fun _ => bind_preserves ih (fun _ => pure_preserves _))

theorem symbolicProgram (backend : CountedBuilder)
    (bodyPreserves : ∀ start stride count initial refill body input qi qo,
      Preserves P (backend start stride count initial refill body input qi qo)) (sizes : Nat → Nat)
    (cs : List HybridSymbolicGlobal.Instruction) : Preserves P (symbolicProgramWith backend sizes cs) :=
  bind_preserves (laws.channels _ _) (fun _ => laws.symbolicInstructions backend bodyPreserves _ _ _)

theorem schedule (backend : CountedBuilder)
    (bodyPreserves : ∀ start stride count initial refill body input qi qo,
      Preserves P (backend start stride count initial refill body input qi qo))
    (layout : Array (Nat × Nat)) (code : HybridUnifiedPipeline.Code)
    (initial : P { memories := layout, nextArray := layout.foldl (fun n p => max n (p.1+1)) 0 }) :
    P (scheduleWith backend layout code).build := by
  cases code with
  | expanded cs =>
    exact (bind_preserves (laws.channels _ _) (fun _ => laws.instructions _ _ _)) _ initial
  | symbolic cs => exact laws.symbolicProgram backend bodyPreserves _ cs _ initial
  | compact c => exact laws.root _ c _ initial
  | regions rs => exact laws.regions _ rs _ initial

end Rules
end IRComparison.Circuit.BuildInvariant
