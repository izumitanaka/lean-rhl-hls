import IRComparison.Hybrid.HybridWordPipeline
import IRComparison.Hybrid.HybridUnifiedPipeline

namespace IRComparison.HybridWord

/-- Kernel metadata is shared with the existing compiler. Counter values are
    reduced to BV32 at use sites; both reverse traversal and wrapping are defined. -/
structure Kernel where
  body : Cmd
  size : Nat
  array : Nat
  start : Int
  stride : Int
  count : Nat
  supplier : Unit → List Int
  native : Word → Word → Word → State → Option State
  correct : ∀ i x y s, body.eval i x y s [] = native i x y s

def Kernel.lower (k : Kernel) : HybridIR.Kernel where
  body := k.body.lower
  native := fun i x y s => k.body.lower.eval i x y s []
  correct := by intros; rfl
  size := k.size
  array := k.array
  start := k.start
  stride := k.stride
  count := k.count
  supplier := k.supplier

def runSource (f : Word → Word → Word → State → Option State) (x y : Word) (stride : Int) :
    Nat → Int → State → Option State
  | 0,_,s => some s
  | n+1,i,s => do runSource f x y stride n (i+stride) (← f (BitVec.ofInt 32 i) x y s)

theorem iterate_native (k : Kernel) (n : Nat) (i : Int) (s : State) :
    iterate k.body x y k.stride n i s = runSource k.native x y k.stride n i s := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih => simp only [iterate,runSource,k.correct,ih]

def Kernel.source (k : Kernel) (x y : Word) (s : State) :=
  runSource k.native x y k.stride k.count k.start s

def source (x y : Word) : List Kernel → State → Option State
  | [],s => some s
  | k::ks,s => do source x y ks (← k.source x y s)

theorem source_correct (ks : List Kernel) (s : State) :
    HybridIR.source (encode x) (encode y) (ks.map Kernel.lower) s.encode =
      (source x y ks s).map State.encode := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    change ((Source.iterate (fun i => k.body.lower.eval i (encode x) (encode y))
      k.stride k.count k.start s.encode).bind
      (HybridIR.source (encode x) (encode y) (ks.map Kernel.lower))) = _
    rw [iterate_correct k.body s, iterate_native]
    cases h : runSource k.native x y k.stride k.count k.start s <;> simp [source, Kernel.source, h, ih]

abbrev Plan (outputs : List Nat) (sizes : Nat → Nat) (ks : List Kernel) :=
  HybridUnifiedPipeline.Plan outputs sizes (ks.map Kernel.lower)

def compileProgram (outputs : List Nat) (sizes : Nat → Nat) (ks : List Kernel) :
    Option (Plan outputs sizes ks) :=
  HybridUnifiedPipeline.compile outputs sizes (ks.map Kernel.lower)

def compileProgramWithSMT (outputs : List Nat) (sizes : Nat → Nat) (ks : List Kernel)
    (directory : System.FilePath) : IO (Option (Plan outputs sizes ks)) :=
  HybridUnifiedPipeline.compileWithSMT outputs sizes (ks.map Kernel.lower) directory

theorem program_correct (p : Plan outputs sizes ks) (s : State)
    (layout : PipelineShapes.Layout sizes s.encode) (ready : p.Ready (encode x) (encode y) s.encode) :
    (p.eval (encode x) (encode y) s.encode).map (PipelineUse.observe outputs) =
      (source x y ks s).map (fun t => PipelineUse.observe outputs t.encode) := by
  rw [p.correct s.encode layout ready, source_correct]
  simp only [Option.map_map, Function.comp_def]

theorem program_finishes (p : Plan outputs sizes ks) (s : State)
    (layout : PipelineShapes.Layout sizes s.encode) (ready : p.Ready (encode x) (encode y) s.encode) :
    ∃ n result, HybridUnifiedPipeline.run (encode x) (encode y) n
      (HybridUnifiedPipeline.start (HybridUnifiedPipeline.lower p) s.encode) = .stopped result ∧
      result.map (PipelineUse.observe outputs) =
        (source x y ks s).map (fun t => PipelineUse.observe outputs t.encode) := by
  obtain ⟨n,r,hr,he⟩ := HybridUnifiedPipeline.plan_finishes p s.encode layout ready
  exact ⟨n,r,hr,by simpa only [source_correct, Option.map_map, Function.comp_def] using he⟩

end IRComparison.HybridWord
