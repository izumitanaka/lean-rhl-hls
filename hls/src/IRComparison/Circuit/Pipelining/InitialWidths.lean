import IRComparison.Circuit.BuildInvariant
import IRComparison.Circuit.CountedBackend
import IRComparison.Circuit.Pipelining.Realization

/-! The builder always reserves BV32 input wires and zero-initializable
private wires. This is an initial-state fact, not a bound on later execution. -/
namespace IRComparison.Circuit.Pipelining.InitialWidths

def ZeroFits (r : Interval) : Prop := r.lo ≤ 0 ∧ 0 ≤ r.hi

def Ready (wires : Array Interval) : Prop :=
  ∃ rest, wires.toList = wordRange :: wordRange :: rest ∧ ∀ r ∈ rest, ZeroFits r

theorem initial : Ready #[wordRange,wordRange] := ⟨[],rfl,by simp⟩

theorem Ready.append (h : Ready wires) (added : Array Interval)
    (zero : ∀ r ∈ added.toList, ZeroFits r) : Ready (wires ++ added) := by
  obtain ⟨rest,eq,valid⟩ := h
  refine ⟨rest ++ added.toList,by simp [eq],?_⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact valid r hr
  · exact zero r hr

theorem Ready.push (h : Ready wires) (r : Interval) :
    Ready (wires.push ⟨min 0 r.lo,max 0 r.hi⟩) := by
  obtain ⟨rest,eq,valid⟩ := h
  refine ⟨rest ++ [⟨min 0 r.lo,max 0 r.hi⟩],by simp [eq],?_⟩
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · exact valid s hs
  · rcases List.mem_singleton.mp hs with rfl
    change min 0 r.lo ≤ 0 ∧ 0 ≤ max 0 r.hi
    constructor <;> omega

def rules : BuildInvariant.Rules (fun b => Ready b.wires) where
  fresh := fun r _ h => h.push r
  queue := fun _ _ h => h
  snapshot := fun _ _ _ h => h

theorem reserve (c : HybridIR.ChannelCmd) (b : Build) (h : Ready b.wires) :
    Ready (ChannelLower.reserve c b).wires := by
  apply h.append
  intro r member
  simp only [Array.mem_toList_iff,Array.mem_ofFn] at member
  obtain ⟨i,rfl⟩ := member
  split <;> simp [ZeroFits,wordRange]

theorem named (start stride count initial refill body input qi qo) :
    BuildInvariant.Preserves (fun b => Ready b.wires)
      (CountedBackend.named.build start stride count initial refill body input qi qo) := by
  intro b h
  exact rules.channelLower _ _ _ _ _ (reserve _ b h)

theorem scheduled (layout : Array (Nat × Nat)) (code : HybridUnifiedPipeline.Code) :
    Ready (scheduleWith CountedBackend.named.build layout code).build.wires :=
  rules.schedule CountedBackend.named.build named layout code initial

theorem scheduled_legacy (layout : Array (Nat × Nat)) (code : HybridUnifiedPipeline.Code) :
    Ready (schedule layout code).build.wires :=
  rules.schedule counted (rules.counted) layout code initial

theorem initialFrame_tail (n : Nat) :
    initialWidthFrame (n+2) = wordRange :: wordRange :: List.replicate n zeroRange := by
  have large (k : Nat) : ¬ k+1+1 < 2 := by omega
  simp [initialWidthFrame,List.range_succ_eq_map,List.map_map,Function.comp_def,large,List.map_const']

theorem zeroFrame_within (rs : List Interval) (zero : ∀ r ∈ rs, ZeroFits r) :
    Frame.within (List.replicate rs.length zeroRange) rs = true := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have first := zero r (by simp)
    have rest := ih (fun s hs => zero s (by simp [hs]))
    simpa [Frame.within,zeroRange,first.1,first.2,List.replicate_succ] using rest

/-- This is the actual Boolean condition checked before structured RTL
execution, derived without assuming circuit validation has succeeded. -/
theorem Ready.check (h : Ready wires) : initialWidthsSafe wires.toList = true := by
  obtain ⟨rest,eq,zero⟩ := h
  simp only [eq,List.length_cons,initialWidthsSafe]
  rw [initialFrame_tail]
  have inside := zeroFrame_within rest zero
  simpa [Frame.within,wordRange] using inside

theorem scheduled_check (layout : Array (Nat × Nat)) (code : HybridUnifiedPipeline.Code) :
    initialWidthsSafe (scheduleWith CountedBackend.named.build layout code).build.wires.toList = true :=
  (scheduled layout code).check

theorem scheduled_legacy_check (layout : Array (Nat × Nat)) (code : HybridUnifiedPipeline.Code) :
    initialWidthsSafe (schedule layout code).build.wires.toList = true :=
  (scheduled_legacy layout code).check

end IRComparison.Circuit.Pipelining.InitialWidths
