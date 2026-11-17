import IRComparison.Circuit.RootSound
import IRComparison.Circuit.LayoutScope

namespace IRComparison.Circuit
open HybridRegions

theorem region_code_trim (r : Region)
    (safe : ∀ a ∈ allCommandArrays r.code.body.target, a < limit) :
    (r.code.eval input x y s).map (trimState limit) = r.code.eval input x y (trimState limit s) := by
  have h := producer_trim (input:=input) (x:=x) (y:=y) (s:=s) r.producer safe
  rw [producer_eval,producer_eval] at h
  have hh := congrArg (Option.map Prod.fst) h
  simpa [Option.map_map,Function.comp_def,trimResult] using hh

theorem region_trim (r : Region) (inputSafe : r.array < limit)
    (safe : ∀ a ∈ allCommandArrays r.code.body.target, a < limit) :
    (r.eval x y s).map (trimState limit) = r.eval x y (trimState limit s) := by
  rw [Region.eval,region_code_trim r safe,Region.eval]
  simp only [trimState,inputSafe,↓reduceIte]

theorem regions_trim (rs : List Region)
    (safe : ∀ r ∈ rs, r.array < limit ∧ ∀ a ∈ allCommandArrays r.code.body.target, a < limit) :
    (HybridRegions.eval x y rs s).map (trimState limit) = HybridRegions.eval x y rs (trimState limit s) := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    have hs := safe r (by simp)
    rw [HybridRegions.eval,HybridRegions.eval,← region_trim r hs.1 hs.2]
    cases he : r.eval x y s with
    | none => rfl
    | some t => exact ih (fun r hr => safe r (by simp [hr]))

theorem trim_snapshot_above (p : Payload) (fresh : limit ≤ slot) :
    trimState limit (p.snapshot slot source).data = trimState limit p.data := by
  unfold trimState Payload.snapshot
  congr 1
  funext a
  by_cases ha : a < limit
  · simp [ha,show a ≠ slot from by omega]
  · simp [ha]

theorem regionCode_extension (sizes : Nat → Nat) (r : Region) : ExtendsBuild (regionCode sizes r) := by
  apply extends_bind _ _ (extends_queue _)
  intro qi
  apply extends_bind _ _ (extends_queue _)
  intro qo
  apply extends_bind _ _ (extends_snapshot _ _)
  intro input
  exact extends_bind _ _ (extends_counted _ _ _ _ _ _ _ _ _) (fun _ => extends_pure _)

theorem regionCode_arrays (sizes : Nat → Nat) (r : Region) (b : Build) :
    (regionCode sizes r b).2.nextArray = b.nextArray+1 := by
  let b3 := ((b.allocateQueue 0).allocateQueue 0).allocateSnapshot r.array sizes
  have h := counted_resources r.code.start r.code.stride r.code.count
    (r.code.initial.map fromMemoryLoad) (r.code.refill.map fromMemoryLoad)
    r.code.body.target b.nextArray b.nextQueue (b.nextQueue+1) b3
  exact congrArg (fun r => r.2.2.1) h

theorem regionCode_frame (sizes : Nat → Nat) (r : Region) (b : Build) (inputs : 2 ≤ b.wires.size) :
    (regionCode sizes r b).1.above b.wires.size := by
  let b3 := ((b.allocateQueue 0).allocateQueue 0).allocateSnapshot r.array sizes
  have h := counted_frame r.code.start r.code.stride r.code.count
    (r.code.initial.map fromMemoryLoad) (r.code.refill.map fromMemoryLoad)
    r.code.body.target b.nextArray b.nextQueue (b.nextQueue+1) b3 inputs
  exact ⟨True.intro,True.intro,h⟩

theorem regionCode_correct (sizes : Nat → Nat) (region : Region) (b : Build) (p : Payload)
    (inputs : 2 ≤ b.wires.size) (fresh : limit ≤ b.nextArray)
    (safe : ∀ a ∈ allCommandArrays region.code.body.target, a < limit)
    (hx : p.wires 0 = x) (hy : p.wires 1 = y) :
    ∃ result, (regionCode sizes region b).1.Eval cap p result ∧
      result.map (fun q => trimState limit q.data) = (region.eval x y p.data).map (trimState limit) := by
  let b3 := ((b.allocateQueue 0).allocateQueue 0).allocateSnapshot region.array sizes
  let p0 := p.snapshot b.nextArray region.array
  let p1 := p0.clear (b.nextQueue+1)
  have readonly : b.nextArray ∉ commandWrites region.code.body.target := by
    intro h
    have := safe _ (commandWrites_mem _ h)
    omega
  have fits : ∀ t out, region.producer.eval (arrayInput (p1.data.arrays b.nextArray)) x y p1.data = some (t,out) → out.length ≤ cap (b.nextQueue+1) := by
    intro t out h
    rw [producer_eval] at h
    cases he : region.code.eval (arrayInput (p1.data.arrays b.nextArray)) x y p1.data with
    | none => simp [he] at h
    | some u => simp [he] at h; simp [h.2]
  obtain ⟨result,hr,ho⟩ := producer_correct (input:=b.nextArray) (qi:=b.nextQueue) (qo:=b.nextQueue+1)
    (cap:=cap) region.producer b3 p1 inputs (by omega) (by simp [p1,Payload.clear]) readonly hx hy fits
  have projected := congrArg (Option.map (fun t : State × List Int × List Int => t.1)) ho
  have full : result.map Payload.data = region.code.eval (arrayInput (p.data.arrays region.array)) x y p0.data := by
    simpa [producer_eval,Option.map_map,Function.comp_def,observeBlock,p1,p0,Payload.clear,Payload.snapshot] using projected
  refine ⟨result,.seq (snapshot_eval p b.nextArray region.array) (.seq (clear_eval p0 (b.nextQueue+1)) hr),?_⟩
  have trimmed := congrArg (Option.map (trimState limit)) full
  simp only [Option.map_map] at trimmed
  rw [region_code_trim region safe,trim_snapshot_above p fresh] at trimmed
  rw [Region.eval,region_code_trim region safe]
  exact trimmed

theorem regionsCode_correct (sizes : Nat → Nat) (rs : List Region) (b : Build) (p : Payload)
    (inputs : 2 ≤ b.wires.size) (fresh : limit ≤ b.nextArray)
    (safe : ∀ r ∈ rs, r.array < limit ∧ ∀ a ∈ allCommandArrays r.code.body.target, a < limit)
    (hx : p.wires 0 = x) (hy : p.wires 1 = y) :
    ∃ result, (regionsCode sizes rs b).1.Eval cap p result ∧
      result.map (fun q => trimState limit q.data) = (HybridRegions.eval x y rs p.data).map (trimState limit) := by
  induction rs generalizing b p with
  | nil => exact ⟨some p,.skip,rfl⟩
  | cons region rs ih =>
    have hrSafe := safe region (by simp)
    have restSafe := fun r hr => safe r (List.mem_cons_of_mem region hr)
    have ext := regionCode_extension sizes region b
    have arrays := regionCode_arrays sizes region b
    have frame := regionCode_frame sizes region b inputs
    obtain ⟨result,hr,ho⟩ := regionCode_correct (cap:=cap) sizes region b p inputs fresh hrSafe.2 hx hy
    generalize hc : regionCode sizes region b = built at *
    obtain ⟨code,b1⟩ := built
    dsimp only at ext frame hr ho arrays
    simp only [regionsCode,bind,pure,StateT.bind,StateT.pure,hc]
    cases result with
    | none =>
      have failure : region.eval x y p.data = none := by
        cases he : region.eval x y p.data <;> simp_all
      exact ⟨none,.seq_error hr,by simp [HybridRegions.eval,failure]⟩
    | some q =>
      have stable := code.preserves_below hr frame rfl
      have qx := (stable 0 (by omega)).symm.trans hx
      have qy := (stable 1 (by omega)).symm.trans hy
      obtain ⟨out,ht,ot⟩ := ih b1 q (Nat.le_trans inputs ext.wires) (by omega) restSafe qx qy
      refine ⟨out,.seq hr ht,?_⟩
      cases he : region.eval x y p.data with
      | none => simp [he] at ho
      | some t =>
        have eq : trimState limit q.data = trimState limit t := by simpa [he] using ho
        rw [regions_trim rs restSafe,eq,← regions_trim rs restSafe] at ot
        simpa [HybridRegions.eval,he] using ot

/-- The counted region path uses the existing loop lowering and machine
semantics. Code size follows region/body syntax, not the iteration count. -/
theorem regions_pipeline_schedule (layout : Array (Nat × Nat)) (rs : List Region)
    (covered : layoutCovers layout (.regions rs) = true)
    (outputsSafe : ∀ a ∈ outputs, a < layoutLimit layout) (s : State) (x y : Int) :
    let machine := (lower layout (.regions rs)).machine
    ∃ result, (schedule layout (.regions rs)).schedule.Eval machine.capacity
      ⟨s,(fun n => if n = 0 then x else if n = 1 then y else 0),fun _ => []⟩ result ∧
      result.map (fun p => PipelineUse.observe outputs p.data) =
        (HybridRegions.eval x y rs s).map (PipelineUse.observe outputs) := by
  let sizes := fun a => ((layout.toList.find? (fun p => p.1 == a)).map Prod.snd).getD 0
  let b : Build := { memories := layout, nextArray := layoutLimit layout }
  let p : Payload := ⟨s,(fun n => if n = 0 then x else if n = 1 then y else 0),fun _ => []⟩
  have safe : ∀ r ∈ rs, r.array < b.nextArray ∧ ∀ a ∈ allCommandArrays r.code.body.target, a < b.nextArray := by
    intro r hr
    constructor
    · exact source_layout_bound covered (List.mem_flatMap.mpr ⟨r,hr,by simp⟩)
    · intro a ha
      exact source_layout_bound covered (List.mem_flatMap.mpr ⟨r,hr,by simp [ha]⟩)
  obtain ⟨r,hr,ho⟩ := regionsCode_correct (x:=x) (y:=y) (limit:=b.nextArray) sizes rs b p (by change 2 ≤ 2; omega) (Nat.le_refl _) safe rfl (by simp [p])
  refine ⟨r,hr,?_⟩
  have projected := congrArg (Option.map (PipelineUse.observe outputs)) ho
  simpa only [Option.map_map,Function.comp_def,b,p,observe_trim outputsSafe] using projected

end IRComparison.Circuit
