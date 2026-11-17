import IRComparison.Circuit.CountedCapacity

namespace IRComparison.Circuit

abbrev WindowLoader := Nat → List Int → List Int → Option (List Int × List Int)
abbrev WindowBody := Nat → State → List Int → List Int → Option (State × List Int)

def iterationStep (load : WindowLoader) (body : WindowBody) (j : Nat) (state : WindowState) : Option WindowState := do
  let (s,old,qi,qo) := state
  let (values,rest) ← load j old qi
  let (t,out) ← body j s qo values
  return (t,values,rest,out)

def iterationLoop (load : WindowLoader) (body : WindowBody) : Nat → Nat → List Int → State → List Int → List Int → Option (State × List Int × List Int)
  | 0,_,_,s,qi,qo => some (s,qi,qo)
  | n+1,j,values,s,qi,qo => do
      let (t,out) ← body j s qo values
      match n with
      | 0 => return (t,qi,out)
      | m+1 => do
          let (next,rest) ← load (j+1) values qi
          iterationLoop load body (m+1) (j+1) next t rest out

def iterationEval (load : WindowLoader) (body : WindowBody) (count : Nat) (s : State) (qi qo : List Int) :=
  match count with
  | 0 => some (s,qi,qo)
  | n+1 => do
      let (values,rest) ← load 0 [] qi
      iterationLoop load body (n+1) 0 values s rest qo

theorem iterationLoop_fold (load : WindowLoader) (body : WindowBody) (n k : Nat)
    (values : List Int) (s : State) (qi qo : List Int) :
    iterationLoop load body (n+1) k values s qi qo = do
      let (t,out) ← body k s qo values
      let (u,_,rest,output) ← (List.range' (k+1) n).foldlM (fun st j => iterationStep load body j st) (t,values,qi,out)
      return (u,rest,output) := by
  induction n generalizing k values s qi qo with
  | zero => rfl
  | succ n ih =>
    rw [iterationLoop]
    simp only [List.range'_succ,List.foldlM_cons]
    cases hb : body k s qo values with
    | none => rfl
    | some pair =>
      obtain ⟨t,out⟩ := pair
      simp only [bind,Option.bind,iterationStep]
      cases hl : load (k+1) values qi with
      | none => rfl
      | some pair =>
        obtain ⟨next,rest⟩ := pair
        simp only [bind,Option.bind]
        rw [ih]
        cases body (k+1) t out next <;> rfl

theorem iterationEval_fold (load : WindowLoader) (body : WindowBody) (count : Nat)
    (s : State) (qi qo : List Int) :
    iterationEval load body count s qi qo =
      ((List.range' 0 count).foldlM (fun st j => iterationStep load body j st) (s,[],qi,qo)).map
        (fun (t,_,rest,out) => (t,rest,out)) := by
  cases count with
  | zero => rfl
  | succ n =>
    simp only [iterationEval,List.range'_succ,List.foldlM_cons,iterationStep]
    cases load 0 [] qi with
    | none => rfl
    | some pair =>
      obtain ⟨values,rest⟩ := pair
      simp only [bind,Option.bind]
      rw [iterationLoop_fold]
      cases body 0 s qo values with
      | none => rfl
      | some pair =>
        obtain ⟨t,out⟩ := pair
        simp only [bind,Option.bind]
        change _ = ((List.range' 1 n).foldlM (fun st j => iterationStep load body j st) (t,values,rest,out)).map _
        cases (List.range' 1 n).foldlM (fun st j => iterationStep load body j st) (t,values,rest,out) <;> rfl

theorem fifoLoads_at (ls : List CompactRouting.Load) :
    (ls.map fromFIFOLoad).map (Load.at i) = CompactRouting.instantiate i ls := by
  simp only [List.map_map,CompactRouting.instantiate]
  apply List.map_congr_left
  intro l _; cases l <;> rfl

theorem memoryLoads_at (ls : List SymbolicWindowSchedule.Load) :
    (ls.map fromMemoryLoad).map (Load.at i) = HybridSymbolicWindowControl.instantiate i ls := by
  simp only [List.map_map,HybridSymbolicWindowControl.instantiate]
  apply List.map_congr_left
  intro l _; cases l <;> rfl

def fifoLoader (start stride : Int) (initial refill : List CompactRouting.Load) : WindowLoader :=
  fun j old q => WindowFIFO.execute (fun _ => none) old
    (CompactRouting.instantiate (start+(j:Int)*stride) (if j = 0 then initial else refill)) q

theorem sourceCountedStep_fifo (start stride x y : Int) (initial refill : List CompactRouting.Load)
    (body : HybridIR.Cmd) (j : Nat) (state : WindowState) :
    sourceCountedStep input start stride x y (initial.map fromFIFOLoad) (refill.map fromFIFOLoad) body j state =
      iterationStep (fifoLoader start stride initial refill) (fun j s q vs => body.eval (start+(j:Int)*stride) x y s q vs) j state := by
  obtain ⟨s,old,qi,qo⟩ := state
  simp only [sourceCountedStep,iterationStep,fifoLoader]
  by_cases hz : j = 0 <;> simp only [hz,↓reduceIte,fifoLoads_at,HybridCompactFIFO.execute_input (other:=fun _ => none)]

end IRComparison.Circuit
