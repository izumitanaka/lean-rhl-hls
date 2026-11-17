import IRComparison.Circuit.SystemVerilog.SerializationSound

namespace IRComparison.Circuit.SystemVerilog

/-- A mathematical list of simultaneous scalar updates. RHS values have
already been sampled at the edge; later writes to the same name win. -/
def Store.patch (s : Store) (updates : List (Name × Int)) : Store :=
  updates.foldl (fun pending entry => pending.setScalar entry.1 entry.2) s

@[simp] theorem Store.patch_nil (s : Store) : s.patch [] = s := rfl
@[simp] theorem Store.patch_cons (s : Store) (n : Name) (v : Int) (rest) :
    s.patch ((n,v)::rest) = (s.setScalar n v).patch rest := rfl
@[simp] theorem Store.patch_append (s : Store) (xs ys) :
    s.patch (xs ++ ys) = (s.patch xs).patch ys := List.foldl_append
@[simp] theorem Store.patch_cell (s : Store) (xs) (n : Name) (j) :
    (s.patch xs).cell n j = s.cell n j := by
  induction xs generalizing s with
  | nil => rfl
  | cons e rest ih => exact ih _

/-- If all writes to a name agree, its final value is independent of their
order and multiplicity. This is used for clear/initialization lists. -/
theorem Store.patch_scalar (s : Store) (xs : List (Name × Int)) (name : Name)
    (value : Int) (consistent : ∀ e ∈ xs, e.1 = name → e.2 = value) :
    (s.patch xs).scalar name =
      if xs.any (fun e => decide (e.1 = name)) then some value else s.scalar name := by
  induction xs generalizing s with
  | nil => rfl
  | cons e rest ih =>
    rw [show s.patch (e::rest) = (s.setScalar e.1 e.2).patch rest from rfl,
      ih _ (fun x hx => consistent x (by simp [hx]))]
    by_cases selected : e.1 = name
    · have val := consistent e (by simp) selected
      simp [List.any_cons,selected,val,Store.setScalar]
    · have hf : decide (e.1 = name) = false := by simp only [decide_eq_false_iff_not]; exact selected
      simp only [List.any_cons,hf,Bool.false_or,Store.setScalar,if_neg (Ne.symm selected)]

@[simp] theorem sequence_nil_eval (env : Environment) (s : Store) :
    (sequence []).eval env s = some s := rfl
@[simp] theorem sequence_cons_eval (x : Statement) (xs) (env : Environment) (s : Store) :
    (sequence (x::xs)).eval env s = (x.eval env s).bind (fun next => (sequence xs).eval env next) := rfl

theorem sequence_eval (xs : List Statement) (env : Environment) (s : Store) :
    (sequence xs).eval env s = xs.foldlM (fun p c => c.eval env p) s := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [sequence_cons_eval,List.foldlM_cons,ih]; rfl

theorem sequence_map_eval (xs : List α) (code : α → Statement) (update : Store → α → Store)
    (each : ∀ x ∈ xs, ∀ s, (code x).eval env s = some (update s x)) (s : Store) :
    (sequence (xs.map code)).eval env s = some (xs.foldl update s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    change ((code x).eval env s).bind _ = _
    rw [each x (by simp)]
    exact ih (fun y hy => each y (by simp [hy])) _

@[simp] theorem sequence_append_eval (xs ys : List Statement) (env : Environment) (s : Store) :
    (sequence (xs ++ ys)).eval env s =
      ((sequence xs).eval env s).bind ((sequence ys).eval env) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,sequence_cons_eval,ih,Option.bind_assoc]

theorem write_integer_eval (env : Environment) (name : Name) (n : Nat) (s : Store) :
    (write name (.integer n)).eval env s =
      some (s.setScalar name (BitVec.ofNat (env.type name).width n).toNat) := by
  simpa [write] using Statement.assign_signed (SignedMeaning.integer (env:=env) n) name s

theorem write_bit_eval (env : Environment) (name : Name) (b : Bool)
    (width : (env.type name).width = 1) (s : Store) :
    (write name (.bit b)).eval env s = some (s.setScalar name (if b then 1 else 0)) :=
  Statement.assign_boolean (BooleanMeaning.bit b) width s

/-- Bit-vector truncation is explicit here, including PC, array lengths and
holding registers. This specification does not evaluate Statement or text. -/
def startUpdates (a : Artifact) (env : Environment) (x y : BitVec 32) : List (Name × Int) :=
  ([(Name.busy,1),(Name.done,0),(Name.error,0),
   (Name.pc,(BitVec.ofNat (env.type .pc).width a.machine.entry).toNat),
   (Name.holding 0,(BitVec.ofInt (env.type (.holding 0)).width x.toNat).toNat),
   (Name.holding 1,(BitVec.ofInt (env.type (.holding 1)).width y.toNat).toNat)] : List (Name × Int)) ++
  ((List.range a.wires.size).drop 2).map (fun n => (Name.holding n,(0 : Int))) ++
  a.originalMemories.toList.map (fun (id,size) =>
    (Name.length id,((BitVec.ofNat (env.type (.length id)).width size).toNat : Int))) ++
  a.machine.capacities.toList.map (fun (q,_) => (Name.used q,(0 : Int)))

 theorem startCode_eval (a : Artifact) (r : FiniteRuntime a.storageShape)
    (wires : Array Wire) (busy : Bool) (ports : RTL.Ports) (s : Store) :
    let env := environment a r wires #[] busy ports
    (startCode a).eval env s = some (s.patch (startUpdates a env ports.x ports.y)) := by
  let env := environment a r wires #[] busy ports
  have port (p : Name) (v : BitVec 32) (ty : env.type p = ⟨32,false⟩)
      (rd : env.scalar p = some (v.toNat : Int)) (n : Name) (pending : Store) :
      (write n (.unsigned (.reference p))).eval env pending =
        some (pending.setScalar n (BitVec.ofInt (env.type n).width v.toNat).toNat) :=
    Statement.assign_signed (unsigned_reference_meaning ty rd (by simp)) _ _
  have clears (xs : List Nat) (name : Nat → Name) (pending : Store) :
      (sequence (xs.map fun n => write (name n) (.integer 0))).eval env pending =
        some (pending.patch (xs.map fun n => (name n,0))) := by
    rw [sequence_map_eval xs _ (fun p n => p.setScalar (name n) 0)
      (by intro n hn p; simpa using write_integer_eval env (name n) 0 p)]
    simp [Store.patch,List.foldl_map]
  have lengths (xs : List (Nat × Nat)) (pending : Store) :
      (sequence (xs.map fun (id,size) => write (.length id) (.integer size))).eval env pending =
        some (pending.patch (xs.map fun (id,size) =>
          (Name.length id,(BitVec.ofNat (env.type (.length id)).width size).toNat))) := by
    rw [sequence_map_eval xs _ _ (by intro e he p; exact write_integer_eval env (.length e.1) e.2 p)]
    simp [Store.patch,List.foldl_map]
  have queues (pending : Store) :
      (sequence (a.machine.capacities.toList.map fun (q,_) => write (.used q) (.integer 0))).eval env pending =
        some (pending.patch (a.machine.capacities.toList.map fun (q,_) => (Name.used q,0))) := by
    rw [sequence_map_eval _ _ (fun p e => p.setScalar (.used e.1) 0)
      (by intro e he p; simpa using write_integer_eval env (.used e.1) 0 p)]
    simp [Store.patch,List.foldl_map]
  change (startCode a).eval env s = _
  simp only [startCode,sequence_append_eval]
  simp only [sequence_cons_eval,sequence_nil_eval,
    write_bit_eval env .busy true rfl,write_bit_eval env .done false rfl,
    write_bit_eval env .error false rfl,write_integer_eval,
    port .x ports.x rfl rfl,port .y ports.y rfl rfl,Option.bind_some]
  rw [clears,Option.bind_some,lengths,Option.bind_some,queues]
  simp [startUpdates,Store.patch_append,Store.patch_cons,Store.patch_nil,env]


/-- Original interface lengths must fit the physical allocation, and repeated
metadata for a name must agree. These are layout obligations, not assumptions
about input values or execution. -/
def StartupLayout (a : Artifact) : Prop :=
  ∀ e ∈ a.originalMemories.toList,
    RTL.originalSize a e.1 = some e.2 ∧ e.2 ≤ a.storageShape.memorySize e.1

theorem Store.patch_unwritten (s : Store) (xs : List (Name × Int)) (name : Name)
    (absent : ∀ e ∈ xs, e.1 ≠ name) : (s.patch xs).scalar name = s.scalar name := by
  rw [s.patch_scalar xs name 0 (fun e he eq => False.elim (absent e he eq))]
  have no : xs.any (fun e => decide (e.1 = name)) = false := by
    simp only [List.any_eq_false,decide_eq_true_eq]
    exact absent
  simp only [no,Bool.false_eq_true,↓reduceIte]

theorem Store.patch_constant (s : Store) (xs : List α) (name : α → Name) (v : Int) (n : Name) :
    (s.patch (xs.map fun x => (name x,v))).scalar n =
      if ∃ x ∈ xs, name x = n then some v else s.scalar n := by
  rw [s.patch_scalar _ n v (by simp)]
  simp only [List.any_map,List.any_eq_true,decide_eq_true_eq,Function.comp_def]

/-- Lookup of original memory metadata is used only for the length register;
startup retains every physical data cell. -/
theorem original_length_patch (a : Artifact) (layout : StartupLayout a) (env : Environment)
    (widths : ∀ n, (env.type (.length n)).width = bits (a.storageShape.memorySize n))
    (s : Store) (n : Nat) :
    (s.patch (a.originalMemories.toList.map fun (id,size) =>
      (Name.length id,((BitVec.ofNat (env.type (.length id)).width size).toNat : Int)))).scalar (.length n) =
      match RTL.originalSize a n with | none => s.scalar (.length n) | some size => some size := by
  cases found : RTL.originalSize a n with
  | none =>
    apply Store.patch_unwritten
    intro e he eq
    obtain ⟨⟨id,size⟩,hm,rfl⟩ := List.mem_map.mp he
    simp only [Name.length.injEq] at eq
    subst id
    have := (layout (n,size) hm).1
    rw [found] at this
    contradiction
  | some size =>
    have consistent : ∀ e ∈ a.originalMemories.toList, e.1 = n → e.2 = size := by
      intro e he eq
      have := (layout e he).1
      rw [eq,found] at this
      exact Option.some.inj this.symm
    rw [s.patch_scalar _ (.length n) size (by
      intro e he eq
      obtain ⟨⟨id,k⟩,hm,rfl⟩ := List.mem_map.mp he
      simp only [Name.length.injEq] at eq
      subst id
      have hsize := consistent (n,k) hm rfl
      change k = size at hsize
      subst k
      dsimp only
      rw [widths,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
      exact Nat.lt_of_le_of_lt (layout (n,size) hm).2 (bits_fits _))]
    have existsEntry : ∃ e ∈ a.originalMemories.toList, e.1 = n := by
      unfold RTL.originalSize at found
      cases f : a.originalMemories.toList.find? (fun p => p.1 == n) with
      | none => simp [f] at found
      | some e =>
        exact ⟨e,List.mem_of_find?_eq_some f,by simpa using List.find?_some f⟩
    simp only [List.any_map,Function.comp_def,Name.length.injEq,List.any_eq_true,decide_eq_true_eq]
    simp only [existsEntry,↓reduceIte]


theorem original_patch_lookup (a : Artifact) (layout : StartupLayout a) (env : Environment)
    (widths : ∀ n, (env.type (.length n)).width = bits (a.storageShape.memorySize n))
    (s : Store) (name : Name) :
    (s.patch (a.originalMemories.toList.map fun e =>
      (Name.length e.1,((BitVec.ofNat (env.type (.length e.1)).width e.2).toNat : Int)))).scalar name =
      match name with
      | .length n => match RTL.originalSize a n with | none => s.scalar name | some size => some size
      | _ => s.scalar name := by
  cases name
  case length n => exact original_length_patch a layout env widths s n
  all_goals apply Store.patch_unwritten; intro e he; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he; simp

def startScalar (a : Artifact) (env : Environment) (x y : BitVec 32) (s : Store) : Name → Option Int
  | .busy => some 1
  | .done | .error => some 0
  | .pc => some (BitVec.ofNat (env.type .pc).width a.machine.entry).toNat
  | .holding n => if n = 0 then some (BitVec.ofInt (env.type (.holding 0)).width x.toNat).toNat
      else if n = 1 then some (BitVec.ofInt (env.type (.holding 1)).width y.toNat).toNat
      else if n < a.wires.size then some 0 else s.scalar (.holding n)
  | .length n => match RTL.originalSize a n with | none => s.scalar (.length n) | some size => some size
  | .used n => if ∃ e ∈ a.machine.capacities.toList, e.1 = n then some 0 else s.scalar (.used n)
  | name => s.scalar name

theorem startUpdates_scalar (a : Artifact) (layout : StartupLayout a) (env : Environment)
    (widths : ∀ n, (env.type (.length n)).width = bits (a.storageShape.memorySize n))
    (s : Store) (x y : BitVec 32) (name : Name) :
    (s.patch (startUpdates a env x y)).scalar name = startScalar a env x y s name := by
  simp only [startUpdates,Store.patch_append]
  rw [Store.patch_constant,original_patch_lookup a layout env widths,Store.patch_constant]
  cases name <;> simp [startScalar,Store.patch_cons,Store.patch_nil,Store.setScalar]
  case used n => simp only [Name.used.injEq]
  case holding n =>
    have mem : n ∈ (List.range a.wires.size).drop 2 ↔ 2 ≤ n ∧ n < a.wires.size := by
      simp only [List.range_eq_range',List.drop_range',Nat.zero_add,Nat.mul_one,List.mem_range'_1]; omega
    simp only [mem]
    by_cases z : n = 0
    · subst n; simp
    · by_cases o : n = 1
      · subst n; simp
      · have two : 2 ≤ n := by omega
        simp [z,o,two]


theorem start_commit (a : Artifact) (layout : StartupLayout a)
    (r : FiniteRuntime a.storageShape) (wires : Array Wire) (busy : Bool) (ports : RTL.Ports) :
    let env := environment a r wires #[] busy ports
    (env.store.patch (startUpdates a env ports.x ports.y)).commit a.storageShape =
      RTL.beginInvocation a r ports.x ports.y := by
  let env := environment a r wires #[] busy ports
  have scalar (name : Name) := startUpdates_scalar a layout env (fun _ => rfl) env.store ports.x ports.y name
  change (env.store.patch (startUpdates a env ports.x ports.y)).commit a.storageShape = _
  have store : env.store.patch (startUpdates a env ports.x ports.y) =
      ⟨startScalar a env ports.x ports.y env.store,env.store.cell⟩ := by
    cases hs : env.store.patch (startUpdates a env ports.x ports.y) with
    | mk ss cc =>
      congr 1
      · funext name
        have h := scalar name
        rw [hs] at h
        exact h
      · funext name j
        have h := Store.patch_cell env.store (startUpdates a env ports.x ports.y) name j
        rw [hs] at h
        exact h
  rw [store]
  unfold Store.commit
  simp only [startUpdates_scalar a layout (environment a r wires #[] busy ports) (fun _ => rfl),Store.patch_cell,startScalar,Option.getD_some]
  unfold RTL.beginInvocation RTL.restoreLengths
  congr 1
  · change BitVec.ofInt _ ((BitVec.ofNat (bits (a.storageShape.states-1)) a.machine.entry).toNat : Int) = _
    simp only [BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · funext n
    simp [env,Environment.store,environment,environmentFor,n.isLt]
  · funext n
    dsimp only
    have alternatives : RTL.originalSize a n.val = none ∨ ∃ size, RTL.originalSize a n.val = some size := by
      cases RTL.originalSize a n.val <;> simp
    rcases alternatives with found | ⟨size,found⟩
    ·
      have bound := (r.arrays n).used.isLt
      have used : min (r.arrays n).used.val (a.storageShape.memorySize n.val) = (r.arrays n).used.val := by omega
      simp [found,env,Environment.store,environment,environmentFor,n.isLt,used]
    · simp [found,env,Environment.store,environment,environmentFor,n.isLt]
  · funext n
    have inside : n.val < a.wires.size := n.isLt
    by_cases z : n.val = 0
    · simp only [if_pos z,env,environment,environmentFor]
      have hw : signedWidth (a.storageShape.wireRange 0) = signedWidth (a.storageShape.wireRange n.val) := congrArg (fun i => signedWidth (a.storageShape.wireRange i)) z.symm
      rw [hw]
      simp only [Option.getD_some,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    · by_cases o : n.val = 1
      · simp only [if_neg z,if_pos o,env,environment,environmentFor]
        have hw : signedWidth (a.storageShape.wireRange 1) = signedWidth (a.storageShape.wireRange n.val) := congrArg (fun i => signedWidth (a.storageShape.wireRange i)) o.symm
        rw [hw]
        simp only [Option.getD_some,BitVec.ofInt_natCast,BitVec.ofNat_toNat,BitVec.setWidth_eq]
      · simp [z,o,inside,env,environment,environmentFor]
  · funext q
    by_cases declared : ∃ e ∈ a.machine.capacities.toList, e.1 = q.val
    · simp only [if_pos declared]
      simp [env,Environment.store,environment,environmentFor,q.isLt]
    · have absent : a.machine.capacities.toList.find? (fun e => e.1 == q.val) = none := by
        apply List.find?_eq_none.mpr
        intro e he
        simp only [beq_iff_eq]
        exact fun eq => declared ⟨e,he,eq⟩
      have cap : a.storageShape.queueSize q.val = 0 := by
        simp [Artifact.storageShape,Machine.capacity,absent]
      have zero : (r.queues q).used.val = 0 := by have := (r.queues q).used.isLt; omega
      simp only [if_neg declared]
      simp [env,Environment.store,environment,environmentFor,q.isLt,cap,zero]
      funext j
      have := j.isLt
      omega

theorem start_busy (a : Artifact) (layout : StartupLayout a)
    (r : FiniteRuntime a.storageShape) (wires : Array Wire) (busy : Bool) (ports : RTL.Ports) :
    let env := environment a r wires #[] busy ports
    (env.store.patch (startUpdates a env ports.x ports.y)).busy = true := by
  dsimp only
  unfold Store.busy
  rw [startUpdates_scalar a layout (environment a r wires #[] busy ports) (fun _ => rfl)]
  rfl


theorem interface_startup_layout (h : RTL.InterfaceLayout a) : StartupLayout a :=
  fun e he => ⟨(h.1 e he).1,(h.1 e he).2.2⟩

/-- Successful production emission carries the static layout contract. This
is a metadata check, not per-input validation of the transformation proof. -/
theorem emitted_interface_layout (h : emit a outputs = .ok text) : RTL.InterfaceLayout a := by
  obtain ⟨code,generated,_⟩ := emit_module h
  have checked : checkModuleArtifact a = .ok () := by
    unfold generateModule at generated
    cases hc : checkModuleArtifact a with
    | error why => simp [hc,bind,Except.bind] at generated
    | ok u => cases u; rfl
  change InterfaceLayout a
  by_cases good : InterfaceLayout a
  · exact good
  · simp [checkModuleArtifact,good,bind,Except.bind] at checked

theorem moduleCode_start (a : Artifact) (layout : StartupLayout a)
    (outputs : List Nat) (cases : List Statement) (wires : Array Wire)
    (r : RTL.InterfaceState a.storageShape) (ports : RTL.Ports)
    (idle : r.busy = false) (noReset : ports.reset = false) (starts : ports.start = true) :
    (moduleCode a outputs cases wires).tick a.storageShape ports r =
      some ⟨RTL.beginInvocation a r.core ports.x ports.y,true⟩ := by
  rw [moduleCode_tick]
  unfold physicalTick clockCode
  rw [idle,RTL.controller_start ports noReset starts]
  simp only [bind,Option.bind,pure]
  rw [startCode_eval]
  simp only [bind,Option.bind,pure,start_commit a layout,start_busy a layout]

def tickText (text : String) (shape : StorageShape) (ports : RTL.Ports)
    (r : RTL.InterfaceState shape) : Option (RTL.InterfaceState shape) :=
  (Concrete.parseModule text).bind (fun code => code.tick shape ports r)

/-- The generated start edge is included, not assumed to have happened. -/
theorem emitted_text_start (emitted : emit a outputs = .ok text)
    (r : RTL.InterfaceState a.storageShape) (ports : RTL.Ports)
    (idle : r.busy = false) (noReset : ports.reset = false) (starts : ports.start = true) :
    tickText text a.storageShape ports r = some ⟨RTL.beginInvocation a r.core ports.x ports.y,true⟩ := by
  obtain ⟨code,parsed,generated,_,readback,_,_,ticks,_⟩ := emit_text_correct emitted
  obtain ⟨cases,es,_,same⟩ := generateModule_components generated
  simp only [tickText,readback,Option.bind_some,ticks,same]
  exact moduleCode_start a (interface_startup_layout (emitted_interface_layout emitted)) _ _ _ _ _ idle noReset starts

/-- Source-to-text theorem including the actual start port edge. The
external environment is responsible only for supplying inputs and obeying
the idle/start protocol; the generated receiver and computation are proved. -/
theorem emitted_text_invocation_readout (p : HybridWord.Plan outputs sizes ks)
    (compiled : compile layout (HybridUnifiedPipeline.lower p) = .ok checked)
    (emitted : emit checked.artifact outputs = .ok text)
    (outputsSafe : ∀ id ∈ outputs, id < layoutLimit layout)
    (outputPorts : ∀ id ∈ outputs, checked.artifact.storageShape.hasMemory id)
    (r : RTL.InterfaceState checked.artifact.storageShape) (ports : RTL.Ports)
    (idle : r.busy = false) (noReset : ports.reset = false) (starts : ports.start = true)
    (sized : PipelineShapes.Layout sizes (RTL.restoreLengths checked.artifact r.core).inputSource.encode)
    (ready : p.Ready (HybridWord.encode ports.x) (HybridWord.encode ports.y)
      (RTL.restoreLengths checked.artifact r.core).inputSource.encode) :
    let a := checked.artifact
    let s := (RTL.restoreLengths a r.core).inputSource
    ∃ cycles result,
      ((tickText text a.storageShape ports r).bind (runText text a.storageShape cycles)) = some result ∧
      result.core.done = true ∧ result.busy = false ∧
      (∀ final, HybridWord.source ports.x ports.y ks s = some final →
        result.core.error = false ∧ ∀ request,
          readText text a.storageShape result.core request = some (stateReadResult a outputs final.encode request)) ∧
      (HybridWord.source ports.x ports.y ks s = none → result.core.error = true) := by
  dsimp only
  rw [emitted_text_start emitted r ports idle noReset starts]
  exact emitted_text_pipeline_readout p compiled emitted outputsSafe outputPorts r.core ports.x ports.y sized ready

end IRComparison.Circuit.SystemVerilog
