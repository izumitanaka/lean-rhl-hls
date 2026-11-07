import IRComparison.Circuit.SystemVerilog.TestSound

namespace IRComparison.Circuit.SystemVerilog

/-- Executed scalar reads follow the validity/nonempty guards already
present in RTL.lowerNode. These premises do not restrict source syntax. -/
def ScalarReady (shape : StorageShape) (runtime : Runtime) : RTL.Scalar RTL.Combinational → Prop
  | .literal _ => True
  | .value e => e.valid.eval runtime = true
  | .queueHead q => q < shape.queues ∧ runtime.queues q ≠ []

theorem Statement.assign_signed (meaning : SignedMeaning env rhs width n) (target : Name) (pending : Store) :
    (Statement.assign (.reference target) rhs).eval env pending =
      some (pending.setScalar target (BitVec.ofInt (env.type target).width n).toNat) := by
  simp only [Statement.eval,Destination.write,meaning.assignment,bind,Option.bind,pure]

theorem Statement.assign_index_signed (address : SignedMeaning env jExpr jw j) (nonnegative : 0 ≤ j)
    (meaning : SignedMeaning env rhs width n) (allocated : (env.cell target j.toNat).isSome = true)
    (pending : Store) :
    (Statement.assign (.index target jExpr) rhs).eval env pending =
      some (pending.setCell target j.toNat (BitVec.ofInt (env.type target).width n).toNat) := by
  obtain ⟨old,stored⟩ := Option.isSome_iff_exists.mp allocated
  simp only [Statement.eval,Destination.write,address.self,bind,Option.bind,Value.integer,Value.ofInt,
    ↓reduceIte,address.fits,show ¬j < 0 by omega,stored,meaning.assignment,pure]

theorem BooleanMeaning.assignment_one (meaning : BooleanMeaning env rhs b) :
    rhs.assignment env 1 = some (BitVec.ofNat 1 (if b then 1 else 0)) := by
  unfold Expr.assignment
  rw [meaning.typed]
  have context : rhs.eval env (some ⟨1,false⟩) = some (truth b) := by
    rw [← meaning.typed,← rhs.eval_self]
    exact meaning.evaluated
  rw [context]
  cases b <;> rfl

theorem Statement.assign_boolean (meaning : BooleanMeaning env rhs b)
    (width : (env.type target).width = 1) (pending : Store) :
    (Statement.assign (.reference target) rhs).eval env pending =
      some (pending.setScalar target (if b then 1 else 0)) := by
  simp only [Statement.eval,Destination.write,bind,Option.bind,pure]
  rw [width,meaning.assignment_one]
  cases b <;> rfl

/-- The FIFO head is read from the old physical bank, independently of
pending writes at the same clock edge. Nonemptiness establishes allocation. -/
theorem finite_head_meaning (a : Artifact) (r : FiniteRuntime a.storageShape) (final : Emission) (values : Array Int)
    (inside : q < a.storageShape.queues) (nonempty : r.decode.queues q ≠ []) :
    SignedMeaning ((environment a r final.text #[]).withTemporaries values)
      (.unsigned (.index (.queue q) (.integer 0))) 33 ((r.decode.queues q).headD 0) := by
  have positive : 0 < (r.queues ⟨q,inside⟩).used.val := by
    have pos := List.length_pos_iff.mpr nonempty
    simpa only [FiniteRuntime.decode,inside,↓reduceDIte,WordBuffer.contents,Array.length_toList,Array.size_ofFn] using pos
  have allocated : 0 < a.storageShape.queueSize q := by
    have used : (r.queues ⟨q,inside⟩).used.val < a.storageShape.queueSize q+1 := (r.queues ⟨q,inside⟩).used.isLt
    omega
  have head : (r.decode.queues q).headD 0 = ((r.queues ⟨q,inside⟩).cells ⟨0,allocated⟩).toNat := by
    simp [FiniteRuntime.decode,inside,WordBuffer.contents,List.headD_eq_head?_getD,List.head?_eq_getElem?,
      Array.getElem?_ofFn,positive]
  rw [head]
  apply unsigned_index_meaning (w:=32) (jw:=bits 0+1) (j:=0) rfl (SignedMeaning.integer 0) (by omega)
  · simp [environment,environmentFor,Environment.withTemporaries,inside,allocated]
  · simp

/-- Every scalar RHS emitted on a valid executed path denotes the reference
RTL scalar value. Width truncation is applied only by the destination write. -/
theorem scalarCode_correct (a : Artifact) (r : FiniteRuntime a.storageShape) (final : Emission) (values : Array Int)
    (rhs : RTL.Scalar RTL.Combinational) (closed : ScalarReferences a.storageShape rhs)
    (ready : ScalarReady a.storageShape r.decode rhs) (good : before.WellFormed)
    (success : scalarCode a rhs before = .ok (expr,after)) (grows : after.Extends final)
    (meaning : CacheMeaning ((environment a r final.text #[]).withTemporaries values) r.decode final) :
    ∃ width, SignedMeaning ((environment a r final.text #[]).withTemporaries values) expr width
      (rhs.evalWith RTL.Combinational.eval r.decode) := by
  cases rhs with
  | literal n =>
    obtain ⟨rfl,_⟩ := pure_success (Expr.literal (bits n.natAbs+2) n (by omega)) success
    have bounds := termTemplate_literal a n (env:=((environment a r final.text #[]).withTemporaries values)) rfl
    exact ⟨_,SignedMeaning.literal (by omega) bounds.fits⟩
  | value e =>
    rw [scalarCode] at success
    obtain ⟨signal,compiled,rfl⟩ := return_success (expression a e) (fun signal => Expr.reference signal.name) success
    have data := (expression_correct a r final values e closed good compiled grows meaning).1
    exact ⟨_,by simpa only [RTL.Scalar.evalWith,RTL.Combinational.eval,
      show e.valid.eval r.decode = true from ready,↓reduceIte,Option.getD_some] using data⟩
  | queueHead q =>
    rw [scalarCode] at success
    obtain ⟨ignored,middle,required,remaining⟩ := bind_success _ _ success
    obtain ⟨rfl,_⟩ := pure_success (Expr.unsigned (.index (.queue q) (.integer 0))) remaining
    exact ⟨33,finite_head_meaning a r final values ready.1 ready.2⟩

/-- Expected bit-pattern update of a scalar destination. `done` also drives
the existing interface busy flag. All other pending storage is preserved. -/
def Store.writeRegister (pending : Store) (env : Environment) (target : RTL.Register) (n : Int) : Store :=
  match target with
  | .pc => pending.setScalar .pc (BitVec.ofInt (env.type .pc).width n).toNat
  | .wire k => pending.setScalar (.holding k) (BitVec.ofInt (env.type (.holding k)).width n).toNat
  | .data k => pending.setScalar (.register k) (BitVec.ofInt (env.type (.register k)).width n).toNat
  | .done => (pending.setScalar .done (if n != 0 then 1 else 0)).setScalar .busy (if n == 0 then 1 else 0)
  | .error => pending.setScalar .error (if n != 0 then 1 else 0)

/-- Correctness of the actual scalar-assignment output pass, for every
destination and scalar RHS, including FIFO reception and completion flags. -/
theorem statementCode_assign_correct (a : Artifact) (r : FiniteRuntime a.storageShape)
    (final : Emission) (values : Array Int) (target : RTL.Register) (rhs : RTL.Scalar RTL.Combinational)
    (closed : ScalarReferences a.storageShape rhs) (ready : ScalarReady a.storageShape r.decode rhs)
    (good : before.WellFormed) (success : statementCode a (.assign target rhs) before = .ok (code,after))
    (grows : after.Extends final)
    (meaning : CacheMeaning ((environment a r final.text #[]).withTemporaries values) r.decode final)
    (pending : Store) :
    let env := (environment a r final.text #[]).withTemporaries values
    code.eval env pending = some (pending.writeRegister env target (rhs.evalWith RTL.Combinational.eval r.decode)) := by
  rw [statementCode] at success
  obtain ⟨expr,middle,compiled,rest⟩ := bind_success _ _ success
  have middleGrows : middle.Extends after := by
    have middleGood := (preserves_scalarCode a rhs before good expr middle compiled).1
    cases target <;> cases rhs <;>
      first
      | exact (preserves_pure _ middle middleGood code after rest).2.1
      | exact (preserves_bind _ _ (preserves_require _ _) (fun _ => preserves_pure _)
          middle middleGood code after rest).2.1
      | exact (preserves_bind _ _ (preserves_wordValue _ _) (fun _ => preserves_pure _)
          middle middleGood code after rest).2.1
      | exact (preserves_bind _ _ (preserves_pure _) (fun _ => preserves_pure _)
          middle middleGood code after rest).2.1
  obtain ⟨width,value⟩ := scalarCode_correct a r final values rhs closed ready good compiled (middleGrows.trans grows) meaning
  cases target with
  | pc =>
    obtain ⟨rfl,_⟩ := pure_success _ rest
    exact Statement.assign_signed value _ pending
  | wire k =>
    obtain ⟨ignored,last,required,returned⟩ := bind_success _ _ rest
    obtain ⟨rfl,_⟩ := pure_success _ returned
    exact Statement.assign_signed value _ pending
  | data k =>
    cases rhs <;>
      obtain ⟨ignored,last,checked,returned⟩ := bind_success _ _ rest <;>
      obtain ⟨rfl,_⟩ := pure_success _ returned <;>
      exact Statement.assign_signed value _ pending
  | error =>
    obtain ⟨rfl,_⟩ := pure_success _ rest
    exact Statement.assign_boolean
      (value.boolean_comparison (SignedMeaning.integer 0) (op:=.ne) rfl (by simp [arithmetic])) rfl pending
  | done =>
    obtain ⟨rfl,_⟩ := pure_success _ rest
    have nonzero := value.boolean_comparison (SignedMeaning.integer 0) (op:=.ne) rfl
      (result:=rhs.evalWith RTL.Combinational.eval r.decode != 0) (by simp [arithmetic])
    have zero := value.boolean_comparison (SignedMeaning.integer 0) (op:=.eq) rfl
      (result:=rhs.evalWith RTL.Combinational.eval r.decode == 0) (by simp [arithmetic])
    simp only [Statement.seq_eval,Statement.assign_boolean (target:=.done) nonzero rfl,Option.bind,
      Statement.assign_boolean (target:=.busy) zero rfl,Store.writeRegister]

end IRComparison.Circuit.SystemVerilog
