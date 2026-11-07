import IRComparison.Circuit.SystemVerilog.NetlistSound

namespace IRComparison.Circuit

/-- Structural invariant of the actual sharing table. No semantic test on
individual input data is performed to establish this invariant. -/
structure Emission.WellFormed (s : Emission) : Prop where
  lengths : s.cache.size = s.text.size
  ordered : SystemVerilog.Ordered 0 s.text.toList
  cached : ∀ entry ∈ s.cache.toList, entry.2.name.Before s.text.size
  widths : ∀ entry ∈ s.cache.toList, ∃ n,
    entry.2.name = .temporary n ∧ (s.text[n]?.map SystemVerilog.Wire.width) = some entry.2.width

structure Emission.Extends (before after : Emission) : Prop where
  declarations : ∃ extra, after.text = before.text ++ extra
  entries : ∃ extra, after.cache = before.cache ++ extra

theorem Emission.Extends.refl (s : Emission) : s.Extends s :=
  ⟨⟨#[],by simp⟩,⟨#[],by simp⟩⟩

theorem Emission.Extends.trans {a b c : Emission} (ab : a.Extends b) (bc : b.Extends c) : a.Extends c := by
  obtain ⟨da,ha⟩ := ab.declarations
  obtain ⟨db,hb⟩ := bc.declarations
  obtain ⟨ca,hca⟩ := ab.entries
  obtain ⟨cb,hcb⟩ := bc.entries
  exact ⟨⟨da++db,by simp [hb,ha,Array.append_assoc]⟩,⟨ca++cb,by simp [hcb,hca,Array.append_assoc]⟩⟩

theorem Emission.Extends.size_le {a b : Emission} (h : a.Extends b) : a.text.size ≤ b.text.size := by
  obtain ⟨extra,he⟩ := h.declarations
  simp [he]

def Builds (action : EmitM α) (post : α → Emission → Prop) : Prop :=
  ∀ before, before.WellFormed → ∀ value after, action before = .ok (value,after) →
    after.WellFormed ∧ before.Extends after ∧ post value after

theorem Builds.weaken (h : Builds action post)
    (weaker : ∀ value state, post value state → other value state) : Builds action other := by
  intro before good value after success
  obtain ⟨well,grows,result⟩ := h before good value after success
  exact ⟨well,grows,weaker value after result⟩

theorem bind_success (action : EmitM α) (next : α → EmitM β)
    {value : β} (success : (action >>= next) before = .ok (value,after)) :
    ∃ middle state, action before = .ok (middle,state) ∧ next middle state = .ok (value,after) := by
  change (action before >>= fun pair => next pair.1 pair.2) = .ok (value,after) at success
  cases step : action before with
  | error why => simp [step,bind,Except.bind] at success
  | ok pair => exact ⟨pair.1,pair.2,rfl,by simpa [step,bind,Except.bind] using success⟩

theorem pure_success (value : α) (success : (pure value : EmitM α) before = .ok (result,after)) :
    result = value ∧ after = before := by
  change Except.ok (value,before) = Except.ok (result,after) at success
  cases success
  exact ⟨rfl,rfl⟩

theorem mapM_builds (items : List α) (action : α → EmitM Signal)
    (each : ∀ item ∈ items, Builds (action item) (fun signal state => signal.name.Before state.text.size)) :
    Builds (items.mapM action) (fun signals state => ∀ signal ∈ signals, signal.name.Before state.text.size) := by
  intro before good signals after success
  induction items generalizing before signals after with
  | nil =>
    have h := pure_success [] success
    rcases h with ⟨rfl,rfl⟩
    exact ⟨good,Emission.Extends.refl _,by simp⟩
  | cons item rest ih =>
    rw [List.mapM_cons] at success
    obtain ⟨head,middle,first,restResult⟩ := bind_success _ _ success
    obtain ⟨middleGood,grows,headScope⟩ := each item (by simp) before good head middle first
    obtain ⟨tail,last,next,returned⟩ := bind_success _ _ restResult
    obtain ⟨restGood,restGrows,tailScope⟩ := ih (fun x hx => each x (by simp [hx])) middle middleGood tail last next
    obtain ⟨rfl,rfl⟩ := pure_success (head::tail) returned
    refine ⟨restGood,grows.trans restGrows,?_⟩
    intro signal member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact SystemVerilog.Name.before_mono headScope restGrows.size_le
    · exact tailScope signal member

/-- A node template references only its generated children and physical
storage. This covers every source RTL term constructor, including division. -/
theorem termTemplate_scope (a : Artifact) (e : RTL.Term) (args : List Signal)
    (inputs : ∀ signal ∈ args, signal.name.Before limit)
    (success : termTemplate a e args = .ok (rhs,width)) : rhs.Before limit := by
  unfold termTemplate at success
  split at success <;>
    simp_all [pure,bind,Except.pure,Except.bind,Functor.map,Except.map,throw,
      SystemVerilog.Expr.Before,SystemVerilog.Name.Before,widen,SystemVerilog.division]
  all_goals repeat first
    | (simp_all [pure,bind,Except.pure,Except.bind,Functor.map,Except.map,throw,
        SystemVerilog.Expr.Before,SystemVerilog.Name.Before,widen,SystemVerilog.division])
    | (split at success)
  all_goals try (rcases success with ⟨rfl,rfl⟩)
  all_goals try (cases success)
  all_goals simp_all [SystemVerilog.Expr.Before,SystemVerilog.Name.Before,widen,SystemVerilog.division]

theorem lift_success (action : Except String α)
    (success : (StateT.lift action : EmitM α) before = .ok (result,after)) :
    action = .ok result ∧ after = before := by
  change (action >>= fun value => Except.ok (value,before)) = .ok (result,after) at success
  cases step : action with
  | error why => simp [step,bind,Except.bind] at success
  | ok value =>
    simp only [step,bind,Except.bind] at success
    cases success
    exact ⟨rfl,rfl⟩

theorem recordTerm_sound (before : Emission) (good : before.WellFormed)
    (scope : rhs.Before before.text.size)
    (success : recordTerm e rhs width before = .ok (signal,after)) :
    after.WellFormed ∧ before.Extends after ∧
      (signal.name.Before after.text.size ∧ (e,signal) ∈ after.cache.toList) := by
  unfold recordTerm at success
  split at success
  · cases success
    refine ⟨⟨?_,?_,?_,?_⟩,⟨?_,?_⟩,?_⟩
    · simp [good.lengths]
    · simp only [Array.toList_push,SystemVerilog.ordered_append,Array.length_toList,Nat.zero_add]
      refine ⟨good.ordered,?_⟩
      simp [SystemVerilog.Ordered,good.lengths,scope]
    · intro entry member
      simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
      rcases member with member | rfl
      · exact SystemVerilog.Name.before_mono (good.cached entry member) (by simp)
      · simp [SystemVerilog.Name.Before,good.lengths]
    · intro entry member
      simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
      rcases member with member | rfl
      · obtain ⟨n,named,declared⟩ := good.widths entry member
        refine ⟨n,named,?_⟩
        have hn : n < before.text.size := by
          have h := good.cached entry member
          simpa [named,SystemVerilog.Name.Before] using h
        simpa [Array.getElem?_push,hn,Nat.ne_of_lt hn] using declared
      · refine ⟨before.cache.size,rfl,?_⟩
        simp [Array.getElem?_push,good.lengths]
    · exact ⟨#[_],by simp only [Array.push_eq_append]; rfl⟩
    · exact ⟨#[_],by simp only [Array.push_eq_append]; rfl⟩
    · simp [SystemVerilog.Name.Before,good.lengths]
  · cases success

theorem get_bind (next : Emission → EmitM α) (before : Emission) :
    ((get >>= next) : EmitM α) before = next before before := rfl

/-- General structural correctness of the actual memoizing traversal. Cache
hits reuse a declared signal; misses append an ordered declaration after all
children. This theorem does not generate proofs for individual source inputs. -/
theorem termText_builds (a : Artifact) (e : RTL.Term) :
    Builds (termText a e) (fun signal state => signal.name.Before state.text.size ∧ (e,signal) ∈ state.cache.toList) := by
  intro before good signal after success
  rw [termText.eq_def] at success
  rw [get_bind] at success
  cases found : before.cache.toList.find? (fun p => p.1 == e) with
  | some pair =>
    simp only [found] at success
    change Except.ok (_,before) = Except.ok (signal,after) at success
    cases success
    have member := List.mem_of_find?_eq_some found
    have matched := List.find?_some found
    simp only [beq_iff_eq] at matched
    exact ⟨good,Emission.Extends.refl before,good.cached pair member,by simpa [← matched] using member⟩
  | none =>
    simp only [found,pure_bind] at success
    obtain ⟨args,middle,children,rest⟩ := bind_success _ _ success
    have each : ∀ child ∈ e.children.attach,
        Builds (termText a child.val) (fun sig state => sig.name.Before state.text.size) := by
      intro child _
      exact (termText_builds a child.val).weaken (fun _ _ h => h.1)
    obtain ⟨middleGood,grows,argScope⟩ := mapM_builds _ _ each before good args middle children
    obtain ⟨pair,last,compiled,stored⟩ := bind_success _ _ rest
    obtain ⟨templateResult,stateEq⟩ := lift_success (termTemplate a e args) compiled
    subst last
    have rhsScope := termTemplate_scope a e args argScope templateResult
    obtain ⟨afterGood,growsAgain,signalScope⟩ := recordTerm_sound middle middleGood rhsScope stored
    exact ⟨afterGood,grows.trans growsAgain,signalScope⟩
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ child.property

def Preserves (action : EmitM α) : Prop := Builds action (fun _ _ => True)

theorem Builds.preserves (h : Builds action post) : Preserves action := by
  intro before good result after success
  obtain ⟨well,grows,_⟩ := h before good result after success
  exact ⟨well,grows,trivial⟩

@[simp] theorem preserves_pure (value : α) : Preserves (pure value : EmitM α) := by
  intro before good result after success
  obtain ⟨rfl,rfl⟩ := pure_success value success
  exact ⟨good,Emission.Extends.refl _,trivial⟩

@[simp] theorem preserves_lift (action : Except String α) : Preserves (StateT.lift action : EmitM α) := by
  intro before good result after success
  obtain ⟨_,rfl⟩ := lift_success action success
  exact ⟨good,Emission.Extends.refl _,trivial⟩

@[simp] theorem preserves_bind (action : EmitM α) (next : α → EmitM β)
    (first : Preserves action) (following : ∀ value, Preserves (next value)) : Preserves (action >>= next) := by
  intro before good result after success
  obtain ⟨value,middle,ha,hb⟩ := bind_success action next success
  obtain ⟨middleGood,grows,_⟩ := first before good value middle ha
  obtain ⟨afterGood,more,_⟩ := following value middle middleGood result after hb
  exact ⟨afterGood,grows.trans more,trivial⟩

@[simp] theorem preserves_map (action : EmitM α) (f : α → β) (h : Preserves action) : Preserves (f <$> action) := by
  rw [map_eq_pure_bind]
  exact preserves_bind action _ h (fun _ => preserves_pure _)

@[simp] theorem preserves_liftM (action : Except String α) : Preserves (liftM action : EmitM α) :=
  preserves_lift action

@[simp] theorem preserves_throw (message : String) : Preserves (throw message : EmitM α) := by
  intro before good result after success
  cases success

@[simp] theorem preserves_require (condition : Bool) (message : String) : Preserves (require condition message) := by
  unfold require
  split <;> simp

@[simp] theorem preserves_termText (a : Artifact) (e : RTL.Term) : Preserves (termText a e) :=
  (termText_builds a e).preserves

@[simp] theorem preserves_mapM (action : α → EmitM β) (items : List α)
    (each : ∀ item, Preserves (action item)) : Preserves (items.mapM action) := by
  induction items with
  | nil => exact preserves_pure []
  | cons item rest ih =>
      simp only [List.mapM_cons]
      exact preserves_bind _ _ (each item)
        (fun _ => preserves_bind _ _ ih (fun _ => preserves_pure _))

@[simp] theorem preserves_validityText (a : Artifact) (v : RTL.Validity) : Preserves (validityText a v) := by
  induction v <;> simp_all (config := {maxDischargeDepth := 20}) [validityText]

@[simp] theorem preserves_expression (a : Artifact) (e : RTL.Combinational) : Preserves (expression a e) := by
  simp [expression]

@[simp] theorem preserves_wordValue (a : Artifact) (e : RTL.Combinational) : Preserves (wordValue a e) := by
  exact preserves_require _ _

@[simp] theorem preserves_scalarCode (a : Artifact) (v : RTL.Scalar RTL.Combinational) : Preserves (scalarCode a v) := by
  cases v <;> simp [scalarCode]

@[simp] theorem preserves_testCode (a : Artifact) (t : RTL.Test RTL.Combinational) : Preserves (testCode a t) := by
  induction t <;> simp_all [testCode]

@[simp] theorem preserves_statementCode (a : Artifact) (s : RTL.Statement RTL.Combinational) : Preserves (statementCode a s) := by
  induction s with
  | skip => exact preserves_pure _
  | assign target rhs => cases target <;> cases rhs <;> simp (config := {maxDischargeDepth := 20}) [statementCode]
  | memory target rhs => cases rhs <;> simp (config := {maxDischargeDepth := 20}) [statementCode]
  | queue target rhs => cases rhs <;> simp (config := {maxDischargeDepth := 20}) [statementCode]
  | seq first second ihFirst ihSecond => simp (config := {maxDischargeDepth := 20}) [statementCode,ihFirst,ihSecond]
  | branch condition yes no ihYes ihNo => simp (config := {maxDischargeDepth := 20}) [statementCode,ihYes,ihNo]

theorem Emission.empty_wellFormed : ({} : Emission).WellFormed := by
  exact ⟨rfl,trivial,by simp,by simp⟩

/-- The complete real generator produces an ordered netlist from its empty
initial sharing table. No extra runtime checker or input restriction is used. -/
theorem generateCode_ordered (a : Artifact) (success : generateCode a = .ok (cases,emission)) :
    SystemVerilog.Ordered 0 emission.text.toList := by
  have h := preserves_mapM (statementCode a) (RTL.artifactProgram a).cases.toList (preserves_statementCode a)
  exact (h {} Emission.empty_wellFormed cases emission success).1.ordered

/-- The returned shared reference has exactly the declared width. Together
with membership in the cache this connects lookup to the generated net. -/
theorem termText_declared (a : Artifact) (e : RTL.Term) (good : before.WellFormed)
    (success : termText a e before = .ok (signal,after)) :
    ∃ n, signal.name = .temporary n ∧
      (after.text[n]?.map SystemVerilog.Wire.width) = some signal.width := by
  obtain ⟨well,_,_,member⟩ := termText_builds a e before good signal after success
  exact well.widths (e,signal) member

/-- The real generator's continuous assignments hold together in its final
shared-signal environment whenever concrete evaluation succeeds. Source-value
preservation and totality of that evaluation are separate proof obligations. -/
theorem generateCode_satisfies (a : Artifact) (r : FiniteRuntime a.storageShape)
    (generated : generateCode a = .ok (cases,emission))
    (evaluated : SystemVerilog.evaluateWires a r emission.text = some values) :
    SystemVerilog.Satisfies (SystemVerilog.environment a r emission.text #[]) values 0 emission.text.toList :=
  SystemVerilog.evaluateWires_satisfies a r emission.text (generateCode_ordered a generated) evaluated

end IRComparison.Circuit
