import IRComparison.Circuit.SharedEmitPhysical
import IRComparison.Circuit.SystemVerilog.TotalSound

namespace IRComparison.Circuit.Shared.NetEmission
open SystemVerilog

/-- Proof-only construction history. Every appended assignment can be evaluated
once the earlier assignments hold; no runtime certificate is constructed. -/
inductive NetTrace (base : Environment) : Wires → Prop where
  | empty : NetTrace base #[]
  | step (prior : NetTrace base before) (positive : 0 < width)
      (good : SystemVerilog.Ordered 0 before.toList) (scope : rhs.Before before.size)
      (defined : ∀ values, NetRealizes (base.withTemporaries values) before →
        ∃ bits, rhs.assignment (base.withTemporaries values) width = some bits) :
      NetTrace base (before.push ⟨.temporary before.size,width,rhs,positive⟩)

theorem NetTrace.total (trace : NetTrace base declarations)
    (declared : ∀ wire ∈ declarations.toList, base.type wire.name = ⟨wire.width,true⟩) :
    ∃ values, appendWires base declarations.toList #[] = some values ∧ values.size = declarations.size := by
  induction trace with
  | empty => exact ⟨#[],rfl,rfl⟩
  | @step before width rhs prior positive good scope defined ih =>
    have declaredBefore : ∀ wire ∈ before.toList, base.type wire.name = ⟨wire.width,true⟩ := by
      intro wire member
      exact declared wire (by simp [member])
    obtain ⟨values,evaluated,size⟩ := ih declaredBefore
    have realized : NetRealizes (base.withTemporaries values) before := by
      intro wire member
      exact ⟨declaredBefore wire member,(appendWires_satisfies base before.toList #[] values good evaluated).equations member⟩
    obtain ⟨bits,assigned⟩ := defined values realized
    refine ⟨values.push bits.toInt,?_,by simp [size]⟩
    rw [Array.toList_push,appendWires_append,evaluated]
    simp [appendWires,← size,assigned,bind,Option.bind]

def BindingsFor (base : Environment) (r : Runtime) (refs : Option (Array Signal)) (before : Wires) : Prop :=
  ∀ values, NetRealizes (base.withTemporaries values) before → Bindings (base.withTemporaries values) r refs

theorem BindingsFor.mono (h : BindingsFor base r refs before) (grows : Extends before after) :
    BindingsFor base r refs after := fun values realized => h values (realized.restrict grows)

theorem fresh_trace (trace : NetTrace base before) (good : SystemVerilog.Ordered 0 before.toList)
    (scope : rhs.Before before.size)
    (defined : ∀ values, NetRealizes (base.withTemporaries values) before →
      ∃ bits, rhs.assignment (base.withTemporaries values) width = some bits)
    (success : fresh rhs width before = .ok (signal,after)) : NetTrace base after := by
  unfold fresh at success
  split at success
  · cases success
    exact .step trace ‹_› good scope defined
  · cases success

theorem mapM_trace (items : List α) (action : α → Builder Signal)
    (structures : ∀ item ∈ items, Builds refs (action item) (fun sig st => sig.name.Before st.size))
    (each : ∀ item ∈ items, ∀ before, SystemVerilog.Ordered 0 before.toList → InScope refs before.size →
      BindingsFor base r refs before → NetTrace base before → ∀ result after,
      action item before = .ok (result,after) → NetTrace base after)
    (good : SystemVerilog.Ordered 0 before.toList) (scope : InScope refs before.size)
    (bindings : BindingsFor base r refs before) (trace : NetTrace base before)
    (success : items.mapM action before = .ok (signals,after)) : NetTrace base after := by
  induction items generalizing before signals after with
  | nil =>
    obtain ⟨rfl,rfl⟩ := pure_success [] success
    exact trace
  | cons item rest ih =>
    rw [List.mapM_cons] at success
    obtain ⟨head,middle,first,next⟩ := bind_success _ _ success
    obtain ⟨tail,last,more,returned⟩ := bind_success _ _ next
    obtain ⟨rfl,rfl⟩ := pure_success (head::tail) returned
    obtain ⟨midGood,grows,_⟩ := structures item (by simp) before good scope head middle first
    exact ih (fun x hx => structures x (by simp [hx])) (fun x hx => each x (by simp [hx]))
      midGood (scope.mono grows.size_le) (bindings.mono grows)
      (each item (by simp) before good scope bindings trace head middle first) more

theorem term_trace (a : Artifact) (r : Runtime) (refs : Option (Array Signal)) (e : RTL.Term)
    (physical : ∀ values, Physical a r (base.withTemporaries values) refs e)
    (bindings : BindingsFor base r refs before)
    (good : SystemVerilog.Ordered 0 before.toList) (scope : InScope refs before.size)
    (trace : NetTrace base before) (success : term a refs e before = .ok (signal,after)) : NetTrace base after := by
  rw [term_step] at success
  cases found : resolved refs e with
  | some entry =>
    cases entry with
    | none =>
      simp only [found] at success
      change Except.error _ = Except.ok _ at success
      cases success
    | some ref =>
      simp only [found] at success
      obtain ⟨rfl,rfl⟩ := pure_success ref success
      exact trace
  | none =>
    simp only [found] at success
    obtain ⟨args,middle,children,next⟩ := bind_success _ _ success
    have structures : ∀ child ∈ e.children.attach, Builds refs (term a refs child.val)
        (fun sig st => sig.name.Before st.size) := by
      intro child _ start valid scope sig finish success
      exact term_builds a refs child.val start valid scope success
    have childPhysical : ∀ child ∈ e.children, ∀ values, Physical a r (base.withTemporaries values) refs child := by
      intro child member values
      have h := physical values
      rw [Physical.eq_def] at h
      exact h.2 child member
    obtain ⟨midGood,grows,argScope⟩ := mapM_builds _ _ structures before good scope args middle children
    have midTrace := mapM_trace _ _ structures
      (fun child _ start valid scope bindings trace sig finish success =>
        term_trace a r refs child.val (childPhysical child.val child.property) bindings valid scope trace success)
      good scope bindings trace children
    obtain ⟨pair,last,template,stored⟩ := bind_success _ _ next
    obtain ⟨compiled,rfl⟩ := lift_success _ template
    apply fresh_trace midTrace midGood (termTemplate_scope a e args argScope compiled) ?_ stored
    intro values realized
    have bound := bindings values (realized.restrict grows)
    have meanings := mapM_correct e.children.attach (fun child => term a refs child.val) Subtype.val
      structures (fun child _ start valid scope sig finish success realized =>
        term_correct a r refs child.val (childPhysical child.val child.property values)
          bound valid scope success realized)
      good scope children realized
    have inputs : Paired (fun child sig => SignedMeaning (base.withTemporaries values)
        (.reference sig.name) sig.width (child.eval r)) e.children args := by
      simpa using (Paired.map_left (f:=Subtype.val)
        (relation:=fun (child : RTL.Term) (sig : Signal) => SignedMeaning (base.withTemporaries values)
          (.reference sig.name) sig.width (child.eval r)) meanings)
    have phys := physical values
    rw [Physical.eq_def] at phys
    exact ⟨_,(termTemplate_correct a r e (phys.1 found) inputs compiled).assignment⟩
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ child.property

theorem validity_trace (a : Artifact) (r : Runtime) (refs : Option (Array Signal)) (v : RTL.Validity)
    (physical : ∀ values, PhysicalValidity a r (base.withTemporaries values) refs v)
    (bindings : BindingsFor base r refs before)
    (good : SystemVerilog.Ordered 0 before.toList) (scope : InScope refs before.size)
    (trace : NetTrace base before) (success : validity a refs v before = .ok (expr,after)) : NetTrace base after := by
  induction v generalizing before expr after with
  | yes | no =>
    obtain ⟨rfl,rfl⟩ := pure_success _ success
    exact trace
  | and u v ihu ihv =>
    rw [validity] at success
    obtain ⟨left,middle,first,next⟩ := bind_success _ _ success
    obtain ⟨right,second,rfl⟩ := map_success _ _ next
    obtain ⟨midGood,grows,_⟩ := validity_builds a refs u before good scope left middle first
    exact ihv (fun vs => (physical vs).2) (bindings.mono grows) midGood (scope.mono grows.size_le)
      (ihu (fun vs => (physical vs).1) bindings good scope trace first) second
  | address n j =>
    rw [validity] at success
    obtain ⟨size,middle,found,next⟩ := bind_success _ _ success
    obtain ⟨known,stateEq⟩ := lift_success (memorySize a n) found
    subst middle
    obtain ⟨signal,compiled,rfl⟩ := return_success _ _ next
    exact term_trace a r refs j (fun vs => (physical vs).1) bindings good scope trace compiled
  | mux c u v ihu ihv =>
    rw [validity] at success
    obtain ⟨condition,middle,first,next⟩ := bind_success _ _ success
    obtain ⟨left,last,second,next⟩ := bind_success _ _ next
    obtain ⟨right,third,rfl⟩ := map_success _ _ next
    obtain ⟨midGood,grows,_⟩ := term_builds a refs c before good scope first
    obtain ⟨lastGood,more,_⟩ := validity_builds a refs u middle midGood (scope.mono grows.size_le) left last second
    have firstTrace := term_trace a r refs c (fun vs => (physical vs).1) bindings good scope trace first
    have secondTrace := ihu (fun vs => (physical vs).2.1) (bindings.mono grows) midGood (scope.mono grows.size_le) firstTrace second
    exact ihv (fun vs => (physical vs).2.2) (bindings.mono (grows.trans more)) lastGood
      (scope.mono (grows.trans more).size_le) secondTrace third

theorem expression_trace (a : Artifact) (r : Runtime) (refs : Option (Array Signal)) (e : RTL.Combinational)
    (physical : ∀ values, Physical a r (base.withTemporaries values) refs e.value ∧
      PhysicalValidity a r (base.withTemporaries values) refs e.valid)
    (bindings : BindingsFor base r refs before)
    (good : SystemVerilog.Ordered 0 before.toList) (scope : InScope refs before.size)
    (trace : NetTrace base before) (success : expression a refs e before = .ok (pair,after)) : NetTrace base after := by
  rw [expression] at success
  obtain ⟨value,middle,first,next⟩ := bind_success _ _ success
  obtain ⟨guard,last,second,next⟩ := bind_success _ _ next
  obtain ⟨valid,third,rfl⟩ := return_success _ _ next
  obtain ⟨midGood,grows,_⟩ := term_builds a refs e.value before good scope first
  obtain ⟨lastGood,more,gScope⟩ := validity_builds a refs e.valid middle midGood
    (scope.mono grows.size_le) guard last second
  have midTrace := term_trace a r refs e.value (fun vs => (physical vs).1) bindings good scope trace first
  have lastTrace := validity_trace a r refs e.valid (fun vs => (physical vs).2) (bindings.mono grows)
    midGood (scope.mono grows.size_le) midTrace second
  apply fresh_trace lastTrace lastGood (rhs:=.select guard (.integer 1) (.integer 0)) ⟨gScope,trivial,trivial⟩ ?_ third
  intro values realized
  have guardMeaning := validity_correct a r refs e.valid (physical values).2
    (bindings values (realized.restrict (grows.trans more))) midGood (scope.mono grows.size_le) second realized
  have one := SignedMeaning.integer (env:=base.withTemporaries values) 1
  have zero := SignedMeaning.integer (env:=base.withTemporaries values) 0
  have boolean := SignedMeaning.select_bool guardMeaning.evaluated one.typed zero.typed (fun _ => one) (fun _ => zero)
  have assigned : AssignedMeaning (base.withTemporaries values) (.select guard (.integer 1) (.integer 0)) 2
      (if e.valid.eval r then 1 else 0) := boolean.assigned (by cases e.valid.eval r <;> decide)
  exact ⟨_,assigned.assignment⟩

theorem code_trace (a : Artifact) (r : Runtime) (refs : Array Signal) (values : Array Int) (c : LocalRTL.Code)
    (physical : ∀ vs, CodePhysical a r (base.withTemporaries vs) c)
    (correspondence : ∀ vs, NetRealizes (base.withTemporaries vs) before → SignalMatches (base.withTemporaries vs) refs values)
    (good : SystemVerilog.Ordered 0 before.toList) (scope : InScope (some refs) before.size)
    (trace : NetTrace base before) (success : code a refs c before = .ok (pair,after)) : NetTrace base after := by
  cases c with
  | source e =>
    exact expression_trace a r none e physical (by intro vs h xs he; cases he)
      good (by intro xs he; cases he) trace success
  | localNode e =>
    apply expression_trace a (LocalRTL.fullRuntime r values) (some refs) e (fun vs => physical vs refs values) ?_ good scope trace success
    intro vs h xs he n signal found
    cases he
    exact (correspondence vs h).meaning n signal found

theorem graph_trace (a : Artifact) (r : Runtime) (cs : List LocalRTL.Code)
    (physical : ∀ c ∈ cs, ∀ values, CodePhysical a r (base.withTemporaries values) c)
    (good : SystemVerilog.Ordered 0 before.toList) (trace : NetTrace base before)
    (success : graph a cs before = .ok (refs,after)) : NetTrace base after := by
  induction cs generalizing before refs after with
  | nil =>
    obtain ⟨rfl,rfl⟩ := pure_success _ success
    exact trace
  | cons c cs ih =>
    rw [graph] at success
    obtain ⟨previous,middle,first,next⟩ := bind_success _ _ success
    obtain ⟨pair,second,rfl⟩ := return_success _ _ next
    obtain ⟨midGood,grows,prevScope⟩ := graph_builds a cs before good (by intro xs he; cases he) previous middle first
    have midTrace := ih (fun c hc => physical c (by simp [hc])) good trace first
    have correspondence := fun values realized => graph_correct a r cs
      (fun c hc => physical c (by simp [hc]) values) good first realized
    exact code_trace a r previous (LocalRTL.fullValues r cs) c (physical c (by simp))
      correspondence midGood prevScope midTrace second

/-- Successful shared-net emission with in-bounds physical references always
has a defined SystemVerilog assignment evaluation. Source failure remains in
the validity signal; it is not confused with failure of netlist evaluation. -/
theorem generate_total (a : Artifact) (r : FiniteRuntime a.storageShape)
    (closed : ∀ c ∈ p.code, CodeReferences a.storageShape c)
    (generated : generate a p = .ok output) :
    ∃ values, evaluateWires a r output.declarations = some values := by
  obtain ⟨refs,built,_,_⟩ := generate_graph generated
  have trace := graph_trace a r.decode p.code
    (fun c hc values => codePhysical_from_refs a r output.declarations values c (closed c hc))
    (before:=#[]) trivial .empty built
  have declared := declared_environment a r ⟨output.declarations,#[]⟩ (generate_ordered generated)
  obtain ⟨values,evaluated,_⟩ := trace.total declared
  exact ⟨values,evaluated⟩

end IRComparison.Circuit.Shared.NetEmission
