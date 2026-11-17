import IRComparison.Circuit.SharedEmitStructure
import IRComparison.Circuit.SharedRTLSignals

namespace IRComparison.Circuit.Shared.NetEmission
open SystemVerilog

/-- All declarations in a fixed final environment satisfy their actual
SystemVerilog assignments. Later the ordered evaluator supplies this fact. -/
def NetRealizes (env : Environment) (decls : Wires) : Prop :=
  ∀ wire ∈ decls.toList, env.type wire.name = ⟨wire.width,true⟩ ∧
    (wire.value.assignment env wire.width).map BitVec.toInt = env.scalar wire.name

theorem NetRealizes.restrict (h : NetRealizes env after) (grows : Extends before after) :
    NetRealizes env before := by
  obtain ⟨extra,he⟩ := grows
  intro wire member
  exact h wire (by simp [he,member])

def Bindings (env : Environment) (r : Runtime) (refs : Option (Array Signal)) : Prop :=
  ∀ xs, refs = some xs → ∀ n signal, xs[n]? = some signal →
    SignedMeaning env (.reference signal.name) signal.width (r.wires n)

def Physical (a : Artifact) (r : Runtime) (env : Environment)
    (refs : Option (Array Signal)) (e : RTL.Term) : Prop :=
  (resolved refs e = none → PhysicalNode a r env e) ∧
    ∀ child ∈ e.children, Physical a r env refs child
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ ‹_›

theorem fresh_correct (meaning : AssignedMeaning env rhs width v)
    (success : fresh rhs width before = .ok (signal,after)) (realized : NetRealizes env after) :
    SignedMeaning env (.reference signal.name) signal.width v := by
  unfold fresh at success
  split at success
  · rename_i positive
    cases success
    have actual := realized ⟨.temporary before.size,width,rhs,positive⟩ (by simp)
    have stored : env.scalar (.temporary before.size) = some v := by
      rw [meaning.assignment,Option.map_some,meaning.fits] at actual
      exact actual.2.symm
    exact SignedMeaning.reference env _ positive actual.1 stored meaning.fits
  · cases success

theorem mapM_correct (items : List α) (action : α → Builder Signal) (source : α → RTL.Term)
    (structureOK : ∀ item ∈ items, Builds refs (action item) (fun sig st => sig.name.Before st.size))
    (each : ∀ item ∈ items, ∀ before, SystemVerilog.Ordered 0 before.toList → InScope refs before.size →
      ∀ signal after, action item before = .ok (signal,after) → NetRealizes env after →
      SignedMeaning env (.reference signal.name) signal.width ((source item).eval r))
    (good : SystemVerilog.Ordered 0 before.toList) (scope : InScope refs before.size)
    (success : items.mapM action before = .ok (signals,after)) (realized : NetRealizes env after) :
    Paired (fun item signal => SignedMeaning env (.reference signal.name) signal.width ((source item).eval r)) items signals := by
  induction items generalizing before signals after with
  | nil =>
    obtain ⟨rfl,rfl⟩ := pure_success [] success
    exact .nil
  | cons item rest ih =>
    rw [List.mapM_cons] at success
    obtain ⟨head,middle,first,next⟩ := bind_success _ _ success
    obtain ⟨tail,last,more,returned⟩ := bind_success _ _ next
    obtain ⟨rfl,rfl⟩ := pure_success (head::tail) returned
    obtain ⟨midGood,grows,_⟩ := structureOK item (by simp) before good scope head middle first
    have midScope := scope.mono grows.size_le
    obtain ⟨_,growsMore,_⟩ := mapM_builds rest action (fun x hx => structureOK x (by simp [hx]))
      middle midGood midScope tail after more
    exact .cons (each item (by simp) before good scope head middle first (realized.restrict growsMore))
      (ih (fun x hx => structureOK x (by simp [hx])) (fun x hx => each x (by simp [hx])) midGood midScope more realized)

theorem term_correct (a : Artifact) (r : Runtime) (refs : Option (Array Signal)) (e : RTL.Term)
    (physical : Physical a r env refs e) (bindings : Bindings env r refs)
    (good : SystemVerilog.Ordered 0 before.toList) (scope : InScope refs before.size)
    (success : term a refs e before = .ok (signal,after)) (realized : NetRealizes env after) :
    SignedMeaning env (.reference signal.name) signal.width (e.eval r) := by
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
      cases refs <;> cases e <;> simp [resolved] at found
      rename_i refs n
      exact bindings refs rfl n signal found
  | none =>
    simp only [found] at success
    obtain ⟨args,middle,children,next⟩ := bind_success _ _ success
    have structures : ∀ child ∈ e.children.attach, Builds refs (term a refs child.val)
        (fun sig st => sig.name.Before st.size) := by
      intro child _ start valid scope sig finish success
      exact term_builds a refs child.val start valid scope success
    obtain ⟨midGood,grows,argScope⟩ := mapM_builds _ _ structures before good scope args middle children
    obtain ⟨pair,last,template,stored⟩ := bind_success _ _ next
    obtain ⟨compiled,rfl⟩ := lift_success _ template
    obtain ⟨_,growsMore,_⟩ := fresh_builds (termTemplate_scope a e args argScope compiled) midGood stored
    have meanings := mapM_correct e.children.attach (fun child => term a refs child.val) Subtype.val
      structures (fun child _ start valid scope sig finish success realized =>
        term_correct a r refs child.val ((by rw [Physical.eq_def] at physical; exact physical.2 _ child.property))
          bindings valid scope success realized) good scope children (realized.restrict growsMore)
    have inputs : Paired (fun child sig => SignedMeaning env (.reference sig.name) sig.width (child.eval r)) e.children args := by
      simpa using (Paired.map_left (f:=Subtype.val)
        (relation:=fun (child : RTL.Term) (sig : Signal) => SignedMeaning env (.reference sig.name) sig.width (child.eval r)) meanings)
    rw [Physical.eq_def] at physical
    exact fresh_correct (termTemplate_correct a r e (physical.1 found) inputs compiled) stored realized
termination_by sizeOf e
decreasing_by exact RTL.Term.child_size _ _ child.property

def PhysicalValidity (a : Artifact) (r : Runtime) (env : Environment)
    (refs : Option (Array Signal)) : RTL.Validity → Prop
  | .yes | .no => True
  | .and u v => PhysicalValidity a r env refs u ∧ PhysicalValidity a r env refs v
  | .address n j => Physical a r env refs j ∧ PhysicalNode a r env (.length n)
  | .mux c u v => Physical a r env refs c ∧
      PhysicalValidity a r env refs u ∧ PhysicalValidity a r env refs v

theorem validity_correct (a : Artifact) (r : Runtime) (refs : Option (Array Signal)) (v : RTL.Validity)
    (physical : PhysicalValidity a r env refs v) (bindings : Bindings env r refs)
    (good : SystemVerilog.Ordered 0 before.toList) (scope : InScope refs before.size)
    (success : validity a refs v before = .ok (expr,after)) (realized : NetRealizes env after) :
    BooleanMeaning env expr (v.eval r) := by
  induction v generalizing before expr after with
  | yes | no =>
    obtain ⟨rfl,rfl⟩ := pure_success _ success
    exact BooleanMeaning.bit _
  | and u v ihu ihv =>
    rw [validity] at success
    obtain ⟨left,middle,first,next⟩ := bind_success _ _ success
    obtain ⟨right,second,rfl⟩ := map_success _ _ next
    obtain ⟨midGood,grows,_⟩ := validity_builds a refs u before good scope left middle first
    obtain ⟨_,more,_⟩ := validity_builds a refs v middle midGood (scope.mono grows.size_le) right after second
    exact (ihu physical.1 good scope first (realized.restrict more)).and
      (ihv physical.2 midGood (scope.mono grows.size_le) second realized)
  | address n j =>
    rw [validity] at success
    obtain ⟨size,middle,found,next⟩ := bind_success _ _ success
    obtain ⟨known,stateEq⟩ := lift_success (memorySize a n) found
    subst middle
    obtain ⟨signal,compiled,rfl⟩ := return_success _ _ next
    exact address_meaning (term_correct a r refs j physical.1 bindings good scope compiled realized)
      (physical.2 size known)
  | mux c u v ihu ihv =>
    rw [validity] at success
    obtain ⟨condition,middle,first,next⟩ := bind_success _ _ success
    obtain ⟨left,last,second,next⟩ := bind_success _ _ next
    obtain ⟨right,third,rfl⟩ := map_success _ _ next
    obtain ⟨midGood,grows,_⟩ := term_builds a refs c before good scope first
    obtain ⟨lastGood,more,_⟩ := validity_builds a refs u middle midGood (scope.mono grows.size_le) left last second
    obtain ⟨_,latest,_⟩ := validity_builds a refs v last lastGood
      (scope.mono (grows.trans more).size_le) right after third
    have cond := term_correct a r refs c physical.1 bindings good scope first
      (realized.restrict (more.trans latest))
    have test := cond.boolean_comparison (SignedMeaning.integer 0) (op:=.ne) rfl
      (result:=c.eval r != 0) (by simp [SystemVerilog.arithmetic])
    exact test.select (ihu physical.2.1 midGood (scope.mono grows.size_le) second (realized.restrict latest))
      (ihv physical.2.2 lastGood (scope.mono (grows.trans more).size_le) third realized)

def Pair.Meaning (env : Environment) (p : Pair) (value : Int) (valid : Bool) : Prop :=
  SignedMeaning env (.reference p.value.name) p.value.width value ∧
  SignedMeaning env (.reference p.valid.name) p.valid.width (if valid then 1 else 0)

theorem expression_correct (a : Artifact) (r : Runtime) (refs : Option (Array Signal)) (e : RTL.Combinational)
    (physical : Physical a r env refs e.value ∧ PhysicalValidity a r env refs e.valid)
    (bindings : Bindings env r refs)
    (good : SystemVerilog.Ordered 0 before.toList) (scope : InScope refs before.size)
    (success : expression a refs e before = .ok (pair,after)) (realized : NetRealizes env after) :
    pair.Meaning env (e.value.eval r) (e.valid.eval r) := by
  rw [expression] at success
  obtain ⟨value,middle,first,next⟩ := bind_success _ _ success
  obtain ⟨guard,last,second,next⟩ := bind_success _ _ next
  obtain ⟨valid,third,rfl⟩ := return_success _ _ next
  obtain ⟨midGood,grows,_⟩ := term_builds a refs e.value before good scope first
  obtain ⟨lastGood,more,gScope⟩ := validity_builds a refs e.valid middle midGood
    (scope.mono grows.size_le) guard last second
  obtain ⟨_,latest,_⟩ := fresh_builds (rhs:=.select guard (.integer 1) (.integer 0))
    ⟨gScope,trivial,trivial⟩ lastGood third
  have valMeaning := term_correct a r refs e.value physical.1 bindings good scope first
    (realized.restrict (more.trans latest))
  have guardMeaning := validity_correct a r refs e.valid physical.2 bindings midGood
    (scope.mono grows.size_le) second (realized.restrict latest)
  have one := SignedMeaning.integer (env:=env) 1
  have zero := SignedMeaning.integer (env:=env) 0
  have boolean := SignedMeaning.select_bool guardMeaning.evaluated one.typed zero.typed (fun _ => one) (fun _ => zero)
  have assigned : AssignedMeaning env (.select guard (.integer 1) (.integer 0)) 2
      (if e.valid.eval r then 1 else 0) := by
    exact boolean.assigned (by cases e.valid.eval r <;> decide)
  exact ⟨valMeaning,fresh_correct assigned third realized⟩

structure SignalMatches (env : Environment) (signals : Array Signal) (values : Array Int) : Prop where
  sizes : signals.size = values.size
  meaning : ∀ (n : Nat) (sig : Signal), signals[n]? = some sig →
    SignedMeaning env (.reference sig.name) sig.width (values[n]?.getD 0)

theorem SignalMatches.push {signals : Array Signal} {values : Array Int} {signal : Signal} {value : Int} (h : SignalMatches env signals values)
    (newMeaning : SignedMeaning env (.reference signal.name) signal.width value) :
    SignalMatches env (signals.push signal) (values.push value) := by
  refine ⟨by simp [h.sizes],?_⟩
  intro n sig found
  by_cases hn : n = signals.size
  · simp [Array.getElem?_push,hn] at found
    subst sig
    have nv : (values.push value)[n]? = some value := by
      rw [hn,h.sizes,Array.getElem?_push_size]
    simpa only [nv,Option.getD_some] using newMeaning
  · have old : signals[n]? = some sig := by simpa [Array.getElem?_push,hn] using found
    simpa [Array.getElem?_push,← h.sizes,hn] using h.meaning n sig old

def CodePhysical (a : Artifact) (r : Runtime) (env : Environment) : LocalRTL.Code → Prop
  | .source e => Physical a r env none e.value ∧ PhysicalValidity a r env none e.valid
  | .localNode e => ∀ refs values,
      Physical a (LocalRTL.fullRuntime r values) env (some refs) e.value ∧
      PhysicalValidity a (LocalRTL.fullRuntime r values) env (some refs) e.valid

theorem code_correct (a : Artifact) (r : Runtime) (refs : Array Signal) (values : Array Int) (c : LocalRTL.Code)
    (physical : CodePhysical a r env c) (correspondence : SignalMatches env refs values)
    (good : SystemVerilog.Ordered 0 before.toList) (scope : InScope (some refs) before.size)
    (success : code a refs c before = .ok (pair,after)) (realized : NetRealizes env after) :
    pair.Meaning env (c.value r values) (c.valid r values) := by
  cases c with
  | source e =>
    exact expression_correct a r none e physical
      (by intro xs h; cases h) good (by intro xs h; cases h) success realized
  | localNode e =>
    apply expression_correct a (LocalRTL.fullRuntime r values) (some refs) e (physical refs values) ?_ good scope success realized
    intro xs he n signal found
    cases he
    exact correspondence.meaning n signal found

theorem graph_correct (a : Artifact) (r : Runtime) (cs : List LocalRTL.Code)
    (physical : ∀ c ∈ cs, CodePhysical a r env c)
    (good : SystemVerilog.Ordered 0 before.toList)
    (success : graph a cs before = .ok (refs,after)) (realized : NetRealizes env after) :
    SignalMatches env refs (LocalRTL.fullValues r cs) := by
  induction cs generalizing before refs after with
  | nil =>
    obtain ⟨rfl,rfl⟩ := pure_success _ success
    exact ⟨rfl,by intro n sig h; simp at h⟩
  | cons c cs ih =>
    rw [graph] at success
    obtain ⟨previous,middle,first,next⟩ := bind_success _ _ success
    obtain ⟨pair,second,rfl⟩ := return_success _ _ next
    obtain ⟨midGood,grows,prevScope⟩ := graph_builds a cs before good (by intro xs h; cases h) previous middle first
    obtain ⟨_,more,_⟩ := code_builds a previous c middle midGood prevScope pair after second
    have previousMeaning := ih (fun c hc => physical c (by simp [hc])) good first (realized.restrict more)
    have pairMeaning := code_correct a r previous (LocalRTL.fullValues r cs) c
      (physical c (by simp)) previousMeaning midGood prevScope second realized
    exact (previousMeaning.push pairMeaning.1).push pairMeaning.2

/-- Observe the emitted value only when its emitted validity is nonzero. -/
def Pair.observe (pair : Pair) (env : Environment) : Option Int := do
  let valid ← (SystemVerilog.Expr.reference pair.valid.name).eval env none
  if valid.integer != 0 then
    return (← (SystemVerilog.Expr.reference pair.value.name).eval env none).integer
  else none

theorem Pair.observe_correct {pair : Pair} {value : Int} {valid : Bool} (h : pair.Meaning env value valid) :
    pair.observe env = if valid then some value else none := by
  simp only [Pair.observe,h.1.self,h.2.self,bind,Option.bind,Value.integer,Value.ofInt,if_true,h.1.fits,h.2.fits]
  cases valid <;> rfl

theorem generate_correct (a : Artifact) (r : Runtime) (p : LocalRTL.Program)
    (physical : ∀ c ∈ p.code, CodePhysical a r env c)
    (success : generate a p = .ok output) (realized : NetRealizes env output.declarations) :
    output.result.observe env = p.fullEval r := by
  obtain ⟨refs,built,hv,hb⟩ := generate_graph success
  have correspondence := graph_correct a r p.code (before:=#[]) physical trivial built realized
  have valueMeaning := correspondence.meaning _ _ hv
  have validMeaning := correspondence.meaning _ _ hb
  simp only [Pair.observe,valueMeaning.self,validMeaning.self,bind,Option.bind,
    Value.integer,Value.ofInt,if_true,valueMeaning.fits,validMeaning.fits,LocalRTL.Program.fullEval]
  split <;> rfl

end IRComparison.Circuit.Shared.NetEmission
