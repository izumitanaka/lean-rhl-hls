import IRComparison.Circuit.SharedEmitConnection

namespace IRComparison.Circuit
open SystemVerilog

/-- Additional graph nets do not require invented cache entries or old expression
reconstruction. Existing cache entries retain their declared names and widths. -/
theorem Emission.WellFormed.extendDeclarations {before : Emission} (good : before.WellFormed)
    (ordered : SystemVerilog.Ordered 0 declarations.toList)
    (grows : Shared.NetEmission.Extends before.text declarations) :
    ({before with text := declarations} : Emission).WellFormed := by
  refine ⟨ordered,?_,?_⟩
  · intro entry member
    exact Name.before_mono (good.cached entry member) grows.size_le
  · intro entry member
    obtain ⟨n,named,width⟩ := good.widths entry member
    refine ⟨n,named,?_⟩
    have inside : n < before.text.size := by
      simpa [named,Name.Before] using good.cached entry member
    obtain ⟨extra,rfl⟩ := grows
    simpa [Array.getElem?_append,inside] using width

namespace Shared.NetEmission

/-- Standalone output is the empty-prefix specialization of the production
append operation, not a second traversal. -/
theorem append_generate (a : Artifact) (p : LocalRTL.Program) :
    generate a p = (append a p #[]).map (fun result => ⟨result.2,result.1⟩) := rfl

theorem append_builds (a : Artifact) (p : LocalRTL.Program)
    (good : SystemVerilog.Ordered 0 before.toList)
    (success : append a p before = .ok (pair,after)) :
    SystemVerilog.Ordered 0 after.toList ∧ Extends before after ∧ pair.InScope after.size := by
  obtain ⟨refs,built,hv,hb⟩ := append_graph success
  obtain ⟨ordered,grows,scope⟩ := graph_builds a p.code before good (by intro xs he; cases he) refs after built
  exact ⟨ordered,grows,scope refs rfl pair.value (by simpa using Array.mem_of_getElem? hv),
    scope refs rfl pair.valid (by simpa using Array.mem_of_getElem? hb)⟩

theorem append_correct (a : Artifact) (r : Runtime) (p : LocalRTL.Program)
    (physical : ∀ c ∈ p.code, CodePhysical a r env c)
    (good : SystemVerilog.Ordered 0 before.toList)
    (success : append a p before = .ok (pair,after)) (realized : NetRealizes env after) :
    pair.observe env = p.fullEval r := by
  obtain ⟨refs,built,hv,hb⟩ := append_graph success
  have h := graph_correct a r p.code physical good built realized
  have value := h.meaning _ _ hv
  have valid := h.meaning _ _ hb
  simp only [Pair.observe,value.self,valid.self,bind,Option.bind,
    Value.integer,Value.ofInt,if_true,value.fits,valid.fits,LocalRTL.Program.fullEval]
  split <;> rfl

/-- Compose the graph writer with the production emission state. The old cache
is untouched: no expanded term is manufactured for a graph node. -/
def intoPair (a : Artifact) (p : LocalRTL.Program) : EmitM Pair := fun before => do
  let (pair,declarations) ← append a p before.text
  pure (pair,{before with text := declarations})

def Pair.signal (pair : Pair) : Signal :=
  {pair.value with valid := .binary .ne (.reference pair.valid.name) (.integer 0)}

def into (a : Artifact) (p : LocalRTL.Program) : EmitM Signal :=
  Pair.signal <$> intoPair a p

theorem intoPair_result (success : intoPair a p before = .ok (pair,after)) :
    append a p before.text = .ok (pair,after.text) ∧ after.cache = before.cache := by
  unfold intoPair at success
  cases h : append a p before.text with
  | error why => simp [h,bind,Except.bind] at success
  | ok result =>
    obtain ⟨value,declarations⟩ := result
    simp only [h,bind,Except.bind,pure,Except.pure] at success
    cases success
    exact ⟨rfl,rfl⟩

theorem intoPair_builds (a : Artifact) (p : LocalRTL.Program) :
    Circuit.Builds (intoPair a p) (fun pair after => pair.InScope after.text.size) := by
  intro before good pair after success
  obtain ⟨built,cache⟩ := intoPair_result success
  obtain ⟨ordered,grows,scope⟩ := append_builds a p good.ordered built
  have stateEq : after = {before with text := after.text} := by cases after; cases before; simp_all
  refine ⟨stateEq ▸ good.extendDeclarations ordered grows,⟨grows,?_⟩,scope⟩
  exact ⟨#[],by simp [cache]⟩

theorem intoPair_correct (a : Artifact) (r : Runtime) (p : LocalRTL.Program)
    (physical : ∀ c ∈ p.code, CodePhysical a r env c)
    (good : before.WellFormed) (success : intoPair a p before = .ok (pair,after))
    (realized : Realizes env after) : pair.observe env = p.fullEval r :=
  append_correct a r p physical good.ordered (intoPair_result success).1 realized

/-- An appended graph does not change the meaning or membership of old cache
entries, even when its declarations are interleaved with ordinary terms. -/
theorem intoPair_cacheMeaning (success : intoPair a p before = .ok (pair,after))
    (meaning : CacheMeaning env r before) : CacheMeaning env r after := by
  intro entry member
  apply meaning entry
  simpa only [(intoPair_result success).2] using member

/-- The adapter returns the actual value and Boolean validity expected by the
production statement writer. Invalid payloads are not silently replaced by zero. -/
theorem into_signal_correct (a : Artifact) (r : Runtime) (p : LocalRTL.Program)
    (physical : ∀ c ∈ p.code, CodePhysical a r env c)
    (good : before.WellFormed) (success : into a p before = .ok (signal,after))
    (realized : Realizes env after) :
    SignedMeaning env (.reference signal.name) signal.width
      ((LocalRTL.fullValues r p.code)[2*p.result]?.getD 0) ∧
    BooleanMeaning env signal.valid
      ((LocalRTL.fullValues r p.code)[2*p.result+1]?.getD 0 != 0) := by
  obtain ⟨pair,built,rfl⟩ := map_success (intoPair a p) Pair.signal success
  obtain ⟨refs,graphBuilt,hv,hb⟩ := append_graph (intoPair_result built).1
  have correspondence := graph_correct a r p.code physical good.ordered graphBuilt realized
  have value := correspondence.meaning _ _ hv
  have valid := correspondence.meaning _ _ hb
  refine ⟨value,?_⟩
  exact valid.boolean_comparison (SignedMeaning.integer 0) (op:=.ne) rfl
    (by simp [SystemVerilog.arithmetic])

theorem intoPair_trace (a : Artifact) (r : Runtime) (p : LocalRTL.Program)
    (physical : ∀ c ∈ p.code, ∀ values, CodePhysical a r (base.withTemporaries values) c)
    (good : before.WellFormed) (trace : NetTrace base before.text)
    (success : intoPair a p before = .ok (pair,after)) : NetTrace base after.text := by
  obtain ⟨refs,built,_,_⟩ := append_graph (intoPair_result success).1
  exact graph_trace a r p.code physical good.ordered trace built

end Shared.NetEmission
end IRComparison.Circuit
