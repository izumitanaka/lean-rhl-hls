import IRComparison.Circuit.SystemVerilog.Netlist

namespace IRComparison.Circuit.SystemVerilog

/-- Dense declaration order, and no forward/self reference. -/
def Ordered : Nat → List Wire → Prop
  | _,[] => True
  | n,w::rest => w.name = .temporary n ∧ w.value.Before n ∧ Ordered (n+1) rest

theorem ordered_append (leftDecls rightDecls : List Wire) (start : Nat) :
    Ordered start (leftDecls ++ rightDecls) ↔ Ordered start leftDecls ∧ Ordered (start+leftDecls.length) rightDecls := by
  induction leftDecls generalizing start with
  | nil => simp [Ordered]
  | cons wire rest ih =>
    simp [Ordered,ih,and_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- The final environment satisfies every continuous assignment, including
its declared width. This does not yet assert source-term correspondence. -/
def Satisfies (base : Environment) (values : Array Int) : Nat → List Wire → Prop
  | _,[] => True
  | n,w::rest => w.name = .temporary n ∧
      (∃ bits : BitVec w.width, w.value.assignment (base.withTemporaries values) w.width = some bits ∧
        values[n]? = some bits.toInt) ∧ Satisfies base values (n+1) rest

theorem Environment.temporaries_append (base : Environment) (values extra : Array Int) :
    Environment.AgreesBefore values.size (base.withTemporaries values) (base.withTemporaries (values ++ extra)) := by
  constructor
  · intro n hn; rfl
  · intro n hn
    cases n <;> simp_all [withTemporaries,Name.Before,Array.getElem?_append]
  · intro n hn; rfl

theorem appendWires_extends (base : Environment) (wires : List Wire) (values result : Array Int)
    (success : appendWires base wires values = some result) :
    ∃ extra, result = values ++ extra ∧ extra.size = wires.length := by
  induction wires generalizing values with
  | nil => cases success; exact ⟨#[],by simp,by simp⟩
  | cons wire rest ih =>
    simp only [appendWires] at success
    split at success
    · cases computed : wire.value.assignment (base.withTemporaries values) wire.width with
      | none => simp [computed] at success
      | some bits =>
        simp only [computed,bind,Option.bind,pure,PUnit.unit] at success
        obtain ⟨extra,he,hl⟩ := ih (values.push bits.toInt) success
        refine ⟨#[bits.toInt] ++ extra,?_,?_⟩
        · simpa only [Array.push_eq_append,Array.append_assoc] using he
        · simp [hl,Nat.add_comm]
    · simp at success

theorem appendWires_satisfies (base : Environment) (wires : List Wire) (values result : Array Int)
    (ordered : Ordered values.size wires) (success : appendWires base wires values = some result) :
    Satisfies base result values.size wires := by
  induction wires generalizing values with
  | nil => trivial
  | cons wire rest ih =>
    obtain ⟨named,inScope,following⟩ := ordered
    simp only [appendWires,named,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,↓reduceIte,
      pure,bind,Option.bind] at success
    cases computed : wire.value.assignment (base.withTemporaries values) wire.width with
    | none => simp [computed] at success
    | some bits =>
      simp only [computed,bind,Option.bind] at success
      have restOrdered : Ordered (values.push bits.toInt).size rest := by simpa using following
      have tail := ih (values.push bits.toInt) restOrdered success
      obtain ⟨extra,extended,hl⟩ := appendWires_extends base rest (values.push bits.toInt) result success
      have extended' : result = values ++ (#[bits.toInt] ++ extra) := by
        simpa only [Array.push_eq_append,Array.append_assoc] using extended
      refine ⟨named,⟨bits,?_,?_⟩,by simpa using tail⟩
      · rw [extended',← wire.value.assignment_agrees inScope (base.temporaries_append values _) wire.width]
        exact computed
      · rw [extended']
        simp [Array.getElem?_append]

/-- Successful evaluation of an ordered generated netlist solves its actual
SystemVerilog assignments simultaneously. Names and data sharing are covered
for arbitrary input environments, not just concrete benchmark states. -/
theorem evaluateWires_satisfies (a : Artifact) (r : FiniteRuntime a.storageShape)
    (declarations : Array Wire) (ordered : Ordered 0 declarations.toList)
    (evaluated : evaluateWires a r declarations = some result) :
    Satisfies (environment a r declarations #[]) result 0 declarations.toList :=
  appendWires_satisfies _ _ #[] _ ordered evaluated

end IRComparison.Circuit.SystemVerilog
