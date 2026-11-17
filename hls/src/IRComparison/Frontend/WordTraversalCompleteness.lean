import IRComparison.Frontend.WordFrontend

namespace IRComparison.WordFrontend
open Lean4Lean LeanTyped LeanTypeInference Lean.Order
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem ClosedTerm.bindingIndex_value (n : Nat) :
    numeralValue (ClosedTerm.bindingIndex n).represented.val = some n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ClosedTerm.bindingIndex,ClosedTerm.app,List.map_cons,
      List.map_nil,applications,numeralValue,ih,Option.map_some]

theorem ClosedTerm.bindingIndex_size (n : Nat) :
    syntaxSize (ClosedTerm.bindingIndex n).val = 2*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ClosedTerm.bindingIndex,ClosedTerm.app,WordFrontend.app,List.map_cons,
      List.map_nil,List.foldl_cons,List.foldl_nil,syntaxSize,ih]
    omega

theorem ClosedTerm.bindingIndex_typed (signatures : NatSignatures env) (n : Nat) :
    DirectTyping env U ctx (ClosedTerm.bindingIndex n).represented.val (.const ``Nat []) := by
  induction n with
  | zero => exact signatures.zero_typed
  | succ n ih => exact signatures.successor_typed ih

theorem closedTerm_complete (shape : RepresentableSyntax source)
    (closed : isClosed source = true) :
    ∃ result, closedTerm source = some result ∧ result.val = source := by
  obtain ⟨represented,found⟩ := shape.translate_complete
  simp only [closedTerm,dif_pos closed,found,bind,Option.bind]
  exact ⟨_,rfl,rfl⟩

/-- Every generated target already has its exact proof-side representation.
This property is preserved by all parser constructors, not tested afterward. -/
theorem Piece.target_translate (piece : Piece env ctx p source spec) :
    ∃ result, translate piece.code = some result ∧ result.val = piece.represented.val :=
  piece.represented.property.translate_complete

/-- Local proof selection cannot fail for an in-scope scalar, regardless of
the number of surrounding scalar bindings. It does not assert that the later
typechecker accepts the selected proof. -/
theorem localFact_complete (p : Inputs) (locals : List Lean.Expr) (n : Nat)
    (bound : n < locals.length) : ∃ proof, localFact p n locals = some proof := by
  induction locals generalizing n with
  | nil => simp at bound
  | cons value rest ih =>
    cases n with
    | zero => exact ⟨_,rfl⟩
    | succ n =>
      have smaller : n < rest.length := by simpa using bound
      obtain ⟨proof,found⟩ := ih n smaller
      simp only [localFact,found,List.getElem?_eq_getElem smaller,bind,Option.bind]
      exact ⟨_,rfl⟩

/-- Pure expression comparison is complete for equal represented terms;
no contract for Lean's external Expr.eqv implementation is assumed. -/
theorem sameTerm_complete (left : Represents a core) (right : Represents b core) :
    sameTerm a b = true := by
  obtain ⟨x,hx,ex⟩ := left.translate_complete
  obtain ⟨y,hy,ey⟩ := right.translate_complete
  simp [sameTerm,hx,hy,ex,ey]

theorem sameTerm_sound (left : Represents a ac) (right : Represents b bc)
    (same : sameTerm a b = true) : ac = bc := by
  obtain ⟨x,hx,ex⟩ := left.translate_complete
  obtain ⟨y,hy,ey⟩ := right.translate_complete
  simpa [sameTerm,hx,hy,ex,ey] using same

/-- Actual let preprocessing uses the already proved pure substitution on
Lean.Expr, so its representation follows without an external primitive axiom. -/
theorem leadingLet_let_represents {value body : Lean.Expr} (valueRep : Represents value valueCore)
    (bodyRep : Represents body bodyCore) :
    ∃ reduced, leadingLet (.letE name ty value body flag) = some reduced ∧
      Represents reduced (bodyCore.inst valueCore) :=
  ⟨LeanBindings.instantiate value body,rfl,bodyRep.instantiate valueRep⟩

theorem leadingLet_beta_represents {value body : Lean.Expr} (valueRep : Represents value valueCore)
    (bodyRep : Represents body bodyCore) :
    ∃ reduced, leadingLet (.app (.lam name ty body info) value) = some reduced ∧
      Represents reduced (bodyCore.inst valueCore) := by
  refine ⟨LeanBindings.instantiate value body,?_,bodyRep.instantiate valueRep⟩
  rfl

end IRComparison.WordFrontend
