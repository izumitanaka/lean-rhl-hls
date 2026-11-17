import IRComparison.Frontend.LeanNegNormalization

namespace IRComparison.LeanArithmeticNormalization
open Lean4Lean LeanTyped LeanArithmetic

/-- A proof plan for normalization of binary arithmetic islands in an actual
    Expr. Leaves preserve the exact source expression; this is not a new input
    AST, and let/conditionals are not claimed to be normalized by this pass. -/
inductive Plan (nativeEnv : Lean.Environment) : Lean.Expr → Type where
  | leaf (core : {v : VExpr // Represents source v}) : Plan nativeEnv source
  | literal (n : Nat) (fact : FixedFact nativeEnv ``Standard.literal LeanLiteralNormalization.signature) :
      Plan nativeEnv (LeanLiteralNormalization.source n)
  | elaboratedLiteral (n : Nat)
      (fact : FixedFact nativeEnv ``LeanLiteralNormalization.elaboratedFact LeanLiteralNormalization.elaboratedSignature) :
      Plan nativeEnv (LeanLiteralNormalization.elaboratedSource n)
  | negative (flavor : LeanNegNormalization.Flavor)
      (fact : FixedFact nativeEnv flavor.fact flavor.signature) (body : Plan nativeEnv arg) :
      Plan nativeEnv (.app flavor.head arg)
  | binary (op : LeanScalar.Op) (fact : OperatorFact nativeEnv op)
      (leftPlan : Plan nativeEnv left) (rightPlan : Plan nativeEnv right) :
      Plan nativeEnv (.app (.app op.surfaceHead left) right)
  | metadata (body : Plan nativeEnv source) : Plan nativeEnv (.mdata data source)

def plan (nativeEnv : Lean.Environment) : (source : Lean.Expr) → Option (Plan nativeEnv source)
  | .app (.const ``Int.neg []) arg => do
      let fact ← loadFixedFact nativeEnv LeanNegNormalization.Flavor.core.fact LeanNegNormalization.Flavor.core.signature
      return .negative .core fact (← plan nativeEnv arg)
  | .app (.app (.app (.const ``Neg.neg [.zero]) (.const ``Int [])) (.const ``Int.instNegInt [])) arg => do
      let fact ← loadFixedFact nativeEnv LeanNegNormalization.Flavor.surface.fact LeanNegNormalization.Flavor.surface.signature
      return .negative .surface fact (← plan nativeEnv arg)
  | .app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Int [])) (.lit (.natVal n)))
      (.app (.const ``instOfNat []) (.lit (.natVal m))) => do
      if same : m = n then
        let fact ← loadFixedFact nativeEnv ``Standard.literal LeanLiteralNormalization.signature
        return same ▸ .literal n fact
      else none
  | .app (.const ``Int.ofNat [])
      (.app (.app (.app (.const ``OfNat.ofNat [.zero]) (.const ``Nat [])) (.lit (.natVal n)))
        (.app (.const ``instOfNatNat []) (.lit (.natVal m)))) => do
      if same : m = n then
        let fact ← loadFixedFact nativeEnv ``LeanLiteralNormalization.elaboratedFact LeanLiteralNormalization.elaboratedSignature
        return same ▸ .elaboratedLiteral n fact
      else none
  | .app (.app head left) right =>
      match LeanScalar.checkBinaryHead head with
      | some ⟨op, same⟩ => do
          let fact ← loadOperator nativeEnv op
          let lp ← plan nativeEnv left
          let rp ← plan nativeEnv right
          return same ▸ .binary op fact lp rp
      | none => return .leaf (← translate (.app (.app head left) right))
  | .mdata _ body => return .metadata (← plan nativeEnv body)
  | source => return .leaf (← translate source)

def Plan.sourceCore : Plan nativeEnv source → VExpr
  | .leaf core => core.val
  | .elaboratedLiteral n _ => LeanLiteralNormalization.elaboratedCore (numeral n)
  | .literal n _ => LeanLiteralNormalization.core (numeral n)
  | .negative flavor _ body => .app flavor.coreHead body.sourceCore
  | .binary _ fact left right =>
      .app (.app fact.view.leftCore.val left.sourceCore) right.sourceCore
  | .metadata body => body.sourceCore

def Plan.normalizedCore : Plan nativeEnv source → VExpr
  | .leaf core => core.val
  | .elaboratedLiteral n _ => LeanLiteralNormalization.target (numeral n)
  | .literal n _ => LeanLiteralNormalization.target (numeral n)
  | .negative _ _ body => LeanNegNormalization.target body.normalizedCore
  | .binary op _ left right =>
      .app (.app (.const op.primitive []) left.normalizedCore) right.normalizedCore
  | .metadata body => body.normalizedCore

/-- The normalized source is still a Lean.Expr. The proof representation is
    never used as a replacement source language for the HLS frontend. -/
def Plan.expression : Plan nativeEnv source → Lean.Expr
  | .leaf (source := source) _ => source
  | .elaboratedLiteral n _ => .app (.const ``Int.ofNat []) (.lit (.natVal n))
  | .literal n _ => .app (.const ``Int.ofNat []) (.lit (.natVal n))
  | .negative _ _ body => .app (.app (.const ``Int.sub []) (LeanBindings.quoteInt 0)) body.expression
  | .binary op _ left right =>
      .app (.app (.const op.primitive []) left.expression) right.expression
  | .metadata body => body.expression

def Plan.proofTerm : Plan nativeEnv source → VExpr
  | .leaf core => .app (.const ``Standard.intRefl []) core.val
  | .elaboratedLiteral n _ => .app (.const ``LeanLiteralNormalization.elaboratedFact []) (numeral n)
  | .literal n _ => .app (.const ``Standard.literal []) (numeral n)
  | .negative flavor _ body =>
      applications (.const flavor.fact []) [body.sourceCore,body.normalizedCore,body.proofTerm]
  | .binary op fact left right =>
      composeBinary
        (.app (.app fact.view.leftCore.val left.sourceCore) right.sourceCore)
        (.const op.primitive []) left.sourceCore right.sourceCore
        left.normalizedCore right.normalizedCore
        (.app (.app (.const (factName op) []) left.sourceCore) right.sourceCore)
        left.proofTerm right.proofTerm
  | .metadata body => body.proofTerm

theorem Plan.represents_source (p : Plan nativeEnv source) : Represents source p.sourceCore := by
  induction p with
  | leaf core => exact core.property
  | elaboratedLiteral n fact => exact LeanLiteralNormalization.elaborated_represents n
  | literal n fact => exact LeanLiteralNormalization.represents n
  | negative flavor fact body ih => exact .app flavor.represents ih
  | binary op fact left right ihl ihr => exact .app (.app fact.left_represents ihl) ihr
  | metadata body ih => exact .metadata ih

theorem Plan.represents_normalized (p : Plan nativeEnv source) :
    Represents p.expression p.normalizedCore := by
  induction p with
  | leaf core => exact core.property
  | elaboratedLiteral n fact => exact .app (.constant rfl) .natural
  | literal n fact => exact .app (.constant rfl) .natural
  | negative flavor fact body ih => exact .app (.app (.constant rfl) (integer_represents 0)) ih
  | binary op fact left right ihl ihr => exact .app (.app (.constant rfl) ihl) ihr
  | metadata body ih => exact ih

/-- Consistency with the old scalar interpretation. This does not identify
    that interpretation with the formal Lean semantics. -/
private theorem surface_inv (op : LeanScalar.Op)
    (h : NativeRHL.ExprAnalysis.Denotes (.app (.app op.surfaceHead l) r) values result) :
    ∃ x y, NativeRHL.ExprAnalysis.Denotes l values x ∧
      NativeRHL.ExprAnalysis.Denotes r values y ∧ result = LeanScalar.meaning op x y := by
  generalize he : Lean.Expr.app (.app op.surfaceHead l) r = e at h
  cases h <;> cases op <;>
    simp_all [LeanScalar.Op.surfaceHead, LeanScalar.meaning,
      NativeRHL.ExprAnalysis.addHead, NativeRHL.ExprAnalysis.subHead,
      NativeRHL.ExprAnalysis.mulHead, NativeRHL.ExprAnalysis.divHead,
      NativeRHL.ExprAnalysis.modHead, NativeRHL.ExprAnalysis.conditional,
      NativeRHL.ExprAnalysis.nonzeroCond]
  all_goals grind

private theorem negative_inv (flavor : LeanNegNormalization.Flavor)
    (h : NativeRHL.ExprAnalysis.Denotes (.app flavor.head arg) values result) :
    ∃ x, NativeRHL.ExprAnalysis.Denotes arg values x ∧ result = -x := by
  generalize he : Lean.Expr.app flavor.head arg = e at h
  cases h <;> cases flavor <;> simp_all [LeanNegNormalization.Flavor.head,
    NativeRHL.ExprAnalysis.addHead, NativeRHL.ExprAnalysis.subHead,
    NativeRHL.ExprAnalysis.mulHead, NativeRHL.ExprAnalysis.divHead,
    NativeRHL.ExprAnalysis.modHead, NativeRHL.ExprAnalysis.conditional,
    NativeRHL.ExprAnalysis.nonzeroCond]
  all_goals grind

theorem Plan.preserves_denotes (p : Plan nativeEnv source)
    (h : NativeRHL.ExprAnalysis.Denotes source values result) :
    NativeRHL.ExprAnalysis.Denotes p.expression values result := by
  induction p generalizing result with
  | leaf core => exact h
  | elaboratedLiteral n fact =>
      have same := NativeRHL.ExprAnalysis.denotes_unique h
        (NativeRHL.ExprAnalysis.Denotes.elaboratedLiteral (env := values) (n := n))
      cases same
      exact .literal
  | literal n fact =>
      have same := NativeRHL.ExprAnalysis.denotes_unique h
        (NativeRHL.ExprAnalysis.Denotes.surfaceLiteral (env := values) (n := n))
      cases same
      exact .literal
  | negative flavor fact body ih =>
      obtain ⟨v,hv,rfl⟩ := negative_inv flavor h
      have result := NativeRHL.ExprAnalysis.Denotes.sub
        (NativeRHL.ExprAnalysis.Denotes.literal (env := values) (n := 0)) (ih hv)
      have arithmetic : Int.sub (Int.ofNat 0) v = -v := Int.zero_sub v
      rw [arithmetic] at result
      exact result
  | metadata body ih => cases h with | metadata h => exact ih h
  | binary op fact left right ihl ihr =>
      obtain ⟨x, y, hx, hy, rfl⟩ := surface_inv op h
      cases op
      · exact .add (ihl hx) (ihr hy)
      · exact .sub (ihl hx) (ihr hy)
      · exact .mul (ihl hx) (ihr hy)
      · exact .div (ihl hx) (ihr hy)

/-- Recompiling a normalized expression preserves the existing scalar
    compiler's generated value. This is a consistency result for both passes;
    the separate formal-Lean-to-value bridge is not assumed here. -/
theorem Plan.compilers_agree (p : Plan nativeEnv source)
    (before : LeanScalar.Artifact layout source)
    (after : LeanScalar.Artifact layout p.expression) (i x y : Int) (s : State) :
    before.native i x y s = after.native i x y s ∧
    before.code.expr.eval i x y s = after.code.expr.eval i x y s := by
  have same := NativeRHL.ExprAnalysis.denotes_unique
    (p.preserves_denotes (before.denotes i x y s)) (after.denotes i x y s)
  exact ⟨same, by rw [before.code.correct, after.code.correct, same]⟩

variable {env : VEnv} {U : Nat} {context : List VExpr}

/-- Remaining obligations concern only source typing and library declarations.
    No source/output equality is requested, even for the leaves. -/
def Plan.Ready {env : VEnv} {U : Nat} {context : List VExpr} : Plan nativeEnv source → Prop
  | .leaf core => env.HasType U context core.val intType
  | .literal n _ =>
      env.constants ``Standard.literal = some ⟨0, LeanLiteralNormalization.signature⟩ ∧
      env.HasType U context (numeral n) LeanLiteralNormalization.natType ∧
      env.HasType U context (LeanLiteralNormalization.core (numeral n)) intType ∧
      env.HasType U context (LeanLiteralNormalization.target (numeral n)) intType
  | .elaboratedLiteral n _ =>
      env.constants ``LeanLiteralNormalization.elaboratedFact = some ⟨0, LeanLiteralNormalization.elaboratedSignature⟩ ∧
      env.HasType U context (numeral n) LeanLiteralNormalization.natType ∧
      env.HasType U context (LeanLiteralNormalization.elaboratedCore (numeral n)) intType ∧
      env.HasType U context (LeanLiteralNormalization.target (numeral n)) intType
  | .negative flavor _ body =>
      env.constants flavor.fact = some ⟨0,flavor.signature⟩ ∧
      env.HasType U context (.app flavor.coreHead body.sourceCore) intType ∧
      env.HasType U context (LeanNegNormalization.target body.normalizedCore) intType ∧
      body.Ready (env := env) (U := U) (context := context)
  | .binary op fact left right =>
      env.constants (factName op) = some fact.view.signature ∧
      env.HasType U context fact.view.leftCore.val (intArrows 2) ∧
      env.HasType U context (.const op.primitive []) (intArrows 2) ∧
      left.Ready (env := env) (U := U) (context := context) ∧
      right.Ready (env := env) (U := U) (context := context)
  | .metadata body => body.Ready (env := env) (U := U) (context := context)

/-- Soundness of the recursive proof-producing pass. Child equalities are
    derived by induction, not provided by the caller or tested on examples. -/
theorem Plan.correct (p : Plan nativeEnv source)
    (reflRegistered : env.constants ``Standard.intRefl = some ⟨0, reflType⟩)
    (transRegistered : env.constants ``Standard.intTrans = some ⟨0, transType⟩)
    (congrRegistered : env.constants ``Standard.intCongr = some ⟨0, congrType⟩)
    (ready : p.Ready (env := env) (U := U) (context := context)) :
    env.HasType U context p.sourceCore intType ∧
    env.HasType U context p.normalizedCore intType ∧
    env.HasType U context p.proofTerm (eqInt p.sourceCore p.normalizedCore) := by
  induction p with
  | leaf core => exact ⟨ready, ready, apply_refl reflRegistered ready⟩
  | elaboratedLiteral n fact =>
      obtain ⟨registered, hn, hs, ht⟩ := ready
      exact ⟨hs, ht, LeanLiteralNormalization.apply_elaborated registered hn⟩
  | literal n fact =>
      obtain ⟨registered, hn, hs, ht⟩ := ready
      exact ⟨hs, ht, LeanLiteralNormalization.apply_literal registered hn⟩
  | negative flavor fact body ih =>
      obtain ⟨registered,hs,ht,hb⟩ := ready
      obtain ⟨bs,bt,bp⟩ := ih hb
      exact ⟨hs,ht,LeanNegNormalization.apply_neg flavor registered bs bt bp⟩
  | binary op fact left right ihl ihr =>
      obtain ⟨registered, hhead, hprimitive, hl, hr⟩ := ready
      obtain ⟨hls, hlt, hlp⟩ := ihl hl
      obtain ⟨hrs, hrt, hrp⟩ := ihr hr
      have hs : env.HasType U context
          (.app (.app fact.view.leftCore.val left.sourceCore) right.sourceCore) intType :=
        .app (.app hhead hls) hrs
      have ht : env.HasType U context
          (.app (.app (.const op.primitive []) left.normalizedCore) right.normalizedCore) intType :=
        .app (.app hprimitive hlt) hrt
      exact ⟨hs, ht, composeBinary_correct transRegistered congrRegistered hs hprimitive
        hls hrs hlt hrt (fact.apply registered hls hrs) hlp hrp⟩
  | metadata body ih => exact ih ready

theorem plan_correct (p : Plan nativeEnv source)
    (_accepted : plan nativeEnv source = some p)
    (reflRegistered : env.constants ``Standard.intRefl = some ⟨0, reflType⟩)
    (transRegistered : env.constants ``Standard.intTrans = some ⟨0, transType⟩)
    (congrRegistered : env.constants ``Standard.intCongr = some ⟨0, congrType⟩)
    (ready : p.Ready (env := env) (U := U) (context := context)) :
    Represents source p.sourceCore ∧
    env.HasType U context p.proofTerm (eqInt p.sourceCore p.normalizedCore) :=
  ⟨p.represents_source, (p.correct reflRegistered transRegistered congrRegistered ready).2.2⟩

end IRComparison.LeanArithmeticNormalization
