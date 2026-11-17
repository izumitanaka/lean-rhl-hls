import IRComparison.Frontend.LeanArithmetic

namespace IRComparison.LeanTyped
open Lean4Lean

namespace Standard
theorem intRefl (x : Int) : x = x := rfl
theorem intTrans (x y z : Int) (first : x = y) (second : y = z) : x = z :=
  first.trans second
theorem intCongr (f : Int → Int → Int) (x x' y y' : Int)
    (hx : x = x') (hy : y = y') : f x y = f x' y' := by rw [hx, hy]
end Standard

/-- Exact monomorphic types of fixed equality-composition lemmas. -/
def reflType : VExpr := .forallE intType (eqInt (.bvar 0) (.bvar 0))

def transType : VExpr :=
  .forallE intType (.forallE intType (.forallE intType
    (.forallE (eqInt (.bvar 2) (.bvar 1))
      (.forallE (eqInt (.bvar 2) (.bvar 1)) (eqInt (.bvar 4) (.bvar 2))))))

def congrType : VExpr :=
  .forallE (intArrows 2)
    (.forallE intType (.forallE intType (.forallE intType (.forallE intType
      (.forallE (eqInt (.bvar 3) (.bvar 2))
        (.forallE (eqInt (.bvar 2) (.bvar 1))
          (eqInt (.app (.app (.bvar 6) (.bvar 5)) (.bvar 3))
            (.app (.app (.bvar 6) (.bvar 4)) (.bvar 2)))))))))

variable {env : VEnv} {U : Nat} {context : List VExpr}

deriving instance DecidableEq for VLevel, VExpr

/-- Import a fixed monomorphic library theorem only if its translated type is
    exactly the expected signature. Equality of Expr's opaque runtime hashes
    is not used as proof of this correspondence. -/
structure FixedFact (nativeEnv : Lean.Environment) (name : Lean.Name) (type : VExpr) where
  declaration : Lean.TheoremVal
  found : nativeEnv.find? name = some (.thmInfo declaration)
  named : declaration.name = name
  monomorphic : declaration.levelParams = []
  represented : Represents declaration.type type

def loadFixedFact (nativeEnv : Lean.Environment) (name : Lean.Name) (type : VExpr) :
    Option (FixedFact nativeEnv name type) :=
  match found : nativeEnv.find? name with
  | some (.thmInfo declaration) => do
      if named : declaration.name = name then
        if mono : declaration.levelParams = [] then
          let actual ← translate declaration.type
          if same : actual.val = type then
            return ⟨declaration, found, named, mono, same ▸ actual.property⟩
          else none
        else none
      else none
  | _ => none

def FixedFact.install (_fact : FixedFact nativeEnv name type) (base : VEnv) : Option VEnv :=
  base.addConst name ⟨0, type⟩

theorem FixedFact.installed (fact : FixedFact nativeEnv name type)
    (accepted : fact.install base = some env) : env.constants name = some ⟨0, type⟩ :=
  VEnv.addConst_self accepted

theorem apply_refl
    (registered : env.constants ``Standard.intRefl = some ⟨0, reflType⟩)
    (hx : env.HasType U context x intType) :
    env.HasType U context (.app (.const ``Standard.intRefl []) x) (eqInt x x) := by
  have fact := VEnv.HasType.const (U := U) (Γ := context) (ls := []) registered (by simp) rfl
  simp only [reflType, eqInt, intType, VExpr.instL, List.map_cons, List.map_nil, VLevel.inst] at fact
  simpa only [eqInt, intType, VExpr.inst, VExpr.instVar_zero] using VEnv.HasType.app fact hx

/-- Composition produces an object-language equality proof, rather than
    pretending propositional equality is definitional equality. -/
theorem apply_trans
    (registered : env.constants ``Standard.intTrans = some ⟨0, transType⟩)
    (hx : env.HasType U context x intType)
    (hy : env.HasType U context y intType)
    (hz : env.HasType U context z intType)
    (hp : env.HasType U context p (eqInt x y))
    (hq : env.HasType U context q (eqInt y z)) :
    env.HasType U context
      (applications (.const ``Standard.intTrans []) [x,y,z,p,q]) (eqInt x z) := by
  have fact := VEnv.HasType.const (U := U) (Γ := context) (ls := []) registered (by simp) rfl
  simp only [transType, eqInt, intType, VExpr.instL, List.map_cons, List.map_nil, VLevel.inst] at fact
  have a := VEnv.HasType.app fact hx
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst, VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a
  have b := VEnv.HasType.app a hy
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst, VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at b
  have c := VEnv.HasType.app b hz
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst, VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at c
  have d := VEnv.HasType.app c hp
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst, VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at d
  have e := VEnv.HasType.app d hq
  simpa only [applications, eqInt, intType, VExpr.inst, VExpr.inst_lift] using e

theorem apply_congr
    (registered : env.constants ``Standard.intCongr = some ⟨0, congrType⟩)
    (hf : env.HasType U context f (intArrows 2))
    (hx : env.HasType U context x intType)
    (hx' : env.HasType U context x' intType)
    (hy : env.HasType U context y intType)
    (hy' : env.HasType U context y' intType)
    (hp : env.HasType U context p (eqInt x x'))
    (hq : env.HasType U context q (eqInt y y')) :
    env.HasType U context
      (applications (.const ``Standard.intCongr []) [f,x,x',y,y',p,q])
      (eqInt (.app (.app f x) y) (.app (.app f x') y')) := by
  have fact := VEnv.HasType.const (U := U) (Γ := context) (ls := []) registered (by simp) rfl
  simp only [congrType, intArrows, eqInt, intType, VExpr.instL,
    List.map_cons, List.map_nil, VLevel.inst] at fact
  have a := VEnv.HasType.app fact hf
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at a
  have b := VEnv.HasType.app a hx
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at b
  have c := VEnv.HasType.app b hx'
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at c
  have d := VEnv.HasType.app c hy
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at d
  have e := VEnv.HasType.app d hy'
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at e
  have g := VEnv.HasType.app e hp
  simp only [Nat.reduceAdd, ← VExpr.lift_instN_lo, VExpr.inst_lift, VExpr.inst,
    VExpr.instVar_lower, VExpr.instVar_succ, VExpr.instVar_zero] at g
  have h := VEnv.HasType.app g hq
  simpa only [applications, eqInt, intType, VExpr.inst, VExpr.inst_lift] using h

/-- Executable composition of the operator proof and the two recursively
    obtained child proofs. It never invokes a per-input proof checker. -/
def composeBinary (source head x y x' y' operatorProof leftProof rightProof : VExpr) : VExpr :=
  applications (.const ``Standard.intTrans [])
    [source, .app (.app head x) y, .app (.app head x') y', operatorProof,
      applications (.const ``Standard.intCongr []) [head,x,x',y,y',leftProof,rightProof]]

theorem composeBinary_correct
    (transRegistered : env.constants ``Standard.intTrans = some ⟨0, transType⟩)
    (congrRegistered : env.constants ``Standard.intCongr = some ⟨0, congrType⟩)
    (hs : env.HasType U context source intType)
    (hf : env.HasType U context head (intArrows 2))
    (hx : env.HasType U context x intType) (hy : env.HasType U context y intType)
    (hx' : env.HasType U context x' intType) (hy' : env.HasType U context y' intType)
    (operator : env.HasType U context operatorProof (eqInt source (.app (.app head x) y)))
    (left : env.HasType U context leftProof (eqInt x x'))
    (right : env.HasType U context rightProof (eqInt y y')) :
    env.HasType U context
      (composeBinary source head x y x' y' operatorProof leftProof rightProof)
      (eqInt source (.app (.app head x') y')) := by
  have oldTyped : env.HasType U context (.app (.app head x) y) intType :=
    .app (.app hf hx) hy
  have newTyped : env.HasType U context (.app (.app head x') y') intType :=
    .app (.app hf hx') hy'
  exact apply_trans transRegistered hs oldTyped newTyped operator
    (apply_congr congrRegistered hf hx hx' hy hy' left right)

end IRComparison.LeanTyped

namespace IRComparison.LeanArithmetic
open Lean4Lean LeanTyped
variable {env : VEnv} {U : Nat} {context : List VExpr}

/-- The parser's concrete binary result now composes with arbitrary proved
    child normalizations, using the same selected operator on both paths. -/
theorem BinaryArtifact.children_correct (a : BinaryArtifact nativeEnv layout source)
    (transRegistered : env.constants ``Standard.intTrans = some ⟨0, transType⟩)
    (congrRegistered : env.constants ``Standard.intCongr = some ⟨0, congrType⟩)
    (opRegistered : env.constants (factName a.op) = some a.fact.view.signature)
    (hs : env.HasType U context a.sourceCore intType)
    (hf : env.HasType U context (.const a.op.primitive []) (intArrows 2))
    (hx : env.HasType U context a.leftCore.val intType)
    (hy : env.HasType U context a.rightCore.val intType)
    (hx' : env.HasType U context x' intType) (hy' : env.HasType U context y' intType)
    (left : env.HasType U context p (eqInt a.leftCore.val x'))
    (right : env.HasType U context q (eqInt a.rightCore.val y')) :
    env.HasType U context
      (composeBinary a.sourceCore (.const a.op.primitive []) a.leftCore.val a.rightCore.val
        x' y' a.proofTerm p q)
      (eqInt a.sourceCore (.app (.app (.const a.op.primitive []) x') y')) :=
  composeBinary_correct transRegistered congrRegistered hs hf hx hy hx' hy'
    (a.normalization_correct opRegistered hx hy) left right

end IRComparison.LeanArithmetic
