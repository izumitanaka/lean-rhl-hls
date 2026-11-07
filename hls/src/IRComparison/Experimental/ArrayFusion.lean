import IRComparison.Core.ArrayControlIR

namespace IRComparison.ArrayFusion

/-- Scalar instructions execute in order; even a failing, unused computation
    is preserved. No substitution duplicates work or discards failure. -/
abbrev Body := List Expr

def scalar (body : Body) (v : Int) : Option Int := body.foldlM (fun v e => ArrayIR.value e v) v

def mapping (body : Body) (xs : List Int) : Option (List Int) := xs.mapM (scalar body)
def generate (body : Body) (xs : List Int) : Option (List Int) :=
  xs.foldlM (fun out v => do return out ++ [← scalar body v]) []

theorem generate_eq (body : Body) (xs : List Int) : generate body xs = mapping body xs := by
  simpa [generate,mapping] using ArrayIR.fold_map (scalar body) xs []

theorem scalar_append (a b : Body) (v : Int) :
    scalar (a++b) v = (scalar a v).bind (scalar b) := by
  unfold scalar
  rw [List.foldlM_append]
  rfl

/-- Option hides unsuccessful partial outputs; there are no observable mapper
    effects. This is the explicit semantic condition allowing loop interchange. -/
theorem map_bind (f g : Int → Option Int) (xs : List Int) :
    (xs.mapM f).bind (List.mapM g) = xs.mapM (fun v => (f v).bind g) := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
    cases hf : f v with
    | none => simp [List.mapM_cons,hf]
    | some w =>
      cases hs : vs.mapM f with
      | none =>
        have ht : vs.mapM (fun v => (f v).bind g) = none := by simpa [hs] using ih.symm
        cases hg : g w <;> simp [List.mapM_cons,hf,hs,hg,ht]
      | some ws =>
        have ht : vs.mapM (fun v => (f v).bind g) = ws.mapM g := by simpa [hs] using ih.symm
        cases hg : g w <;> simp [List.mapM_cons,hf,hs,hg,ht]

theorem mapping_append (a b : Body) (xs : List Int) :
    mapping (a++b) xs = (mapping a xs).bind (mapping b) := by
  have h : scalar (a++b) = fun v => (scalar a v).bind (scalar b) := funext (scalar_append a b)
  unfold mapping
  rw [h]
  exact (map_bind (scalar a) (scalar b) xs).symm

@[simp] theorem mapping_nil (xs : List Int) : mapping [] xs = some xs := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
    simp only [mapping,List.mapM_cons]
    change (mapping [] vs).bind (fun ys => some (v::ys)) = some (v::vs)
    rw [ih]; rfl

/-- Each entry is a complete traversal, allocating a new destination array.
    Intermediate arrays are private, input/output ranges coincide by construction. -/
abbrev Loops := List Body

def runLoops : Loops → List Int → Option (List Int)
  | [],xs => some xs
  | b::bs,xs => (generate b xs).bind (runLoops bs)

/-- Fuse traversals by concatenating their scalar instruction bodies. -/
def fuseLoops (loops : Loops) : Body := loops.flatten

theorem fuseLoops_correct (loops : Loops) (xs : List Int) :
    generate (fuseLoops loops) xs = runLoops loops xs := by
  induction loops generalizing xs with
  | nil => simp [fuseLoops,generate_eq,runLoops]
  | cons b bs ih =>
    simp only [fuseLoops,List.flatten_cons,generate_eq,mapping_append,runLoops]
    cases h : mapping b xs with
    | none => rfl
    | some ys => simpa [generate_eq] using ih ys

/-- Functional producer/consumer composition remains explicit until fusion. -/
inductive Maps where
  | input
  | map (body : Body) (input : Maps)
  deriving Repr

def Maps.eval : Maps → List Int → Option (List Int)
  | .input,xs => some xs
  | .map b p,xs => (p.eval xs).bind (mapping b)

/-- Push composition into the element computation; no mutable state allocation. -/
def fuseMaps : Maps → Body
  | .input => []
  | .map b p => fuseMaps p ++ b

theorem fuseMaps_correct (p : Maps) (xs : List Int) : mapping (fuseMaps p) xs = p.eval xs := by
  induction p with
  | input => simp [fuseMaps,Maps.eval]
  | map b p ih => rw [fuseMaps,mapping_append,ih]; rfl

def loopsEval (p : Loops) (a : Array Int) := (runLoops p a.toList).map List.toArray
def mapsEval (p : Maps) (a : Array Int) := (p.eval a.toList).map List.toArray

theorem single_generate (e : Expr) (a : Array Int) :
    (generate [e] a.toList).map List.toArray = (ArrayIR.Imperative.generate e).eval a := by
  simp only [generate_eq,mapping,ArrayIR.Imperative.eval,ArrayIR.fold_map,List.nil_append]
  have h : scalar [e] = ArrayIR.value e := by funext v; simp [scalar]
  rw [h]
  cases a.toList.mapM (ArrayIR.value e) <;> rfl

end IRComparison.ArrayFusion
