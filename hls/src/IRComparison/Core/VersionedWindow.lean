import IRComparison.Core.VersionedWindowBody
namespace IRComparison.VersionedWindow
open AffineAddress SymbolicWindowExpr WindowSchedule
abbrev Body := VersionedHybrid.Term

def run (body : Body) (i x y : Int) (s : State) (ls : List Int := []) := body.eval i x y [s] ls

structure Compiled (array depth : Nat) (coefficient : Int) (offsets : List Int) (source : Body) where
  code : Body
  guards : List Linear
  frame : ∀ i x y s locals out, run source i x y s locals = some out → out.arrays array = s.arrays array
  correct : ∀ i, Valid guards i → ∀ (data : Array Int) (values locals : List Int) (s : State) (x y : Int),
    s.arrays array = data → Matches (arrayInput data) (keys coefficient offsets i) values → locals.length = depth →
    run code i x y s (locals++values) = run source i x y s locals

def compile (array depth : Nat) (coefficient : Int) (offsets : List Int) (source : Body) :
    Option (Compiled array depth coefficient offsets source) := do
  let p ← VersionedWindowBody.compile array depth coefficient offsets source
  return ⟨p.code,p.guards,fun i x y s ls out h => p.frame i x y s [] ls out h,
    fun i h data values locals s x y hf hh hl => p.correct i h data values locals s [] x y hf hh hl⟩
def accesses := VersionedWindowBody.accesses
end IRComparison.VersionedWindow
