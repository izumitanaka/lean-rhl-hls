import IRComparison.Frontend.WordNativeInput
import IRComparison.Frontend.WordNaturalLiteral
import IRComparison.Frontend.WordGeneratedCode
import IRComparison.Frontend.FixedHLS

/-! First end-to-end source family for the structural completeness connection.
This is uniform in array identifiers, capacities and declarations. It is not
the general source grammar theorem: closure helpers and the remaining static
source induction still have to be connected. -/
namespace IRComparison.WordFrontend.FixedCopyCompleteness
open Lean4Lean LeanTyped LeanTypeInference Certificate Arithmetic NativeCompleteness

/-- Ordinary Lean computation, also used below to identify the executable
source of the backend theorem. No source IR or preconstructed Entry is given. -/
def program (destination origin count : Nat) (s : HybridWord.State) : Option HybridWord.State :=
  s.copy destination origin count

def original (destination origin count : Nat) (dn on cn : NatNotation) : Lean.Expr :=
  app ``HybridWord.State.copy [parameters.s,dn.native destination,on.native origin,cn.native count]

def quotedCode (destination origin count : Nat) (dn on cn : NatNotation) : Lean.Expr :=
  app ``HybridWord.Cmd.copy [dn.native destination,on.native origin,cn.native count]

theorem source_syntax (destination origin count : Nat) (dn on cn : NatNotation) :
    ScopedSyntax.Form StandardLibrary.model context parameters (original destination origin count dn on cn) :=
  .atom (.copy (dn.argument StandardLibrary.library.scalars.toSignatures destination)
    (on.argument StandardLibrary.library.scalars.toSignatures origin)
    (cn.argument StandardLibrary.library.scalars.toSignatures count))

/-- Source-only evidence for the representative family. It records actual
Lean binders and constants, not the result of running the HLS parser. -/
structure Source (value : Lean.Expr) where
  destination : Nat
  origin : Nat
  count : Nat
  dn : NatNotation
  on : NatNotation
  cn : NatNotation
  ni : Lean.Name
  nx : Lean.Name
  ny : Lean.Name
  ns : Lean.Name
  bi : Lean.BinderInfo
  bx : Lean.BinderInfo
  byInfo : Lean.BinderInfo
  bs : Lean.BinderInfo
  shape : LeanSourceEntry.strip value =
    .lam ni word (.lam nx word (.lam ny word (.lam ns state (original destination origin count dn on cn) bs) byInfo) bx) bi

def sourceView (value : Lean.Expr) : Option (Source value) :=
  match h : LeanSourceEntry.strip value with
  | .lam ni (.const ``HybridWord.Word [])
      (.lam nx (.const ``HybridWord.Word [])
        (.lam ny (.const ``HybridWord.Word [])
          (.lam ns (.const ``HybridWord.State [])
            (.app (.app (.app (.app (.const ``HybridWord.State.copy []) (.bvar 0)) d) o) n) bs)
          byInfo) bx) bi => do
    let dv ← NatNotation.view d
    let ov ← NatNotation.view o
    let nv ← NatNotation.view n
    return ⟨dv.value,ov.value,nv.value,dv.form,ov.form,nv.form,ni,nx,ny,ns,bi,bx,byInfo,bs,by
      have args : [d,o,n] = [dv.form.native dv.value,ov.form.native ov.value,nv.form.native nv.value] :=
        (congrArg (fun x => [x,o,n]) dv.shape).trans
          ((congrArg (fun x => [dv.form.native dv.value,x,n]) ov.shape).trans
            (congrArg (fun x => [dv.form.native dv.value,ov.form.native ov.value,x]) nv.shape))
      exact h.trans (congrArg (fun args =>
        Lean.Expr.lam ni word (.lam nx word (.lam ny word (.lam ns state
          (app ``HybridWord.State.copy (.bvar 0::args)) bs) byInfo) bx) bi) args)⟩
  | _ => none

end IRComparison.WordFrontend.FixedCopyCompleteness
