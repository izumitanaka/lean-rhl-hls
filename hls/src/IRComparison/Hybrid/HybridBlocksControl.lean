import IRComparison.Hybrid.HybridCommandControl
import IRComparison.Hybrid.HybridRuntime
import IRComparison.Core.FIFOReadControl

namespace IRComparison.HybridBlocksControl
open HybridIR

inductive Config where
  | start (blocks : List Block) (old : List Int) (state : State) (inputQueue outputQueue : List Int)
  | loading (block : Block) (rest : List Block) (state : State) (outputQueue : List Int) (loader : FIFOReadControl.Config)
  | body (index : Int) (rest : List Block) (values inputQueue : List Int) (control : HybridCommandControl.Config)
  | stopped (result : Option (State × List Int × List Int))

def step (input : Input) (x y : Int) : Config → Config
  | .stopped r => .stopped r
  | .start [] _ s qi qo => .stopped (some (s,qi,qo))
  | .start (b::bs) old s qi qo => .loading b bs s qo (.loading b.loads old [] qi)
  | .loading _ _ _ _ (.stopped none) => .stopped none
  | .loading b bs s qo (.stopped (some (vs,qi))) =>
    .body b.index bs vs qi (.running [(b.body,vs)] s qo)
  | .loading b bs s qo loader@(.loading ..) => .loading b bs s qo (FIFOReadControl.step input loader)
  | .body _ _ _ _ (.stopped none) => .stopped none
  | .body _ bs vs qi (.stopped (some (s,qo))) => .start bs vs s qi qo
  | .body i bs vs qi control@(.running ..) => .body i bs vs qi (HybridCommandControl.step i x y control)

inductive Reaches (input : Input) (x y : Int) : Config → Config → Prop where
  | refl (a) : Reaches input x y a a
  | next : Reaches input x y (step input x y a) b → Reaches input x y a b

theorem Reaches.trans (h : Reaches input x y a b) (k : Reaches input x y b c) : Reaches input x y a c := by
  induction h with
  | refl => exact k
  | next _ ih => exact .next (ih k)

theorem lift_load (h : FIFOReadControl.Reaches input a b) :
    Reaches input x y (.loading block rest s qo a) (.loading block rest s qo b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih =>
    cases a with
    | loading => exact .next ih
    | stopped => simpa [FIFOReadControl.step] using ih

theorem lift_body (h : HybridCommandControl.Reaches i x y a b) :
    Reaches input x y (.body i rest vs qi a) (.body i rest vs qi b) := by
  induction h with
  | refl => exact .refl _
  | @next a b h ih =>
    cases a with
    | running => exact .next ih
    | stopped => simpa [HybridCommandControl.step] using ih

theorem correct (blocks : List Block) (old : List Int) (s : State) (qi qo : List Int) :
    Reaches input x y (.start blocks old s qi qo) (.stopped (blocksEval input x y blocks old s qi qo)) := by
  induction blocks generalizing old s qi qo with
  | nil => exact .next (.refl _)
  | cons b bs ih =>
    apply Reaches.next
    have loaded := FIFOReadControl.correct (input:=input) b.loads old [] qi
    simp only [List.nil_append,Option.map_id_fun] at loaded
    apply (lift_load loaded).trans
    cases hl : WindowFIFO.execute input old b.loads qi with
    | none =>
      simp only [hl,blocksEval,bind,Option.bind]
      exact .next (.refl _)
    | some pair =>
      obtain ⟨vs,remaining⟩ := pair
      simp only [hl,blocksEval,bind,Option.bind]
      apply Reaches.next
      have bodyRun := HybridCommandControl.correct (i:=b.index) (x:=x) (y:=y) b.body s qo vs []
      have finished : HybridCommandControl.Reaches b.index x y (.running [(b.body,vs)] s qo)
          (.stopped (b.body.eval b.index x y s qo vs)) := by
        apply bodyRun.trans
        cases b.body.eval b.index x y s qo vs with
        | none => exact .refl _
        | some pair => obtain ⟨t,out⟩ := pair; exact .next (.refl _)
      apply (lift_body finished).trans
      cases hb : b.body.eval b.index x y s qo vs with
      | none => exact .next (.refl _)
      | some pair =>
        obtain ⟨t,out⟩ := pair
        exact .next (ih vs t remaining out)

def run (input : Input) (x y : Int) : Nat → Config → Config
  | 0,c => c
  | n+1,c => run input x y n (step input x y c)

theorem Reaches.finite (h : Reaches input x y a b) : ∃ n, run input x y n a = b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | next _ ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,hn⟩

theorem finishes (blocks : List Block) (old : List Int) (s : State) (qi qo : List Int) :
    ∃ n, run input x y n (.start blocks old s qi qo) = .stopped (blocksEval input x y blocks old s qi qo) :=
  (correct blocks old s qi qo).finite

end IRComparison.HybridBlocksControl
