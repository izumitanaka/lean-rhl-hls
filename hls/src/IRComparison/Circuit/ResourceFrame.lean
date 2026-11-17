import IRComparison.Circuit.CountedParts

namespace IRComparison.Circuit

def Build.resources (b : Build) := (b.memories,b.queues,b.nextArray,b.nextQueue)

def PreservesResources (f : Builder α) : Prop := ∀ b, (f b).2.resources = b.resources

theorem resources_pure (a : α) : PreservesResources (pure a) := fun _ => rfl

theorem resources_bind (f : Builder α) (g : α → Builder β)
    (hf : PreservesResources f) (hg : ∀ a, PreservesResources (g a)) : PreservesResources (f >>= g) := by
  intro b
  exact (hg (f b).1 (f b).2).trans (hf b)

theorem resources_fresh (r : Interval) : PreservesResources (fresh r) := fun _ => rfl

theorem command_resources (c : HybridIR.Cmd) (i : Expr) (locals : List Expr) (output : Nat) :
    PreservesResources (command i locals output c) := by
  induction c generalizing i locals with
  | skip | assign | store | send => exact resources_pure _
  | letValue e b ih =>
    apply resources_bind _ _ (fun _ => rfl)
    intro n
    exact resources_bind _ _ (ih i (.wire n::locals)) (fun _ => resources_pure _)
  | seq a b ia ib =>
    exact resources_bind _ _ (ia i locals) (fun _ => resources_bind _ _ (ib i locals) (fun _ => resources_pure _))
  | branch e a b ia ib =>
    exact resources_bind _ _ (ia i locals) (fun _ => resources_bind _ _ (ib i locals) (fun _ => resources_pure _))
  | «repeat» n b ih =>
    exact resources_bind _ _ (resources_fresh _) (fun _ => resources_bind _ _ (ih i locals) (fun _ => resources_pure _))
  | forRange e b ih =>
    apply resources_bind _ _ (fun _ => rfl)
    intro n
    apply resources_bind _ _ (fun _ => rfl)
    intro _
    apply resources_bind _ _ (resources_fresh _)
    intro k
    exact resources_bind _ _ (ih i (.wire k::locals)) (fun _ => resources_pure _)

theorem newSlots_resources (n : Nat) : PreservesResources (newSlots n) := by
  induction n with
  | zero => exact resources_pure _
  | succ n ih => exact resources_bind _ _ (resources_fresh _) (fun _ => resources_bind _ _ ih (fun _ => resources_pure _))

theorem take_resources (q slot : Nat) (e : Expr) : PreservesResources (take q slot e) := by
  apply resources_bind _ _ (fun _ => rfl)
  intro _
  apply resources_bind _ _ (fun _ => rfl)
  intro _
  apply resources_bind _ _ (resources_fresh _)
  intro _
  exact resources_bind _ _ (resources_fresh _) (fun _ => resources_pure _)

theorem compactLoadOne_resources (i : Expr) (input qi : Nat) (old : List Expr) (slot : Nat) (l : Load) :
    PreservesResources (compactLoadOne i input qi old slot l) := by
  cases l with
  | memory | saved => exact resources_pure _
  | take => exact take_resources _ _ _

theorem loads_resources (i : Expr) (input qi : Nat) (old : List Expr) (ls : List Load) (slots : List Nat) :
    PreservesResources (loads i input qi old ls slots) := by
  induction ls generalizing slots with
  | nil => exact resources_pure _
  | cons l ls ih =>
    cases slots with
    | nil => exact resources_pure _
    | cons n ns =>
      exact resources_bind _ _ (compactLoadOne_resources _ _ _ _ _ _)
        (fun _ => resources_bind _ _ (ih ns) (fun _ => resources_pure _))

theorem prepareCounted_resources (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) :
    PreservesResources (prepareCounted start stride count initial refill body input qi qo) := by
  apply resources_bind _ _ (resources_fresh _)
  intro k
  apply resources_bind _ _ (newSlots_resources _)
  intro held
  apply resources_bind _ _ (newSlots_resources _)
  intro scratch
  apply resources_bind _ _ (loads_resources _ _ _ _ _ _)
  intro _
  apply resources_bind _ _ (command_resources _ _ _ _)
  intro _
  apply resources_bind _ _ (loads_resources _ _ _ _ _ _)
  intro _
  apply resources_bind _ _ (loads_resources _ _ _ _ _ _)
  intro _
  exact resources_bind _ _ (command_resources _ _ _ _) (fun _ => resources_pure _)

theorem counted_resources (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) :
    PreservesResources (counted start stride count initial refill body input qi qo) := by
  intro b
  by_cases hz : count = 0
  · simp [counted,hz,StateT.run,pure,StateT.pure]
  · have h := prepareCounted_resources start stride count initial refill body input qi qo b
    simpa [counted,hz,bind,pure,StateT.bind,StateT.pure] using h

theorem prepareCounted_counter (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) (b : Build) :
    (prepareCounted start stride count initial refill body input qi qo b).1.counter = b.wires.size := by
  simp only [prepareCounted,fresh,bind,pure,StateT.bind,StateT.pure]
  repeat' split
  all_goals rfl

end IRComparison.Circuit
