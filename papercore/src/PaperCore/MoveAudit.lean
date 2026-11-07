import PaperCore.Correspondence

namespace PaperCore.MoveAudit

def source : State Heap := ⟨[],[]⟩
def target : State Streams := ⟨[("b",0)],[]⟩

/-- Typing a name as ordinary does not, under the printed partial-state
    relation alone, imply that its register is defined. Both can be absent. -/
theorem undefined_ordinary_corresponds :
    Corresponds (fun x => x = "y") (fun _ => False) source target [] := by
  constructor
  · intro x hx
    subst x
    rfl
  · intro a ha
    exact False.elim ha

theorem inserted_move_stuck (meaning : Op → Int → Int → Int) :
    ¬ ∃ out, TargetExec meaning (.assign "b" (.var "y")) target out := by
  rintro ⟨out,h⟩
  cases h with
  | assign value => simp [Expr.eval,target,List.lookup] at value

/- Tr-InsMove has the syntactic substitution [y/b]Q as its precondition.
   For Q=True, it contains no occurrence of y. Without a separate definedness
   requirement or a state-typing assumption, this insertion is not executable.
   The user approved retaining operand definedness independently of Q.
   PaperCore.movePre and PaperCore.insertMove_valid implement that repair. -/

#print axioms undefined_ordinary_corresponds
#print axioms inserted_move_stuck
end PaperCore.MoveAudit
