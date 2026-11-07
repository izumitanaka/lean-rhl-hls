import PaperCore.DirectBody
import PaperCore.SequenceTransitions

namespace PaperCore.BodyCursorSMT
open AccessAnalysis IndexSequence
open PaperCore (SMT)
open PaperCore.SMTMeaning (eval conj_member)

/-- Each program point has independent progression parameters. Empty and
    singleton sequences retain their irrelevant parameter freedom. -/
def affine (name : String) (counter : SMT) : SMT :=
  SMT.add (.param (name ++ ".constant")) (SMT.mul (.param (name ++ ".slope")) counter)

def template (name : String) (counter : SMT) : Template :=
  ⟨affine (name ++ ".first") counter, .param (name ++ ".step"), affine (name ++ ".count") counter⟩

def values (params : String → Int) (name : String) (k : Int) : Values :=
  ⟨params (name ++ ".first.constant") + params (name ++ ".first.slope") * k,
   params (name ++ ".step"),
   params (name ++ ".count.constant") + params (name ++ ".count.slope") * k⟩

theorem evaluates (hc : eval zero params vars counter = .integer k) :
    (template name counter).Evaluates (values params name k) zero params vars := by
  constructor <;> simp [template,values,affine,String.append_assoc,SMT.add,SMT.mul,SMT.op,eval,hc,PaperCore.SMTMeaning.operation]

def address (index : Affine) (counter : SMT) : SMT :=
  SMT.add (SMT.mul (.num index.scale) counter) (.num index.offset)

theorem address_evaluates (hc : eval zero params vars counter = .integer k) :
    eval zero params vars (address index counter) = .integer (index.eval k) := by
  simp [address,Affine.eval,SMT.add,SMT.mul,SMT.op,eval,hc,PaperCore.SMTMeaning.operation]

abbrev Layout := Array → String

def update (layout : Layout) (array : Array) (name : String) : Layout :=
  fun other => if other = array then name else layout other

def nextName (point : Nat) : String := "cursor.after." ++ toString point

def transition (event : SymbolicAccess) (before after : Template) (counter : SMT) : SMT :=
  match event.direction with
  | .read => popConstraint before after (address event.index counter)
  | .write => safePushConstraint before after (address event.index counter)

/-- Generate each read/pop or write/fresh-push condition in actual order. -/
def query (counter : SMT) (point : Nat) (layout : Layout) : List SymbolicAccess → SMT
  | [] => SMT.truth
  | event :: rest =>
    SMT.conj [transition event (template (layout event.array) counter) (template (nextName point) counter) counter,
      query counter (point+1) (update layout event.array (nextName point)) rest]

def finalLayout (point : Nat) (layout : Layout) : List SymbolicAccess → Layout
  | [] => layout
  | event :: rest => finalLayout (point+1) (update layout event.array (nextName point)) rest

/-- Only the arrays in the input trace need a represented queue. -/
def MatchesOn (arrays : Array → Prop) (params : String → Int) (k : Int) (layout : Layout) (indices : IndexMap) : Prop :=
  ∀ array, arrays array → indices.lookup array = some (values params (layout array) k).sequence

theorem matches_update (agrees : MatchesOn arrays params k layout indices) :
    MatchesOn arrays params k (update layout array name)
      (put indices array (values params name k).sequence) := by
  intro other tracked
  by_cases same : other = array
  · subst other; simp [update]
  · simpa [update,same,lookup_put_other _ _ _ _ same] using agrees other tracked

theorem query_sound (events : List SymbolicAccess)
    (hc : eval zero params vars counter = .integer k)
    (tracked : ∀ event ∈ events, arrays event.array)
    (agrees : MatchesOn arrays params k layout indices)
    (model : eval zero params vars (query counter point layout events) = .boolean true) :
    ∃ afterIndices,
      DirectBody.consume indices (events.map (SymbolicAccess.eval k)) = some afterIndices ∧
      MatchesOn arrays params k (finalLayout point layout events) afterIndices := by
  induction events generalizing point layout indices with
  | nil => exact ⟨indices,rfl,agrees⟩
  | cons event rest ih =>
    have step := conj_member _ _ zero params vars model (by simp :
      transition event (template (layout event.array) counter) (template (nextName point) counter) counter ∈ _)
    have tail := conj_member _ _ zero params vars model (by simp :
      query counter (point+1) (update layout event.array (nextName point)) rest ∈ _)
    have old := agrees event.array (tracked event (by simp))
    have consumed : DirectBody.consumeOne indices (event.eval k) =
        some (put indices event.array (values params (nextName point) k).sequence) := by
      cases hd : event.direction with
      | read =>
        have pop : eval zero params vars (popConstraint (template (layout event.array) counter)
            (template (nextName point) counter) (address event.index counter)) = .boolean true := by
          simpa [transition,hd] using step
        have same := (popConstraint_sound (evaluates hc) (evaluates hc) (address_evaluates hc) pop).2.2
        rw [same] at old
        simp [DirectBody.consumeOne,SymbolicAccess.eval,hd,old]
      | write =>
        have push : eval zero params vars (safePushConstraint (template (layout event.array) counter)
            (template (nextName point) counter) (address event.index counter)) = .boolean true := by
          simpa [transition,hd] using step
        obtain ⟨_,_,same,fresh⟩ := safePushConstraint_sound (evaluates hc) (evaluates hc) (address_evaluates hc) push
        simp [DirectBody.consumeOne,SymbolicAccess.eval,hd,old,fresh,same]
    obtain ⟨afterIndices,done,after⟩ := ih
      (fun e he => tracked e (List.mem_cons_of_mem _ he)) (matches_update agrees) tail
    refine ⟨afterIndices,?_,after⟩
    simpa [List.map_cons,DirectBody.consume,consumed] using done

#print axioms query_sound
end PaperCore.BodyCursorSMT
