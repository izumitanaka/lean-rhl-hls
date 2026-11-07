import PaperCore.Correspondence

namespace PaperCore.InsertionAudit

def source : State Heap := ⟨[],[]⟩
def target : State Streams := ⟨[("b",0)],[("a",[])]⟩
def indices : IndexMap := [("a",[])]

/-- Even the approved exact-length correspondence permits an empty stream.
    The buffer register exists, so this is not an uninitialized-register case. -/
theorem empty_corresponds :
    Corresponds (fun _ => False) (fun a => a = "a") source target indices := by
  constructor
  · intro x hx; exact False.elim hx
  · intro a ha
    subst a
    exact ⟨[],[],rfl,rfl,by simp,Contents.nil⟩

/-- An unconditional inserted read cannot execute in that related state. -/
theorem inserted_read_stuck : ¬ ∃ out, StreamStep (.read "b" "a") target out := by
  exact stream_read_empty target "a" "b" rfl

/- Historical rule audit motivating the approved nonempty condition:
   uniftr.tex Tr-InsRBuf has precondition
       [a[hd(Ia)]/b, tl(Ia)/Ia] Q.
   For the syntactic assertion Q = True, substitution yields True, with no
   head or tail term remaining. Under the printed "undefined term occurring
   in a formula makes it false" convention, that formula is still true.
   The state above satisfies structural correspondence, yet the insertion
   cannot execute. The user approved an explicit nonempty-index condition.
   PaperCore.Insertion.readPre now retains this definedness requirement
   independently of Q; the manuscript has not been edited. -/

#print axioms empty_corresponds
#print axioms inserted_read_stuck
end PaperCore.InsertionAudit
