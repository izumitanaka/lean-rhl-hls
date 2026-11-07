import PaperCore.Language
import PaperCore.Correspondence

namespace PaperCore.ProgramState

def sourceArrays : Source Op → List Array
  | .assign .. => []
  | .action (.read _ a _) | .action (.write a _ _) => [a]
  | .seq a b | .branch _ a b => sourceArrays a ++ sourceArrays b
  | .loop _ _ _ _ body | .kernel body => sourceArrays body

def emptyStreams (arrays : List Array) : Streams := arrays.map (fun a => (a,[]))

theorem lookup_empty (arrays : List Array) (member : a ∈ arrays) :
    (emptyStreams arrays).lookup a = some [] := by
  induction arrays with
  | nil => simp at member
  | cons b rest ih =>
    by_cases same : a = b
    · subst a; simp [emptyStreams]
    · have tail : a ∈ rest := by simpa [same] using member
      simp only [emptyStreams,List.map_cons,List.lookup]
      cases (a == b) <;> simp_all [emptyStreams]


end PaperCore.ProgramState
