import PaperCore.HybridAlternatives

namespace PaperCore.Hybrid.Alternatives
open Pipeline (Plan)
open QueueInterface SolverReply

/-- IO only collects candidate responses. Hybrid.Alternatives.build rechecks every request
    against the queue interface derived from its preceding accepted stage. -/
def solve {Op : Type} {classify : Op → Option AccessAnalysis.Arithmetic} {source : Source Op}
    (plan : Plan classify variables arrays source) (queues : List Queues) (directory : String) (point : Nat := 0) :
    IO (Replies plan × List Queues × Nat) := do
  match plan with
  | .assign .. => return ((),queues,point)
  | .branch _ _ yes no =>
    let (yesReplies,yesQueues,next) ← solve yes queues directory point
    let (noReplies,noQueues,last) ← solve no queues directory next
    return ((yesReplies,noReplies),yesQueues ++ noQueues,last)
  | .kernel body => solve body queues directory point
  | .leaf stage =>
    let mut replies : List Reply := []
    let mut outputs : List Queues := []
    let mut next := point
    for queue in queues do
      IO.FS.createDirAll directory
      let base := directory ++ "/query-" ++ toString next
      let request := PaperCore.SMT.script (stage.query queue)
      IO.FS.writeFile (base ++ ".smt2") request
      let response ← IO.Process.output {cmd := "z3", args := #["-T:15",base ++ ".smt2"]}
      IO.FS.writeFile (base ++ ".stdout") response.stdout
      IO.FS.writeFile (base ++ ".stderr") response.stderr
      let reply : Reply := ⟨request,response.stdout⟩
      let some after := stage.accept queue reply
        | throw (IO.userError ("query " ++ toString next ++ ": no accepted model; " ++ response.stdout.take 160))
      replies := replies ++ [reply]
      outputs := outputs ++ [after]
      next := next + 1
    return (replies,outputs,next)
  | .seq left right =>
    let (first,middle,next) ← solve left queues directory point
    let (second,after,last) ← solve right middle directory next
    return ((first,second),after,last)

end PaperCore.Hybrid.Alternatives
