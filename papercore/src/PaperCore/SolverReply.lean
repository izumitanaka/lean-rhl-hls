import PaperCore.SMT.SMTConnection

namespace PaperCore.SolverReply

structure Reply where
  request : String
  response : String

def parameters (bindings : List (String × Int)) : String → Int := fun name => (bindings.lookup name).getD 0


end PaperCore.SolverReply
