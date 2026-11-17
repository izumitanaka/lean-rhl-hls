import IRComparison.Circuit.SharedAnalysis
import IRComparison.Circuit.ExpressionMapping
import IRComparison.Circuit.ChannelCounted
import IRComparison.Circuit.ChannelLower

namespace IRComparison.Circuit.Shared

instance : ExpressionEvaluation Program where
  eval := Program.eval
  zero := ⟨[.input (.lit 0)],0⟩
  zero_some := by intros; rfl
  invalid := ⟨[.input .fail],0⟩
  invalid_none := by intros; rfl

instance : Pipelining.ExpressionDependencies Program where
  reads := Program.reads
  agrees := Program.agrees

/-- Ordinary counter/address leaves remain small. ReadCode is compiled directly
into graph nodes and is never expanded to Circuit.read by this lowering. -/
def ofExpr (e : Circuit.Expr) : Program := ⟨[.input e],0⟩

def naturalIndex (p : Program) : Program :=
  ⟨.natIndex p.result :: p.graph,p.graph.length⟩

@[simp] theorem ofExpr_eval (e : Circuit.Expr) (s : State) (w : Nat → Int) :
    (ofExpr e).eval s w = e.eval s w := by
  simp [ofExpr,Program.eval,values,get,Node.eval]

@[simp] theorem naturalIndex_eval (p : Program) (s : State) (w : Nat → Int) :
    (naturalIndex p).eval s w = (p.eval s w).map (fun n => (n.toNat : Int)) := by
  simp only [naturalIndex,Program.eval,values,Node.eval,get,← values_size (s:=s) (w:=w) p.graph,
    Array.getElem?_push_size,Option.getD_some]
  cases (values s w p.graph)[p.result]?.getD none <;> rfl

@[simp] theorem ofExpr_range (wr : Nat → Interval) (e : Circuit.Expr) :
    (ofExpr e).range wr = Circuit.range wr e := by
  simp [ofExpr,Program.range,ranges,bound,Node.range]

/-- A graph result supplies the interval used for allocating the capture. -/
def freshFor (p : Program) : Builder Nat := fun b =>
  Circuit.fresh (p.range (fun n => b.wires[n]?.getD wordRange)) b

def bounds (p : Program) : Builder Interval := fun b =>
  (p.range (fun n => b.wires[n]?.getD wordRange),b)

def counterLoop (k : Nat) (limit : Circuit.Expr) (body : Schedule Program) : Schedule Program :=
  .seq (.step (.wire k (ofExpr (.lit 0))))
    (.loop (ofExpr (.bin .lt (.wire k) limit))
      (.seq body (.step (.wire k (ofExpr (.bin .add (.wire k) (.lit 1)))))))

/-- Same scalar captures and structured loops as the production command pass.
The expression field now holds a shared graph from its creation onward. -/
def command (i : Circuit.Expr) (locals : List Circuit.Expr) (output : Nat) :
    HybridIR.Cmd → Builder (Schedule Program)
  | .skip => pure .skip
  | .assign r e => pure (.step (.assign r (compile i (.wire 0) (.wire 1) locals [] e)))
  | .store a j e => pure (.step (.store a (compile i (.wire 0) (.wire 1) locals [] j)
      (compile i (.wire 0) (.wire 1) locals [] e)))
  | .send e => pure (.step (.send output (compile i (.wire 0) (.wire 1) locals [] e)))
  | .letValue e b => do
      let e := compile i (.wire 0) (.wire 1) locals [] e
      let v ← freshFor e
      return .seq (.step (.wire v e)) (← command i (.wire v::locals) output b)
  | .seq a b => do
      let first ← command i locals output a
      return .seq first (← command i locals output b)
  | .branch e a b => do
      let yes ← command i locals output a
      let no ← command i locals output b
      return .branch (compile i (.wire 0) (.wire 1) locals [] e) yes no
  | .repeat n b => do
      let k ← Circuit.fresh ⟨0,n⟩
      return counterLoop k (.lit n) (← command i locals output b)
  | .forRange e b => do
      let e := naturalIndex (compile i (.wire 0) (.wire 1) locals [] e)
      let n ← freshFor e
      let k ← Circuit.fresh (← bounds e)
      let body ← command i (.wire k::locals) output b
      return .seq (.step (.wire n e)) (counterLoop k (.wire n) body)

/-- Named buffer operations are retained; all ReadCode operands use the same
shared compiler. Buffer-validity registers are pre-existing clocked state. -/
def channel (buffers : ChannelLower.Buffers) (i : Circuit.Expr) (locals : List Circuit.Expr) :
    HybridIR.ChannelCmd → Builder (Schedule Program)
  | .skip => pure .skip
  | .assign r e => pure (.step (.assign r (compile i (.wire 0) (.wire 1) locals [] e)))
  | .store a j e => pure (.step (.store a (compile i (.wire 0) (.wire 1) locals [] j)
      (compile i (.wire 0) (.wire 1) locals [] e)))
  | .send q e => pure (.step (.send q (compile i (.wire 0) (.wire 1) locals [] e)))
  | .hold b e => pure (.seq (.step (.wire (buffers.value b) (compile i (.wire 0) (.wire 1) locals [] e)))
      (.step (.wire (buffers.valid b) (ofExpr (.lit 1)))))
  | .receive q b => pure (.seq (.step (.receive q (buffers.value b)))
      (.step (.wire (buffers.valid b) (ofExpr (.lit 1)))))
  | .letBuffer b c => do
      let v ← Circuit.fresh
      return .seq (.step (.wire v (ofExpr (buffers.read b)))) (← channel buffers i (.wire v::locals) c)
  | .letValue e c => do
      let e := compile i (.wire 0) (.wire 1) locals [] e
      let v ← freshFor e
      return .seq (.step (.wire v e)) (← channel buffers i (.wire v::locals) c)
  | .seq a b => do
      let first ← channel buffers i locals a
      return .seq first (← channel buffers i locals b)
  | .branch e a b => do
      let yes ← channel buffers i locals a
      let no ← channel buffers i locals b
      return .branch (compile i (.wire 0) (.wire 1) locals [] e) yes no
  | .repeat n c => do
      let k ← Circuit.fresh ⟨0,n⟩
      return counterLoop k (.lit n) (← channel buffers i locals c)
  | .forRange e c => do
      let e := naturalIndex (compile i (.wire 0) (.wire 1) locals [] e)
      let n ← freshFor e
      let k ← Circuit.fresh (← bounds e)
      let body ← channel buffers i (.wire k::locals) c
      return .seq (.step (.wire n e)) (counterLoop k (.wire n) body)

end IRComparison.Circuit.Shared
