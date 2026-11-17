import IRComparison.Circuit.SystemVerilog.ConcreteExpression

namespace IRComparison.Circuit.SystemVerilog

def Destination.literalReadback : Destination → Destination
  | .reference n => .reference n
  | .index n a => .index n a.literalReadback

def Statement.literalReadback : Statement → Statement
  | .skip => .skip
  | .assign d e => .assign d.literalReadback e.literalReadback
  | .seq a b => .seq a.literalReadback b.literalReadback
  | .branch c a b => .branch c.literalReadback a.literalReadback b.literalReadback
  | .forRange n count body => .forRange n count body.literalReadback


namespace Concrete

def destination : Destination → List Tree
  | .reference n => [name n]
  | .index n a => [name n,.group .square [expression a]]

def rangeHeader (n : Name) (count : Nat) : Tree := .group .round [
  atom "reg",.group .square [natural (bits count-1),atom ":",atom "0"],name n,atom "=",atom "0",atom ";",
  name n,atom "<",signed (bits count+1) count (by omega),atom ";",
  name n,atom "=",name n,atom "+",atom "1"]

def readCount (t : Tree) : Option Nat := do
  let (width,count) ← signedDecimal (← readAtom t)
  if width = bits count+1 then some count else none

theorem read_count (count : Nat) :
    readCount (signed (bits count+1) count (by omega)) = some count := by
  unfold readCount
  simp only [signed,atom,readAtom,bind,Option.bind]
  rw [signedDecimal_print _ _ (by omega)]
  simp

def readRangeHeader : Tree → Option (Name × Nat)
  | .group .round [.atom ⟨"reg",_⟩,.group .square [high,.atom ⟨":",_⟩,.atom ⟨"0",_⟩],n0,
      .atom ⟨"=",_⟩,.atom ⟨"0",_⟩,.atom ⟨";",_⟩,n1,.atom ⟨"<",_⟩,bound,.atom ⟨";",_⟩,
      n2,.atom ⟨"=",_⟩,n3,.atom ⟨"+",_⟩,.atom ⟨"1",_⟩] => do
      let h ← readNatural high
      let name0 ← readName n0
      let name1 ← readName n1
      let name2 ← readName n2
      let name3 ← readName n3
      let count ← readCount bound
      if h+1 = bits count ∧ name0 = name1 ∧ name0 = name2 ∧ name0 = name3 then
        some (name0,count) else none
  | _ => none

theorem rangeHeader_readback (n : Name) (count : Nat) :
    readRangeHeader (rangeHeader n count) = some (n,count) := by
  have positive : 0 < bits count := by unfold bits; omega
  simp only [rangeHeader,atom,readRangeHeader,read_natural,read_name,read_count,bind,Option.bind]
  simp [show bits count-1+1 = bits count by omega]

/-- Explicit begin/end groups retain sequencing structure while staying in
the ordinary SV statement grammar. Lvalues are not parenthesized. -/
def statement : Statement → Tree
  | .skip => .group .block []
  | .assign d e => .group .block (destination d ++ [atom "<=",expression e,atom ";"])
  | .seq a b => .group .block [statement a,statement b]
  | .branch c a b => .group .block [atom "if",.group .round [expression c],statement a,atom "else",statement b]
  | .forRange n count body => .group .block [atom "for",rangeHeader n count,statement body]

def readStatement : Tree → Option Statement
  | .group .block [] => some .skip
  | .group .block [n,.atom ⟨"<=",_⟩,e,.atom ⟨";",_⟩] => do
      return .assign (.reference (← readName n)) (← readExpression e)
  | .group .block [n,.group .square [a],.atom ⟨"<=",_⟩,e,.atom ⟨";",_⟩] => do
      return .assign (.index (← readName n) (← readExpression a)) (← readExpression e)
  | .group .block [a,b] => do return .seq (← readStatement a) (← readStatement b)
  | .group .block [.atom ⟨"if",_⟩,.group .round [c],a,.atom ⟨"else",_⟩,b] => do
      return .branch (← readExpression c) (← readStatement a) (← readStatement b)
  | .group .block [.atom ⟨"for",_⟩,header,body] => do
      let (n,count) ← readRangeHeader header
      return .forRange n count (← readStatement body)
  | _ => none
termination_by t => sizeOf t

theorem statement_readback (s : Statement) : readStatement (statement s) = some s.literalReadback := by
  induction s with
  | skip => simp only [statement,readStatement,Statement.literalReadback]
  | assign d e =>
    cases d <;> simp only [statement,destination,List.cons_append,List.nil_append,atom,readStatement,
      read_name,expression_readback,Statement.literalReadback,Destination.literalReadback] <;> rfl
  | seq a b ha hb => simp only [statement,readStatement,ha,hb,Statement.literalReadback]; rfl
  | branch c a b ha hb =>
    simp only [statement,atom,readStatement,expression_readback,ha,hb,Statement.literalReadback]; rfl
  | forRange n count body ih =>
    simp only [statement,atom,readStatement,rangeHeader_readback,ih,Statement.literalReadback]; rfl

def printStatement (s : Statement) : String := print [statement s]
def parseStatement (text : String) : Option Statement := do
  let [tree] ← parse text | none
  readStatement tree

theorem parse_printStatement (s : Statement) : parseStatement (printStatement s) = some s.literalReadback := by
  unfold parseStatement printStatement
  rw [parse_print]
  exact statement_readback s


end Concrete
end IRComparison.Circuit.SystemVerilog
