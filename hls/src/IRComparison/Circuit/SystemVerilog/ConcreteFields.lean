import IRComparison.Circuit.SystemVerilog.ConcreteStatement
import IRComparison.Circuit.SystemVerilog.Declarations
import IRComparison.Circuit.SystemVerilog.ReadPort

namespace IRComparison.Circuit.SystemVerilog.Concrete

def descendingRange (width : Nat) : Tree :=
  .group .square [natural (width-1),atom ":",atom "0"]
def ascendingRange (capacity : Nat) : Tree :=
  .group .square [atom "0",atom ":",natural (max 1 capacity-1)]
def readWidth : Tree → Option Nat
  | .group .square [high,.atom ⟨":",_⟩,.atom ⟨"0",_⟩] => (readNatural high).map (·+1)
  | _ => none
def readCapacity : Tree → Option Nat
  | .group .square [.atom ⟨"0",_⟩,.atom ⟨":",_⟩,high] => (readNatural high).map (·+1)
  | _ => none

@[simp] theorem read_width (width : Nat) (positive : 0 < width) :
    readWidth (descendingRange width) = some width := by
  simp only [descendingRange,atom,readWidth,read_natural,Option.map_some]
  congr 1; omega
@[simp] theorem read_capacity (capacity : Nat) :
    readCapacity (ascendingRange capacity) = some (max 1 capacity) := by
  simp only [ascendingRange,atom,readCapacity,read_natural,Option.map_some]
  congr 1; omega

def declaration : Declaration → List Tree
  | .scalar n w true => [atom "reg",atom "signed",descendingRange w,name n,atom ";"]
  | .scalar n w false => [atom "reg",descendingRange w,name n,atom ";"]
  | .bank n w cap => [atom "(*",atom "mem2reg",atom "*)",atom "reg",descendingRange w,
      name n,ascendingRange cap,atom ";"]

def physicalDeclaration : Declaration → Declaration
  | .scalar n w s => .scalar n w s
  | .bank n w cap => .bank n w (max 1 cap)

def readDeclarations : List Tree → Option (List Declaration × List Tree)
  | [] => some ([],[])
  | head::rest =>
    if readAtom head = some "reg" then
      match rest with
      | .atom ⟨"signed",_⟩ :: range :: n :: .atom ⟨";",_⟩ :: tail => do
          let width ← readWidth range
          let ident ← readName n
          let (ds,left) ← readDeclarations tail
          return (.scalar ident width true::ds,left)
      | .group .square rs :: n :: .atom ⟨";",_⟩ :: tail => do
          let width ← readWidth (.group .square rs)
          let ident ← readName n
          let (ds,left) ← readDeclarations tail
          return (.scalar ident width false::ds,left)
      | _ => none
    else if readAtom head = some "(*" then
      match rest with
      | .atom ⟨"mem2reg",_⟩ :: .atom ⟨"*)",_⟩ :: .atom ⟨"reg",_⟩ ::
          range :: n :: capacity :: .atom ⟨";",_⟩ :: tail => do
          let width ← readWidth range
          let ident ← readName n
          let count ← readCapacity capacity
          let (ds,left) ← readDeclarations tail
          return (.bank ident width count::ds,left)
      | _ => none
    else some ([],head::rest)

theorem declarations_readback (ds : List Declaration) (rest : List Tree)
    (positive : ∀ d ∈ ds, 0 < d.width)
    (stop : readDeclarations rest = some ([],rest)) :
    readDeclarations (ds.flatMap declaration ++ rest) = some (ds.map physicalDeclaration,rest) := by
  induction ds with
  | nil => exact stop
  | cons d ds ih =>
    have hd := positive d (by simp)
    have ht : ∀ d ∈ ds, 0 < d.width := fun d h => positive d (by simp [h])
    cases d with
    | scalar n w s =>
      cases s <;>
        simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.map_cons,declaration,
          List.append_assoc,atom,readDeclarations,readAtom,Option.some.injEq,↓reduceIte,read_width w hd,read_name,bind,Option.bind,ih ht,physicalDeclaration] <;> first | rfl | (simp only [descendingRange,atom,readDeclarations,readWidth,read_natural,read_name,bind,Option.bind,Option.map_some,ih ht]; simp [readAtom,physicalDeclaration, show w-1+1=w by change 0 < w at hd; omega])
    | bank n w cap =>
      simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.map_cons,declaration,
        List.append_assoc,atom,readDeclarations,readAtom,Option.some.injEq,↓reduceIte,read_width w hd,read_name,read_capacity,bind,Option.bind,ih ht,physicalDeclaration]
      rfl

def wire (w : Wire) : List Tree :=
  [atom "wire",atom "signed",descendingRange w.width,name w.name,atom "=",expression w.value,atom ";"]
def wireReadback (w : Wire) : Wire := {w with value := w.value.literalReadback}

def readWires : List Tree → Option (List Wire × List Tree)
  | .atom ⟨"wire",_⟩ :: .atom ⟨"signed",_⟩ :: range :: n :: .atom ⟨"=",_⟩ :: e :: .atom ⟨";",_⟩ :: rest => do
      let width ← readWidth range
      let ident ← readName n
      let value ← readExpression e
      if positive : 0 < width then
        let (ws,tail) ← readWires rest
        return (⟨ident,width,value,positive⟩::ws,tail)
      else none
  | rest => some ([],rest)

theorem wires_readback (ws : List Wire) (rest : List Tree)
    (stop : readWires rest = some ([],rest)) :
    readWires (ws.flatMap wire ++ rest) = some (ws.map wireReadback,rest) := by
  induction ws with
  | nil => exact stop
  | cons w ws ih =>
    simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.map_cons,wire,List.append_assoc,
      atom,readWires,read_width _ w.positive,read_name,expression_readback,bind,Option.bind,dif_pos w.positive,ih,wireReadback]
    rfl

theorem declarations_stop_at_wires (ws : List Wire) (tail : List Tree) :
    readDeclarations (ws.flatMap wire ++ atom "always"::tail) =
      some ([],ws.flatMap wire ++ atom "always"::tail) := by
  cases ws <;> simp [List.flatMap_cons,wire,atom,readDeclarations,readAtom]
  rw [readDeclarations.eq_def]
  rfl

end IRComparison.Circuit.SystemVerilog.Concrete
