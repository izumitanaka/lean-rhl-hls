import IRComparison.Circuit.SystemVerilog.ConcreteFields

namespace IRComparison.Circuit.SystemVerilog.Concrete

def registerEntry (id : Nat) (n : Name) : List Tree := [natural id,atom ":",.group .block [
  atom "read_data",atom "=",name n,atom ";",atom "read_valid",atom "=",atom "1",atom ";"]]

def arrayEntry (id : Nat) (len bank : Name) : List Tree := [natural id,atom ":",.group .block [
  atom "if",.group .round [atom "read_addr",atom "<",name len],.group .block [
    atom "read_data",atom "=",name bank,.group .square [atom "read_addr"],atom ";",
    atom "read_valid",atom "=",atom "1",atom ";"]]]

def readRegisterEntries : List Tree → Option (List (Nat × Name))
  | [] => some []
  | id :: .atom ⟨":",_⟩ :: .group .block [.atom ⟨"read_data",_⟩,.atom ⟨"=",_⟩,n,.atom ⟨";",_⟩,
      .atom ⟨"read_valid",_⟩,.atom ⟨"=",_⟩,.atom ⟨"1",_⟩,.atom ⟨";",_⟩] :: rest => do
      return (← readNatural id,← readName n)::(← readRegisterEntries rest)
  | _ => none

def readArrayEntries : List Tree → Option (List (Nat × Name × Name))
  | [] => some []
  | id :: .atom ⟨":",_⟩ :: .group .block [.atom ⟨"if",_⟩,
      .group .round [.atom ⟨"read_addr",_⟩,.atom ⟨"<",_⟩,len],
      .group .block [.atom ⟨"read_data",_⟩,.atom ⟨"=",_⟩,bank,.group .square [.atom ⟨"read_addr",_⟩],
        .atom ⟨";",_⟩,.atom ⟨"read_valid",_⟩,.atom ⟨"=",_⟩,.atom ⟨"1",_⟩,.atom ⟨";",_⟩]] :: rest => do
      return (← readNatural id,← readName len,← readName bank)::(← readArrayEntries rest)
  | _ => none

theorem registers_readback (entries : List (Nat × Name)) :
    readRegisterEntries (entries.flatMap fun (id,n) => registerEntry id n) = some entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨id,n⟩
    simp only [registerEntry,atom] at ih
    simp only [List.flatMap_cons,registerEntry,List.cons_append,List.nil_append,atom,
      readRegisterEntries,read_natural,read_name]
    rw [ih]
    rfl

theorem arrays_readback (entries : List (Nat × Name × Name)) :
    readArrayEntries (entries.flatMap fun (id,len,bank) => arrayEntry id len bank) = some entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨id,len,bank⟩
    simp only [arrayEntry,atom] at ih
    simp only [List.flatMap_cons,arrayEntry,List.cons_append,List.nil_append,atom,
      readArrayEntries,read_natural,read_name]
    rw [ih]
    rfl

/-- The default case is placed first; native SV selects it only if no
non-default item matches. Entries retain their original order. -/
def portCase (entries : List Tree) : Tree := .group .cases <|
  [.group .round [atom "read_id"],atom "default",atom ":",.group .block []] ++ entries

def readPort (code : ReadCode) : Tree := .group .block [
  atom "read_data",atom "=",atom "0",atom ";",atom "read_valid",atom "=",atom "0",atom ";",
  atom "if",.group .round [atom "read_reg"],
  .group .block [portCase (code.registers.flatMap fun (id,n) => registerEntry id n)],atom "else",
  .group .block [portCase (code.arrays.flatMap fun (id,len,bank) => arrayEntry id len bank)]]

def readPortCase : Tree → Option (List Tree)
  | .group .cases (.group .round [.atom ⟨"read_id",_⟩] :: .atom ⟨"default",_⟩ ::
      .atom ⟨":",_⟩ :: .group .block [] :: entries) => some entries
  | _ => none

def readReadPort : Tree → Option ReadCode
  | .group .block [.atom ⟨"read_data",_⟩,.atom ⟨"=",_⟩,.atom ⟨"0",_⟩,.atom ⟨";",_⟩,
      .atom ⟨"read_valid",_⟩,.atom ⟨"=",_⟩,.atom ⟨"0",_⟩,.atom ⟨";",_⟩,
      .atom ⟨"if",_⟩,.group .round [.atom ⟨"read_reg",_⟩],.group .block [regs],.atom ⟨"else",_⟩,
      .group .block [arrays]] => do
      return ⟨← readRegisterEntries (← readPortCase regs),← readArrayEntries (← readPortCase arrays)⟩
  | _ => none

theorem readPort_readback (code : ReadCode) : readReadPort (readPort code) = some code := by
  simp only [readPort,atom,readReadPort,portCase,List.cons_append,List.nil_append,readPortCase,
    bind,Option.bind,registers_readback,arrays_readback]
  rfl

end IRComparison.Circuit.SystemVerilog.Concrete
