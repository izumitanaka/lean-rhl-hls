import IRComparison.Circuit.SystemVerilog.Syntax

namespace IRComparison.Circuit.SystemVerilog

/-- The combinational read port's concrete case entries. Names are explicit,
so a proof must account for the actual bank selected by each external ID. -/
structure ReadCode where
  registers : List (Nat × Name)
  arrays : List (Nat × Name × Name)
  deriving Repr

def readCode (a : Artifact) (outputs : List Nat) : ReadCode where
  registers := (a.machine.nodes.toList.flatMap Node.registers).eraseDups.map
    (fun id => (id,.register id))
  arrays := outputs.map (fun id => (id,.length id,.memory id))

/-- The actual read-port renderer consumed by emit. It uses blocking
assignments in a combinational process, with explicit defaults. -/
def ReadCode.text (code : ReadCode) : String := String.intercalate "\n" <|
  ["  always @* begin read_data=0; read_valid=0; if (read_reg) begin case(read_id)"] ++
  code.registers.map (fun (id,name) =>
    s!"    {id}: begin read_data={name.text}; read_valid=1; end") ++
  ["    default: begin end endcase end else begin case(read_id)"] ++
  code.arrays.map (fun (id,length,bank) =>
    s!"    {id}: if (read_addr < {length.text}) begin read_data={bank.text}[read_addr]; read_valid=1; end") ++
  ["    default: begin end endcase end end"]

structure ReadRequest where
  register : Bool := false
  id : BitVec 32 := 0
  address : BitVec 32 := 0
  deriving Repr

structure ReadReply where
  data : BitVec 32 := 0
  valid : Bool := false
  deriving Repr, DecidableEq

end IRComparison.Circuit.SystemVerilog
