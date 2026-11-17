import IRComparison.Circuit.SystemVerilog.PreparationSound

namespace IRComparison.Circuit.SystemVerilog.ExternalPorts

variable {id address size : Nat} {register : Bool} {value : Int}

/-- This is an external-interface condition, not a restriction on the internal
Nat-ID language. Both existing configuration and read ports have width 32. -/
def limit : Nat := 2^32

def Fits (a : Artifact) (outputs : List Nat) : Prop :=
  (∀ p ∈ a.memories.toList, p.1 < limit ∧ p.2 ≤ limit) ∧
  (∀ r ∈ a.machine.nodes.toList.flatMap Node.registers, r < limit) ∧
  (∀ id ∈ outputs, id ∈ a.memories.toList.map Prod.fst)

instance : Decidable (Fits a outputs) := by
  unfold Fits
  infer_instance

/-- Failure diagnoses an inaccessible interface; it does not truncate IDs or
change the internal compiler's success theorem. -/
def check (a : Artifact) (outputs : List Nat) : Except String (PLift (Fits a outputs)) :=
  if h : Fits a outputs then .ok ⟨h⟩
  else .error "32-bit external interface: undeclared output, ID >= 2^32, or array length > 2^32"

def request (register : Bool) (id address : Nat) : Option ReadRequest :=
  if id < limit ∧ address < limit then
    some ⟨register,BitVec.ofNat 32 id,BitVec.ofNat 32 address⟩
  else none

theorem request_exact (hi : id < limit) (hj : address < limit) :
    ∃ p, request register id address = some p ∧ p.register = register ∧
      p.id.toNat = id ∧ p.address.toNat = address := by
  refine ⟨⟨register,BitVec.ofNat 32 id,BitVec.ofNat 32 address⟩,?_,rfl,?_,?_⟩
  · simp [request,hi,hj]
  · change id % 2^32 = id
    exact Nat.mod_eq_of_lt hi
  · change address % 2^32 = address
    exact Nat.mod_eq_of_lt hj

theorem request_rejects (h : limit ≤ id ∨ limit ≤ address) :
    request register id address = none := by
  simp only [request]
  split
  · rename_i yes; rcases h with h | h <;> omega
  · rfl

/-- Every cell in a declared memory can be named, provided the explicit
interface contract holds. Length 2^32 is allowed: its last address is 2^32-1. -/
theorem array_request (h : Fits a outputs) (mem : (id,size) ∈ a.memories.toList)
    (inside : address < size) :
    ∃ p, request false id address = some p ∧ p.register = false ∧
      p.id.toNat = id ∧ p.address.toNat = address :=
  request_exact (h.1 _ mem).1 (Nat.lt_of_lt_of_le inside (h.1 _ mem).2)

theorem register_request (h : Fits a outputs)
    (declared : id ∈ a.machine.nodes.toList.flatMap Node.registers) :
    ∃ p, request true id 0 = some p ∧ p.register = true ∧ p.id.toNat = id ∧ p.address.toNat = 0 :=
  request_exact (h.2.1 id declared) (by decide)

theorem oversized_id_rejected (mem : (id,size) ∈ a.memories.toList) (large : limit ≤ id) :
    ¬ Fits a outputs := by
  intro h
  have := (h.1 _ mem).1
  omega

theorem oversized_length_rejected (mem : (id,size) ∈ a.memories.toList) (large : limit < size) :
    ¬ Fits a outputs := by
  intro h
  have := (h.1 _ mem).2
  omega

def configuration (register : Bool) (id address : Nat) (value : BitVec 32) : Option Configuration := do
  let p ← request register id address
  return ⟨p.register,p.id,p.address,value⟩

theorem configuration_exact (hi : id < limit) (hj : address < limit) (v : BitVec 32) :
    ∃ c, configuration register id address v = some c ∧ c.register = register ∧
      c.id.toNat = id ∧ c.address.toNat = address ∧ c.value = v := by
  obtain ⟨p,hp,hr,hi,hj⟩ := request_exact (register:=register) hi hj
  exact ⟨⟨p.register,p.id,p.address,v⟩,by simp [configuration,hp],hr,hi,hj,rfl⟩

/-- Accessibility of a successful exposed output is stronger than correctness
for an arbitrary already-representable request. The selected output must fit its
declared capacity. This does NOT assert reachability of every initial state. -/
theorem output_request (h : Fits a outputs) (exposed : id ∈ outputs)
    (within : ∀ size, (id,size) ∈ a.memories.toList → (s.arrays id).size ≤ size)
    (cell : (s.arrays id)[address]? = some value) :
    ∃ p, request false id address = some p ∧
      stateReadResult a outputs s p = ⟨BitVec.ofInt 32 value,true⟩ := by
  obtain ⟨⟨bank,size⟩,mem,equal⟩ := List.mem_map.mp (h.2.2 id exposed)
  dsimp only at equal
  subst bank
  have inside : address < size := by
    have bound := Array.getElem?_eq_some_iff.mp cell
    exact Nat.lt_of_lt_of_le bound.1 (within size mem)
  obtain ⟨p,hp,hr,hi,hj⟩ := array_request h mem inside
  exact ⟨p,hp,by simp [stateReadResult,hr,hi,hj,exposed,cell]⟩

/-- The same request works through the actual emitted text's parsed read port.
No claim about IEEE SystemVerilog outside the existing modeled subset is added. -/
theorem emitted_output_request (h : Fits a outputs)
    (emitted : emit a outputs = .ok text)
    (declared : ∀ id ∈ outputs, a.storageShape.hasMemory id)
    (r : FiniteRuntime a.storageShape) (exposed : id ∈ outputs)
    (within : ∀ size, (id,size) ∈ a.memories.toList → (r.decode.data.arrays id).size ≤ size)
    (cell : (r.decode.data.arrays id)[address]? = some value) :
    ∃ p, request false id address = some p ∧
      readText text a.storageShape r p = some ⟨BitVec.ofInt 32 value,true⟩ := by
  obtain ⟨p,hp,hs⟩ := output_request h exposed within cell
  refine ⟨p,hp,?_⟩
  obtain ⟨code,parsed,generated,_,parses,_,_,_,reads⟩ := emit_text_correct emitted
  simp only [readText,parses,bind,Option.bind]
  rw [reads]
  obtain ⟨cases,emission,_,same⟩ := generateModule_components generated
  subst code
  change (readCode a outputs).eval (environment a r emission.text #[]) p = _
  rw [readCode_correct a outputs declared]
  exact congrArg some hs

end IRComparison.Circuit.SystemVerilog.ExternalPorts
