import IRComparison.Circuit.CountedBackend
import IRComparison.Circuit.InstructionFrame

namespace IRComparison.Circuit
open HybridSymbolicGlobal (Instruction)

def BlocksContract.ofCounted (start stride : Int) (count : Nat) (initial refill : List Load)
    (body : HybridIR.Cmd) (input qi qo : Nat) (b : Build)
    (inputs : 2 ≤ b.wires.size) (distinct : qi ≠ qo)
    (readonly : input ∉ commandWrites body)
    (known : sendBound body = some bound) (capacity : count*bound ≤ cap qo) :
    BlocksContract cap (counted start stride count initial refill body input qi qo b).1 input qi qo
      (referenceBlocks start stride count initial refill body) := by
  constructor
  · exact Schedule.above_mono _ (counted_frame start stride count initial refill body input qi qo b inputs) inputs
  · intro p x y hx hy empty
    exact counted_full_reference start stride count initial refill body input qi qo b p inputs distinct empty readonly hx hy known capacity

theorem prepareSymbolicWith_contract (backend : CountedBackend) (sizes mapping : Nat → Nat) (raw : Instruction)
    (b : Build) (inputs : 2 ≤ b.wires.size) (floor : limit ≤ b.nextArray)
    (channels : ChannelMap ids mapping b.nextQueue) (consistent : instructionChannels ids (symbolicReference raw))
    (outputMembers : ∀ a ∈ (symbolicOutput raw).toList, a ∈ ids)
    (bodyScope : ∀ a ∈ allCommandArrays (symbolicBody raw).body, a < limit)
    (known : sendBound (symbolicBody raw).body = some bound)
    (capacity : ∀ a ∈ (symbolicOutput raw).toList, symbolicBudget raw ≤ cap (mapping a))
    (covered : CoversQueues cap (prepareSymbolicWith backend.build sizes mapping raw b).2) :
    InstructionContract ids mapping limit b.nextQueue cap (prepareSymbolicWith backend.build sizes mapping raw b).1 (symbolicReference raw) := by
  let c := symbolicReference raw
  change instructionChannels ids c at consistent
  change ∀ a ∈ c.output.toList, a ∈ ids at outputMembers
  change ∀ a ∈ c.output.toList, symbolicBudget raw ≤ cap (mapping a) at capacity

  let b0 := b.allocateSnapshot c.input sizes
  have inputExtend := chooseInput_extension mapping c.mode b0
  have inputMatches := chooseInput_matches (b:=b0) channels consistent
  have inputStorage := chooseInput_storage mapping c.mode b0
  change CoversQueues cap (let (qi,b1) := chooseInputQueue mapping c.mode b0;
    let (qo,b2) := chooseOutputQueue mapping (symbolicBudget raw) c.output b1;
    (backend.build (symbolicBody raw).start (symbolicBody raw).stride (symbolicBody raw).count (symbolicInitial raw) (symbolicRefill raw) (symbolicBody raw).body b.nextArray qi qo b2).2) at covered
  change InstructionContract ids mapping limit b.nextQueue cap
    (let (qi,b1) := chooseInputQueue mapping c.mode b0;
    let (qo,b2) := chooseOutputQueue mapping (symbolicBudget raw) c.output b1;
    let (body,_) := backend.build (symbolicBody raw).start (symbolicBody raw).stride (symbolicBody raw).count (symbolicInitial raw) (symbolicRefill raw) (symbolicBody raw).body b.nextArray qi qo b2;
    ⟨b.nextArray,qi,qo,body⟩) c
  generalize hi : chooseInputQueue mapping c.mode b0 = pair at *
  obtain ⟨qi,b1⟩ := pair
  dsimp only at inputExtend inputMatches inputStorage covered ⊢
  have outputExtend := chooseOutput_extension mapping (symbolicBudget raw) c.output b1
  have outputMatches := chooseOutput_matches (mapping:=mapping) (b:=b1)
    (budget:=symbolicBudget raw) outputMembers
  have outputStorage := chooseOutput_storage mapping (symbolicBudget raw) c.output b1
  have distinct := choices_distinct (budget:=symbolicBudget raw) channels consistent inputMatches.1 inputMatches.2 outputMembers
  generalize ho : chooseOutputQueue mapping (symbolicBudget raw) c.output b1 = pair at *
  obtain ⟨qo,b2⟩ := pair
  dsimp only at outputExtend outputMatches outputStorage distinct covered ⊢
  have blockExtend := backend.extension (symbolicBody raw).start (symbolicBody raw).stride (symbolicBody raw).count (symbolicInitial raw) (symbolicRefill raw) (symbolicBody raw).body b.nextArray qi qo b2
  generalize hc : backend.build (symbolicBody raw).start (symbolicBody raw).stride (symbolicBody raw).count (symbolicInitial raw) (symbolicRefill raw) (symbolicBody raw).body b.nextArray qi qo b2 = pair at *
  obtain ⟨body,b3⟩ := pair
  dsimp only at blockExtend covered ⊢
  have coveredBody := covered.before blockExtend
  have coveredInput := coveredBody.before outputExtend
  have inputCap : ∀ array order, c.mode = .memory array order true → order.length ≤ cap qi := by
    intro array order hm
    have hh := chooseInput_capacity (b:=b0) (mapping:=mapping) (cap:=cap) (mode:=c.mode)
      (by rw [hi]; exact coveredInput) hm
    simpa only [hi] using hh
  have outputCap : (symbolicBody raw).count*bound ≤ cap qo := by
    have hh := chooseOutput_capacity (b:=b1) (mapping:=mapping) (cap:=cap) (output:=c.output)
      (budget:=symbolicBudget raw) (by rw [ho]; exact coveredBody) (by simpa [known] using capacity)
    rw [ho] at hh
    simpa only [symbolicBudget,known,Option.getD_some] using hh
  have readonly : b.nextArray ∉ commandWrites (symbolicBody raw).body := by
    intro write
    have := bodyScope _ (commandWrites_mem _ write)
    omega
  have bodyInputs : 2 ≤ b2.wires.size := Nat.le_trans inputs (Nat.le_trans inputExtend.wires outputExtend.wires)
  have bodyContract := backend.correct (symbolicBody raw).start (symbolicBody raw).stride (symbolicBody raw).count
    (symbolicInitial raw) (symbolicRefill raw) (symbolicBody raw).body b.nextArray qi qo b2 cap bound bodyInputs distinct readonly known outputCap
  rw [hc] at bodyContract
  refine ⟨floor,inputMatches.1,?_,distinct,inputCap,bodyContract⟩
  exact outputMatches.lower inputExtend.nextQueue

abbrev prepareSymbolic_contract {limit : Nat} {ids : List Nat} {bound : Nat} {cap : Nat → Nat} :=
  prepareSymbolicWith_contract (limit:=limit) (ids:=ids) (bound:=bound) (cap:=cap) CountedBackend.legacy

end IRComparison.Circuit
