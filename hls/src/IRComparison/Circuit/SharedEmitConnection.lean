import IRComparison.Circuit.SharedEmitTotal
import IRComparison.Circuit.SharedRTLBindings
import IRComparison.Circuit.SystemVerilog.SerializationSound
import IRComparison.Circuit.SystemVerilog.ConcreteWireTail

namespace IRComparison.Circuit.Shared.NetEmission
open SystemVerilog

/-- Actual ordered netlist evaluation supplies all continuous-assignment
premises. No correspondence of temporary nets is assumed from the caller. -/
theorem realized_evaluation {values : Array Int} (success : generate a p = .ok output)
    (r : FiniteRuntime a.storageShape)
    (evaluated : evaluateWires a r output.declarations = some values) :
    NetRealizes ((environment a r output.declarations #[]).withTemporaries values) output.declarations :=
  evaluateWires_realizes a r ⟨output.declarations,#[]⟩ (generate_ordered success) evaluated

/-- Parse the emitted declaration fragment using the existing concrete lexer
and parser. This is not a parser for unrestricted SystemVerilog. -/
def readText (text : String) : Option (Array Wire) := do
  let trees ← Concrete.parse text
  let (wires,rest) ← Concrete.readWiresTail trees
  if rest.isEmpty then some wires.toArray else none

theorem read_text (output : Output) :
    readText output.text = some (output.declarations.map Concrete.wireReadback) := by
  simp only [readText,Output.text,Concrete.parse_print,bind,Option.bind,Concrete.readWiresTail_eq]
  rw [← List.append_nil (output.declarations.toList.flatMap Concrete.wire),
    Concrete.wires_readback _ [] rfl]
  simp only [bind,Option.bind,List.isEmpty_nil,if_true]
  congr 1
  rw [← Array.toList_map]

/-- Text evaluation retains literal bit patterns and physical reference widths. -/
def evaluateText (a : Artifact) (r : FiniteRuntime a.storageShape) (text : String) : Option (Array Int) := do
  let wires ← readText text
  evaluateWires a r wires

theorem evaluate_text (a : Artifact) (r : FiniteRuntime a.storageShape) (output : Output) :
    evaluateText a r output.text = evaluateWires a r output.declarations := by
  simp only [evaluateText,read_text,bind,Option.bind,evaluateWires,environment,
    environmentFor_readback,Array.toList_map,appendWires_readback]

theorem emitted_read_correct {values : Array Int} (a : Artifact) (r : FiniteRuntime a.storageShape)
    (program : HybridIR.ReadCode) (wr : Nat → Interval)
    (success : generate a (LocalRTL.compile wr (Shared.compile i x y ls ts program)) = .ok output)
    (evaluated : evaluateText a r output.text = some values)
    (closed : ∀ c ∈ (LocalRTL.compile wr (Shared.compile i x y ls ts program)).code,
      CodeReferences a.storageShape c)
    (hb : InputsBound r.decode.data r.decode.wires wr)
    (hi : i.eval r.decode.data r.decode.wires = some iv)
    (hx : x.eval r.decode.data r.decode.wires = some xv)
    (hy : y.eval r.decode.data r.decode.wires = some yv)
    (hl : Matches r.decode.data r.decode.wires ls lvs) (ht : Matches r.decode.data r.decode.wires ts tvs) :
    output.result.observe ((environment a r output.declarations #[]).withTemporaries values) =
      program.eval iv xv yv r.decode.data lvs tvs := by
  have physical := fun c hc => codePhysical_from_refs a r output.declarations values c (closed c hc)
  have evaluatedWires : evaluateWires a r output.declarations = some values := by
    simpa only [evaluate_text] using evaluated
  rw [generate_correct a r.decode _ physical success (realized_evaluation success r evaluatedWires),
    LocalRTL.compile_fullEval_correct]
  exact Shared.compile_bitEval_correct program hb hi hx hy hl ht

/-- The emitted declaration text evaluates, and observing its value/validity
pair agrees with the local shared program. Evaluation success is a conclusion. -/
theorem emitted_total_correct (a : Artifact) (r : FiniteRuntime a.storageShape)
    (closed : ∀ c ∈ p.code, CodeReferences a.storageShape c)
    (generated : generate a p = .ok output) :
    ∃ values, evaluateText a r output.text = some values ∧
      output.result.observe ((environment a r output.declarations #[]).withTemporaries values) = p.fullEval r.decode := by
  obtain ⟨values,evaluated⟩ := generate_total a r closed generated
  refine ⟨values,by simpa only [evaluate_text] using evaluated,?_⟩
  exact generate_correct a r.decode p
    (fun c hc => codePhysical_from_refs a r output.declarations values c (closed c hc)) generated
    (realized_evaluation generated r evaluated)

/-- ReadCode to an evaluated shared SystemVerilog declaration fragment, including
source failure. Generation success and physical input bounds are explicit;
netlist evaluation success is derived, not assumed. -/
theorem emitted_read_total_correct (a : Artifact) (r : FiniteRuntime a.storageShape)
    (program : HybridIR.ReadCode) (wr : Nat → Interval)
    (success : generate a (LocalRTL.compile wr (Shared.compile i x y ls ts program)) = .ok output)
    (closed : ∀ c ∈ (LocalRTL.compile wr (Shared.compile i x y ls ts program)).code,
      CodeReferences a.storageShape c)
    (hb : InputsBound r.decode.data r.decode.wires wr)
    (hi : i.eval r.decode.data r.decode.wires = some iv)
    (hx : x.eval r.decode.data r.decode.wires = some xv)
    (hy : y.eval r.decode.data r.decode.wires = some yv)
    (hl : Matches r.decode.data r.decode.wires ls lvs) (ht : Matches r.decode.data r.decode.wires ts tvs) :
    ∃ values, evaluateText a r output.text = some values ∧
      output.result.observe ((environment a r output.declarations #[]).withTemporaries values) =
        program.eval iv xv yv r.decode.data lvs tvs := by
  obtain ⟨values,evaluated⟩ := generate_total a r closed success
  have textEvaluated : evaluateText a r output.text = some values := by
    simpa only [evaluate_text] using evaluated
  exact ⟨values,textEvaluated,emitted_read_correct a r program wr success textEvaluated closed hb hi hx hy hl ht⟩

end IRComparison.Circuit.Shared.NetEmission
