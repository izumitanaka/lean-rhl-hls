# Proof and implementation map

Read the [technical note](TECHNICAL-NOTE.md) first for the theorem premises. File locations are grouped by role; declaration names retain the `IRComparison` namespace.

| Stage | Implementation and theorem entry points |
| --- | --- |
| Supported Lean input | [LeanWordCommand](../hls/src/IRComparison/Frontend/LeanWordCommand.lean), [WordFrontend](../hls/src/IRComparison/Frontend/WordFrontend.lean): `WordFrontend.Result.correct` and generated `wordBody_correct` declarations |
| Definition provenance and typing | [LeanEnvironmentProvenance](../hls/src/IRComparison/Frontend/LeanEnvironmentProvenance.lean), [LeanEntryEnvironment](../hls/src/IRComparison/Frontend/LeanEntryEnvironment.lean), [LeanTyped](../hls/src/IRComparison/Frontend/LeanTyped.lean) |
| BV32 body and source kernel sequence | [HybridWord](../hls/src/IRComparison/Hybrid/HybridWord.lean), [HybridWordGlobal](../hls/src/IRComparison/Hybrid/HybridWordGlobal.lean): `source_correct`, `program_correct`, `program_finishes` |
| Window/body transformation | [HybridWindowRead](../hls/src/IRComparison/Hybrid/HybridWindowRead.lean), [HybridWindowBody](../hls/src/IRComparison/Hybrid/HybridWindowBody.lean), [HybridWindowPlan](../hls/src/IRComparison/Hybrid/HybridWindowPlan.lean): compiled-body correctness and `Plan.blocks_correct` |
| Whole-array policy and communication | [HybridGlobal](../hls/src/IRComparison/Hybrid/HybridGlobal.lean), [HybridUnifiedPipeline](../hls/src/IRComparison/Hybrid/HybridUnifiedPipeline.lean), [HybridCompactChain](../hls/src/IRComparison/Hybrid/HybridCompactChain.lean) |
| SMT candidates and arithmetic recheck | [CompactSequence](../hls/src/IRComparison/Memory/CompactSequence.lean): `response_sound`, `equivalent_correct`, `accept`; [PaperCore SMTConnection](../papercore/src/PaperCore/SMT/SMTConnection.lean) |
| Sequential control | [HybridCommandControl](../hls/src/IRComparison/Hybrid/HybridCommandControl.lean), [HybridCompactChainControl](../hls/src/IRComparison/Hybrid/HybridCompactChainControl.lean) |
| Finite circuit | [Backend](../hls/src/IRComparison/Circuit/Backend.lean), [FinitePipelineSound](../hls/src/IRComparison/Circuit/FinitePipelineSound.lean): `finite_pipeline_finishes` |
| RTL interpretation | [RTL/PipelineSound](../hls/src/IRComparison/Circuit/RTL/PipelineSound.lean), [RTL/InterfaceRunSound](../hls/src/IRComparison/Circuit/RTL/InterfaceRunSound.lean) |
| Emitted text | [Emit](../hls/src/IRComparison/Circuit/Emit.lean), [SystemVerilog/SerializationSound](../hls/src/IRComparison/Circuit/SystemVerilog/SerializationSound.lean) |
| Reset/configuration/start and readout | [SystemVerilog/PreparationSound](../hls/src/IRComparison/Circuit/SystemVerilog/PreparationSound.lean): `emitted_text_reset_config_start_readout` |
| Assumption audit | [Audit.lean](../hls/Audit.lean) |

The `Core` and `Memory` directories are shared infrastructure, not merely historical experiments. `Examples` contains both current workloads and comparison cases. The standalone `Experimental/ArrayFusion` module is not enabled by the main pipeline. `Components` contains separate clocked-operation experiments; the current backend's arithmetic remains combinational.

The reference PaperCore compiler starts at [CertifiedPipeline](../papercore/src/PaperCore/CertifiedPipeline.lean). Its paper-AST semantics and generic SMT premises remain distinct from the supported Lean/BV32 path.
