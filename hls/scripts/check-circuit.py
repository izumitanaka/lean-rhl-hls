#!/usr/bin/env python3
"""Generate, simulate, and optionally synthesize the experimental RTL backend.

Lean's finite-circuit theorem is general; these tests cross-check the proved subset serializer against external tools.
Requires lake, iverilog/vvp, and (with --synth) yosys on PATH.
"""
import argparse
import json
import hashlib
import os
import time
from pathlib import Path
import shutil
import subprocess
import signal


def generate_case(root, name, timeout):
    """Keep logs and reap the entire lake/Lean process group on a timeout."""
    environment = os.environ.copy()
    for key in ["HLS_CASE", "HLS_CASES", "HLS_LIST_CASES"]:
        environment.pop(key, None)
    environment["HLS_CASE"] = name
    directory = root / "artifacts/circuit" / name
    directory.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    with (directory / "generation.log").open("w") as log:
        process = subprocess.Popen(["lake", "env", "lean", "--run", "scripts/circuit-check.lean"],
                                   cwd=root, env=environment, stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        try:
            returncode = process.wait(timeout=timeout)
            status = "passed" if returncode == 0 else "failed"
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            returncode, status = None, "timeout"
    return {"case": name, "status": status, "returncode": returncode,
            "seconds": time.perf_counter() - started, "limit_seconds": timeout,
            "log": str((directory / "generation.log").relative_to(root))}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--synth", action="store_true")
    parser.add_argument("--skip-generate", action="store_true")
    parser.add_argument("--case", action="append", default=[])
    parser.add_argument("--generation-timeout", type=float, default=600,
                        help="per-case Lean generation/validation limit in seconds (default: 600)")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    for tool in ["iverilog", "vvp"] + (["yosys"] if args.synth else []):
        if not shutil.which(tool):
            raise SystemExit(f"Required tool not found: {tool}")
    generation = []
    selected_names = args.case
    if args.generation_timeout <= 0:
        parser.error("--generation-timeout must be positive")
    if args.skip_generate:
        previous = root / "artifacts/circuit" / (("selected-" if args.case else "") + "generation-results.json")
        if previous.exists():
            generation = [r for r in json.loads(previous.read_text())
                          if not args.case or r["case"] in args.case]
    if not args.skip_generate:
        subprocess.run(["lake", "build", "IRComparison.Circuit.RTL.InterfaceRunSound", "IRComparison.Circuit.SystemVerilog.PreparationSound", "IRComparison.Examples.WordWorkloads", "IRComparison.Examples.WordFrontendExamples", "IRComparison.Examples.HLSBenchmarks"], cwd=root, check=True)
        subprocess.run(["python3", "scripts/hls-benchmark-fixtures.py"], cwd=root, check=True)
        environment = os.environ.copy()
        environment["HLS_LIST_CASES"] = "1"
        listing = subprocess.run(["lake", "env", "lean", "--run", "scripts/circuit-check.lean"],
                                 cwd=root, check=True, env=environment, capture_output=True, text=True)
        available = [line[5:] for line in listing.stdout.splitlines() if line.startswith("CASE ")]
        if not available or set(args.case) - set(available):
            raise SystemExit(f"Unknown cases or empty case list: {sorted(set(args.case)-set(available))}")
        selected_names = args.case or available
        for name in selected_names:
            row = generate_case(root, name, args.generation_timeout)
            generation.append(row)
            print(name, "Lean", row["status"], f"{row['seconds']:.1f}s", flush=True)
            prefix = "selected-" if args.case else ""
            (root / "artifacts/circuit" / (prefix + "generation-results.json")).write_text(
                json.dumps(generation, indent=2) + "\n")
    failed_generation = {r["case"] for r in generation if r["status"] != "passed"}
    results = []
    synthesized = {}
    for directory in sorted((root / "artifacts/circuit").iterdir()):
        if not (directory / "tb.sv").exists():
            continue
        if selected_names and directory.name not in selected_names:
            continue
        if directory.name in failed_generation:
            continue
        subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", "sim", "design.sv", "tb.sv"],
                       cwd=directory, check=True, capture_output=True, text=True)
        simulation_started = time.perf_counter()
        simulation = subprocess.run(["vvp", "sim"], cwd=directory, check=True,
                                    capture_output=True, text=True, timeout=120)
        (directory / "simulation.log").write_text(simulation.stdout + simulation.stderr)
        if "PASS cycles=" not in simulation.stdout:
            raise RuntimeError(f"Missing success marker for {directory.name}")
        row = {"case": directory.name, "simulation": simulation.stdout.splitlines()[0],
               "rtl_sha256": hashlib.sha256((directory / "design.sv").read_bytes()).hexdigest(),
               "simulation_seconds": time.perf_counter() - simulation_started}
        if (directory / "metrics.json").exists():
            row["metrics"] = json.loads((directory / "metrics.json").read_text())
        if args.synth:
            digest = row["rtl_sha256"]
            if digest in synthesized:
                original = synthesized[digest]
                row["synthesis"] = original["synthesis"]
                row["synthesis_reused_from"] = original["case"]
                # Identical RTL is synthesized once per run; every testbench
                # still runs independently with its own reference values.
                for filename in ["statistics.json", "netlist.json"]:
                    shutil.copyfile(root / "artifacts/circuit" / original["case"] / filename,
                                    directory / filename)
                (directory / "synthesis.log").write_text(
                    f"Identical RTL SHA256 {digest}; reused synthesis from {original['case']} in this run.\n")
            else:
                synthesis_started = time.perf_counter()
                with (directory / "synthesis.log").open("w") as log:
                    subprocess.run(["yosys", "-Q", "-T", "-p",
                                    "read_verilog -sv design.sv; synth -top hls_top; check; "
                                    "tee -o statistics.json stat -json; write_json netlist.json"],
                                   cwd=directory, stdout=log, stderr=subprocess.STDOUT,
                                   check=True, timeout=600)
                stats = json.loads((directory / "statistics.json").read_text())
                row["synthesis"] = stats["modules"]["\\hls_top"]
                row["synthesis_seconds"] = time.perf_counter() - synthesis_started
                synthesized[digest] = row
        results.append(row)
        print(directory.name, row["simulation"], "synthesized" if args.synth else "", flush=True)
    prefix = "selected-" if args.case else ""
    destination = root / "artifacts/circuit" / (prefix + ("synthesis-results.json" if args.synth else "simulation-results.json"))
    destination.write_text(json.dumps(results, indent=2) + "\n")
    if not results:
        (root / "artifacts/circuit" / (prefix + "manifest.json")).write_text(json.dumps({
            "status": "no completed cases", "test_count": 0, "selection": args.case or "all",
            "generation_failures": [r for r in generation if r["status"] != "passed"]}, indent=2)+"\n")
        raise SystemExit("No cases completed; see generation-results.json and per-case logs")
    source_digest = hashlib.sha256()
    for path in sorted((root / "src").rglob("*.lean")):
        source_digest.update(str(path.relative_to(root)).encode() + b"\0" + path.read_bytes())
    manifest = {
        "status": "general source-to-serialized-SystemVerilog-subset execution and read-port observations including reset/config/start; independent text parsing and production printer certified; host correctness and full IEEE semantics excluded",
        "lean_sources_sha256": source_digest.hexdigest(),
        "proofs": ["Circuit.Schedule.assemble_finishes", "Circuit.command_finishes",
                   "Circuit.expandedLoads_correct", "Circuit.counted_correct",
                   "Circuit.duplex_static_correct", "Circuit.producer_static_correct",
                   "Circuit.receiver_correct", "Circuit.compact_pipeline_finishes",
                   "Circuit.unified_compact_finishes", "Circuit.expanded_pipeline_finishes",
                   "Circuit.unified_pipeline_finishes", "Circuit.Checked.execution",
                   "Circuit.word_pipeline_finishes", "Circuit.storage_reachable",
                   "Circuit.finite_execution", "Circuit.finite_pipeline_finishes",
                   "Circuit.RTL.lowerNode_correct", "Circuit.RTL.combinational_correct",
                   "Circuit.RTL.lowerCombinational_tick", "Circuit.RTL.Bank.shift_correct",
                   "Circuit.RTL.artifact_run_correct", "Circuit.RTL.rtl_pipeline_finishes",
                   "Circuit.finiteRun_from_agreement", "Circuit.finite_observation_from_initial",
                   "Circuit.RTL.rtl_pipeline_from_initial", "Circuit.FiniteRuntime.withUnused_decode",
                   "Circuit.RTL.interface_pipeline_finishes", "Circuit.RTL.beginInvocation_agrees",
                   "Circuit.SystemVerilog.Expr.text_correct", "Circuit.SystemVerilog.Statement.text_correct",
                   "Circuit.SystemVerilog.widened_binary_correct", "Circuit.SystemVerilog.scalar_nonblocking",
                   "Circuit.SystemVerilog.literal_printed_bits", "Circuit.SystemVerilog.snapshot_copy_correct",
                   "Circuit.generateCode_ordered", "Circuit.termText_declared",
                   "Circuit.SystemVerilog.division_meaning", "Circuit.SystemVerilog.termTemplate_correct",
                   "Circuit.SystemVerilog.termText_correct", "Circuit.SystemVerilog.generateCode_cache_correct",
                   "Circuit.SystemVerilog.physicalTree_finite", "Circuit.SystemVerilog.generateCode_finite_values",
                   "Circuit.SystemVerilog.generateCode_references", "Circuit.SystemVerilog.generateCode_checked_values",
                   "Circuit.SystemVerilog.generateCode_total", "Circuit.SystemVerilog.validityText_correct",
                   "Circuit.SystemVerilog.expression_correct", "Circuit.SystemVerilog.testCode_correct",
                   "Circuit.SystemVerilog.artifact_tests_ready", "Circuit.SystemVerilog.statementCode_branch_decision",
                   "Circuit.SystemVerilog.statementCode_assign_correct", "Circuit.SystemVerilog.fifo_shift_correct",
                   "Circuit.SystemVerilog.statementCode_store_correct", "Circuit.SystemVerilog.statementCode_copy_correct",
                   "Circuit.SystemVerilog.statementCode_send_correct", "Circuit.SystemVerilog.statementCode_tail_correct",
                   "Circuit.SystemVerilog.generateCode_execution_total", "Circuit.SystemVerilog.finite_store_matches",
                   "Circuit.SystemVerilog.lowerNode_frame", "Circuit.SystemVerilog.statementCode_refines",
                   "Circuit.SystemVerilog.generateCode_refines", "Circuit.SystemVerilog.generateCode_tick_refines",
                   "Circuit.SystemVerilog.statementCode_refines_control", "Circuit.SystemVerilog.Store.Matches.commit_packed",
                   "Circuit.SystemVerilog.commit_environment", "Circuit.SystemVerilog.physicalTick_quiet_refines",
                   "Circuit.SystemVerilog.physicalRun_agrees", "Circuit.SystemVerilog.physical_pipeline_from_started",
                   "Circuit.SystemVerilog.readCode_correct", "Circuit.SystemVerilog.readCode_observed",
                   "Circuit.SystemVerilog.physical_pipeline_readout", "Circuit.SystemVerilog.storageDeclarations_type",
                   "Circuit.SystemVerilog.storageDeclarations_memory_capacity", "Circuit.SystemVerilog.storageDeclarations_queue_capacity",
                   "Circuit.SystemVerilog.storageDeclarations_positive", "Circuit.SystemVerilog.moduleCode_tick",
                   "Circuit.SystemVerilog.moduleCode_run", "Circuit.SystemVerilog.generateModule_components",
                   "Circuit.SystemVerilog.emit_module", "Circuit.SystemVerilog.moduleCode_storage",
                   "Circuit.SystemVerilog.emitted_pipeline_readout", "Circuit.SystemVerilog.emit_text_correct", "Circuit.SystemVerilog.emitted_text_pipeline_readout", "Circuit.SystemVerilog.Concrete.parse_printModule", "Circuit.SystemVerilog.emitted_text_start", "Circuit.SystemVerilog.emitted_text_preparation", "Circuit.SystemVerilog.emitted_text_reset_config_start_readout"],
        "remaining": ["synchronous RAM, multi-cycle operators, and parallel scheduling (future extensions)"],
        "premises": ["successful compilation and declared output ports",
                     "existing source layout and Plan.Ready",
                     "static interface metadata fits the physical banks (checked by the emitter)",
                     "source input is the specified result of the supplied reset/configuration commands",
                     "one reset edge, idle configuration edges, one start edge; control inputs deasserted during compute"],
        "trusted": ["formal specification of the generated two-state SystemVerilog subset; this is not a proof of the full IEEE four-state/event standard", "Lean kernel and external simulation/synthesis/physical tools"],
        "regression": "actual emitted String independently parsed and evaluated through reset/config/start and compute; every physical startup field checked against the mathematical preparation specification; invalid configuration writes checked as no-ops; read ports and declaration types checked; emitted text also simulated and synthesized with external tools; no substitution for general proof",
        "memory": "finite register banks; combinational reads; clocked writes",
        "initial_contents": "arbitrary fixed BV32 words until overwritten; explicit initializers respected; no required preservation across invocations",
        "arithmetic": "combinational; BV32 data and inferred signed intermediate widths",
        "test_count": len(results),
        "generation_failures": [r for r in generation if r["status"] != "passed"],
        "selection": args.case or "all",
        "independent_oracle_cases": sum(bool(r.get("metrics", {}).get("independent_oracle")) for r in results),
        "unique_rtl_count": len({r["rtl_sha256"] for r in results}),
        "synthesis_jobs": len(synthesized),
        "fixture_sha256": hashlib.sha256((root / "artifacts/benchmarks/fixtures.json").read_bytes()).hexdigest(),
        "synthesis": args.synth,
        "iverilog": subprocess.run(["iverilog", "-V"], capture_output=True, text=True).stdout.splitlines()[0],
    }
    if args.synth:
        manifest["yosys"] = subprocess.run(["yosys", "-V"], capture_output=True, text=True, check=True).stdout.strip()
    (root / "artifacts/circuit" / (prefix + "manifest.json")).write_text(json.dumps(manifest, indent=2) + "\n")
    if failed_generation:
        raise SystemExit(f"Generation incomplete for {len(failed_generation)} cases; successful results and failure logs saved")


if __name__ == "__main__":
    main()
