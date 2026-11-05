# Dispatch for Worker (Phase 5 Milestone 1)

## Identity
- Type: teamwork_worker
- Role: Phase 5 Milestone 1 Implementation Worker
- Working directory: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_worker_p5m1
- Parent: Phase 5 Orchestrator (8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0)

## Mandatory Integrity Warning
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

## Mandatory Inputs & Reports to Read
- ORIGINAL_REQUEST.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md`
- COMPLETION_PLAN.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/COMPLETION_PLAN.md`
- SCOPE.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/orchestrator_phase5/SCOPE.md`
- Explorer 1 Report: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_explorer_p5m1_1/handoff.md` and `analysis.md`
- Explorer 2 Report: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_explorer_p5m1_2/handoff.md` and `analysis.md`
- Explorer 3 Report: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_explorer_p5m1_3/handoff.md` and `analysis.md`

## Exclusive File Ownership
You exclusively own and may edit or create:
- `config/ollama_gemma_config.json`
- `tools/ollama_lean4_client.py`
- `Modelfile.gromov-lean4`
- `tools/extract_accepted_proofs.lean`
- `tools/build_accepted_proofs_dataset.py`
- `tools/export_declarations.lean`
- `tools/premise_retrieval.py`
- `data/gemma_accepted_proofs.jsonl`
- `data/mathlib_project_declarations.jsonl`
- `data/bm25_index.pkl`
- `.agents/gemma_usage.jsonl`
- `tests/PhaseAxiomCensus.lean`
- `tools/phase_axiom_census.sh`

## Deliverables & Tasks
1. **Ollama 9B Plumbing & Client Fixes**:
   - Update `config/ollama_gemma_config.json` to enforce strict 9B-only models (`gemma-lean4:latest`, `gemma2:9b-instruct-q5_K_M`, `gemma2:9b`).
   - Fix `tools/ollama_lean4_client.py`:
     * Actively call `load_config()`.
     * Query `/api/tags` to filter models, redirecting any 12B/27B requests to 9B.
     * Replace `__probe_check__` with `GET /api/version` to eliminate all synthetic 404s.
     * Pass `keep_alive: "30m"`.
     * Implement structured JSONL logging of all real `/api/generate` proving queries to `.agents/gemma_usage.jsonl` (excluding health checks).
     * Add `--with-premises` flag integrating with `tools/premise_retrieval.py`.

2. **Gemma 9B Specialization (Modelfile.gromov-lean4)**:
   - Construct `Modelfile.gromov-lean4` using `FROM gemma2:9b-instruct-q5_K_M` embedding the Gromov Compactness / Mathlib v4.16 system prompt and curated accepted proof exemplars (as detailed in Explorer 1's report).
   - Execute `ollama create gemma-lean4:latest -f Modelfile.gromov-lean4`.
   - Verify with `ollama show gemma-lean4:latest --modelfile` that "3DSymFlux" and "SymFluxLean" are completely eradicated.

3. **Accepted Proofs Dataset & BM25 Premise Index**:
   - Implement `tools/extract_accepted_proofs.lean` and `tools/build_accepted_proofs_dataset.py` to populate `data/gemma_accepted_proofs.jsonl` with verified zero-sorry pairs.
   - Implement `tools/export_declarations.lean` and `tools/premise_retrieval.py` to create `data/bm25_index.pkl`.
   - Benchmark premise retrieval latency (< 5ms) and verify query results on Mathlib lemmas.

4. **Fast Kernel Axiom Census Tool (P0-6)**:
   - Implement `tests/PhaseAxiomCensus.lean` using the memoized single-traversal design from Explorer 3.
   - Implement `tools/phase_axiom_census.sh` wrapper.
   - Run verification:
     * Full library: `lake env lean tests/PhaseAxiomCensus.lean` (must finish in < 15 seconds, report 1194 clean / 54 sorryAx-dependent constants matching baseline).
     * Clean module: `MODULE_PREFIX=GromovCompactness.Extensions.Homology lake env lean tests/PhaseAxiomCensus.lean` (must exit 0 with STATUS: CLEAN).
     * Dirty module: `MODULE_PREFIX=GromovCompactness.Extensions.Automorphisms lake env lean tests/PhaseAxiomCensus.lean` (must exit 1, listing the 6 sorry-dependent theorems).

5. **Self-Verification**:
   - Run all builds and tests:
     * `python3 tools/workflow_control.py status`
     * `lake build`
     * `python3 tools/ollama_lean4_client.py check` (verify 0 404s, clean 9B detection)
     * `python3 tools/ollama_lean4_client.py query --prompt "State Hofer's lemma in Lean 4" --json`
     * `python3 tools/premise_retrieval.py query "holomorphic derivative Cauchy Riemann"`
     * Census runs as above.
   - Write full execution outputs, commands, and results in `changes.md` and `handoff.md`.
