# Dispatch for Remediation Worker (Phase 5 Milestone 1 Iteration 2)

## Identity
- Type: teamwork_worker
- Role: Phase 5 Milestone 1 Remediation Worker
- Working directory: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m1_iter2
- Parent: Phase 5 Orchestrator (8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0)

## Mandatory Integrity Warning
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

## Mandatory Inputs to Read
- ORIGINAL_REQUEST.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md`
- GATE_STATUS.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/orchestrator_phase5/GATE_STATUS.md`
- Remediation Explorer 1 Handoff: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter2_1/handoff.md`
- Remediation Explorer 2 Handoff: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter2_2/handoff.md`
- Remediation Explorer 3 Handoff: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter2_3/handoff.md`

## Exclusive File Ownership
- `tools/ollama_lean4_client.py`
- `tools/build_accepted_proofs_dataset.py`
- `data/gemma_accepted_proofs.jsonl`
- `tests/PhaseAxiomCensus.lean`
- `tools/phase_axiom_census.sh`

## Deliverables & Tasks
1. **Ollama Client 9B Policy CLI Enforcement (`tools/ollama_lean4_client.py`)**:
   - Implement `resolve_model_for_task` and wire into `cmd_query`, `cmd_autoformalize`, `cmd_suggest_tactic`.
   - Implement pre-dispatch validation in `query_ollama` checking `is_allowed_9b_model`.
   - Redirect any disallowed model request (12B/27B/70B) to the detected 9B model (`gemma-lean4:latest` or `gemma2:9b-instruct-q5_K_M`) with a warning to stderr.
   - Run `python3 tools/ollama_lean4_client.py test` (must pass 100%) and verify that `--model gemma2:27b` and `--model gemma4:12B` do not call Ollama with disallowed tags or cause 404s.

2. **Accepted Proofs Dataset Regeneration (`tools/build_accepted_proofs_dataset.py` & `data/gemma_accepted_proofs.jsonl`)**:
   - Apply fixes from Explorer 2:
     * Eliminate fallback `by exact <self>` dummy proofs; skip declarations lacking genuine source proof blocks.
     * Fix docstring delimiter (`-/`) and comment masking in `harvest_test_proofs`, anchoring regex to line starts.
     * Sanitize docstrings (`(Zero-sorry)` -> `(Kernel-verified)`).
   - Run `python3 tools/build_accepted_proofs_dataset.py --force`.
   - Verify that `wc -l data/gemma_accepted_proofs.jsonl` yields approximately 937 authentic records, and `python3 -c "import json; assert all('sorry' not in l for l in open('data/gemma_accepted_proofs.jsonl'))"` passes without assertion error.

3. **Census Tool Empty Prefix / Scope Handling (`tests/PhaseAxiomCensus.lean` & `tools/phase_axiom_census.sh`)**:
   - Apply fixes from Explorer 3:
     * Check if prefix is empty or anonymous -> throwError with `STATUS: ERROR (empty module prefix)`.
     * Check if `total == 0` -> throwError with `STATUS: ERROR (0 declarations found for prefix <targetPrefix>)`.
   - Run `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Automorphism` (typo): must output `STATUS: ERROR (0 declarations found)` and exit with code 1.
   - Run `./tools/phase_axiom_census.sh GromovCompactness.Extensions.Homology`: must output `STATUS: CLEAN (0 sorryAx)` and exit with code 0.
   - Run `./tools/phase_axiom_census.sh GromovCompactness`: must output `STATUS: FAILED (54 sorryAx)` and exit with code 1.

4. **Self-Verification**:
   - Run `lake build` (code 0).
   - Document all verification results, commands, and outputs in `changes.md` and `handoff.md`.


## 2026-11-04T22:49:55Z
You are worker_m1_iter2.
Your working directory is: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m1_iter2
Read your task in: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m1_iter2/DISPATCH.md
Read ORIGINAL_REQUEST.md: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md
Read Explorer 1 Handoff: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter2_1/handoff.md
Read Explorer 2 Handoff: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter2_2/handoff.md
Read Explorer 3 Handoff: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter2_3/handoff.md

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

Implement all 3 remediation deliverables:
1. Strict 9B CLI policy enforcement in `tools/ollama_lean4_client.py` (redirecting 12B/27B/70B to 9B with warning, 0 404s).
2. Clean dataset regeneration in `tools/build_accepted_proofs_dataset.py` & `data/gemma_accepted_proofs.jsonl` (no fallback dummy proofs, clean test regex, sanitize docstring sorry mentions).
3. Census tool empty prefix handling in `tests/PhaseAxiomCensus.lean` & `tools/phase_axiom_census.sh` (throw error and exit 1 on total == 0 or empty prefix).
4. Run self-verification commands, lake build, test suite, and record results in changes.md and handoff.md, then message me.
