# Dispatch for Worker (Phase 5 Milestone 1 Iteration 3)

## Identity
- Type: teamwork_worker
- Role: Phase 5 Milestone 1 Iteration 3 Forensic Remediation Worker
- Working directory: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m1_iter3
- Parent: Phase 5 Orchestrator (8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0)

## Mandatory Integrity Warning
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

## Mandatory Inputs to Read
- ORIGINAL_REQUEST.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md`
- GATE_STATUS.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/orchestrator_phase5/GATE_STATUS.md`
- Auditor Handoff (Iteration 2): `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/auditor_m1_iter2/handoff.md`
- Explorer 1 Handoff (Iteration 3): `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter3_1/handoff.md`
- Explorer 2 Handoff (Iteration 3): `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter3_2/handoff.md`
- Explorer 3 Handoff (Iteration 3): `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter3_3/handoff.md`

## Exclusive File Ownership
- `tools/extract_accepted_proofs.lean`
- `tools/build_accepted_proofs_dataset.py`
- `data/raw_accepted_theorems.jsonl`
- `data/gemma_accepted_proofs.jsonl`

## Deliverables & Tasks
1. **Dynamic Axiom Extraction (`tools/extract_accepted_proofs.lean`)**:
   - Update `tools/extract_accepted_proofs.lean` to dynamically collect and export the exact axiom array for each clean theorem using memoized axiom traversal (matching `tests/PhaseAxiomCensus.lean`).
   - Run `tools/extract_accepted_proofs.lean` to regenerate `data/raw_accepted_theorems.jsonl` with genuine kernel-derived axiom arrays (`"axioms": [...]`).

2. **Depth-0 Lexical Parsing & Integrity Fixes (`tools/build_accepted_proofs_dataset.py`)**:
   - Implement the depth-0 bracket-balanced lexical scanner (`find_declaration_assignment`, `mask_comments_and_strings`, `clean_proof_trailing`) from Explorer 2 and Explorer 1:
     * Never split on `:=` inside parentheses/brackets/braces (e.g. `(M := M)`).
     * Never truncate proofs to `"by"`. Require proof bodies to be substantive (`is_substantive_proof`).
     * Check source code of every declaration chunk: if `sorry` or `admit` occurs anywhere, strictly skip the declaration.
     * In `harvest_test_proofs`, dynamically verify axioms or filter against dirty constants; never hardcode standard axioms without kernel attestation.
     * In `slice_source_proof`, use the depth-0 scanner to isolate signature from proof body, eliminating the 47 library syntax corruptions.

3. **Regenerate Dataset (`data/gemma_accepted_proofs.jsonl`)**:
   - Run `python3 tools/build_accepted_proofs_dataset.py --force`.
   - Verify:
     * 0 records with `proof.strip() == "by"`
     * 0 records with `proof.strip() == "M)"` or broken brackets
     * 0 records containing `sorry` or `admit`
     * 0 hardcoded axiom facades
     * Substantive, syntactically clean Lean 4 proofs across all records.

4. **Self-Verification**:
   - Execute all 4 auditor verification commands from `auditor_m1_iter2/handoff.md` §5.
   - Run `lake build` (exit 0).
   - Document all changes and test outputs in `changes.md` and `handoff.md`.


## 2026-11-04T23:27:09Z
You are worker_m1_iter3.
Your working directory is: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m1_iter3
Read your task in: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m1_iter3/DISPATCH.md
Read ORIGINAL_REQUEST.md: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md
Read Auditor Handoff: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/auditor_m1_iter2/handoff.md
Read Explorer 1 Handoff: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter3_1/handoff.md
Read Explorer 2 Handoff: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter3_2/handoff.md
Read Explorer 3 Handoff: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m1_iter3_3/handoff.md

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

Implement all Milestone 1 Iteration 3 forensic audit remediation deliverables:
1. Update `tools/extract_accepted_proofs.lean` to dynamically collect and export genuine axiom arrays from the Lean kernel.
2. Update `tools/build_accepted_proofs_dataset.py` with depth-0 bracket-balanced lexical scanning, substantive proof enforcement (rejecting "by" and empty proofs), strict skipping of any chunk containing "sorry" or "admit", and elimination of hardcoded axiom claims.
3. Regenerate `data/gemma_accepted_proofs.jsonl`.
4. Run self-verification against all auditor verification commands in handoff.md §5, run `lake build`, and write results in changes.md and handoff.md, then message me.
