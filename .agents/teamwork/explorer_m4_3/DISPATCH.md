# Dispatch: Milestone 4 Explorer 3 (explorer_m4_3)

## Mission
Investigate Component 5 `#audit_wiring` in `tests/PhaseAxiomCensus.lean` and the specialized 9B Gemma proving loop integration for Milestone 4.
Analyze the implementation of `#audit_wiring` command in Lean 4 metaprogramming to verify the connected call graph and zero direct `sorry`, and establish the proving loop commands using `tools/ollama_lean4_client.py` and `tools/premise_retrieval.py`.

## Mandatory Inputs & References
- ORIGINAL_REQUEST: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md` (MUST read first)
- COMPLETION_PLAN: `/Users/pablosuarez/Desktop/SympTopAutoForm/COMPLETION_PLAN.md` (§5.1, §5.5, P0-6, P0-11)
- User Approved Directive: `core_wiring_plan.md` (Component 5 #audit_wiring)
- SCOPE: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/orchestrator_phase5/SCOPE.md`
- Target Files:
  - `/Users/pablosuarez/Desktop/SympTopAutoForm/tests/PhaseAxiomCensus.lean`
  - `/Users/pablosuarez/Desktop/SympTopAutoForm/tools/ollama_lean4_client.py`
  - `/Users/pablosuarez/Desktop/SympTopAutoForm/tools/premise_retrieval.py`
- Working Directory: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_3`

## Specific Investigation Tasks
1. Inspect `tests/PhaseAxiomCensus.lean`:
   - How does the existing single-traversal census command work?
   - How should `#audit_wiring` be implemented as a Lean 4 elaboration command (`elab "#audit_wiring"` or `#audit_wiring_phase5`)?
   - What exact checks must `#audit_wiring` execute?
     a. Verify `GromovCompactness.gromov_compactness_genus_zero` transitively references:
        `gromov_compactness_core`, `stabilize_prestable_tree`, `assemble_prestable_limit`, `exists_concentration_data`, `defect_measure_identity`, `resolve_single_defect_tree`, `TargetThresholds`, `nonlinear_elliptic_bootstrap`, `puncture_sobolev_extension`.
     b. Verify that `gromov_compactness_core`, `gromov_subsequence_alternative`, `stabilize_prestable_tree`, `resolve_single_defect_tree`, `weak_energy_measure_compactness`, and `removal_of_singularities` have **zero direct `sorry`** in their proof bodies.
2. Inspect the 9B Gemma proving loop:
   - Check local Ollama daemon status (`http://localhost:11434`) and model `gemma-lean4:latest`.
   - Check `tools/ollama_lean4_client.py` and `tools/premise_retrieval.py`.
   - Verify that calls to `/api/generate` log to `.agents/gemma_usage.jsonl`.
3. Provide a concrete blueprint and patch for `tests/PhaseAxiomCensus.lean` and proving instructions for the Worker.
4. Write your report to `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_3/handoff.md`.

## 2026-11-05T07:46:00Z
You are explorer_m4_3.
Your working directory is: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_3
MANDATORY: Read /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md first.
Then read your task instructions in /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_3/DISPATCH.md.
Investigate Component 5 `#audit_wiring` in `tests/PhaseAxiomCensus.lean` and the specialized 9B Gemma proving loop integration (`tools/ollama_lean4_client.py` and `tools/premise_retrieval.py`).
Provide a concrete blueprint and patch for `tests/PhaseAxiomCensus.lean` and proving instructions for the Worker.
Write your report to /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_3/handoff.md.
Notify me with send_message when complete.
