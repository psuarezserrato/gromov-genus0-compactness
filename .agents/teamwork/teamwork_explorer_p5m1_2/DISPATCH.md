# Dispatch for Explorer 2 (Milestone 1)

## Identity
- Type: teamwork_explorer
- Role: Proved Theorems Extraction & Premise Retrieval Explorer
- Working directory: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_explorer_p5m1_2
- Parent: Phase 5 Orchestrator (8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0)

## Objective
Investigate how to:
1. Extract all accepted zero-`sorry` `(goal, proof)` pairs from the repository's proved theorems and test suites into `data/gemma_accepted_proofs.jsonl`. Check existing theorem extraction tools or Lean scripts in the repository (`tools/` or `tests/`).
2. Build a local BM25 premise-retrieval index over Mathlib + project declarations so prompts include real Mathlib premise names, addressing the primary 9B failure mode (hallucinated lemma names).
3. Check Python dependencies (`rank_bm25`, `uv`, etc.) and data formatting.
4. Provide concrete code architecture and commands for the Worker to implement.

## Scope Boundaries
- Read-only investigation. Do not edit source files.
- Document concrete recommendations and plan in `analysis.md` and `handoff.md`.

## Mandatory Reading
- ORIGINAL_REQUEST.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md`
- COMPLETION_PLAN.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/COMPLETION_PLAN.md` (specifically §5.1, §5.2 item 9, §5.5)
- SCOPE.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/orchestrator_phase5/SCOPE.md`


## 2026-11-04T21:42:41Z
[Message] timestamp=2026-11-04T21:42:41Z sender=8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0 priority=MESSAGE_PRIORITY_HIGH
content:
You are teamwork_explorer_p5m1_2.
Your working directory is: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_explorer_p5m1_2
Read your task description in: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_explorer_p5m1_2/DISPATCH.md
Read ORIGINAL_REQUEST.md: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md
Read COMPLETION_PLAN.md: /Users/pablosuarez/Desktop/SympTopAutoForm/COMPLETION_PLAN.md

Investigate:
1. How to extract all accepted zero-sorry (goal, proof) pairs from the repository's 748 verified theorems and adversarial tests into `data/gemma_accepted_proofs.jsonl`. Check existing tools/scripts.
2. How to construct a local BM25 premise-retrieval index over Mathlib + project declarations (`env.constants` export or declaration extraction) in pure Python.
3. Check python environment, package dependencies (`rank_bm25`, `uv`), and how the client will consume the index.
4. Prepare concrete specifications and pseudo-code/scripts for the Worker.

Write your report to `analysis.md` and `handoff.md` in your working directory, and message me when finished.
