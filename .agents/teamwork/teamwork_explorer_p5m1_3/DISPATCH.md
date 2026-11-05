# Dispatch for Explorer 3 (Milestone 1)

## Identity
- Type: teamwork_explorer
- Role: Kernel Axiom Census Tool (P0-6) Explorer
- Working directory: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_explorer_p5m1_3
- Parent: Phase 5 Orchestrator (8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0)

## Objective
Investigate how to build `tests/PhaseAxiomCensus.lean` (P0-6):
1. Analyze existing `tests/ReportAxiomCensus.lean` and identify why it takes ~12 minutes.
2. Design a single-traversal `CollectAxioms.State` mechanism across all declarations in a specified module prefix (e.g. `GromovCompactness` or sub-namespaces).
3. Ensure it runs in < 3 minutes, prints the exact constant names that depend on `sorryAx`, and produces a zero exit code if and only if zero `sorryAx` dependencies are found in the target module.
4. Verify CLI argument parsing or environment options for scoped checks.

## Scope Boundaries
- Read-only investigation. Do not edit source files.
- Document concrete recommendations and plan in `analysis.md` and `handoff.md`.

## Mandatory Reading
- ORIGINAL_REQUEST.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md`
- COMPLETION_PLAN.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/COMPLETION_PLAN.md` (specifically §0, P0-6)
- SCOPE.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/orchestrator_phase5/SCOPE.md`


## 2026-11-04T21:42:48Z
You are teamwork_explorer_p5m1_3.
Your working directory is: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_explorer_p5m1_3
Read your task description in: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_explorer_p5m1_3/DISPATCH.md
Read ORIGINAL_REQUEST.md: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md
Read COMPLETION_PLAN.md: /Users/pablosuarez/Desktop/SympTopAutoForm/COMPLETION_PLAN.md

Investigate:
1. Examine `tests/ReportAxiomCensus.lean` and identify performance bottlenecks (repeated traversal vs single traversal with memoized `CollectAxioms.State`).
2. Design `tests/PhaseAxiomCensus.lean` taking an optional module prefix (e.g. `GromovCompactness` or sub-module like `GromovCompactness.Extensions.Automorphisms`), performing a single traversal in < 3 minutes.
3. Ensure it outputs the exact names of all constants depending on `sorryAx` (or prints CLEAN if 0) and sets the process exit code appropriately.
4. Verify execution method (`lake env lean tests/PhaseAxiomCensus.lean`) and how gates will call it.

Write your report to `analysis.md` and `handoff.md` in your working directory, and message me when finished.
