# Dispatch Task: Phase 3 Model A Scaffolding Worker

- **Identity**: `worker_phase3_model_a` (role: teamwork_worker)
- **Working Directory**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase3_model_a/`
- **Parent Conversation ID**: `02ef07b4-e669-479a-8a3d-86a44c7477a8` (Phase 3 Project Orchestrator)
- **Original User Request**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md` (MUST read first)
- **Blueprint Reference**: `/Users/pablosuarez/Desktop/SympTopAutoForm/GROMOV_COMPACTNESS_BLUEPRINT.md`
- **Plan Reference**: `/Users/pablosuarez/Desktop/SympTopAutoForm/AUTOFORMALIZATION_PLAN.md`
- **Explorer Reports to Consume**:
  - `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/spec_miner_phase3_bubbling/handoff.md` (C01–C03, B03–B07)
  - `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/spec_miner_phase3_compactness/handoff.md` (G01–G05)
  - `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_phase3_blueprint/handoff.md` (Blueprint, Exports, Build rules)

## Mandatory Integrity Warning
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

## Objective
Implement and verify Phase 3 Model A (sorry-First-Pass Skeleton) across all assigned modules:
1. Create all 13 Phase 3 Lean 4 modules with the exact type signatures, docstrings, and structures specified in the handoff reports:
   - `GromovCompactness/Compactness/Measures.lean` (C01)
   - `GromovCompactness/Compactness/Concentration.lean` (C02)
   - `GromovCompactness/Compactness/Defect.lean` (C03)
   - `GromovCompactness/Bubbling/Neck.lean` (B03)
   - `GromovCompactness/Bubbling/OneLevel.lean` (B04)
   - `GromovCompactness/Bubbling/GhostBranching.lean` (B05)
   - `GromovCompactness/Bubbling/Rank.lean` (B06 - include the complete zero-sorry proof of `energy_rank_strict_decrease`!)
   - `GromovCompactness/Bubbling/LocalTree.lean` (B07)
   - `GromovCompactness/Compactness/Assembly.lean` (G01)
   - `GromovCompactness/Compactness/Stabilize.lean` (G02)
   - `GromovCompactness/Compactness/GenusZero.lean` (G03)
   - `GromovCompactness/Topology/ComponentCount.lean` (G04)
   - `GromovCompactness/Main.lean` (G05)
2. Update `GromovCompactness.lean` to re-export all Phase 3 modules.
3. Update `blueprint/src/content.tex`:
   - Add `\leanok` on declaration headers (e.g. `\begin{theorem}[...]\leanok`) for Model A typechecked statements.
   - **CRITICAL INTEGRITY RULE**: DO NOT add `\leanok` inside proof blocks (`\begin{proof}\leanok ...`) for unproved lemmas/theorems. Proof `\leanok` is strictly reserved for Model B (zero-sorry).
4. Update `tools/workflow_control.py` lines 103–104 to map G04 to `GromovCompactness/Topology/ComponentCount.lean` and G05 to `GromovCompactness/Main.lean`.
5. Run build and tests:
   - `lake build GromovCompactness` must succeed with exit code 0 and zero non-sorry warnings.
   - Compile blueprint PDF: `cd blueprint && TEXINPUTS=src:$TEXINPUTS latexmk -pdf -interaction=nonstopmode -output-directory=print src/print.tex`
   - Run `python3 tools/workflow_control.py test` and `python3 tools/workflow_control.py status`
6. Write a comprehensive handoff report to:
   `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase3_model_a/handoff.md`
   Document commands and results in your handoff report.

## 2026-11-04T15:11:38Z
**Context**: Phase 3 Model A Scaffolding Progress Check
**Content**: All 13 Phase 3 Lean modules are observed present on disk. Checking in on compilation status (`lake build GromovCompactness`), blueprint verification, and preparation of `handoff.md`.
**Action**: Update `progress.md` with current verification steps and deliver `handoff.md` once tests pass.
