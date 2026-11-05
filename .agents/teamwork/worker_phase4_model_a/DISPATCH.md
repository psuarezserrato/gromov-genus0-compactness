# Dispatch Task: Worker Phase 4 Model A Scaffolding

- **Agent Identity**: `worker_phase4_model_a`
- **Role**: teamwork_worker
- **Working Directory**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase4_model_a/`
- **Original User Request Path**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md` (MANDATORY: read first)
- **Phase 4 Scope Document**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/orchestrator_phase4/SCOPE.md`
- **Explorer 1 Handoff**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_phase4_m1_1/handoff.md` (and `proposed_VaryingJ.lean`, `proposed_MarkedCurves.lean`)
- **Explorer 2 Handoff**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_phase4_m1_2/handoff.md` (contains complete `Homology.lean` and `Automorphisms.lean` code)
- **Explorer 3 Handoff**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_phase4_m1_3/handoff.md` (contains `proposed_ModuliSpace.lean`, `proposed_workflow_control.patch`, and blueprint sync text)

## Exclusively Owned Files
You have exclusive write access to:
- `GromovCompactness/Extensions/VaryingJ.lean` (E01)
- `GromovCompactness/Extensions/MarkedCurves.lean` (E02)
- `GromovCompactness/Extensions/Homology.lean` (E03)
- `GromovCompactness/Extensions/Automorphisms.lean` (E04)
- `GromovCompactness/Extensions/ModuliSpace.lean` (E05)
- `GromovCompactness.lean` (re-exports)
- `blueprint/src/content.tex` (Chapter 5 synchronization)
- `tools/workflow_control.py` (contract inventory expansion to 39/39 contracts)

## Mission
Implement Phase 4 Model A Scaffolding Architecture across the 5 contracts (`E01`–`E05`):
1. Create `GromovCompactness/Extensions/` directory and scaffold the 5 modules:
   - `VaryingJ.lean`: Using the certified implementation from Explorer 1 (`proposed_VaryingJ.lean`).
   - `MarkedCurves.lean`: Using the certified implementation from Explorer 1 (`proposed_MarkedCurves.lean`).
   - `Homology.lean`: Using the certified implementation from Explorer 2 (`handoff.md` §3.2).
   - `Automorphisms.lean`: Using the certified implementation from Explorer 2 (`handoff.md` §3.3).
   - `ModuliSpace.lean`: Using the certified implementation from Explorer 3 (`proposed_ModuliSpace.lean`).
2. Re-export all 5 modules in `GromovCompactness.lean`.
3. Synchronize `blueprint/src/content.tex` with the Chapter 5 Lean bindings (`\lean{...}`, `\uses{...}`, and `\leanok` on zero-sorry declarations).
4. Update `tools/workflow_control.py` using Explorer 3's patch / design so all 39 contracts (`F00`–`E05`) are tracked. Verify `python3 tools/workflow_control.py status` detects 39/39 contracts.
5. Compile the Lean project: `lake build GromovCompactness` (MUST exit code 0).
6. Compile the blueprint PDF: `cd blueprint/src && pdflatex -interaction=batchmode print.tex` (MUST exit code 0 and produce `blueprint/src/print.pdf`).
7. Write your handoff report to `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase4_model_a/handoff.md`.

## Mandatory Integrity Warning
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.
