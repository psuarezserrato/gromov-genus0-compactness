# Dispatch Task: Milestone 3 Explorer 3 (P0-7 Assembly Frames, P0-8 ModuliSpace Defs, P0-9 Docstrings)

## Identity & Role
You are `explorer_m3_3` (`teamwork_explorer`).
Working directory: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_3`.

Path to ORIGINAL_REQUEST.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md`

## Mission & Scope
Investigate and design machine-checked Lean 4 blueprints for:
1. **Task P0-7 (Assembly Rescaling Frames)**:
   - In `GromovCompactness/Compactness/Assembly.lean`:
     * Restate `assemble_global_frames` so it constructs global coordinate frames from `CalibratedRescaling` data rather than assuming uncalibrated or ad-hoc rescalings.
2. **Task P0-8 (Eliminate `sorry`-defined `def` and `instance` in `ModuliSpace.lean`)**:
   - In `GromovCompactness/ModuliSpace/ModuliSpace.lean`:
     * Eliminate all `sorry`-built `def` or `instance` declarations (`COMPLETION_PLAN.md` §0 & §2 P0-8 mandate: zero `sorry`-built `def` or `instance` declarations may remain anywhere in the library).
     * Check: `GromovConverges`, `gromovDist`, `moduliSpaceMetric`, `ModuliSpaceInClass`.
     * Provide concrete, zero-sorry mathematical definitions / types.
3. **Task P0-9 (Docstring & Reduction Audit)**:
   - In `GromovCompactness/Main.lean` and related modules:
     * Audit docstrings for misleading claims.
     * Label all reduction theorems taking open statements as explicit hypotheses as conditional (per `COMPLETION_PLAN.md` §0 rules: reduction theorems must be explicitly labelled conditional and do not count as closing open contracts).

Deliver a structured Hard Handoff report in `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_3/handoff.md` with compilable code blueprints, and message the orchestrator (`8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0`).


## 2026-11-05T05:59:12Z
Your working directory is /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_3.
You are explorer_m3_3 (teamwork_explorer).

Path to ORIGINAL_REQUEST.md: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md

Read your full task dispatch in /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_3/DISPATCH.md.

Mission:
Investigate and author machine-checked Lean 4 blueprints for:
1. Task P0-7: Restate assemble_global_frames in GromovCompactness/Compactness/Assembly.lean using CalibratedRescaling data.
2. Task P0-8: In GromovCompactness/ModuliSpace/ModuliSpace.lean, eliminate all sorry-defined def and instance declarations (GromovConverges, gromovDist, moduliSpaceMetric, ModuliSpaceInClass). Provide concrete, zero-sorry mathematical definitions and instances.
3. Task P0-9: In GromovCompactness/Main.lean and related modules, audit docstrings and label reduction theorems as conditional.

Deliver your report in .agents/teamwork/explorer_m3_3/handoff.md and message the orchestrator (8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0).
