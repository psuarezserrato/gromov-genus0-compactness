# Dispatch: Milestone N3 Worker (Local-Chart PDE Certificates)

## Role & Identity
You are `worker_n3` (`teamwork_worker`).
Your working directory is `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_worker_n3/`.

## MANDATORY INTEGRITY WARNING
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

## Constraints & File Locks
- **Exclusive Write Ownership**:
  - `GromovCompactness/Geometry/NormalCharts.lean`
  - `tests/TestNormalCharts.lean`
- **LOCKED FILES (DO NOT TOUCH - STRICTLY ENFORCED)**:
  - `Compactness/Assembly.lean`
  - `Compactness/GenusZero.lean`
  - `Main.lean`
  - `tests/CertificateSanity.lean`
- **Zero Chart-Compatibility Axioms**: Do NOT add any chart-compatibility axioms to `ClosedTameTarget`.
- **Git Discipline**: Avoid `git reset --hard` or `git checkout .` on `main`. Make standard commits.

## Reference Materials
1. Master Request: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md` (READ FIRST)
2. Project Scope: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/orchestrator_normal_charts/SCOPE.md`
3. Implementation Plan: `/Users/pablosuarez/.gemini/antigravity/brain/4a39bd36-01dc-4865-bd8a-d1bf4124b124/normal_darboux_charts_plan.md`
4. Pre-verified Explorer Reports:
   - Explorer 1 (`discharge_h_weitz` and `discharge_h_hit_exit`):
     `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_explorer_n3_1/handoff.md`
   - Explorer 2 (`discharge_h_osc`, `discharge_h_decay`, and `discharge_h_punc`):
     `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_explorer_n3_2/handoff.md`
   - Explorer 3 (`discharge_h_tower` and `discharge_h_aa`):
     `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_explorer_n3_3/handoff.md`

## Objectives & Deliverables
1. **Implement Proof Bodies in `GromovCompactness/Geometry/NormalCharts.lean`**:
   - `discharge_h_weitz`: Bochner curvature decomposition with $c = 0$, connection terms vanishing at origin $\Gamma(0) = 0$, and curvature constant $b$.
   - `discharge_h_hit_exit`: Boundary-hit monotonicity ($r^2 \le E$) and ball exit via Stokes exactness.
   - `discharge_h_osc`: Cylindrical collar oscillation via Euclidean length-area slice integration in normal charts.
   - `discharge_h_decay`: Cylindrical energy decay via Widman hole-filling and dyadic geometric decay.
   - `discharge_h_punc`: Puncture Sobolev extension across removable singularity via collar oscillation and elliptic extension.
   - `discharge_h_tower`: Finite-order $C^n$ tower via Schauder bootstrap induction $C^{k,\alpha} \to C^{k+1,\alpha}$.
   - `discharge_h_aa`: Smooth local Arzelà-Ascoli extraction via equicontinuity, interior Schauder jet bounds, and Cantor diagonal extraction.
   - Complete `exists_centeredNormalChart` and `exists_uniform_normal_chart_family`.
2. **Update Tests in `tests/TestNormalCharts.lean`**:
   - Verify that Tests 12.1 through 12.7 for all 7 certificates compile and execute with exit code 0.
3. **Build & Census Verification**:
   - Run `lake build` and verify 0 compilation errors across all workspace targets.
   - Run unit tests (`TestNormalCharts.lean`, `StressTestNormalCharts.lean`, `TestAdversarialNormalCharts.lean`) and verify exit code 0.
   - Run `lake env lean tests/PhaseAxiomCensus.lean` and verify 0 `sorryAx` on all completed declarations.

## Reporting
Document all implementation steps, compilation commands, and verification logs in `handoff.md` in your working directory:
`/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/teamwork_worker_n3/handoff.md`.
Maintain `progress.md` for liveness.
When finished, notify parent (`1e6690b3-e7c2-48c0-8bdc-c6cb8d25b692`) via `send_message`.


## 2026-11-08T00:39:31Z
Status check from parent: Please report on your current progress for Milestone N3 implementation (`NormalCharts.lean` certificate proofs). Update your progress.md with latest timestamp and completed steps.
