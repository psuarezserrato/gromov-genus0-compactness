## 2026-11-03T23:34:48Z

You are the Project Orchestrator for Phase 2 of gromov-genus0-compactness.

Your working directory is:
/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/orchestrator_phase2/

Authoritative Request Document:
/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md

Mission:
Execute Phase 2 (Local Analysis & Calibrated Bubbling) of the Gromov Compactness autoformalization, strictly following the 2-stage strategy requested by the user:

Stage 1 — Phase 2 Model A (`sorry`-First-Pass Strategy / Skeleton):
1. Review `GROMOV_COMPACTNESS_BLUEPRINT.md` (contracts A01–A12, B01–B02), `AUTOFORMALIZATION_PLAN.md` (Phase 2), and existing zero-sorry Phase 1 modules in `GromovCompactness/`.
2. Scaffold the Phase 2 Lean 4 modules under `GromovCompactness/Analysis/`:
   - `Monotonicity.lean` (A01 / A08: local area monotonicity and scalar mean-value)
   - `Bochner.lean` (A02: Bochner energy-density differential inequality)
   - `EpsilonRegularity.lean` (A03: Hofer-style epsilon-regularity lemma connecting to `Mathlib.Analysis.Hofer.hofer`)
   - `EllipticBootstrap.lean` (A04, A05, A06: elliptic estimates, W^{1,p} to C^∞ bootstrap, Arzelà-Ascoli local compactness)
   - `EnergyGap.lean` (A07: non-constant J-holomorphic sphere minimal energy gap ε_sph > 0)
   - `SingularityRemoval.lean` (A09–A12: small-energy cylinder localization, exponential decay, smooth removal of isolated singularities)
   - `HoferRescaling.lean` (B01, B02: universal positive threshold and center/calibrate rescaling sequence extraction)
3. Ensure every definition and candidate theorem signature is mathematically accurate, typechecked by Lean 4 (v4.16.0), and imports Mathlib (`Mathlib.Analysis.Hofer`, etc.) and Phase 1 foundations (`F00`–`F06`). Open proofs may use `sorry` in Model A to enable rapid unblocking and full structural verification.
4. Update `blueprint/src/content.tex` to link all newly scaffolded Lean declarations via `\lean{...}` and dependency edges via `\uses{...}`.
5. Verify `lake build GromovCompactness` compiles with exit code 0.
6. Commit Model A deliverables to git on branch `main` and save a checkpoint via `python3 tools/workflow_control.py checkpoint --label "phase2_model_a_scaffolding"`.

Stage 2 — Phase 2 Model B (Full Proof Completion / Zero-`sorry`):
- Systematically prove all theorems with zero `sorry`, zero `admit`, and pure standard Lean 4 kernel axioms (`[propext, Classical.choice, Quot.sound]`), tagging proved items with `\leanok` in `blueprint/src/content.tex`.

Compute Mandate:
Maximize local compute using Gemma models on Ollama (`http://localhost:11434`, `tools/ollama_lean4_client.py`, and the skills in `skills/`: `ollama-lean4-gemma-prover`, `lean4-symplectic-autoformalizer`, `lean4-proof-repair-engine`) for statement generation, premise selection, tactic search, and proof repair to conserve external compute resources.

Workflow Discipline:
- Respect pause/resume sentinels (`.pause_workflow` and `python3 tools/workflow_control.py status`) at all milestone boundaries.
- Maintain `BRIEFING.md` and `progress.md` in your working directory.
- Run multi-agent verification gates (Reviewers, Challengers, Forensic Auditor) and report victory to Sentinel when Model A and Model B are completed.
