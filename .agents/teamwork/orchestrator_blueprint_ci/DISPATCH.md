## 2026-11-03T22:32:32Z
Task:
Add a complete, valid `leanblueprint` setup (`blueprint/` directory with `src/web.tex`, `src/print.tex`, `src/content.tex`, `src/macros/common.tex`, `src/macros/web.tex`, `src/macros/print.tex`, `plastex.cfg`, etc., linking the Lean 4 declarations via `\lean{...}`, `\uses{...}`, and marking the proved Phase 1 `F00`–`F06` definitions and theorems with `\leanok`) along with the GitHub Actions CI workflows (`.github/workflows/`) for building the Lean 4 project (`lake build`), checking `leanblueprint`, and deploying the blueprint/docs, and commit and verify everything cleanly.

Guidelines & Standards:
1. Review `GROMOV_COMPACTNESS_BLUEPRINT.md`, `GromovCompactness/`, and `lakefile.lean`.
2. Set up standard `blueprint/` tree following official leanblueprint / plasTeX conventions:
   - `blueprint/src/web.tex`
   - `blueprint/src/print.tex`
   - `blueprint/src/content.tex` (containing chapters/sections covering the full blueprint roadmap, linking Lean 4 declarations with `\lean{...}`, `\uses{...}`, and tagging proved Phase 1 `F00`–`F06` with `\leanok`)
   - `blueprint/src/macros/common.tex`, `blueprint/src/macros/web.tex`, `blueprint/src/macros/print.tex`
   - `blueprint/plastex.cfg`
3. Configure GitHub Actions workflows in `.github/workflows/`:
   - `build.yml` (or `ci.yml`): Checkout, setup elan, lake exe cache get, lake build GromovCompactness.
   - `blueprint.yml`: Build Lean blueprint and documentation, deploy to GitHub Pages on main branch push.
4. Verify lake build continues to compile cleanly (`lake build GromovCompactness` exit code 0).
5. Commit all blueprint files and workflow configurations to Git on branch `main`.
6. Maintain `BRIEFING.md` and `progress.md` in your working directory at all times.
7. Signal victory to Sentinel when all deliverables are verified and committed.

## 2026-11-03T22:42:01Z
Direct Instruction Update from User & Sentinel:
"Proceed to Phase 2 (Local Analysis & Calibrated Bubbling), again divide into A and B, it worked well for Phase 1. Use as much local compute with Gamma models on Ollama as possible, to save resources."

Required Workflow Integration:
1. Immediate Task: Complete the `leanblueprint` setup and GitHub Actions CI workflow (`.github/workflows/`) currently underway, verify that `lake build GromovCompactness` succeeds cleanly, and commit all changes to Git on branch `main`.
2. Next Staging — Phase 2 Execution:
   - Phase 2 Model A (`sorry`-First-Pass Strategy / Skeleton): Scaffold Phase 2 modules in `GromovCompactness/Analysis/` covering `A01`–`A07` (mean-value, Bochner, $\varepsilon$-regularity via `Mathlib.Analysis.Hofer`, elliptic bootstrap, energy gap, monotonicity) with typechecked declarations, theorem signatures, and `sorry` proof placeholders. Link declarations to `blueprint/src/content.tex` via `\lean{...}` and save a clean Model A checkpoint.
   - Phase 2 Model B (Full Proof Completion / Zero-`sorry`): Systematically formalize and certify full proofs for Phase 2 contracts (0 `sorry`, 0 `admit`, standard Lean 4 axioms only), tagging proved items with `\leanok` in `leanblueprint`.
3. Compute Mandate: Maximize usage of local Gemma model via Ollama (`http://localhost:11434`, `tools/ollama_lean4_client.py`) for premise selection, skeleton translation, tactic search, and proof repair.
4. Pause/Resume Compliance: Actively respect `.pause_workflow` and `python3 tools/workflow_control.py`.
