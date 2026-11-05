## 2026-11-03T22:51:31Z
You are the Worker for gromov-genus0-compactness.
Your working directory is:
/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_blueprint_ci/

MANDATORY INTEGRITY WARNING:
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

You MUST read the following files before starting:
1. /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md
2. /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_bp_lean/handoff.md
3. /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_bp_plastex/handoff.md
4. /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_bp_ci/handoff.md

Your exclusive write ownership:
- blueprint/plastex.cfg
- blueprint/src/plastex.cfg
- blueprint/src/web.tex
- blueprint/src/print.tex
- blueprint/src/content.tex
- blueprint/src/macros/common.tex
- blueprint/src/macros/web.tex
- blueprint/src/macros/print.tex
- .github/workflows/build.yml
- .github/workflows/blueprint.yml

Your objectives:
1. Implement the complete `blueprint/` directory tree:
   - `blueprint/plastex.cfg` and `blueprint/src/plastex.cfg` per Explorer 2 specifications.
   - `blueprint/src/web.tex` per Explorer 2 specifications.
   - `blueprint/src/print.tex` per Explorer 2 specifications.
   - `blueprint/src/macros/common.tex`, `blueprint/src/macros/web.tex`, `blueprint/src/macros/print.tex` per Explorer 2 specifications.
   - `blueprint/src/content.tex`: synthesizes the mathematical exposition with the complete Lean 4 declaration mappings from Explorer 1 (`F00` through `F06` tagged with `\lean{...}` and `\leanok`, `\uses{...}` for dependency edges, plus the roadmap sections for Layers 2–4).
2. Implement `.github/workflows/`:
   - `.github/workflows/build.yml` per Explorer 3 specifications.
   - `.github/workflows/blueprint.yml` per Explorer 3 specifications.
3. Validate and verify:
   - Run `lake build GromovCompactness` to ensure the project still builds cleanly with exit code 0.
   - Validate the YAML syntax of `.github/workflows/build.yml` and `.github/workflows/blueprint.yml` using python PyYAML.
   - Verify all blueprint TeX files and macro files exist and have non-zero size.
4. Stage and commit to Git:
   - Inspect `git status` on branch `main`.
   - Stage `blueprint/` and `.github/workflows/` (and any related blueprint configs).
   - Commit cleanly with a descriptive commit message (e.g., "Add leanblueprint structure and GitHub Actions CI workflows for Lean 4 and GitHub Pages").
   - Record git commit SHA, branch, and status.
5. Write your complete handoff report to `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_blueprint_ci/handoff.md` and notify with send_message. Keep progress.md updated during your run.
