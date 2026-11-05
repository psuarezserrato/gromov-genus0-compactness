# Scope: Blueprint & CI Automation

## Architecture
- `blueprint/` tree:
  - `src/web.tex`: Web entry point for plasTeX with leanblueprint package
  - `src/print.tex`: LaTeX print edition setup with geometry, expl3, and xparse
  - `src/content.tex`: Detailed mathematical text with chapters/sections reflecting GROMOV_COMPACTNESS_BLUEPRINT.md, linking formal declarations with `\lean{...}`, dependencies with `\uses{...}`, and Phase 1 proved nodes with `\leanok`.
  - `src/macros/common.tex`: Common mathematical and formatting macros (`\providecommand{\C}{}\renewcommand{\C}{\mathbb{C}}`, symplectic symbols)
  - `src/macros/web.tex`: Web-specific macros
  - `src/macros/print.tex`: Print-specific macros with robust `\uses` and `\proves` handlers
  - `src/extra_styles.css`: Custom stylesheet for plasTeX web rendering
  - `plastex.cfg` and `src/plastex.cfg`: plasTeX configuration files
- `.github/workflows/`:
  - `build.yml`: CI build on push / pull request checking Lean 4 project compilation (`elan`, `lake exe cache get`, `lake build GromovCompactness`)
  - `blueprint.yml`: CI build and deployment of leanblueprint (PDF and HTML) to GitHub Pages on push to `main`

## Feature Inventory
| # | Feature | Description | Milestone | Source | Status |
|---|---------|-------------|-----------|--------|--------|
| 1 | Lean 4 Symbol & Blueprint Alignment | Extract declarations and proof statuses from `GromovCompactness/` and `GROMOV_COMPACTNESS_BLUEPRINT.md` | M1 | Survey | DONE |
| 2 | plasTeX & leanblueprint Configuration | Setup standard configuration files `plastex.cfg`, `web.tex`, `print.tex`, macros | M2 | PlasTeX Spec | DONE |
| 3 | Blueprint Content & Declaration Linking | Author `content.tex` linking Lean 4 symbols via `\lean{...}`, `\uses{...}`, `\leanok` for Phase 1 `F00`–`F06` | M2 | Mathematical Blueprint | DONE |
| 4 | GitHub Actions Lean 4 Build Workflow | Setup `.github/workflows/build.yml` for CI build | M3 | GitHub Actions | DONE |
| 5 | GitHub Actions Blueprint Deployment Workflow | Setup `.github/workflows/blueprint.yml` for Pages deployment | M3 | GitHub Actions | DONE |
| 6 | Verification & Git Commit | Build verification (`lake build GromovCompactness`, `pdflatex print.tex`) and git commit on `main` | M4 | Verification | DONE |

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|------|-------|-------------|--------|
| 1 | Survey & Architecture Extraction | 3 parallel explorers to map Lean declarations, plasTeX setup, CI workflows | none | DONE |
| 2 | Blueprint Structure & Content Setup | Worker creates blueprint/ directory, macros, plastex.cfg, content.tex with \lean, \uses, \leanok | M1 | DONE |
| 3 | GitHub Actions CI Setup | Worker creates .github/workflows/build.yml and blueprint.yml | M1 | DONE |
| 4 | Verification, Git Commit, and Multi-Agent Audit | Worker verifies lake build, commits to git, 2 Reviewers, 2 Challengers, 1 Auditor (Iterations 1 & 2) | M2, M3 | DONE |

## Interface Contracts
- `GromovCompactness/` ↔ `blueprint/src/content.tex`:
  - Declaration names match exact Lean 4 identifiers (all 17 Phase 1 declarations verified with 0 sorry and standard kernel axioms)
  - Proved items in Phase 1 (`F00`–`F06`) are annotated with `\leanok`
  - Roadmapped items in Layers 2–4 (`A01`–`G05`, `E01`–`E05`) are documented with `\lean{...}` candidate contracts and omit `\leanok`
- `lakefile.lean` / `lean-toolchain` ↔ `.github/workflows/`:
  - Toolchain version `v4.16.0` matches
  - Lake commands use `lake exe cache get` and `lake build GromovCompactness`
  - `lake-manifest.json` is committed in git ensuring reproducible Mathlib cache retrieval
