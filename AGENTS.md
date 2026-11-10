# SympTopAutoForm — Agent Rules & Verification Gate

## 1. Kernel Soundness & Anti-Tautology Rules

- **Zero `sorry` / Custom Axioms**: Every Lean declaration must compile with `0 sorryAx` and depend only on Lean's three standard axioms: `[propext, Classical.choice, Quot.sound]`. Never introduce `sorry`, `admit`, `axiom`, `unsafe`, or `implemented_by`.
- **Substantive Mathematical Statements Only**: Never "discharge" a blueprint node or certificate via a tautological implication (`P → P`), vacuous hypothesis, or altered core definition. When a theorem requires geometric/analytic hypotheses (e.g., centered normal-chart bounds, isolated preimages, sequential metric axioms `(MS1)`–`(MS2)`), verify those hypotheses are non-vacuously satisfiable on concrete targets.
- **Protected Core Signatures**:
  - Do **not** modify `GromovCompactness/Geometry/Target.lean`.
  - Preserve existing public theorem names and type signatures so downstream modules and `tests/*.lean` continue to compile; add strengthened or unconditional theorems alongside existing ones.

## 2. Fast Incremental `lake build` Architecture

- **Avoid Rebuilding Foundational Hubs Unnecessarily**: Modifying `GromovCompactness/Geometry/Sphere.lean`, `Topology/SmoothLocal.lean`, or `Analysis/Energy.lean` triggers recompilation of ~3,000 downstream build jobs. Place new helper constructors and bridge lemmas in leaf or downstream modules (`GromovCompactness/Extensions/*.lean`, `GromovCompactness/Main.lean`, or at the tail of the narrowest consuming module) whenever possible.
- **Targeted Iteration**: Iterate with `lake build <Module.Name>` first, then run a full `lake build` and `lake env lean tests/TestNormalCharts.lean` once module errors are zero.

## 3. Blueprint, Dependency Graph & Report Gate

Whenever modifying `blueprint/src/content.tex` or discharging/updating blueprint nodes:

1. **Acyclic & Resolved `\uses{...}` Labels**:
   - Check that every label inside `\uses{...}` exists in `blueprint/src/content.tex` and introduces no cycle in `blueprint/dep_graph.dot`.
   - Every `\lean{...}` entry must be a fully-qualified Lean declaration name (e.g. `GromovCompactness.Extensions.moebiusFrame_three_point_rigidity`).
2. **Rebuild Web Graph & `blueprint_dep_graph.pdf`**:
   - Run `./blueprint/export_dep_graph.sh` (activates conda env `leanblueprint`, runs `leanblueprint web`, updates `blueprint/dep_graph.dot` and `blueprint/lean_decls`, and renders `report/blueprint_dep_graph.pdf`).
   - Confirm zero `ERROR:` lines from `plasTeX`.
3. **Compile Print & Report PDFs Properly**:
   - Do **not** rely on `leanblueprint pdf` if it invokes `latex content.tex` directly; compile `print.tex` in two passes:
     `(cd blueprint/src && pdflatex -interaction=nonstopmode -output-directory=../print print.tex && pdflatex -interaction=nonstopmode -output-directory=../print print.tex)`
   - Recompile the paper/report after updating `report/blueprint_dep_graph.pdf`:
     `(cd report && pdflatex -interaction=nonstopmode gromov_lean_report.tex && pdflatex -interaction=nonstopmode gromov_lean_report.tex)`
4. **Verify Node Colors & All `blueprint/lean_decls` Axioms**:
   - Use `~/.gemini/config/skills/lean-blueprint-autoformalization/scripts/verify_blueprint.py` (from the global `lean-blueprint-autoformalization` skill) to verify `fillcolor` counts (`#1CAC78` proved, `#B0ECA3` definition, `0` `#9CEC8B` / `#A3D6FF` regressions) and `#print axioms` across every declaration in `blueprint/lean_decls`.
