# Dispatch Task: Phase 3 Model B Milestone 5 Prover (G01–G05)

- **Identity**: `worker_phase3_model_b_m5` (role: teamwork_worker)
- **Working Directory**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase3_model_b_m5/`
- **Parent Conversation ID**: `02ef07b4-e669-479a-8a3d-86a44c7477a8` (Phase 3 Project Orchestrator)
- **Original User Request**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md` (MUST read first)
- **Blueprint Reference**: `/Users/pablosuarez/Desktop/SympTopAutoForm/GROMOV_COMPACTNESS_BLUEPRINT.md`
- **Plan Reference**: `/Users/pablosuarez/Desktop/SympTopAutoForm/AUTOFORMALIZATION_PLAN.md`
- **Predecessor Handoffs**:
  - `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase3_model_b_m3/handoff.md`
  - `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase3_model_b_m4/handoff.md`
  - `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/spec_miner_phase3_compactness/handoff.md`

## Mandatory Integrity Warning
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

## Objective
Execute **Phase 3 Model B (Full Proof Completion / Zero-sorry)** for Milestone 5 across:
1. `GromovCompactness/Compactness/Assembly.lean` (G01: Global Prestable Limit Data & Frame Assembly)
2. `GromovCompactness/Compactness/Stabilize.lean` (G02: Root Stabilization, Degree 1/2 Reduction & Convergence Upgrade)
3. `GromovCompactness/Compactness/GenusZero.lean` (G03: Core Genus 0 Compactness Theorem & CompactnessWitness)
4. `GromovCompactness/Topology/ComponentCount.lean` (G04: Principal & Ghost Component Bounds $P \le \lfloor B/h \rfloor$, $G \le P-2$, $|V| \le 2P-2$)
5. `GromovCompactness/Main.lean` (G05: Master Genus 0 Gromov Compactness Integration & Axiom Audit)

## Specific Tasks
- In `Assembly.lean`: Implement zero-sorry frame composition along tree paths, transition collapse reduction, and prestable tree limit construction.
- In `Stabilize.lean`: Implement zero-sorry root degree reduction (deg 1 pruning, deg 2 bridging), energy preservation under stabilization, and the smooth convergence upgrade across deleted nodes.
- In `GenusZero.lean`: Formalize `CompactnessWitness` properties, the non-empty witness reduction, and `gromov_subsequence_alternative`.
- In `ComponentCount.lean`: Implement complete machine-checked zero-sorry proofs for:
  - `principal_components_energy_bound`: $P \cdot h \le B \implies P \le \lfloor B / h \rfloor$.
  - `component_count_bounds`: $G \le P - 2$ and $|V| \le 2P - 2$ for $|V| > 1$, and $(|V| : \mathbb{Z}) \le \max(1, 2\lfloor B/h \rfloor - 2)$ universally.
  - `component_count_bounds_marked`: $k$-marked curve bounds $G \le P + k - 2$.
- In `Main.lean`: Integrate `gromov_compactness_genus_zero`, connecting `gromov_compactness_core` with `component_count_bounds`.
- Ensure all proved declarations depend strictly on standard Lean 4 kernel axioms (`[propext, Classical.choice, Quot.sound]`). Verify with `#print axioms`.
- Maximize local compute with Gemma models on Ollama (`http://localhost:11434`, `tools/ollama_lean4_client.py`) for tactic search and premise completion.
- Update `blueprint/src/content.tex`: add `\leanok` inside proof blocks (`\begin{proof}\leanok ...`) strictly for theorems and lemmas that have complete machine-checked zero-sorry proofs.
- Verify `lake build GromovCompactness` compiles with exit code 0 and zero non-sorry warnings.
- Run `latexmk -pdf` on `blueprint/src/print.tex` to ensure blueprint PDF compiles cleanly.
- Write a comprehensive handoff report to:
  `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase3_model_b_m5/handoff.md`
