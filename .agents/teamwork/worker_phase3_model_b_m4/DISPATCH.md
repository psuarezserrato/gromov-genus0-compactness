# Dispatch Task: Phase 3 Model B Milestone 4 Prover (B05–B07)

- **Identity**: `worker_phase3_model_b_m4` (role: teamwork_worker)
- **Working Directory**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase3_model_b_m4/`
- **Parent Conversation ID**: `02ef07b4-e669-479a-8a3d-86a44c7477a8` (Phase 3 Project Orchestrator)
- **Original User Request**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md` (MUST read first)
- **Blueprint Reference**: `/Users/pablosuarez/Desktop/SympTopAutoForm/GROMOV_COMPACTNESS_BLUEPRINT.md`
- **Plan Reference**: `/Users/pablosuarez/Desktop/SympTopAutoForm/AUTOFORMALIZATION_PLAN.md`
- **Predecessor Handoff**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase3_model_b_m3/handoff.md`

## Mandatory Integrity Warning
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

## Objective
Execute **Phase 3 Model B (Full Proof Completion / Zero-sorry)** for Milestone 4 across:
1. `GromovCompactness/Bubbling/GhostBranching.lean` (B05: Ghost Branching Condition)
2. `GromovCompactness/Bubbling/Rank.lean` (B06: Energy Rank Strict Decrease — already 0-sorry, verify & expand companion bounds if needed)
3. `GromovCompactness/Bubbling/LocalTree.lean` (B07: Well-Founded Defect Tree Induction)

## Specific Tasks
- In `GhostBranching.lean`: Close `ghost_component_branches` using the newly certified zero-sorry `OneLevelDecomposition.ghost_branching` from `OneLevel.lean`. Prove stable ghost degree properties ($d \ge 3$).
- In `Rank.lean`: Maintain and verify existing zero-sorry proofs of `energy_rank_strict_decrease` and associated arithmetic bounds.
- In `LocalTree.lean`: Implement zero-sorry induction reductions, well-founded termination guarantees on $\lfloor m / h \rfloor \in \mathbb{N}$, and properties of `LocalDefectTree` / `graft_trees`.
- Systematically prove foundation lemmas, reduction theorems, and algebraic/tree identities using standard Lean 4 kernel axioms (`[propext, Classical.choice, Quot.sound]`).
- Utilize local compute with Gemma models on Ollama (`http://localhost:11434`, `tools/ollama_lean4_client.py`) for tactic search and premise selection.
- Update `blueprint/src/content.tex`: add `\leanok` inside proof blocks strictly for machine-checked zero-sorry proofs.
- Verify `lake build GromovCompactness` compiles with exit code 0 and zero non-sorry warnings.
- Run `latexmk -pdf` on `blueprint/src/print.tex` to ensure blueprint PDF compiles cleanly.
- Write a comprehensive handoff report to:
  `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase3_model_b_m4/handoff.md`

## 2026-11-04T16:22:17Z
[Message] timestamp=2026-11-04T16:22:17Z sender=02ef07b4-e669-479a-8a3d-86a44c7477a8 priority=MESSAGE_PRIORITY_HIGH content=You are `worker_phase3_model_b_m4`, a specialized teamwork_worker responsible for Phase 3 Model B (Full Proof Completion / Zero-sorry) Milestone 4 in Lean 4.

Your working directory is:
/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase3_model_b_m4/

Parent Conversation ID: 02ef07b4-e669-479a-8a3d-86a44c7477a8 (Phase 3 Project Orchestrator)

MANDATORY FIRST STEP:
Read the following files before taking any action:
1. /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md (authoritative user request)
2. /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase3_model_b_m4/DISPATCH.md
3. /Users/pablosuarez/Desktop/SympTopAutoForm/GROMOV_COMPACTNESS_BLUEPRINT.md
4. /Users/pablosuarez/Desktop/SympTopAutoForm/AUTOFORMALIZATION_PLAN.md
5. Predecessor handoff report: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase3_model_b_m3/handoff.md
