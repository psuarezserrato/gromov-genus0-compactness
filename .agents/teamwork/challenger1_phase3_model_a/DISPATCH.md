# Dispatch Task: Challenger 1 Phase 3 Model A Adversarial Verification

- **Identity**: `challenger1_phase3_model_a` (role: teamwork_challenger)
- **Working Directory**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/challenger1_phase3_model_a/`
- **Parent Conversation ID**: `02ef07b4-e669-479a-8a3d-86a44c7477a8` (Phase 3 Project Orchestrator)
- **Original User Request**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md` (MUST read first)
- **Blueprint Reference**: `/Users/pablosuarez/Desktop/SympTopAutoForm/GROMOV_COMPACTNESS_BLUEPRINT.md`
- **Plan Reference**: `/Users/pablosuarez/Desktop/SympTopAutoForm/AUTOFORMALIZATION_PLAN.md`
- **Worker Report**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_phase3_model_a/handoff.md`

## Objective
Adversarially challenge and stress-test the Phase 3 Model A code and theorems:
1. Write a standalone Lean 4 test script in `tests/ChallengePhase3ModelA.lean` testing:
   - Evaluation of `energy_rank_strict_decrease` across edge cases ($m = h$, $m = 2h$, fractional ranks, huge ranks).
   - Component bounds evaluation: $G \le P - 2$, $|V| \le 2P - 2$, and $(|V| : \mathbb{Z}) \le \max(1, 2\lfloor B/h \rfloor - 2)$ on $|V| = 1$ (single sphere without bubbling) and $|V| > 1$.
   - Instantiate and typecheck structures `WeakMeasureConvergence`, `ConcentrationData`, `OneLevelDecomposition`, `PrestableLimitData`, `CompactnessWitness`.
2. Compile and execute `lake env lean tests/ChallengePhase3ModelA.lean`.
3. Deliver a clear gate verdict: `APPROVE` or `REQUEST_CHANGES` in `handoff.md`.
