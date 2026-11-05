## 2026-11-04T09:46:43Z
You are the Implementation Worker (`worker_m4_singularities`).
Your working directory is: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m4_singularities/`.
Your parent is Phase 2 Project Orchestrator Gen 4 (ID: `782f5169-44c1-411e-be82-5441546f0b2e`).

MANDATORY FIRST STEP:
Read the Authoritative User Request Document:
`/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md`

ADDITIONAL MANDATORY CONTEXT FILES:
- Synthesis Report: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/orchestrator_phase2_modelB_gen4/synthesis_m4.md`
- Explorer 1 Handoff & Test Lemmas:
  `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_1/handoff.md`
  `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_1/TestLemmas.lean`
- Explorer 2 Handoff & Test Lemmas:
  `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_2/handoff.md`
  `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_2/TestLemmas.lean`
- Explorer 3 Handoff & Proposed File:
  `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_3/handoff.md`
  `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_3/proposed_SingularityRemoval.lean`
  `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_3/singularity_removal.patch`

EXCLUSIVE WRITE OWNERSHIP:
- `/Users/pablosuarez/Desktop/SympTopAutoForm/GromovCompactness/Analysis/EnergyGap.lean`
- `/Users/pablosuarez/Desktop/SympTopAutoForm/GromovCompactness/Analysis/SingularityRemoval.lean`
You have EXCLUSIVE write ownership of these two files. DO NOT modify any other files in `GromovCompactness/`.

MANDATORY INTEGRITY WARNING:
> DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

OBJECTIVE:
Implement the zero-`sorry` auxiliary foundation lemmas, energy algebra, conformal cylinder decay estimates, Grönwall differential inequality bounds, Cauchy-Schwarz boundary oscillation bounds, degenerate collar emptiness, topological density lemmas, and reduction theorems in `EnergyGap.lean` and `SingularityRemoval.lean` exactly as specified in `synthesis_m4.md` and the Explorer handoffs.

1. In `GromovCompactness/Analysis/EnergyGap.lean`:
   - Add `[MetricSpace M]` to `sphere_energy_gap`.
   - Add non-constancy characterization lemmas: `nonconstant_iff_exists_ne`, `exists_outside_of_nonconstant`.
   - Add energy algebra of constant maps: `riemannianEnergyDensity_const`, `energyMeasureExtended_const`, `energyMeasure_const`, `totalEnergy_const`, `totalEnergy_eq_zero_of_forall_eq`.
   - Add energy non-negativity and subset monotonicity: `totalEnergy_nonneg`, `energyMeasure_le_totalEnergy`.
   - Add reduction theorems: `sphere_energy_gap_of_monotonicity_and_exit` and `sphere_energy_gap_of_stokes_and_diameter`.
   - Update `sphere_energy_gap` to use the zero-`sorry` reduction.

2. In `GromovCompactness/Analysis/SingularityRemoval.lean`:
   - Conformal bridge identity: `annulus_ratio_rpow_eq_exp_neg`.
   - Grönwall differential inequality: `exp_decay_of_diff_ineq`, `exp_decay_bound_of_diff_ineq`.
   - Decay factor bounds: `exp_decay_factor_nonneg`, `exp_decay_factor_pos`, `exp_decay_factor_le_one`, `exp_decay_factor_lt_one`, `exp_decay_factor_mono`, `neck_factor_le_two`, `neck_factor_pos`, `one_sub_exp_neg_div_le`, `one_sub_exp_neg_div_nonneg`.
   - Loop boundary oscillation bounds: `cauchy_schwarz_quadratic`, `loop_length_le_sqrt_energy`, `loop_diam_le_sqrt_energy`.
   - Neck energy threshold and localization: `exists_neck_energy_threshold`, `localization_of_diam_bound`, `annulus_set_empty_of_le`, `annulus_at_empty_of_le`.
   - Topological density and uniqueness: `punctured_sphere_singleton_eq_compl`, `isOpen_punctured_sphere`, `jholomorphicOn_congr`, `continuous_of_jholomorphicOn`, `ball_subset_closure_punctured_ball`, `eqOn_ball_of_eqOn_punctured_ball`, `extension_value_at_zero_unique`, `removal_of_singularities_unique`.
   - Constant curve specializations: `removal_of_singularities_const`, `removal_of_singularities_const_unique`.
   - Reduction theorem: `removal_of_singularities_reduction`.
   - Update `cylinder_localization` (Contract A09), `cylinder_exponential_decay` (Contract A10), `puncture_sobolev_extension` (Contract A11), and `removal_of_singularities` (Contract A12).

3. Verification:
   - Build target: `lake build GromovCompactness` (must succeed with exit code 0).
   - Test suites: run all test suites in `tests/`.
   - Axiom check: run `#print axioms` on the new theorems to confirm that only standard Lean 4 kernel axioms (`[propext, Classical.choice, Quot.sound]`) are used.

OUTPUT:
Write your full completion and verification report to:
`/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m4_singularities/handoff.md`

Use `send_message` with recipient `782f5169-44c1-411e-be82-5441546f0b2e` to report your completion and summarized results.
