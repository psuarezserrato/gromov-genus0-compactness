# Dispatch Task: Milestone 2 Remediation Implementation (P0-1, P0-2, P0-3)

## Identity & Role
You are `worker_m2_3` (`teamwork_worker`).
Your working directory is `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m2_3`.
You own exclusively:
- `GromovCompactness/Analysis/Energy.lean`
- `tests/TestEnergyP01.lean`
- `tests/ChallengeMilestone2Phase5.lean`

## MANDATORY INTEGRITY WARNING
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

## Context & Inputs
1. `ORIGINAL_REQUEST.md`: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md`
2. Forensic Audit failure report from Iteration 1: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/auditor_m2/handoff.md`
3. Explorer blueprints from Iteration 2:
   - `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m2_iter2_3/handoff.md` (Facade cleanup, `CP1_ClosedTameTarget`, concrete nonconstant test, trace scaling integration)
   - `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m2_iter2_2/handoff.md` and `BlueprintTest.lean` (10 machine-checked theorems: trace scaling, measure homothety, integral scaling cancellation)
   - `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m2_iter2_1/handoff.md` and `scratch_test.lean` (Affine scaling cancellation and metric trace scaling)

## Exact Tasks to Implement

### 1. In `GromovCompactness/Analysis/Energy.lean`:
- **Wire `metric_c_linear_trace_scaling` into `energy_density_eq_omega`**:
  Move `metric_c_linear_trace_scaling` up to directly precede `energy_density_eq_omega`. Use `linear_combination (1 / 2 : ℝ) * h_trace` to prove `energy_density_eq_omega`. This eliminates the dead-code defect.
- **Insert canonical target `CP1_ClosedTameTarget` and concrete nonconstant map theorems (P0-1)**:
  Copy the exact machine-checked Lean 4 declarations from `explorer_m2_iter2_3/handoff.md` §3.1 Step 2:
  * `stdOmega` and lemmas (`stdOmega_skew`, `stdOmega_closed`, `stdOmega_tame`, `stdOmega_nondegenerate`)
  * `CP1_ClosedTameTarget : ClosedTameTarget I_CP1 CP1`
  * `concrete_nonconstant_map_nonconstant` (north_pole ≠ south_pole)
  * `concrete_nonconstant_map_smooth` (`contMDiff_id`)
  * `concrete_nonconstant_map_jhol`
  * `riemannianEnergyDensity_id` (identically 1)
  * `concrete_nonconstant_map_finite_energy` (`energyMeasureExtended I_CP1 id Set.univ < ⊤`)
  * `concrete_nonconstant_map_positive_energy` (`0 < totalEnergy I_CP1 id`)
- **Add Authentic Trace Scaling & Change-of-Variables Theorems (P0-2)**:
  Include the machine-checked theorems from `explorer_m2_iter2_2/handoff.md`:
  * `c_linear_dirichlet_trace_scaling`
  * `dilation_trace_scaling`
  * `volume_map_translation`
  * `volume_map_homothety`
  * `det_mulLeft_complex`
  * `volume_map_rotation`
  * `volume_map_affine`
  * `lintegral_comp_homothety`
  * `dilation_factor_cancellation`
  * `lintegral_scaled_density_eq`
  * `lintegral_affine_scaling_cancellation`
- **COMPLETE DELETION of `ConformalEquiv` & `h_equiv` facade / circularity**:
  * Delete `structure ConformalEquiv`, `infix:25 " ≃ᴹ "`, `instance : CoeFun (CP1 ≃ᴹ CP1)`, `ConformalEquiv.id`, and `ConformalEquiv.comp`.
  * Delete duplicate lemma `energyMeasure_conformal_invariant`.
  * Add genuine unconditional theorems for identity: `energy_conformal_invariant_id` and `totalEnergy_conformal_invariant_id`.
  * Add honest conditional reduction theorems for arbitrary frames: `energy_conformal_invariant` and `totalEnergy_conformal_invariant` taking `(ϕ : MoebiusFrame)` and `(h_pullback : energyMeasureExtended I (u ∘ ϕ.toHomeo) = Measure.map ϕ.toHomeo.symm (energyMeasureExtended I u))` with explicit docstrings explaining it is a conditional reduction from pullback equivariance.
- **Update `#print axioms` block**:
  Include all new theorems at the end of `Energy.lean`.

### 2. Create `tests/TestEnergyP01.lean`:
Create this standalone acceptance test file exactly as specified in `explorer_m2_iter2_3/handoff.md` §3.2, verifying:
- Nonconstancy of test curve `u = id`
- Smoothness of `u = id`
- J-holomorphicity of `u = id`
- Finiteness of extended energy measure `< ⊤`
- Strict positivity of total energy `0 < totalEnergy` (using `.toReal` only after finiteness)
- `test_P01_unified` combining all criteria with `#print axioms test_P01_unified`.

### 3. Update `tests/ChallengeMilestone2Phase5.lean`:
- Remove all obsolete tests referencing `ConformalEquiv`.
- Insert Test 4.5 (`test_concrete_nonconstant_map_finite_positive_energy`).
- Insert Tests 5.1, 5.2, 5.3 (`test_energy_conformal_invariant_id`, `test_totalEnergy_conformal_invariant_id`, `test_energy_conformal_invariant_conditional`).
- Update Probe 6 axiom checks.

## Verification Requirements
You must execute and report the output of:
1. `lake build` (must exit 0 with 0 errors).
2. Negative grep check:
   `git grep "ConformalEquiv"` -> must return 0 matches.
   `git grep "h_equiv"` -> must return 0 matches.
3. Fast axiom census:
   `./tools/phase_axiom_census.sh GromovCompactness.Analysis.Energy` -> must report 0 `sorryAx`, standard axioms only.
4. Run test files:
   `lake env lean tests/TestEnergyP01.lean`
   `lake env lean tests/ChallengeMilestone2Phase5.lean`
   Both must succeed with 0 errors and standard kernel axioms.

Deliver your results in `.agents/teamwork/worker_m2_3/handoff.md` and message the orchestrator (`8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0`).


## 2026-11-05T05:28:00Z
Received dispatch from parent orchestrator 8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0.
Objective: Execute the machine-checked blueprints from explorer_m2_iter2_3, explorer_m2_iter2_2, and explorer_m2_iter2_1 to remediate Energy.lean, TestEnergyP01.lean, and ChallengeMilestone2Phase5.lean.
