# Dispatch Task: Milestone 3 Implementation Worker (P0-4 through P0-11)

## Identity & Role
You are `worker_m3` (`teamwork_worker`).
Working directory: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m3`.

Path to ORIGINAL_REQUEST.md: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md`

## Mandatory Verbatim Integrity Warning
DO NOT CHEAT. All implementations must be genuine. DO NOT hardcode test results, create dummy/facade implementations, or circumvent the intended task. A teamwork_auditor will independently verify your work. Integrity violations WILL be detected and your work WILL be rejected.

## Owned Files & Scope
You exclusively own and modify:
1. `GromovCompactness/Analysis/EllipticBootstrap.lean`
2. `GromovCompactness/Analysis/SingularityRemoval.lean`
3. `GromovCompactness/Analysis/Monotonicity.lean`
4. `GromovCompactness/Analysis/Bochner.lean`
5. `GromovCompactness/Analysis/EpsilonRegularity.lean`
6. `GromovCompactness/Compactness/Stabilize.lean`
7. `GromovCompactness/Compactness/GenusZero.lean`
8. `GromovCompactness/Compactness/Assembly.lean`
9. `GromovCompactness/Bubbling/LocalTree.lean`
10. `GromovCompactness/Compactness/Measures.lean`
11. `GromovCompactness/Compactness/Concentration.lean`
12. `GromovCompactness/Extensions/ModuliSpace.lean`
13. `GromovCompactness/Main.lean` (and any related docstrings in `EnergyGap.lean`, `HoferRescaling.lean`, `Homology.lean`)
14. `tests/ChallengeMilestone3Phase5.lean` (Milestone 3 acceptance test suite)

## Implementation Inputs & Blueprints
You have three fully formulated, machine-checked handoff reports and patch sets from the Explorers:
- **Explorer 1 (P0-10 & P0-4/P0-5)**:
  * Read `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_1/handoff.md` and `analysis.md`.
  * Splicing instructions:
    - In `EllipticBootstrap.lean`: Keep `sobolevSeminorm` and `sobolevNorm` intact. Add $C^{k,\alpha}$ Hölder norms (`supNormOn`, `holderSeminorm`, `derivHolderSeminorm`, `ckHolderNorm`), the 8 zero-sorry structural lemmas, restate `interior_cauchy_riemann_estimate` (`A04a`), replace `morrey_sobolev_embedding` with `cauchy_pompeiu_holder_gain` (`A04b`), define `shrinkingRadius` hierarchy and lemmas, and prove the $C^{k,\alpha}$ Schauder bootstrap induction with ZERO `sorry`.
    - In `SingularityRemoval.lean`: Add `dense_punctured_sphere` (0 sorry), strengthen `puncture_sobolev_extension` (`A11`) to continuous + WeakJHolomorphicOn, prove `singularity_removal_bootstrap_bridge` (0 sorry) from `nonlinear_elliptic_bootstrap` (`A05`), and close `removal_of_singularities` (`A12`) with ZERO direct `sorry`!
    - In `Monotonicity.lean` & `Bochner.lean` & `EpsilonRegularity.lean`: Align differential inequality $\Delta e \ge -b e^2 - c e$ via default trailing parameters `(c : ℝ := 0) (hc : 0 ≤ c := by norm_num)`, and clarify Euclidean density on discs.

- **Explorer 2 (P0-11 Core Call-Graph Wiring Components 1–4)**:
  * Read `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_2/handoff.md` and `analysis.md`.
  * Splicing instructions:
    - In `Stabilize.lean`: Enrich `stabilize_prestable_tree_of_stable_root` and `stabilize_prestable_tree_of_nonconst_root` to all 5 fields of `CompactnessWitness`. Prove `stabilize_prestable_tree` via well-founded induction on `Fintype.card pdata.tree.V` with ZERO direct `sorry`.
    - In `GenusZero.lean`: Prove `gromov_compactness_core` with ZERO direct `sorry` by calling `assemble_prestable_limit` (`G01`) and `stabilize_prestable_tree` (`G02`). Prove `gromov_subsequence_alternative` with ZERO direct `sorry`.
    - In `Assembly.lean`: Formulate `prestable_limit_singleton_subseq` (0 sorry) and wire `assemble_prestable_limit` (`G01`) with ZERO direct `sorry` to `C02`, `C03`, `prestable_limit_singleton_subseq`, and `B07`.
    - In `LocalTree.lean`: Wire `resolve_single_defect_tree` (`B07`) with ZERO direct `sorry` using `energy_rank_induction`, `local_defect_tree_of_empty_children` ($q = \emptyset$), `B06`, and `B04`.
    - In `Measures.lean` & `Concentration.lean`: Prove `weak_energy_measure_compactness` (`C01`) with ZERO direct `sorry` from `weak_measure_compactness` via `weak_energy_measure_compactness_of_weak_measure_compactness`, and wire directly into `exists_concentration_data` (`C02`).

- **Explorer 3 (P0-7 Rescaling Frames, P0-8 ModuliSpace Defs, P0-9 Docstrings)**:
  * Read `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_3/handoff.md`, `analysis.md`, and inspect patches:
    * `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_3/proposed_Assembly.patch` (combine with Explorer 2's `Assembly.lean` wiring so both coexist seamlessly).
    * `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_3/proposed_ModuliSpace.patch` (complete elimination of sorry-defined defs/instances, genuine topology with 0-sorry axioms).
    * `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_3/proposed_Docstrings.patch` (conditional reduction docstrings).

## Verification Requirements
1. `lake build` must exit 0 with 0 errors.
2. Fast axiom census on modified modules must report 0 `sorryAx` on target closed declarations:
   - `MODULE_PREFIX=GromovCompactness.Analysis.EllipticBootstrap ./tools/phase_axiom_census.sh`
   - `MODULE_PREFIX=GromovCompactness.Analysis.SingularityRemoval ./tools/phase_axiom_census.sh`
   - `MODULE_PREFIX=GromovCompactness.Compactness.Stabilize ./tools/phase_axiom_census.sh`
   - `MODULE_PREFIX=GromovCompactness.Compactness.GenusZero ./tools/phase_axiom_census.sh`
   - `MODULE_PREFIX=GromovCompactness.Compactness.Assembly ./tools/phase_axiom_census.sh`
   - `MODULE_PREFIX=GromovCompactness.Bubbling.LocalTree ./tools/phase_axiom_census.sh`
   - `MODULE_PREFIX=GromovCompactness.Compactness.Measures ./tools/phase_axiom_census.sh`
   - `MODULE_PREFIX=GromovCompactness.Extensions.ModuliSpace ./tools/phase_axiom_census.sh`
3. Negative grep check: confirm zero `sorry`-defined `def` or `instance` declarations exist anywhere in `GromovCompactness/`.
4. Acceptance test suite `tests/ChallengeMilestone3Phase5.lean` must compile and pass cleanly with standard kernel axioms `[propext, Classical.choice, Quot.sound]`.

Deliver your completion report in `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m3/handoff.md` and message the orchestrator (`8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0`).
