# Dispatch: Milestone 4 Implementation Worker (worker_m4)

## Mission
Implement and verify Phase 5 Milestone 4:
1. Wire `extract_smooth_limit_off_singular_set` in `GromovCompactness/Compactness/Concentration.lean` to call `removal_of_singularities (I := I) (M := M)` so that the call-graph from `gromov_compactness_genus_zero` transitively includes `nonlinear_elliptic_bootstrap` (A05) and `puncture_sobolev_extension` (A11).
2. Integrate Component 5 `#audit_wiring` into `tests/PhaseAxiomCensus.lean` (from `explorer_m4_3/phase_axiom_census_wiring.patch` or `proposed_PhaseAxiomCensus.lean`).
3. In `GromovCompactness/Extensions/Automorphisms.lean`, close the 4 leaf declarations with **100% ZERO sorry**:
   - `#30`: `moebius_three_point_rigidity`
   - `#31`: `ghost_component_pure_automorphism_trivial`
   - `#33`: `pure_component_automorphisms_finite`
   - `#34`: `full_automorphisms_finite_iff_pure_finite`
   Use the verified zero-sorry blueprints from `explorer_m4_1/Scratch.lean` and `explorer_m4_2/TestAutomorphisms.lean`, leveraging the 9B `gemma-lean4:latest` model via `tools/ollama_lean4_client.py` where appropriate.
4. Verify with `lake build` that the entire repository compiles with 0 errors.
5. Run `lake env lean tests/PhaseAxiomCensus.lean` and verify that `#audit_wiring` succeeds (`STATUS: WIRING AUDIT PASSED`).
6. Run `MODULE_PREFIX=GromovCompactness.Extensions.Automorphisms ./tools/phase_axiom_census.sh` and verify that `Automorphisms.lean` is 100% `sorryAx`-free (`[propext, Classical.choice, Quot.sound]`).

## Exclusive Write Ownership
You exclusively own:
- `GromovCompactness/Extensions/Automorphisms.lean`
- `GromovCompactness/Compactness/Concentration.lean`
- `tests/PhaseAxiomCensus.lean`
- `.agents/teamwork/worker_m4/`

## Mandatory Inputs & References
- ORIGINAL_REQUEST: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md` (MUST read first)
- COMPLETION_PLAN: `/Users/pablosuarez/Desktop/SympTopAutoForm/COMPLETION_PLAN.md` (§3.4 E04 & §5.5)
- SCOPE: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/orchestrator_phase5/SCOPE.md`
- Explorer 1 Blueprint: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_1/Scratch.lean`
- Explorer 2 Blueprint: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_2/TestAutomorphisms.lean`
- Explorer 3 Blueprint: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_3/handoff.md`, `proposed_PhaseAxiomCensus.lean`, and `concentration_wiring.patch`
- Working Directory: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m4`

## MANDATORY INTEGRITY WARNING
> DO NOT CHEAT. All implementations must be genuine. DO NOT
> hardcode test results, create dummy/facade implementations, or
> circumvent the intended task. A teamwork_auditor will independently
> verify your work. Integrity violations WILL be detected and your
> work WILL be rejected.

## Deliverable
Write `handoff.md` in `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m4/handoff.md` with:
- Observation (compilation logs, axiom checks, `#audit_wiring` outputs)
- Logic Chain
- Caveats
- Conclusion
- Verification Method (commands to reproduce)


## 2026-11-05T08:01:31Z
You are worker_m4.
Your working directory is: /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m4
MANDATORY: Read /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/ORIGINAL_REQUEST.md first.
Then read your instructions in /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m4/DISPATCH.md.

MANDATORY INTEGRITY WARNING:
> DO NOT CHEAT. All implementations must be genuine. DO NOT
> hardcode test results, create dummy/facade implementations, or
> circumvent the intended task. A teamwork_auditor will independently
> verify your work. Integrity violations WILL be detected and your
> work WILL be rejected.

You have exclusive write ownership of:
- `GromovCompactness/Extensions/Automorphisms.lean`
- `GromovCompactness/Compactness/Concentration.lean`
- `tests/PhaseAxiomCensus.lean`
- `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m4/`

Tasks:
1. Wire `extract_smooth_limit_off_singular_set` in `GromovCompactness/Compactness/Concentration.lean` to invoke `removal_of_singularities (I := I) (M := M)` (see `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_3/concentration_wiring.patch` or `proposed_Concentration.lean`).
2. Integrate Component 5 `#audit_wiring` into `tests/PhaseAxiomCensus.lean` (see `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_3/phase_axiom_census_wiring.patch` or `proposed_PhaseAxiomCensus.lean`).
3. In `GromovCompactness/Extensions/Automorphisms.lean`, prove the 4 target leaf declarations with 100% ZERO `sorry`:
   - `#30`: `moebius_three_point_rigidity`
   - `#31`: `ghost_component_pure_automorphism_trivial`
   - `#33`: `pure_component_automorphisms_finite`
   - `#34`: `full_automorphisms_finite_iff_pure_finite`
   Follow the machine-checked proofs from `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_1/Scratch.lean` and `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_2/TestAutomorphisms.lean`.
4. Run `lake build` and verify that the full library builds cleanly with 0 errors.
5. Run `lake env lean tests/PhaseAxiomCensus.lean` and verify that `#audit_wiring` succeeds (`STATUS: WIRING AUDIT PASSED`).
6. Run `MODULE_PREFIX=GromovCompactness.Extensions.Automorphisms ./tools/phase_axiom_census.sh` and verify that `Automorphisms.lean` is 100% `sorryAx`-free (`[propext, Classical.choice, Quot.sound]`).
7. Write your 5-component handoff report to `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/worker_m4/handoff.md`.
Notify me with send_message when complete.


## 2026-11-05T08:03:16Z
**Context**: Milestone 4 Implementation (#30 & #31 Rigidity finding)
**Content**: `explorer_m4_1` has delivered its detailed handoff at `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_1/handoff.md`.
Crucial finding for #30 (`moebius_three_point_rigidity`):
- Per `COMPLETION_PLAN.md` line 120, #30 is a direct corollary of `exists_unique_moebius_three_points` (F02) in PGL(2, ℂ).
- In `Sphere.lean`, `MoebiusFrame` has `matrix : MoebiusMatrix` and `toHomeo : CP1 ≃ₜ CP1`.
- `explorer_m4_1` verified `moebius_three_point_rigidity_proj` specializing `moebius_three_points_unique` in 4 lines with 0 `sorry` and standard axioms `[propext, Classical.choice, Quot.sound]`.
- For #31, `ghost_component_pure_automorphism_trivial_of_rigidity` is verified in `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_1/Scratch.lean` with 0 `sorry`.
Please inspect `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_1/handoff.md` and `Scratch.lean` as you implement #30 and #31 in `Automorphisms.lean`.
**Action**: Integrate genuine zero-sorry proofs accordingly.


## 2026-11-05T08:04:07Z
**Context**: Milestone 4 Implementation (#33 & #34 Finiteness blueprints)
**Content**: `explorer_m4_2` has completed its report at `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_2/handoff.md` and certified all zero-sorry proofs in:
`/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_2/TestAutomorphisms.lean`
- `full_automorphisms_finite_iff_pure_finite_proof` (#34) is proven with 0 `sorry` and kernel axioms `[propext, Classical.choice, Quot.sound]`.
- `pure_component_automorphisms_finite_of_components` (#33) is proven with 0 `sorry`.
Please inspect `TestAutomorphisms.lean` to integrate these zero-sorry proofs into `GromovCompactness/Extensions/Automorphisms.lean`.
**Action**: Integrate genuine zero-sorry proofs into `Automorphisms.lean`.
