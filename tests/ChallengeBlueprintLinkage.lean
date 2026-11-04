/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: challenger2_m6
-/
import GromovCompactness

/-!
# Empirical Verification of Blueprint Declaration Linkage (Phase 2 Milestone 6)

This file directly verifies that the 14 `\lean{...}` paths in `blueprint/src/content.tex`
for Phase 2 correspond to genuine, elaborated Lean declarations in the compiled library.
-/

-- A01: scalar_mean_value_inequality
#check GromovCompactness.Analysis.scalar_mean_value_inequality

-- A02: bochner_differential_inequality
#check GromovCompactness.Analysis.bochner_differential_inequality

-- A03: epsilon_regularity
#check GromovCompactness.Analysis.epsilon_regularity

-- A04: interior_cauchy_riemann_estimate
#check GromovCompactness.Analysis.interior_cauchy_riemann_estimate

-- A05: nonlinear_elliptic_bootstrap
#check GromovCompactness.Analysis.nonlinear_elliptic_bootstrap

-- A06: local_smooth_compactness
#check GromovCompactness.Analysis.local_smooth_compactness

-- A07: sphere_energy_gap
#check GromovCompactness.Analysis.sphere_energy_gap

-- A08: target_monotonicity
#check GromovCompactness.Analysis.target_monotonicity

-- A09: cylinder_localization
#check GromovCompactness.Analysis.cylinder_localization

-- A10: cylinder_exponential_decay
#check GromovCompactness.Analysis.cylinder_exponential_decay

-- A11: puncture_sobolev_extension
#check GromovCompactness.Analysis.puncture_sobolev_extension

-- A12: removal_of_singularities
#check GromovCompactness.Analysis.removal_of_singularities

-- B01: TargetThresholds
#check GromovCompactness.Bubbling.TargetThresholds

-- B02: CalibratedRescaling
#check GromovCompactness.Bubbling.CalibratedRescaling

def checkAll14Linkages : Unit := ()

-- Phase 1 checks
#check GromovCompactness.Audit.LibraryAuditRecord
#check GromovCompactness.ClosedTameTarget
#check GromovCompactness.ClosedTameTarget.metric
#check GromovCompactness.metric_pos_def
#check GromovCompactness.JHolomorphicOn
#check GromovCompactness.jholomorphic_coordinate_invariance
#check GromovCompactness.MoebiusFrame
#check GromovCompactness.exists_unique_moebius_three_points
#check GromovCompactness.energyMeasure
#check GromovCompactness.energy_eq_pullback_omega
#check GromovCompactness.energy_conformal_invariant
#check GromovCompactness.energy_point_null
#check GromovCompactness.SmoothLocalConvergesOn
#check GromovCompactness.smooth_local_jhol_closure
#check GromovCompactness.Bookkeeping.countable_diagonal_extraction
#check GromovCompactness.StableSphereTreeLimit
#check GromovCompactness.ghost_components_bound

def checkAllPhase1Linkages : Unit := ()
