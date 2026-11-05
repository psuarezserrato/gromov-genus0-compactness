import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EpsilonRegularity
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.SingularityRemoval

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness
open GromovCompactness.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
### 1. EnergyGap.lean Verification
-/

-- Check characterizations of non-constancy
#check nonconstant_iff_exists_ne
#check exists_ne_of_nonconstant
#check exists_outside_of_nonconstant

-- Check energy properties of constant maps
#check riemannianEnergyDensity_const
#check energyMeasureExtended_const
#check energyMeasure_const
#check totalEnergy_const
#check totalEnergy_eq_zero_of_forall_eq

-- Check total energy non-negativity and measure monotonicity
#check totalEnergy_nonneg
#check energyMeasure_le_totalEnergy

-- Check modular reduction theorems
#check sphere_energy_gap_of_monotonicity_and_exit
#check sphere_energy_gap_of_stokes_and_diameter

-- Check main contract
#check sphere_energy_gap

/-!
### 2. SingularityRemoval.lean Verification
-/

-- Check conformal bridge & Grönwall
#check annulus_ratio_rpow_eq_exp_neg
#check exp_decay_of_diff_ineq
#check exp_decay_bound_of_diff_ineq

-- Check decay factor bounds
#check exp_decay_factor_nonneg
#check exp_decay_factor_pos
#check exp_decay_factor_le_one
#check exp_decay_factor_lt_one
#check exp_decay_factor_mono
#check neck_factor_le_two
#check neck_factor_pos
#check one_sub_exp_neg_div_le
#check one_sub_exp_neg_div_nonneg

-- Check loop boundary oscillation
#check cauchy_schwarz_quadratic
#check loop_length_le_sqrt_energy
#check loop_diam_le_sqrt_energy

-- Check neck localization & degenerate collar emptiness
#check exists_neck_energy_threshold
#check localization_of_diam_bound
#check annulus_set_empty_of_le
#check annulus_at_empty_of_le

-- Check topological density & uniqueness
#check punctured_sphere_singleton_eq_compl
#check isOpen_punctured_sphere
#check jholomorphicOn_congr
#check continuous_of_jholomorphicOn
#check ball_subset_closure_punctured_ball
#check eqOn_ball_of_eqOn_punctured_ball
#check extension_value_at_zero_unique
#check removal_of_singularities_unique
#check removal_of_singularities_unique'

-- Check constant curve specializations
#check removal_of_singularities_const
#check removal_of_singularities_const_unique

-- Check reduction theorem
#check removal_of_singularities_reduction

-- Check main contracts
#check cylinder_localization
#check cylinder_exponential_decay
#check puncture_sobolev_extension
#check removal_of_singularities

/-!
### 3. Axiom Verification
-/
#print axioms nonconstant_iff_exists_ne
#print axioms exists_ne_of_nonconstant
#print axioms exists_outside_of_nonconstant
#print axioms riemannianEnergyDensity_const
#print axioms energyMeasureExtended_const
#print axioms energyMeasure_const
#print axioms totalEnergy_const
#print axioms totalEnergy_eq_zero_of_forall_eq
#print axioms totalEnergy_nonneg
#print axioms energyMeasure_le_totalEnergy
#print axioms sphere_energy_gap_of_monotonicity_and_exit
#print axioms sphere_energy_gap_of_stokes_and_diameter

#print axioms annulus_ratio_rpow_eq_exp_neg
#print axioms exp_decay_of_diff_ineq
#print axioms exp_decay_bound_of_diff_ineq
#print axioms exp_decay_factor_nonneg
#print axioms exp_decay_factor_pos
#print axioms exp_decay_factor_le_one
#print axioms exp_decay_factor_lt_one
#print axioms exp_decay_factor_mono
#print axioms neck_factor_le_two
#print axioms neck_factor_pos
#print axioms one_sub_exp_neg_div_le
#print axioms one_sub_exp_neg_div_nonneg
#print axioms cauchy_schwarz_quadratic
#print axioms loop_length_le_sqrt_energy
#print axioms loop_diam_le_sqrt_energy
#print axioms exists_neck_energy_threshold
#print axioms localization_of_diam_bound
#print axioms annulus_set_empty_of_le
#print axioms annulus_at_empty_of_le
#print axioms punctured_sphere_singleton_eq_compl
#print axioms isOpen_punctured_sphere
#print axioms jholomorphicOn_congr
#print axioms continuous_of_jholomorphicOn
#print axioms ball_subset_closure_punctured_ball
#print axioms eqOn_ball_of_eqOn_punctured_ball
#print axioms extension_value_at_zero_unique
#print axioms removal_of_singularities_unique
#print axioms removal_of_singularities_unique'
#print axioms removal_of_singularities_const
#print axioms removal_of_singularities_const_unique
#print axioms removal_of_singularities_reduction
