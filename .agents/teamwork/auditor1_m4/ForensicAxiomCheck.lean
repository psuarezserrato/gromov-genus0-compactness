import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.SingularityRemoval

open GromovCompactness.Analysis

-- EnergyGap.lean declarations:
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

-- SingularityRemoval.lean declarations:
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
