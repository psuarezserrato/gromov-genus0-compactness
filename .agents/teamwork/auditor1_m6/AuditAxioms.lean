import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Analysis.Bochner
import GromovCompactness.Analysis.EpsilonRegularity
import GromovCompactness.Analysis.EllipticBootstrap
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.SingularityRemoval
import GromovCompactness.Analysis.HoferRescaling

namespace GromovCompactness.Analysis

-- Monotonicity.lean
#print axioms laplacian2D
#print axioms mvi_branch_zero
#print axioms scalar_mean_value_inequality
#print axioms rank_e3
#print axioms isConnected_sphere_3
#print axioms connectedSpace_CP1
#print axioms continuous_dist_u
#print axioms dist_le_of_mem_closure_preimage_ball
#print axioms dist_eq_r_of_mem_frontier_preimage_ball
#print axioms frontier_preimage_ball_nonempty
#print axioms exists_boundary_hit
#print axioms continuous_of_jhol
#print axioms target_monotonicity

-- Bochner.lean
#print axioms iteratedFDeriv_two_zero_of_not_diff
#print axioms laplacian2D_zero_of_not_diff
#print axioms laplacian2D_of_iterated_one_zero
#print axioms laplacian2D_const
#print axioms energy_density_const_map
#print axioms fderiv_eq_zero_of_global_min
#print axioms bochner_differential_inequality

-- EpsilonRegularity.lean
#print axioms integral_translate_ball
#print axioms ball_translate_to_closedBall
#print axioms epsilon_regularity

-- EllipticBootstrap.lean (key reduction theorems & contracts)
#print axioms cauchyRiemann_const
#print axioms cauchyRiemann_zero
#print axioms cauchyRiemann_id
#print axioms sobolevSeminorm_nonneg
#print axioms sobolevNorm_nonneg
#print axioms sobolevNorm_mono_order
#print axioms sobolevNorm_zero_le_order
#print axioms constant_map_cauchy_riemann_estimate
#print axioms constant_map_morrey_embedding
#print axioms interior_cauchy_riemann_estimate
#print axioms morrey_sobolev_embedding
#print axioms elliptic_bootstrap_wkp_of_cauchy_riemann
#print axioms elliptic_bootstrap_wkp_of_dbar_zero
#print axioms sobolev_weak_jhol_c_infty
#print axioms sobolev_weak_jhol_c_top
#print axioms weakJHolomorphicOn_const
#print axioms nonlinear_elliptic_bootstrap_const
#print axioms local_smooth_compactness_of_const
#print axioms nonlinear_elliptic_bootstrap
#print axioms local_smooth_compactness

-- EnergyGap.lean
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
#print axioms sphere_energy_gap

-- SingularityRemoval.lean
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
#print axioms neck_localization_threshold_pos
#print axioms neck_diameter_bound
#print axioms degenerate_annulus_empty
#print axioms isOpen_punctured_sphere
#print axioms punctured_sphere_dense
#print axioms jholomorphicOn_of_eqOn_open
#print axioms continuous_extension_unique
#print axioms constant_curve_extends
#print axioms constant_curve_unique_extension
#print axioms removal_of_singularities_reduction
#print axioms cylinder_localization
#print axioms cylinder_exponential_decay
#print axioms puncture_sobolev_extension
#print axioms removal_of_singularities

-- HoferRescaling.lean
#print axioms exists_target_thresholds_of_modules
#print axioms exists_target_thresholds
#print axioms exists_calibrated_rescaling_of_ivt
#print axioms exists_calibrated_rescaling

end GromovCompactness.Analysis
