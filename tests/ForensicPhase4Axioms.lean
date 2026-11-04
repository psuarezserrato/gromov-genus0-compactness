import GromovCompactness
import GromovCompactness.Extensions.Homology
import GromovCompactness.Extensions.MarkedCurves
import GromovCompactness.Extensions.ModuliSpace
import GromovCompactness.Extensions.VaryingJ
import GromovCompactness.Extensions.Automorphisms

open GromovCompactness.Extensions

-- E03: Homology.lean
#print axioms integral_homology_preserved
#print axioms tree_homology_eq_fixed_class
#print axioms fixed_homology_pairing_eq_total_energy
#print axioms tree_energy_eq_symplectic_area
#print axioms compactnessWitness_symplectic_area_conv
#print axioms symplectic_area_identity_of_const_area

-- E02: MarkedCurves.lean
#print axioms deligne_mumford_0_4_crossRatio
#print axioms marked_ghost_components_bound
#print axioms marked_component_count_bounds
#print axioms crossRatioC_translation
#print axioms crossRatioC_scaling
#print axioms crossRatioC_standard
#print axioms ghost_bubble_stability

-- E05: ModuliSpace.lean
#print axioms stableMapEquiv_refl
#print axioms stableMapEquiv_symm
#print axioms stableMapEquiv_trans

-- E01: VaryingJ.lean
#print axioms exists_uniform_target_thresholds
#print axioms symmetrizedMetric_symm
#print axioms symmetrizedMetric_pos_def
#print axioms symmetrizedMetric_J_invariant
#print axioms jholomorphic_eq_with_target_J
#print axioms riemannianEnergyDensityWithJ_nonneg
#print axioms energy_density_with_J_eq_omega

-- E04: Automorphisms.lean
#print axioms instFintypeTreeAutomorphism
#print axioms StableMapAutomorphism.id
#print axioms pure_automorphisms_finite_of_full_finite
