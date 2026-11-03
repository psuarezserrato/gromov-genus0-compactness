/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Analysis.Energy
import GromovCompactness.Topology.SmoothLocal

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open GromovCompactness Set Metric

namespace GromovCompactness.TestChallenge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Adversarial Challenge Test Harness for Milestone 4
Testing `Analysis/Energy.lean` (F03) and `Topology/SmoothLocal.lean` (F04).

We empirically stress-test:
1. `energy_point_null` on concrete points (north pole, origin, arbitrary points)
2. `energy_circle_null` on circles (unit circle, arbitrary center/radius, degenerate)
3. `energy_density_eq_omega` on J-holomorphic curves and pointwise CR maps
4. `smooth_local_limit_unique` on distinct constant limits, deriving `False`
-/

-- ============================================================================
-- 1. Test `energy_point_null`
-- ============================================================================

-- Test 1A: Concrete point north_pole has energy 0
theorem test_energy_point_null_north_pole (u : CP1 → M) :
    energyMeasure I u {north_pole} = 0 :=
  energy_point_null I u north_pole

-- Test 1B: Concrete point at origin (stereo_chart.symm 0) has energy 0
theorem test_energy_point_null_origin (u : CP1 → M) :
    energyMeasure I u {stereo_chart.symm 0} = 0 :=
  energy_point_null I u (stereo_chart.symm 0)

-- Test 1C: Concrete point at 1 (stereo_chart.symm 1) has energy 0
theorem test_energy_point_null_one (u : CP1 → M) :
    energyMeasure I u {stereo_chart.symm 1} = 0 :=
  energy_point_null I u (stereo_chart.symm 1)

-- Test 1D: Concrete point at Complex.I (stereo_chart.symm Complex.I) has energy 0
theorem test_energy_point_null_I (u : CP1 → M) :
    energyMeasure I u {stereo_chart.symm Complex.I} = 0 :=
  energy_point_null I u (stereo_chart.symm Complex.I)

-- Test 1E: Arbitrary point p has energy 0
theorem test_energy_point_null_arbitrary (u : CP1 → M) (p : CP1) :
    energyMeasure I u {p} = 0 :=
  energy_point_null I u p

-- Test 1F: Sharpness of nonnegativity on singletons (0 ≤ E({p}) and E({p}) = 0)
theorem test_energy_point_sharp_nonneg (u : CP1 → M) (p : CP1) :
    0 ≤ energyMeasure I u {p} ∧ energyMeasure I u {p} = 0 :=
  ⟨energy_nonneg I u {p}, energy_point_null I u p⟩

-- ============================================================================
-- 2. Test `energy_circle_null`
-- ============================================================================

-- Test 2A: Unit circle centered at 0 has energy 0
theorem test_energy_circle_null_unit (u : CP1 → M) :
    energyMeasure I u (circle_at 0 1) = 0 :=
  energy_circle_null I u 0 1

-- Test 2B: Arbitrary circle with center a and radius r has energy 0
theorem test_energy_circle_null_arbitrary (u : CP1 → M) (a : ℂ) (r : ℝ) :
    energyMeasure I u (circle_at a r) = 0 :=
  energy_circle_null I u a r

-- Test 2C: Degenerate circle with radius 0 has energy 0
theorem test_energy_circle_null_radius_zero (u : CP1 → M) (a : ℂ) :
    energyMeasure I u (circle_at a 0) = 0 :=
  energy_circle_null I u a 0

-- Test 2D: Circle with negative radius has energy 0
theorem test_energy_circle_null_radius_neg (u : CP1 → M) (a : ℂ) :
    energyMeasure I u (circle_at a (-5)) = 0 :=
  energy_circle_null I u a (-5)

-- ============================================================================
-- 3. Test `energy_density_eq_omega` on J-holomorphic curves
-- ============================================================================

-- Test 3A: Pointwise equality for any map satisfying the Cauchy-Riemann equation at z
theorem test_energy_density_eq_omega_pointwise (u : CP1 → M) (z : CP1)
    (h_cr : ∀ v, mfderiv I_CP1 I u z (J_CP1 v) = ClosedTameTarget.J (u z) (mfderiv I_CP1 I u z v)) :
    riemannianEnergyDensity I u z = symplecticAreaDensity I u z :=
  energy_density_eq_omega I u z h_cr

-- Test 3B: Global equality for any J-holomorphic curve u : CP1 → M
theorem test_energy_density_eq_omega_jhol (u : CP1 → M)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) (z : CP1) :
    riemannianEnergyDensity I u z = symplecticAreaDensity I u z := by
  apply energy_density_eq_omega I u z
  intro v
  exact h_jhol.2 z (Set.mem_univ z) v

-- Test 3C: Measure equality on any subset A for a J-holomorphic curve
theorem test_energy_eq_pullback_omega_jhol (u : CP1 → M)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) (A : Set CP1) :
    energyMeasure I u A = pullbackOmegaMeasure I u A :=
  energy_eq_pullback_omega I u h_jhol A

-- Test 3D: Measure equality specialized to a disk
theorem test_energy_eq_pullback_omega_disk (u : CP1 → M)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) (a : ℂ) (r : ℝ) :
    energyMeasure I u (disk_at a r) = pullbackOmegaMeasure I u (disk_at a r) :=
  energy_eq_pullback_omega I u h_jhol (disk_at a r)

-- ============================================================================
-- 4. Test `smooth_local_limit_unique` on distinct constant limits
-- ============================================================================

-- Test 4A: If u_seq converges to constant c1 and constant c2 on nonempty open Ω in T2Space M,
-- then c1 = c2.
theorem test_smooth_local_limit_unique_constants [T2Space M]
    (u_seq : ℕ → (CP1 → M)) (c₁ c₂ : M) (Ω : Set CP1)
    (h_open : IsOpen Ω) (h_nonempty : Ω.Nonempty)
    (h1 : SmoothLocalConvergesOn I u_seq (fun _ => c₁) Ω)
    (h2 : SmoothLocalConvergesOn I u_seq (fun _ => c₂) Ω) :
    c₁ = c₂ := by
  have h_eq : EqOn (fun _ => c₁) (fun _ => c₂) Ω :=
    smooth_local_limit_unique I u_seq (fun _ => c₁) (fun _ => c₂) Ω h_open h_nonempty h1 h2
  rcases h_nonempty with ⟨z, hz⟩
  exact h_eq hz

-- Test 4B (Adversarial stress test): Distinct constants cannot both be limits on nonempty open Ω
theorem test_distinct_constants_cannot_both_be_limits [T2Space M]
    (u_seq : ℕ → (CP1 → M)) (c₁ c₂ : M) (h_ne : c₁ ≠ c₂) (Ω : Set CP1)
    (h_open : IsOpen Ω) (h_nonempty : Ω.Nonempty)
    (h1 : SmoothLocalConvergesOn I u_seq (fun _ => c₁) Ω)
    (h2 : SmoothLocalConvergesOn I u_seq (fun _ => c₂) Ω) :
    False := by
  have heq : c₁ = c₂ := test_smooth_local_limit_unique_constants I u_seq c₁ c₂ Ω h_open h_nonempty h1 h2
  exact h_ne heq

-- Test 4C: Conjunction form: a sequence cannot simultaneously converge to distinct constants
theorem test_not_converge_to_distinct_constants [T2Space M]
    (u_seq : ℕ → (CP1 → M)) (c₁ c₂ : M) (h_ne : c₁ ≠ c₂) (Ω : Set CP1)
    (h_open : IsOpen Ω) (h_nonempty : Ω.Nonempty) :
    ¬ (SmoothLocalConvergesOn I u_seq (fun _ => c₁) Ω ∧
       SmoothLocalConvergesOn I u_seq (fun _ => c₂) Ω) := by
  intro ⟨h1, h2⟩
  exact test_distinct_constants_cannot_both_be_limits I u_seq c₁ c₂ h_ne Ω h_open h_nonempty h1 h2

-- Test 4D: Concrete adversarial test on the open disk `disk_at 0 1`
theorem test_distinct_constants_disk [T2Space M]
    (u_seq : ℕ → (CP1 → M)) (c₁ c₂ : M) (h_ne : c₁ ≠ c₂) :
    ¬ (SmoothLocalConvergesOn I u_seq (fun _ => c₁) (disk_at 0 1) ∧
       SmoothLocalConvergesOn I u_seq (fun _ => c₂) (disk_at 0 1)) := by
  apply test_not_converge_to_distinct_constants I u_seq c₁ c₂ h_ne (disk_at 0 1)
  · exact is_open_disk_at 0 1
  · use stereo_chart.symm 0
    dsimp [disk_at]
    exact mem_image_of_mem _ (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))

-- Test 4E: Concrete adversarial test on `Set.univ`
theorem test_distinct_constants_univ [T2Space M]
    (u_seq : ℕ → (CP1 → M)) (c₁ c₂ : M) (h_ne : c₁ ≠ c₂) :
    ¬ (SmoothLocalConvergesOn I u_seq (fun _ => c₁) Set.univ ∧
       SmoothLocalConvergesOn I u_seq (fun _ => c₂) Set.univ) := by
  apply test_not_converge_to_distinct_constants I u_seq c₁ c₂ h_ne Set.univ
  · exact isOpen_univ
  · exact ⟨north_pole, mem_univ north_pole⟩

-- Test 4F: Subdomain restriction cannot rescue distinct limits
theorem test_restriction_and_distinct_limits [T2Space M]
    (u_seq : ℕ → (CP1 → M)) (c₁ c₂ : M) (h_ne : c₁ ≠ c₂)
    (h_univ1 : SmoothLocalConvergesOn I u_seq (fun _ => c₁) Set.univ)
    (h_univ2 : SmoothLocalConvergesOn I u_seq (fun _ => c₂) Set.univ) :
    False := by
  have h_disk1 := smooth_local_restriction I u_seq (fun _ => c₁) (subset_univ (disk_at 0 1)) h_univ1
  have h_disk2 := smooth_local_restriction I u_seq (fun _ => c₂) (subset_univ (disk_at 0 1)) h_univ2
  exact test_distinct_constants_disk I u_seq c₁ c₂ h_ne ⟨h_disk1, h_disk2⟩

#print axioms test_energy_point_null_north_pole
#print axioms test_energy_point_null_origin
#print axioms test_energy_point_null_one
#print axioms test_energy_point_null_I
#print axioms test_energy_point_null_arbitrary
#print axioms test_energy_point_sharp_nonneg
#print axioms test_energy_circle_null_unit
#print axioms test_energy_circle_null_arbitrary
#print axioms test_energy_circle_null_radius_zero
#print axioms test_energy_circle_null_radius_neg
#print axioms test_energy_density_eq_omega_pointwise
#print axioms test_energy_density_eq_omega_jhol
#print axioms test_energy_eq_pullback_omega_jhol
#print axioms test_energy_eq_pullback_omega_disk
#print axioms test_smooth_local_limit_unique_constants
#print axioms test_distinct_constants_cannot_both_be_limits
#print axioms test_not_converge_to_distinct_constants
#print axioms test_distinct_constants_disk
#print axioms test_distinct_constants_univ
#print axioms test_restriction_and_distinct_limits

end GromovCompactness.TestChallenge
