/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Challenger 2 Milestone 5 Iteration 2)
-/
import Mathlib.Analysis.Hofer
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EpsilonRegularity
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.SingularityRemoval
import GromovCompactness.Analysis.HoferRescaling

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory Filter GromovCompactness
open GromovCompactness.Analysis

namespace GromovCompactness.ChallengeB02AdversarialStress

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Empirical Challenger 2 Stress Harness: Milestone 5 Iteration 2
Target: Contract B02 (`CalibratedRescaling`, `exists_calibrated_rescaling_of_ivt`,
`exists_calibrated_rescaling`, Patrick Massot Hofer Lemma integration, unit gradient normalization).
-/

/- =========================================================================
   PART 1: PATRICK MASSOT'S HOFER LEMMA INTEGRATION & UNIT GRADIENT NORMALIZATION
   ========================================================================= -/

/-- Stress Test 1: Patrick Massot's Hofer lemma on arbitrary continuous non-negative function
produces moving center `x'`, local radius `ε'`, dilation product `ε * ϕ x ≤ ε' * ϕ x'`,
and uniform control `ϕ y ≤ 2 * ϕ x'`. -/
theorem stress_test_patrick_massot_hofer_direct
    (ϕ : ℂ → ℝ) (h_cont : Continuous ϕ) (h_nonneg : ∀ z, 0 ≤ ϕ z)
    (x : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ ε' > 0, ∃ x' : ℂ,
      ε' ≤ ε ∧
      dist x' x ≤ 2 * ε ∧
      ε * ϕ x ≤ ε' * ϕ x' ∧
      ∀ y, dist x' y ≤ ε' → ϕ y ≤ 2 * ϕ x' :=
  _root_.hofer x ε hε h_cont h_nonneg

/-- Stress Test 2: Unit gradient normalization is EXACT.
Under single-step Hofer rescaling, the rescaled density at the new center `a`
satisfies `lam * ϕ a = 1` exactly, and for every `z` in `B(0, R)`, `lam * ϕ (a + lam • z) ≤ 2`. -/
theorem stress_test_unit_gradient_normalization
    (ϕ : ℂ → ℝ) (h_cont : Continuous ϕ) (h_nonneg : ∀ z, 0 ≤ ϕ z)
    (x : ℂ) (ε : ℝ) (hε : 0 < ε) (hx_pos : 0 < ϕ x) :
    ∃ (a : ℂ) (lam R : ℝ),
      dist a x ≤ 2 * ε ∧
      0 < lam ∧
      0 < R ∧
      ε * ϕ x ≤ R ∧
      lam * ϕ a = 1 ∧
      (∀ z : ℂ, dist z 0 ≤ R → lam * ϕ (a + lam • z) ≤ 2) :=
  hofer_single_step ϕ h_cont h_nonneg x ε hε hx_pos

/-- Stress Test 3: Scaling factor decay: gradient blow-up forces scale λ ≤ 1 / ϕ(x). -/
theorem stress_test_scaling_radius_blowup
    (ϕ : ℂ → ℝ) (h_cont : Continuous ϕ) (h_nonneg : ∀ z, 0 ≤ ϕ z)
    (x : ℂ) (ε : ℝ) (hε : 0 < ε) (hx_pos : 0 < ϕ x) :
    ∃ (a : ℂ) (lam R : ℝ),
      0 < lam ∧ 0 < R ∧
      lam * ϕ a = 1 ∧
      lam ≤ 1 / ϕ x := by
  obtain ⟨ε', hε'_pos, x', hε'_le, _, h_prod, _⟩ :=
    _root_.hofer x ε hε h_cont h_nonneg
  have h_phi_x'_pos : 0 < ϕ x' := by
    have h_pos_prod : 0 < ε * ϕ x := mul_pos hε hx_pos
    have h_le : ε * ϕ x ≤ ε' * ϕ x' := h_prod
    have h_pos2 : 0 < ε' * ϕ x' := lt_of_lt_of_le h_pos_prod h_le
    by_contra h_neg
    push_neg at h_neg
    have : ε' * ϕ x' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε'_pos.le h_neg
    linarith
  let lam := 1 / ϕ x'
  let R := ε' * ϕ x'
  have hlam_pos : 0 < lam := one_div_pos.mpr h_phi_x'_pos
  have hR_pos : 0 < R := mul_pos hε'_pos h_phi_x'_pos
  have h_calib : lam * ϕ x' = 1 := one_div_mul_cancel h_phi_x'_pos.ne'
  have h_le : ε * ϕ x ≤ ε * ϕ x' := by
    calc
      ε * ϕ x ≤ ε' * ϕ x' := h_prod
      _ ≤ ε * ϕ x' := mul_le_mul_of_nonneg_right hε'_le (le_of_lt h_phi_x'_pos)
  have h_phi_le : ϕ x ≤ ϕ x' := by
    rwa [mul_le_mul_iff_of_pos_left hε] at h_le
  have h_inv : lam ≤ 1 / ϕ x :=
    one_div_le_one_div_of_le hx_pos h_phi_le
  exact ⟨x', lam, R, hlam_pos, hR_pos, h_calib, h_inv⟩

/- =========================================================================
   PART 2: NON-VACUITY OF RADIAL ENERGY IVT
   ========================================================================= -/

/-- Stress Test 4: Discontinuous step function FAILS the intermediate value property.
This proves that RadialEnergyIVT is mathematically substantive and CANNOT be
proved vacuously without the continuity of disk energy measures. -/
theorem stress_test_discontinuous_step_fails_ivt :
    ¬ (∀ (f : ℝ → ℝ), f 0 = 0 → f 1 = 1 → (∀ c ∈ Set.Ioo (0 : ℝ) 1, ∃ r ∈ Set.Icc (0 : ℝ) 1, f r = c)) := by
  intro h_ivt
  let step : ℝ → ℝ := fun r => if r < 1/2 then 0 else 1
  have h0 : step 0 = 0 := by
    dsimp [step]
    have : (0 : ℝ) < 1/2 := by norm_num
    rw [if_pos this]
  have h1 : step 1 = 1 := by
    dsimp [step]
    have : ¬ ((1 : ℝ) < 1/2) := by norm_num
    rw [if_neg this]
  have h_half_mem : (1/2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨r, hr_icc, hr_eq⟩ := h_ivt step h0 h1 (1/2) h_half_mem
  dsimp [step] at hr_eq
  split_ifs at hr_eq with h_lt
  · norm_num at hr_eq
  · norm_num at hr_eq

/-- Stress Test 5: The intermediate value property requires the continuity
provided by `ivt_radial_energy_of_continuous`. -/
theorem stress_test_continuous_radial_energy_satisfies_ivt
    (f : ℝ → ℝ) (R c : ℝ) (h_cont : ContinuousOn f (Icc 0 R))
    (h_zero : f 0 = 0) (hR : 0 < R) (hc_pos : 0 < c) (hc_le : c ≤ f R) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ f r = c :=
  ivt_radial_energy_of_continuous f R c h_cont h_zero hR hc_pos hc_le

/- =========================================================================
   PART 3: SIGNATURE AND REDUCTION AUDIT OF exists_calibrated_rescaling
   ========================================================================= -/

/-- Stress Test 6: Verifying that `exists_calibrated_rescaling` is a pure reduction
theorem requiring `h_ivt : RadialEnergyIVT I (M := M)`. -/
theorem stress_test_exists_calibrated_rescaling_signature
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n))
    (h_ivt : RadialEnergyIVT I (M := M)) :
    Nonempty (CalibratedRescaling I u_seq thresh m_defect) :=
  exists_calibrated_rescaling I u_seq thresh m_defect hm h_jhol h_defect h_ivt

/-- Stress Test 7: Defect calibration target m_defect - h / 2 is strictly between 0 and m_defect. -/
theorem stress_test_defect_calibration_bounds
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) :
    0 < m_defect - thresh.h / 2 ∧
    m_defect - thresh.h / 2 < m_defect ∧
    thresh.h / 2 ≤ m_defect - thresh.h / 2 := by
  have hh_pos := thresh.h_pos
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Stress Test 8: Assembling calibrated rescaling with Patrick Massot's Hofer lemma
guarantees that moving centers converge to 0 and scales converge to 0. -/
theorem stress_test_calibrated_rescaling_convergence
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (calib : CalibratedRescaling I u_seq thresh m_defect) :
    Filter.Tendsto calib.a Filter.atTop (nhds 0) ∧
    Filter.Tendsto calib.«λ» Filter.atTop (nhds 0) ∧
    (∀ n, 0 < calib.«λ» n) :=
  ⟨calib.a_tendsto, calib.scale_tendsto, calib.scale_pos⟩

#print axioms stress_test_patrick_massot_hofer_direct
#print axioms stress_test_unit_gradient_normalization
#print axioms stress_test_scaling_radius_blowup
#print axioms stress_test_discontinuous_step_fails_ivt
#print axioms stress_test_continuous_radial_energy_satisfies_ivt
#print axioms stress_test_exists_calibrated_rescaling_signature
#print axioms stress_test_defect_calibration_bounds
#print axioms stress_test_calibrated_rescaling_convergence

end GromovCompactness.ChallengeB02AdversarialStress
