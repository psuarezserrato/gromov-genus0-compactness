/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Challenger 2 Milestone 5)
-/
import Mathlib.Analysis.Hofer
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Data.Set.Card
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
open Metric Set MeasureTheory Filter GromovCompactness Finset
open GromovCompactness.Analysis

namespace GromovCompactness.ChallengeMilestone5Rescaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Empirical Adversarial Challenge Suite: Milestone 5 Calibrated Rescaling
Challenger: challenger2_m5 (Calibrated Rescaling Challenger)
Target: GromovCompactness/Analysis/HoferRescaling.lean (Contract B02 & Supporting Foundations)

This challenge suite performs rigorous code-executing adversarial challenge testing of
Contract B02 (`CalibratedRescaling`, `exists_calibrated_rescaling_of_ivt`,
`exists_calibrated_rescaling`, `hofer_single_step`, `bubble_energy_ge_sphere_gap`)
across 5 comprehensive categories:

- Category 1: Single-step Hofer rescaling (`hofer_single_step`):
  unit calibration ‖dv(0)‖ = 1, uniform bound ‖dv(z)‖ ≤ 2 on B(0, R), scaling radius λ R = ε' ≤ ε₀.
- Category 2: Asymptotic convergence of calibrated moving centers and radii:
  testing a_n → 0 and λ_n → 0 with `tendsto_dist_zero_of_le_inv_succ` and `tendsto_scale_zero_of_le_inv_succ`.
- Category 3: Radial energy intermediate value reduction (`exists_calibrated_rescaling_of_ivt`):
  testing exact attainment E(u_n; D_{λ_n}(a_n)) = m_defect - h / 2.
- Category 4: Bubble energy gap (`bubble_energy_ge_sphere_gap`):
  lower bound E(v_∞) ≥ ε_sph ≥ h > 0.
- Category 5: Adversarial attack resistance:
  confirming that zero-energy maps or invalid defect hypotheses cannot instantiate `CalibratedRescaling`.
-/

/- =========================================================================
   CATEGORY 1: SINGLE-STEP HOFER RESCALING (hofer_single_step)
   ========================================================================= -/

/-- Test 1.1: Single-step Hofer rescaling on a constant positive gradient density. -/
theorem test_cat1_hofer_constant_density (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∃ (a : ℂ) (lam R : ℝ),
      dist a 0 ≤ 2 * ε ∧
      0 < lam ∧ 0 < R ∧
      ε * C ≤ R ∧
      lam * C = 1 ∧
      (∀ z : ℂ, dist z 0 ≤ R → lam * C ≤ 2) := by
  have h_cont : Continuous (fun _ : ℂ => C) := continuous_const
  have h_nonneg : ∀ y : ℂ, 0 ≤ (fun _ : ℂ => C) y := fun _ => le_of_lt hC
  have h_pos : 0 < (fun _ : ℂ => C) 0 := hC
  obtain ⟨a, lam, R, h_dist, hlam, hR, hR_ge, h_calib, h_bound⟩ :=
    hofer_single_step (fun _ => C) h_cont h_nonneg 0 ε hε h_pos
  exact ⟨a, lam, R, h_dist, hlam, hR, hR_ge, h_calib, h_bound⟩

/-- Test 1.2: Exact calibration identity λ = 1 / ϕ(a) and unit normalization. -/
theorem test_cat1_hofer_unit_calibration_exact (ϕ : ℂ → ℝ) (h_cont : Continuous ϕ)
    (h_nonneg : ∀ y, 0 ≤ ϕ y) (x : ℂ) (ε : ℝ) (hε : 0 < ε) (hx_pos : 0 < ϕ x) :
    ∃ (a : ℂ) (lam : ℝ), 0 < lam ∧ 0 < ϕ a ∧ lam * ϕ a = 1 ∧ lam = 1 / ϕ a := by
  obtain ⟨a, lam, R, _, hlam_pos, _, _, h_calib, _⟩ :=
    hofer_single_step ϕ h_cont h_nonneg x ε hε hx_pos
  have h_phi_a_pos : 0 < ϕ a := by
    by_contra h_not
    push_neg at h_not
    have : lam * ϕ a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam_pos.le h_not
    linarith
  have h_inv : lam = 1 / ϕ a := by
    calc
      lam = lam * 1 := (mul_one lam).symm
      _ = lam * (ϕ a * (1 / ϕ a)) := by rw [mul_one_div_cancel h_phi_a_pos.ne']
      _ = (lam * ϕ a) * (1 / ϕ a) := by ring
      _ = 1 * (1 / ϕ a) := by rw [h_calib]
      _ = 1 / ϕ a := one_mul _
  exact ⟨a, lam, hlam_pos, h_phi_a_pos, h_calib, h_inv⟩

/-- Test 1.3: Evaluation of uniform gradient bound at origin is consistent with unit calibration. -/
theorem test_cat1_hofer_origin_bound_consistent (ϕ : ℂ → ℝ) (h_cont : Continuous ϕ)
    (h_nonneg : ∀ y, 0 ≤ ϕ y) (x : ℂ) (ε : ℝ) (hε : 0 < ε) (hx_pos : 0 < ϕ x) :
    ∃ (a : ℂ) (lam : ℝ), lam * ϕ a = 1 ∧ lam * ϕ a ≤ 2 := by
  obtain ⟨a, lam, R, _, _, hR_pos, _, h_calib, h_bound⟩ :=
    hofer_single_step ϕ h_cont h_nonneg x ε hε hx_pos
  have h0 : dist (0 : ℂ) 0 ≤ R := by simp [hR_pos.le]
  have hb0 := h_bound 0 h0
  simp only [smul_zero, add_zero] at hb0
  exact ⟨a, lam, h_calib, hb0⟩

/-- Test 1.4: Metric inclusion of rescaled ball: dist(a + λ • z, a) ≤ ε' ≤ ε₀. -/
theorem test_cat1_hofer_ball_inclusion (a : ℂ) (lam R ε' ε₀ : ℝ)
    (h_eq : lam * R = ε') (h_pos : 0 ≤ lam) (h_le : ε' ≤ ε₀)
    (z : ℂ) (hz : dist z 0 ≤ R) :
    dist (a + lam • z) a ≤ ε₀ := by
  have h_inc := hofer_rescaling_ball_inclusion a lam R ε' h_eq h_pos z hz
  exact h_inc.trans h_le

/-- Test 1.5: Scaling law: gradient blow-up forces scale λ < δ and radius R > ε₀ / δ. -/
theorem test_cat1_hofer_scaling_law (M_val ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hδ : 0 < δ)
    (hM : 1 / δ < M_val) :
    let lam := 1 / M_val
    let R := ε₀ * M_val
    0 < lam ∧ lam < δ ∧ ε₀ / δ < R := by
  intro lam R
  have hM_pos : 0 < M_val := lt_trans (one_div_pos.mpr hδ) hM
  have hlam_pos : 0 < lam := one_div_pos.mpr hM_pos
  have hlam_lt : lam < δ := by
    dsimp [lam]
    have : (1 : ℝ) / M_val < (1 : ℝ) / (1 / δ) :=
      one_div_lt_one_div_of_lt (one_div_pos.mpr hδ) hM
    rwa [one_div_one_div] at this
  have hR_gt : ε₀ / δ < R := by
    dsimp [R]
    calc
      ε₀ / δ = ε₀ * (1 / δ) := by ring
      _ < ε₀ * M_val := mul_lt_mul_of_pos_left hM hε₀
  exact ⟨hlam_pos, hlam_lt, hR_gt⟩

/-- Test 1.6: Rescaled curve at origin evaluates to center point u(stereo_chart.symm a). -/
theorem test_cat1_rescaled_curve_origin (u : CP1 → M) (a : ℂ) (lam : ℝ) :
    rescaled_curve u a lam 0 = u (stereo_chart.symm a) := by
  dsimp [rescaled_curve]
  simp

/- =========================================================================
   CATEGORY 2: ASYMPTOTIC CONVERGENCE OF MOVING CENTERS AND RADII
   ========================================================================= -/

/-- Test 2.1: Squeeze convergence of complex moving centers a_n = (1 / (n + 1) : ℂ). -/
theorem test_cat2_tendsto_centers_inv_succ_complex :
    Filter.Tendsto (fun n : ℕ => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) Filter.atTop (nhds 0) := by
  have h_dist : ∀ n : ℕ, dist ((((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) 0 ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    rw [dist_zero_right, Complex.norm_real]
    have : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    rw [Real.norm_of_nonneg this]
  exact tendsto_dist_zero_of_le_inv_succ (fun n => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) 0 h_dist

/-- Test 2.2: Squeeze convergence of half-harmonic scaling sequence λ_n = 1 / (2 * (n + 1)). -/
theorem test_cat2_tendsto_scales_half_inv_succ :
    Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (2 * ((n : ℝ) + 1))) Filter.atTop (nhds 0) := by
  have h_pos : ∀ n : ℕ, 0 < (1 : ℝ) / (2 * ((n : ℝ) + 1)) := by
    intro n; positivity
  have h_le : ∀ n : ℕ, (1 : ℝ) / (2 * ((n : ℝ) + 1)) ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have h1 : 0 < (n : ℝ) + 1 := by positivity
    have h2 : (n : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by linarith
    exact one_div_le_one_div_of_le h1 h2
  exact tendsto_scale_zero_of_le_inv_succ _ h_pos h_le

/-- Test 2.3: Quadratic scale decay squeeze: λ_n ≤ 1 / (n + 1)^2 forces λ_n → 0. -/
theorem test_cat2_quadratic_scale_decay_squeeze
    (lam : ℕ → ℝ) (h_pos : ∀ n, 0 < lam n)
    (h_quad : ∀ n, lam n ≤ 1 / ((n : ℝ) + 1)^2) :
    Filter.Tendsto lam Filter.atTop (nhds 0) := by
  have h_le : ∀ n, lam n ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have h1 : (n : ℝ) + 1 ≤ ((n : ℝ) + 1)^2 := by
      have : 1 ≤ (n : ℝ) + 1 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      nlinarith
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have h_inv : 1 / ((n : ℝ) + 1)^2 ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le hpos h1
    exact (h_quad n).trans h_inv
  exact tendsto_scale_zero_of_le_inv_succ lam h_pos h_le

/-- Test 2.4: Moving affine points a_n + λ_n • w converge to 0 when bounded by 1 / (n + 1). -/
theorem test_cat2_affine_shifted_points_tendsto_zero
    (a : ℕ → ℂ) (lam : ℕ → ℝ) (h_a : ∀ n, dist (a n) 0 ≤ 1 / ((n : ℝ) + 1))
    (h_lam_pos : ∀ n, 0 < lam n) (h_lam_le : ∀ n, lam n ≤ 1 / ((n : ℝ) + 1))
    (w : ℂ) (hw : ‖w‖ ≤ 1) :
    Filter.Tendsto (fun n => a n + (lam n) • w) Filter.atTop (nhds 0) := by
  have h_dist : ∀ n, dist (a n + (lam n) • w) 0 ≤ 2 / ((n : ℝ) + 1) := by
    intro n
    rw [dist_zero_right]
    calc
      ‖a n + (lam n) • w‖ ≤ ‖a n‖ + ‖(lam n) • w‖ := norm_add_le _ _
      _ = dist (a n) 0 + |lam n| * ‖w‖ := by rw [dist_zero_right, norm_smul, Real.norm_eq_abs]
      _ ≤ 1 / ((n : ℝ) + 1) + (lam n) * 1 := by
        have h_abs : |lam n| = lam n := abs_of_pos (h_lam_pos n)
        rw [h_abs]
        have h_w : lam n * ‖w‖ ≤ lam n * 1 := mul_le_mul_of_nonneg_left hw (h_lam_pos n).le
        linarith [h_a n]
      _ ≤ 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by linarith [h_lam_le n]
      _ = 2 / ((n : ℝ) + 1) := by ring
  rw [tendsto_iff_dist_tendsto_zero]
  have h_two_tendsto : Filter.Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
    have h_lim : Filter.Tendsto (fun n : ℕ => (2 : ℝ) * (1 / ((n : ℝ) + 1))) Filter.atTop (nhds (2 * 0)) :=
      Filter.Tendsto.const_mul 2 tendsto_inv_succ
    rw [mul_zero] at h_lim
    have h_eq : (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 1)) = (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) := by
      ext n; ring
    rwa [h_eq]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_two_tendsto ?_ h_dist
  intro n
  exact dist_nonneg

/-- Test 2.5: Metric space generality: Squeeze holds for arbitrary metric spaces and any target point x₀. -/
theorem test_cat2_metric_space_generality {X : Type*} [MetricSpace X]
    (x_seq : ℕ → X) (x₀ : X) (h_dist : ∀ n, dist (x_seq n) x₀ ≤ 1 / ((n : ℝ) + 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, x_seq n ∈ Metric.ball x₀ ε := by
  have h_tendsto := tendsto_dist_zero_of_le_inv_succ x_seq x₀ h_dist
  rw [Metric.tendsto_atTop] at h_tendsto
  obtain ⟨N, hN⟩ := h_tendsto ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [Metric.mem_ball]
  exact hN n hn

/- =========================================================================
   CATEGORY 3: RADIAL ENERGY INTERMEDIATE VALUE REDUCTION (exists_calibrated_rescaling_of_ivt)
   ========================================================================= -/

/-- Test 3.1: Intermediate Value Theorem for a linear radial energy profile f(r) = E₀ * (r / R). -/
theorem test_cat3_ivt_linear_model (E₀ R c : ℝ) (hE₀ : 0 < E₀) (hR : 0 < R)
    (hc_pos : 0 < c) (hc_le : c ≤ E₀) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ E₀ * (r / R) = c := by
  let f : ℝ → ℝ := fun r => E₀ * (r / R)
  have h_cont : ContinuousOn f (Set.Icc 0 R) := by
    apply Continuous.continuousOn
    continuity
  have h_zero : f 0 = 0 := by
    dsimp [f]; ring
  have h_c_le : c ≤ f R := by
    dsimp [f]
    rw [div_self hR.ne', mul_one]
    exact hc_le
  obtain ⟨r, hr_pos, hr_le, hfr⟩ := ivt_radial_energy_of_continuous f R c h_cont h_zero hR hc_pos h_c_le
  exact ⟨r, hr_pos, hr_le, hfr⟩

/-- Test 3.2: Intermediate Value Theorem for quadratic energy profile f(r) = E₀ * (r / R)^2. -/
theorem test_cat3_ivt_quadratic_energy_profile (E₀ R c : ℝ) (hE₀ : 0 < E₀) (hR : 0 < R)
    (hc_pos : 0 < c) (hc_le : c ≤ E₀) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ E₀ * (r / R)^2 = c := by
  let f : ℝ → ℝ := fun r => E₀ * (r / R)^2
  have h_cont : ContinuousOn f (Set.Icc 0 R) := by
    apply Continuous.continuousOn
    continuity
  have h_zero : f 0 = 0 := by
    dsimp [f]; ring
  have h_c_le : c ≤ f R := by
    dsimp [f]
    rw [div_self hR.ne', one_pow, mul_one]
    exact hc_le
  obtain ⟨r, hr_pos, hr_le, hfr⟩ := ivt_radial_energy_of_continuous f R c h_cont h_zero hR hc_pos h_c_le
  exact ⟨r, hr_pos, hr_le, hfr⟩

/-- Test 3.3: Exact calibration identity: energy on disk D_{λ_n}(a_n) is strictly m_defect - h / 2. -/
theorem test_cat3_calibrated_energy_exact_identity
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (calib : CalibratedRescaling I u_seq thresh m_defect) (n : ℕ) :
    energyMeasure I (u_seq n) (disk_at (calib.a n) (calib.«λ» n)) = m_defect - thresh.h / 2 ∧
    m_defect - energyMeasure I (u_seq n) (disk_at (calib.a n) (calib.«λ» n)) = thresh.h / 2 := by
  have h1 := calib.calibrated_energy n
  have h2 : m_defect - energyMeasure I (u_seq n) (disk_at (calib.a n) (calib.«λ» n)) = thresh.h / 2 := by
    rw [h1]; ring
  exact ⟨h1, h2⟩

/-- Test 3.4: Positivity and gap of intermediate calibration target m_defect - h / 2. -/
theorem test_cat3_defect_intermediate_target_strictly_positive
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) :
    0 < thresh.h / 2 ∧
    thresh.h / 2 ≤ m_defect - thresh.h / 2 ∧
    0 < m_defect - thresh.h / 2 := by
  have h_pos := thresh.h_pos
  have h1 : 0 < thresh.h / 2 := by linarith
  have h2 : thresh.h / 2 ≤ m_defect - thresh.h / 2 := by linarith
  have h3 : 0 < m_defect - thresh.h / 2 := lt_of_lt_of_le h1 h2
  exact ⟨h1, h2, h3⟩

/-- Test 3.5: Full constructive reduction of Contract B02 under RadialEnergyIVT. -/
theorem test_cat3_full_ivt_reduction_instantiation
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n))
    (h_ivt : RadialEnergyIVT I (M := M)) :
    Nonempty (CalibratedRescaling I u_seq thresh m_defect) :=
  exists_calibrated_rescaling_of_ivt I u_seq thresh m_defect hm h_jhol h_defect h_ivt

/- =========================================================================
   CATEGORY 4: BUBBLE ENERGY GAP (bubble_energy_ge_sphere_gap)
   ========================================================================= -/

/-- Test 4.1: Direct bubble energy gap lower bound E(v_∞) ≥ ε_sph. -/
theorem test_cat4_bubble_energy_ge_sphere_gap
    (thresh : TargetThresholds I M) (v_lim : CP1 → M)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v_lim Set.univ)
    (h_nonconst : ¬ ∃ c : M, ∀ z, v_lim z = c) :
    thresh.ε_sph ≤ totalEnergy I v_lim :=
  bubble_energy_ge_sphere_gap (I := I) thresh v_lim h_jhol h_nonconst

/-- Test 4.2: Universal threshold h bounds bubble energy from below: h ≤ E(v_∞). -/
theorem test_cat4_bubble_energy_ge_bubbling_threshold_h
    (thresh : TargetThresholds I M) (v_lim : CP1 → M)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v_lim Set.univ)
    (h_nonconst : ¬ ∃ c : M, ∀ z, v_lim z = c) :
    thresh.h ≤ totalEnergy I v_lim := by
  have h_sph := bubble_energy_ge_sphere_gap (I := I) thresh v_lim h_jhol h_nonconst
  exact thresh.h_le_sph.trans h_sph

/-- Test 4.3: Strict positivity of bubble energy: 0 < E(v_∞) for any non-constant bubble. -/
theorem test_cat4_bubble_energy_strictly_positive
    (thresh : TargetThresholds I M) (v_lim : CP1 → M)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v_lim Set.univ)
    (h_nonconst : ¬ ∃ c : M, ∀ z, v_lim z = c) :
    0 < totalEnergy I v_lim := by
  have h_le := test_cat4_bubble_energy_ge_bubbling_threshold_h (I := I) thresh v_lim h_jhol h_nonconst
  exact lt_of_lt_of_le thresh.h_pos h_le

/-- Test 4.4: Sub-threshold sphere gap energy forces constancy of the bubble limit. -/
theorem test_cat4_subthreshold_energy_forces_constant_bubble
    (thresh : TargetThresholds I M) (v_lim : CP1 → M)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v_lim Set.univ)
    (h_sub : totalEnergy I v_lim < thresh.ε_sph) :
    ∃ c : M, ∀ z, v_lim z = c := by
  by_contra h_nonconst
  have h_ge := bubble_energy_ge_sphere_gap (I := I) thresh v_lim h_jhol h_nonconst
  linarith

/-- Test 4.5: Sub-threshold h energy forces constancy of the bubble limit. -/
theorem test_cat4_sub_h_energy_forces_constant_bubble
    (thresh : TargetThresholds I M) (v_lim : CP1 → M)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v_lim Set.univ)
    (h_sub : totalEnergy I v_lim < thresh.h) :
    ∃ c : M, ∀ z, v_lim z = c := by
  by_contra h_nonconst
  have h_ge := test_cat4_bubble_energy_ge_bubbling_threshold_h (I := I) thresh v_lim h_jhol h_nonconst
  linarith

/-- Test 4.6: Defect mass m_defect ≥ h ensures at least one quantum of bubbling capacity. -/
theorem test_cat4_defect_mass_ge_one_bubble (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect) :
    1 ≤ m_defect / thresh.h := by
  exact (one_le_div₀ thresh.h_pos).mpr hm

/- =========================================================================
   CATEGORY 5: ADVERSARIAL ATTACK RESISTANCE
   ========================================================================= -/

/-- Test 5.1: Adversarial attack: Constant sequence cannot satisfy concentration defect hypothesis. -/
theorem test_cat5_constant_sequence_refutes_defect_hypothesis
    (c₀ : M) (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (fun _ => c₀) (disk_at a_n R_n)) :
    False := by
  obtain ⟨a₀, R₀, _, _, _, h_en⟩ := h_defect 0
  have h_zero : energyMeasure I (fun _ => c₀) (disk_at a₀ R₀) = 0 :=
    energyMeasure_const I c₀ (disk_at a₀ R₀)
  rw [h_zero] at h_en
  have h_pos : 0 < thresh.h / 2 := by linarith [thresh.h_pos]
  have h_ge : thresh.h / 2 ≤ m_defect - thresh.h / 2 := by linarith
  linarith

/-- Test 5.2: Adversarial attack: Constant sequence cannot instantiate CalibratedRescaling. -/
theorem test_cat5_zero_energy_refutes_calibrated_rescaling
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (h_zero : ∀ n a r, energyMeasure I (u_seq n) (disk_at a r) = 0)
    (calib : CalibratedRescaling I u_seq thresh m_defect) :
    False := by
  have h_cal := calib.calibrated_energy 0
  rw [h_zero 0 (calib.a 0) (calib.«λ» 0)] at h_cal
  have h_pos : 0 < thresh.h / 2 := by linarith [thresh.h_pos]
  have h_ge : thresh.h / 2 ≤ m_defect - thresh.h / 2 := by linarith
  linarith

/-- Test 5.3: Adversarial attack: Sub-threshold sequence energy < h / 2 refutes defect concentration. -/
theorem test_cat5_subthreshold_energy_violates_defect
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (h_small : ∀ n a r, energyMeasure I (u_seq n) (disk_at a r) < thresh.h / 2)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n)) :
    False := by
  obtain ⟨a₀, R₀, _, _, _, h_en⟩ := h_defect 0
  have h_bd := h_small 0 a₀ R₀
  have h_ge : thresh.h / 2 ≤ m_defect - thresh.h / 2 := by linarith
  linarith

/-- Test 5.4: Adversarial attack: Non-positive defect mass m_defect ≤ 0 is refuted by threshold positivity. -/
theorem test_cat5_nonpositive_defect_mass_contradiction
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect)
    (h_nonpos : m_defect ≤ 0) :
    False := by
  have h_pos := thresh.h_pos
  linarith

/-- Test 5.5: Adversarial attack: Degenerate threshold h = 0 is refuted by TargetThresholds positivity. -/
theorem test_cat5_zero_threshold_h_refuted
    (thresh : TargetThresholds I M) (h_zero : thresh.h = 0) :
    False := by
  have h_pos := thresh.h_pos
  linarith

/-- Test 5.6: Adversarial attack: Hofer rescaling with identically zero density ϕ ≡ 0 cannot calibrate. -/
theorem test_cat5_hofer_identically_zero_density_cannot_calibrate
    (lam : ℝ) (h_calib : lam * (0 : ℝ) = 1) :
    False := by
  rw [mul_zero] at h_calib
  norm_num at h_calib

#print axioms test_cat1_hofer_constant_density
#print axioms test_cat1_hofer_unit_calibration_exact
#print axioms test_cat1_hofer_origin_bound_consistent
#print axioms test_cat1_hofer_ball_inclusion
#print axioms test_cat1_hofer_scaling_law
#print axioms test_cat1_rescaled_curve_origin
#print axioms test_cat2_tendsto_centers_inv_succ_complex
#print axioms test_cat2_tendsto_scales_half_inv_succ
#print axioms test_cat2_quadratic_scale_decay_squeeze
#print axioms test_cat2_affine_shifted_points_tendsto_zero
#print axioms test_cat2_metric_space_generality
#print axioms test_cat3_ivt_linear_model
#print axioms test_cat3_ivt_quadratic_energy_profile
#print axioms test_cat3_calibrated_energy_exact_identity
#print axioms test_cat3_defect_intermediate_target_strictly_positive
#print axioms test_cat3_full_ivt_reduction_instantiation
#print axioms test_cat4_bubble_energy_ge_sphere_gap
#print axioms test_cat4_bubble_energy_ge_bubbling_threshold_h
#print axioms test_cat4_bubble_energy_strictly_positive
#print axioms test_cat4_subthreshold_energy_forces_constant_bubble
#print axioms test_cat4_sub_h_energy_forces_constant_bubble
#print axioms test_cat4_defect_mass_ge_one_bubble
#print axioms test_cat5_constant_sequence_refutes_defect_hypothesis
#print axioms test_cat5_zero_energy_refutes_calibrated_rescaling
#print axioms test_cat5_subthreshold_energy_violates_defect
#print axioms test_cat5_nonpositive_defect_mass_contradiction
#print axioms test_cat5_zero_threshold_h_refuted
#print axioms test_cat5_hofer_identically_zero_density_cannot_calibrate

end GromovCompactness.ChallengeMilestone5Rescaling
