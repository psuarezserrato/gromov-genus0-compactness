/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Connected.Clopen
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness

namespace GromovCompactness.Analysis

/-!
# Tasks A01 & A08: Mean-Value Inequality and Target Monotonicity

This module formalizes:
1. `scalar_mean_value_inequality` (Contract A01): The scalar mean-value inequality for functions
   satisfying the subharmonic differential inequality $\Delta e \ge -b e^2$.
2. `target_monotonicity` (Contract A08): The quadratic area growth formula
   $E(u; u^{-1}(B_r(x))) \ge c r^2$ for pseudo-holomorphic curves inside target metric balls.

References:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §1.2 & §1.3.
- Sergei Ivashkovich & Vsevolod Shevchishin, arXiv:math/9912046, Lemma 2.1.1 & §2.1.
- Dusa McDuff & Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology* (2012), Lemma 4.3.2 & Prop 4.4.1.
- `gromov_compactness.pdf` §4.1 (Contract A01) and §4.3 (Contract A08).
-/

/-- Standard 2D Euclidean Laplacian of a real-valued function on ℂ. -/
noncomputable def laplacian2D (e : ℂ → ℝ) (z : ℂ) : ℝ :=
  (iteratedFDeriv ℝ 2 e z) ![1, 1] + (iteratedFDeriv ℝ 2 e z) ![Complex.I, Complex.I]

/-- When the integral of a non-negative continuous function vanishes on an open ball,
the function vanishes identically on concentric interior balls. -/
lemma mvi_branch_zero (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall (0 : ℂ) r))
    (h_int_zero : ∫ w in Metric.ball (0 : ℂ) r, e w = 0)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) (r / 2)) :
    e z = 0 := by
  have hz_in_ball : z ∈ Metric.ball (0 : ℂ) r := by
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  have h_sub : Metric.ball (0 : ℂ) r ⊆ Metric.closedBall (0 : ℂ) r := ball_subset_closedBall
  have he_cont_ball : ContinuousOn e (Metric.ball (0 : ℂ) r) := he_cont.mono h_sub
  have he_intble : IntegrableOn e (Metric.ball (0 : ℂ) r) volume := by
    have h_comp : IsCompact (Metric.closedBall (0 : ℂ) r) := isCompact_closedBall 0 r
    have h_intble_closed : IntegrableOn e (Metric.closedBall (0 : ℂ) r) volume :=
      he_cont.integrableOn_compact (μ := volume) h_comp
    exact h_intble_closed.mono_set h_sub
  have he_ae_nonneg : 0 ≤ᵐ[volume.restrict (Metric.ball (0 : ℂ) r)] e := by
    apply Filter.Eventually.of_forall
    intro w
    exact he_nonneg w
  have he_ae_zero : e =ᵐ[volume.restrict (Metric.ball (0 : ℂ) r)] 0 := by
    rw [← setIntegral_eq_zero_iff_of_nonneg_ae he_ae_nonneg he_intble]
    exact h_int_zero
  have he_eq : EqOn e 0 (Metric.ball (0 : ℂ) r) :=
    Measure.eqOn_open_of_ae_eq he_ae_zero isOpen_ball he_cont_ball continuousOn_const
  exact he_eq hz_in_ball

/-- Existence of Heinz maximum point on `closedBall 0 r` for `(r - ‖w‖)² e(w)`. -/
lemma heinz_maximum_exists (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r)) :
    ∃ z₀ ∈ Metric.closedBall (0 : ℂ) r,
      ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        (r - ‖w‖)^2 * e w ≤ (r - ‖z₀‖)^2 * e z₀ := by
  have h_comp : IsCompact (Metric.closedBall (0 : ℂ) r) := isCompact_closedBall 0 r
  have h_nonempty : (Metric.closedBall (0 : ℂ) r).Nonempty := ⟨0, Metric.mem_closedBall.mpr (by simp [hr.le])⟩
  have h_cont_f : ContinuousOn (fun w => (r - ‖w‖)^2 * e w) (Metric.closedBall 0 r) := by
    apply ContinuousOn.mul
    · have h_norm : ContinuousOn (fun w : ℂ => r - ‖w‖) (Metric.closedBall 0 r) :=
        continuousOn_const.sub continuous_norm.continuousOn
      exact h_norm.pow 2
    · exact he_cont
  rcases h_comp.exists_isMaxOn h_nonempty h_cont_f with ⟨z₀, hz₀_mem, hz₀_max⟩
  exact ⟨z₀, hz₀_mem, hz₀_max⟩

/-- When the integral of `e` on `ball 0 r` is strictly positive, any Heinz maximizer `z₀`
lies in the open ball `ball 0 r` and satisfies `0 < e z₀`. -/
lemma heinz_maximum_interior (r : ℝ) (_hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (h_pos : 0 < ∫ w in Metric.ball (0 : ℂ) r, e w)
    (z₀ : ℂ) (hz₀ : z₀ ∈ Metric.closedBall 0 r)
    (h_max : ∀ w ∈ Metric.closedBall 0 r, (r - ‖w‖)^2 * e w ≤ (r - ‖z₀‖)^2 * e z₀) :
    z₀ ∈ Metric.ball (0 : ℂ) r ∧ 0 < e z₀ := by
  have h_max_val : 0 < (r - ‖z₀‖)^2 * e z₀ := by
    by_contra h_le_zero
    push_neg at h_le_zero
    have h_zero_max : (r - ‖z₀‖)^2 * e z₀ = 0 := by
      have h1 : 0 ≤ (r - ‖z₀‖)^2 * e z₀ := mul_nonneg (sq_nonneg _) (he_nonneg z₀)
      linarith
    have h_all_zero : ∀ w ∈ Metric.ball (0 : ℂ) r, e w = 0 := by
      intro w hw
      have hw_closed : w ∈ Metric.closedBall (0 : ℂ) r := Metric.ball_subset_closedBall hw
      have h_bound := h_max w hw_closed
      rw [h_zero_max] at h_bound
      have h_nonneg_w : 0 ≤ (r - ‖w‖)^2 * e w := mul_nonneg (sq_nonneg _) (he_nonneg w)
      have h_eq_zero : (r - ‖w‖)^2 * e w = 0 := le_antisymm h_bound h_nonneg_w
      have hw_dist : ‖w‖ < r := by
        have := Metric.mem_ball.mp hw
        rwa [dist_zero_right] at this
      have h_diff_pos : 0 < r - ‖w‖ := by linarith
      have h_sq_pos : 0 < (r - ‖w‖)^2 := sq_pos_of_pos h_diff_pos
      exact (mul_eq_zero.mp h_eq_zero).resolve_left h_sq_pos.ne'
    have h_int_zero : (∫ w in Metric.ball (0 : ℂ) r, e w) = 0 := by
      rw [setIntegral_congr_fun isOpen_ball.measurableSet (fun w hw => h_all_zero w hw), integral_zero]
    linarith
  constructor
  · by_contra h_not_ball
    have hz_norm : ‖z₀‖ = r := by
      have h_le : ‖z₀‖ ≤ r := by
        have := Metric.mem_closedBall.mp hz₀
        rwa [dist_zero_right] at this
      have h_not_lt : ¬ ‖z₀‖ < r := by
        intro hlt
        apply h_not_ball
        rw [Metric.mem_ball, dist_zero_right]
        exact hlt
      linarith
    have h_diff_zero : (r - ‖z₀‖)^2 = 0 := by rw [hz_norm, sub_self, sq, mul_zero]
    rw [h_diff_zero, zero_mul] at h_max_val
    linarith
  · by_contra h_not_pos
    push_neg at h_not_pos
    have he_z0_zero : e z₀ = 0 := le_antisymm h_not_pos (he_nonneg z₀)
    rw [he_z0_zero, mul_zero] at h_max_val
    linarith

/-- On `closedBall z₀ ρ` with `ρ = (r - ‖z₀‖) / 2`, we have `closedBall z₀ ρ ⊆ ball 0 r`
and `e w ≤ 4 * e z₀`. -/
lemma heinz_ball_subset_and_bound (r : ℝ) (z₀ : ℂ) (hz₀ : z₀ ∈ Metric.ball (0 : ℂ) r)
    (e : ℂ → ℝ) (he_nonneg : ∀ z, 0 ≤ e z)
    (h_max : ∀ w ∈ Metric.closedBall 0 r, (r - ‖w‖)^2 * e w ≤ (r - ‖z₀‖)^2 * e z₀) :
    let ρ := (r - ‖z₀‖) / 2
    Metric.closedBall z₀ ρ ⊆ Metric.ball 0 r ∧
    ∀ w ∈ Metric.closedBall z₀ ρ, e w ≤ 4 * e z₀ := by
  intro ρ
  have hz₀_norm : ‖z₀‖ < r := by
    have := Metric.mem_ball.mp hz₀
    rwa [dist_zero_right] at this
  have hρ_pos : 0 < ρ := by
    change 0 < (r - ‖z₀‖) / 2
    linarith [hz₀_norm]
  constructor
  · intro w hw
    have hw_dist : dist w z₀ ≤ ρ := Metric.mem_closedBall.mp hw
    have hw_norm_le : ‖w‖ ≤ ‖z₀‖ + ρ := by
      calc ‖w‖ = ‖z₀ + (w - z₀)‖ := by ring_nf
      _ ≤ ‖z₀‖ + ‖w - z₀‖ := norm_add_le _ _
      _ = ‖z₀‖ + dist w z₀ := by rw [dist_eq_norm]
      _ ≤ ‖z₀‖ + ρ := by linarith
    have hw_norm_lt : ‖w‖ < r := by
      change ‖w‖ ≤ ‖z₀‖ + (r - ‖z₀‖) / 2 at hw_norm_le
      linarith [hw_norm_le, hz₀_norm]
    rw [Metric.mem_ball, dist_zero_right]
    exact hw_norm_lt
  · intro w hw
    have hw_dist : dist w z₀ ≤ ρ := Metric.mem_closedBall.mp hw
    have hw_norm_le : ‖w‖ ≤ ‖z₀‖ + ρ := by
      calc ‖w‖ = ‖z₀ + (w - z₀)‖ := by ring_nf
      _ ≤ ‖z₀‖ + ‖w - z₀‖ := norm_add_le _ _
      _ = ‖z₀‖ + dist w z₀ := by rw [dist_eq_norm]
      _ ≤ ‖z₀‖ + ρ := by linarith
    have hr_sub_w : ρ ≤ r - ‖w‖ := by
      change (r - ‖z₀‖) / 2 ≤ r - ‖w‖
      change ‖w‖ ≤ ‖z₀‖ + (r - ‖z₀‖) / 2 at hw_norm_le
      linarith [hw_norm_le]
    have hw_in_closed : w ∈ Metric.closedBall 0 r := by
      rw [Metric.mem_closedBall, dist_zero_right]
      change ‖w‖ ≤ ‖z₀‖ + (r - ‖z₀‖) / 2 at hw_norm_le
      linarith [hw_norm_le, hz₀_norm]
    have h_max_w := h_max w hw_in_closed
    have h_lhs : ρ^2 * e w ≤ (r - ‖w‖)^2 * e w := by
      have hρ_sq : ρ^2 ≤ (r - ‖w‖)^2 := by
        nlinarith
      exact mul_le_mul_of_nonneg_right hρ_sq (he_nonneg w)
    have h_rhs : (r - ‖z₀‖)^2 * e z₀ = 4 * ρ^2 * e z₀ := by
      have : r - ‖z₀‖ = 2 * ρ := by dsimp [ρ]; ring
      rw [this]
      ring
    rw [h_rhs] at h_max_w
    have h_chain : ρ^2 * e w ≤ 4 * ρ^2 * e z₀ := le_trans h_lhs h_max_w
    have h_cancel : ρ^2 * e w ≤ ρ^2 * (4 * e z₀) := by
      calc ρ^2 * e w ≤ 4 * ρ^2 * e z₀ := h_chain
      _ = ρ^2 * (4 * e z₀) := by ring
    have hρ_sq_pos : 0 < ρ^2 := sq_pos_of_pos hρ_pos
    exact (mul_le_mul_iff_of_pos_left hρ_sq_pos).mp h_cancel

/-- Transfers a bound on the Heinz maximum `(r - ‖z₀‖)² e(z₀)` to a uniform bound on `closedBall 0 (r/2)`. -/
lemma heinz_transfer_to_half_ball (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z) (z₀ : ℂ) (_hz₀ : z₀ ∈ Metric.closedBall 0 r)
    (h_max : ∀ w ∈ Metric.closedBall 0 r, (r - ‖w‖)^2 * e w ≤ (r - ‖z₀‖)^2 * e z₀)
    (M_bound : (r - ‖z₀‖)^2 * e z₀ ≤ (8 / Real.pi) * ∫ w in Metric.ball 0 r, e w) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e z ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w) := by
  intro z hz
  have hz_dist : dist z 0 ≤ r / 2 := Metric.mem_closedBall.mp hz
  have hz_norm : ‖z‖ ≤ r / 2 := by rwa [dist_zero_right] at hz_dist
  have hz_in_r : z ∈ Metric.closedBall (0 : ℂ) r := by
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have h_max_z := h_max z hz_in_r
  have hr_sub_z : r / 2 ≤ r - ‖z‖ := by linarith
  have h_r2_4 : (r / 2)^2 ≤ (r - ‖z‖)^2 := by nlinarith
  have h_lhs : (r / 2)^2 * e z ≤ (r - ‖z‖)^2 * e z := mul_le_mul_of_nonneg_right h_r2_4 (he_nonneg z)
  have h_chain : (r / 2)^2 * e z ≤ (8 / Real.pi) * ∫ w in Metric.ball 0 r, e w :=
    le_trans (le_trans h_lhs h_max_z) M_bound
  have h_r2_4_eq : (r / 2)^2 = r^2 / 4 := by ring
  rw [h_r2_4_eq] at h_chain
  set E_val := ∫ w in Metric.ball 0 r, e w
  have h_r2_pos : 0 < r^2 := sq_pos_of_pos hr
  have hr_pow_eq : r^(-2 : ℝ) = (r^2)⁻¹ := by
    rw [Real.rpow_neg hr.le, Real.rpow_two]
  calc e z = ((r^2 / 4)⁻¹ * (r^2 / 4)) * e z := by
         rw [inv_mul_cancel₀ (by positivity), one_mul]
       _ = (r^2 / 4)⁻¹ * ((r^2 / 4) * e z) := by ring
       _ ≤ (r^2 / 4)⁻¹ * ((8 / Real.pi) * E_val) := mul_le_mul_of_nonneg_left h_chain (by positivity)
       _ = (4 / r^2) * (8 / Real.pi) * E_val := by ring
       _ = (32 / Real.pi) * (r^2)⁻¹ * E_val := by ring
       _ = (32 / Real.pi) * r^(-2 : ℝ) * E_val := by rw [← hr_pow_eq]

/-- Heinz radius-selection contradiction / bound when `e₀` satisfies the subharmonic disk inequality on `(0, ρ]`. -/
lemma heinz_central_value_bound_c_zero (b : ℝ) (hb : 0 ≤ b)
    (e₀ : ℝ) (he₀ : 0 < e₀) (ρ : ℝ) (hρ : 0 < ρ) (E : ℝ) (_hE : 0 ≤ E)
    (h_smv : ∀ t ∈ Set.Ioc 0 ρ, e₀ ≤ (Real.pi * t^2)⁻¹ * E + 2 * b * e₀^2 * t^2)
    (h_energy : E < Real.pi / (16 * (b + 1))) :
    (2 * ρ)^2 * e₀ ≤ (8 / Real.pi) * E := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  by_cases h_case : 2 * b * e₀ * ρ^2 ≤ 1 / 2
  · have hρ_mem : ρ ∈ Set.Ioc 0 ρ := ⟨hρ, le_refl ρ⟩
    have h_bound := h_smv ρ hρ_mem
    have h_term2 : 2 * b * e₀^2 * ρ^2 = (2 * b * e₀ * ρ^2) * e₀ := by ring
    rw [h_term2] at h_bound
    have h_le_half : (2 * b * e₀ * ρ^2) * e₀ ≤ (1 / 2) * e₀ := mul_le_mul_of_nonneg_right h_case he₀.le
    have h_half_bound : e₀ ≤ (Real.pi * ρ^2)⁻¹ * E + (1 / 2) * e₀ := le_trans h_bound (by linarith)
    have h_sub : (1 / 2) * e₀ ≤ (Real.pi * ρ^2)⁻¹ * E := by linarith
    have h_ρ2_pos : 0 < ρ^2 := sq_pos_of_pos hρ
    calc (2 * ρ)^2 * e₀ = 4 * ρ^2 * e₀ := by ring
         _ = 8 * ρ^2 * ((1 / 2) * e₀) := by ring
         _ ≤ 8 * ρ^2 * ((Real.pi * ρ^2)⁻¹ * E) := mul_le_mul_of_nonneg_left h_sub (by positivity)
         _ = 8 * ρ^2 * (Real.pi⁻¹ * (ρ^2)⁻¹ * E) := by rw [mul_inv]
         _ = (8 / Real.pi) * E := by
           have h_cancel : ρ^2 * (ρ^2)⁻¹ = 1 := mul_inv_cancel₀ h_ρ2_pos.ne'
           calc 8 * ρ^2 * (Real.pi⁻¹ * (ρ^2)⁻¹ * E) = (8 * Real.pi⁻¹ * E) * (ρ^2 * (ρ^2)⁻¹) := by ring
                _ = (8 * Real.pi⁻¹ * E) * 1 := by rw [h_cancel]
                _ = (8 / Real.pi) * E := by ring
  · push_neg at h_case
    have hb_pos : 0 < b := by
      by_contra hb_zero
      have : b = 0 := le_antisymm (not_lt.mp hb_zero) hb
      subst this
      linarith
    have h_denom_pos : 0 < 4 * b * e₀ := by positivity
    let t2 := 1 / (4 * b * e₀)
    have ht2_pos : 0 < t2 := one_div_pos.mpr h_denom_pos
    let t := Real.sqrt t2
    have ht_pos : 0 < t := Real.sqrt_pos.mpr ht2_pos
    have ht_sq : t^2 = t2 := Real.sq_sqrt ht2_pos.le
    have ht_lt_ρ : t < ρ := by
      have h_sq_lt : t^2 < ρ^2 := by
        rw [ht_sq]
        dsimp [t2]
        have : 1 / (4 * b * e₀) < ρ^2 := by
          have h_mul : 1 / 2 < (2 * b * e₀) * ρ^2 := h_case
          calc 1 / (4 * b * e₀) = (1 / 2) * (1 / (2 * b * e₀)) := by ring
               _ < ((2 * b * e₀) * ρ^2) * (1 / (2 * b * e₀)) := mul_lt_mul_of_pos_right h_mul (by positivity)
               _ = ρ^2 := by
                 have : (2 * b * e₀) ≠ 0 := by positivity
                 calc ((2 * b * e₀) * ρ^2) * (1 / (2 * b * e₀)) = ρ^2 * ((2 * b * e₀) * (1 / (2 * b * e₀))) := by ring
                      _ = ρ^2 * 1 := by rw [mul_one_div_cancel this]
                      _ = ρ^2 := mul_one _
        exact this
      have h1 : Real.sqrt (t^2) < Real.sqrt (ρ^2) := (Real.sqrt_lt_sqrt_iff (sq_nonneg t)).mpr h_sq_lt
      rw [Real.sqrt_sq ht_pos.le, Real.sqrt_sq hρ.le] at h1
      exact h1
    have ht_mem : t ∈ Set.Ioc 0 ρ := ⟨ht_pos, ht_lt_ρ.le⟩
    have h_smv_t := h_smv t ht_mem
    have h_term2 : 2 * b * e₀^2 * t^2 = (1 / 2) * e₀ := by
      rw [ht_sq]
      dsimp [t2]
      have hb_ne : b ≠ 0 := hb_pos.ne'
      have he_ne : e₀ ≠ 0 := he₀.ne'
      field_simp
      ring
    rw [h_term2] at h_smv_t
    have h_sub : (1 / 2) * e₀ ≤ (Real.pi * t^2)⁻¹ * E := by linarith
    rw [ht_sq] at h_sub
    dsimp [t2] at h_sub
    have h_false : False := by
      have hb_ne : b ≠ 0 := hb_pos.ne'
      have he_ne : e₀ ≠ 0 := he₀.ne'
      have h_eq : (Real.pi * (1 / (4 * b * e₀)))⁻¹ = 4 * b * e₀ / Real.pi := by
        field_simp
      rw [h_eq] at h_sub
      have h_cancel : (1 / 2) ≤ (4 * b / Real.pi) * E := by
        have : (1 / 2) * e₀ ≤ ((4 * b / Real.pi) * E) * e₀ := by
          calc (1 / 2) * e₀ ≤ (4 * b * e₀ / Real.pi) * E := h_sub
          _ = ((4 * b / Real.pi) * E) * e₀ := by ring
        exact (mul_le_mul_iff_of_pos_right he₀).mp this
      have h_pi_pos : 0 < Real.pi / (4 * b) := by positivity
      have h_mul_pi : (Real.pi / (4 * b)) * (1 / 2) ≤ (Real.pi / (4 * b)) * ((4 * b / Real.pi) * E) :=
        mul_le_mul_of_nonneg_left h_cancel (le_of_lt h_pi_pos)
      have h_simp : (Real.pi / (4 * b)) * ((4 * b / Real.pi) * E) = E := by
        field_simp
      rw [h_simp] at h_mul_pi
      have h_left : (Real.pi / (4 * b)) * (1 / 2) = Real.pi / (8 * b) := by ring
      rw [h_left] at h_mul_pi
      have h_lt : E < Real.pi / (8 * b) := by
        calc E < Real.pi / (16 * (b + 1)) := h_energy
        _ < Real.pi / (8 * b) := by
          have h1 : 8 * b < 16 * (b + 1) := by linarith
          have h2 : 0 < 8 * b := by linarith
          exact div_lt_div_of_pos_left hpi_pos h2 h1
      linarith
    exfalso
    exact h_false

lemma heinz_bound_general (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e₀ : ℝ) (he₀ : 0 < e₀) (ρ : ℝ) (hρ : 0 < ρ) (E : ℝ) (hE : 0 ≤ E)
    (h_smv : ∀ t ∈ Set.Ioc 0 ρ, e₀ ≤ (Real.pi * t^2)⁻¹ * E + 2 * (b + c + 1) * e₀^2 * t^2)
    (h_energy : E < Real.pi / (16 * (b + c + 2))) :
    (2 * ρ)^2 * e₀ ≤ (8 / Real.pi) * E := by
  have hb' : 0 ≤ b + c + 1 := by linarith
  have h_energy' : E < Real.pi / (16 * (b + c + 1 + 1)) := by
    have : (b + c + 1 + 1) = b + c + 2 := by ring
    rwa [this]
  exact heinz_central_value_bound_c_zero (b + c + 1) hb' e₀ he₀ ρ hρ E hE h_smv h_energy'

lemma central_value_le_of_smv_integral (v₀ t E_t : ℝ) (ht : 0 < t)
    (h_bound : Real.pi * t^2 * v₀ ≤ E_t) :
    v₀ ≤ (Real.pi * t^2)⁻¹ * E_t := by
  have ht2_pos : 0 < Real.pi * t^2 := by
    have : 0 < t^2 := sq_pos_of_pos ht
    positivity
  calc v₀ = ((Real.pi * t^2)⁻¹ * (Real.pi * t^2)) * v₀ := by
         rw [inv_mul_cancel₀ ht2_pos.ne', one_mul]
       _ = (Real.pi * t^2)⁻¹ * (Real.pi * t^2 * v₀) := by ring
       _ ≤ (Real.pi * t^2)⁻¹ * E_t := mul_le_mul_of_nonneg_left h_bound (inv_nonneg.mpr ht2_pos.le)

lemma smv_split_identity (t E_val K : ℝ) (ht : 0 < t) :
    (Real.pi * t^2)⁻¹ * (E_val + Real.pi * K * t^4 / 8) =
    (Real.pi * t^2)⁻¹ * E_val + K * t^2 / 8 := by
  have ht2_pos : 0 < Real.pi * t^2 := by
    have : 0 < t^2 := sq_pos_of_pos ht
    positivity
  have h_cancel : (Real.pi * t^2)⁻¹ * (Real.pi * K * t^4 / 8) = K * t^2 / 8 := by
    calc (Real.pi * t^2)⁻¹ * (Real.pi * K * t^4 / 8) = (Real.pi * t^2)⁻¹ * (Real.pi * t^2 * (K * t^2 / 8)) := by ring
         _ = ((Real.pi * t^2)⁻¹ * (Real.pi * t^2)) * (K * t^2 / 8) := by ring
         _ = 1 * (K * t^2 / 8) := by rw [inv_mul_cancel₀ ht2_pos.ne']
         _ = K * t^2 / 8 := one_mul _
  rw [mul_add, h_cancel]

lemma smv_leaf_bound (v₀ t E_t K : ℝ) (ht : 0 < t)
    (h_bound : Real.pi * t^2 * v₀ ≤ E_t + Real.pi * K * t^4 / 8) :
    v₀ ≤ (Real.pi * t^2)⁻¹ * E_t + K * t^2 / 8 := by
  have h1 := central_value_le_of_smv_integral v₀ t (E_t + Real.pi * K * t^4 / 8) ht h_bound
  rw [smv_split_identity t E_t K ht] at h1
  exact h1

theorem heinz_smv_step_from_mean_value
    (b c e₀ ρ E_r t : ℝ) (_hb : 0 ≤ b) (_hc : 0 ≤ c) (_he₀ : 0 < e₀)
    (ht : t ∈ Set.Ioc 0 ρ)
    (h_mv : Real.pi * t^2 * e₀ ≤ E_r + Real.pi * (16 * (b + c + 1) * e₀^2) * t^4 / 8) :
    e₀ ≤ (Real.pi * t^2)⁻¹ * E_r + 2 * (b + c + 1) * e₀^2 * t^2 := by
  have h := smv_leaf_bound e₀ t E_r (16 * (b + c + 1) * e₀^2) ht.1 h_mv
  nlinarith [h]

theorem heinz_subharmonic_modification_bound
    (r b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e : ℂ → ℝ) (_he_nonneg : ∀ z, 0 ≤ e z)
    (z₀ : ℂ) (he₀_pos : 0 < e z₀)
    (ρ : ℝ) (t : ℝ) (ht : t ∈ Set.Ioc 0 ρ)
    (_h_sub_ball : Metric.ball z₀ t ⊆ Metric.ball (0 : ℂ) r)
    (h_int_mono : (∫ w in Metric.ball z₀ t, e w) ≤ (∫ w in Metric.ball (0 : ℂ) r, e w))
    (h_subharm_mv : Real.pi * t^2 * e z₀ ≤
      (∫ w in Metric.ball z₀ t, e w) +
      Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8) :
    e z₀ ≤ (Real.pi * t^2)⁻¹ * (∫ w in Metric.ball (0 : ℂ) r, e w) +
      2 * (b + c + 1) * (e z₀)^2 * t^2 := by
  have h_mv : Real.pi * t^2 * e z₀ ≤
      (∫ w in Metric.ball (0 : ℂ) r, e w) +
      Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8 := by linarith
  exact heinz_smv_step_from_mean_value b c (e z₀) ρ
    (∫ w in Metric.ball (0 : ℂ) r, e w) t hb hc he₀_pos ht h_mv

theorem heinz_setIntegral_ball_mono
    (r t : ℝ) (z₀ : ℂ) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_int : IntegrableOn e (Metric.ball (0 : ℂ) r) volume)
    (h_sub : Metric.ball z₀ t ⊆ Metric.ball (0 : ℂ) r) :
    (∫ w in Metric.ball z₀ t, e w) ≤ (∫ w in Metric.ball (0 : ℂ) r, e w) := by
  apply MeasureTheory.setIntegral_mono_set he_int
    (Filter.Eventually.of_forall (fun w => he_nonneg w))
  exact Filter.Eventually.of_forall (fun w hw => h_sub hw)

lemma iteratedFDeriv_two_apply_eq_fderiv_eval (f : ℂ → ℝ) (z v w : ℂ)
    (hf : DifferentiableAt ℝ (fderiv ℝ f) z) :
    iteratedFDeriv ℝ 2 f z ![v, w] = fderiv ℝ (fun x => fderiv ℝ f x w) z v := by
  rw [iteratedFDeriv_succ_apply_left]
  simp only [Matrix.cons_val_zero]
  have h1 : iteratedFDeriv ℝ 1 f = fun x => (continuousMultilinearCurryFin1 ℝ ℂ ℝ).symm (fderiv ℝ f x) := by
    ext x m
    rw [iteratedFDeriv_one_apply]
    rfl
  rw [h1]
  have h_fderiv1 : fderiv ℝ (fun x => (continuousMultilinearCurryFin1 ℝ ℂ ℝ).symm (fderiv ℝ f x)) z =
      (continuousMultilinearCurryFin1 ℝ ℂ ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) z) :=
    (continuousMultilinearCurryFin1 ℝ ℂ ℝ).symm.toContinuousLinearEquiv.comp_fderiv
  have h_fderiv2 : fderiv ℝ (fun x => fderiv ℝ f x w) z =
      (ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ f) z) :=
    (((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt).comp z hf.hasFDerivAt).fderiv
  rw [h_fderiv1, h_fderiv2]
  rfl

lemma norm_sq_eq_re_im (w : ℂ) :
    ‖w‖ ^ 2 = Complex.reCLM w * Complex.reCLM w + Complex.imCLM w * Complex.imCLM w := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  rfl

lemma hasFDerivAt_clm_sq (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    HasFDerivAt (fun w : ℂ => L w * L w) ((2 * L z) • L) z := by
  have h := (L.hasFDerivAt (x := z)).mul (L.hasFDerivAt (x := z))
  convert h using 1
  ext v
  simp [two_mul]
  ring

lemma fderiv_norm_sq_sub (z₀ z : ℂ) :
    fderiv ℝ (fun w : ℂ => ‖w - z₀‖ ^ 2) z =
      (2 * Complex.reCLM (z - z₀)) • Complex.reCLM + (2 * Complex.imCLM (z - z₀)) • Complex.imCLM := by
  have h_sub : HasFDerivAt (fun w : ℂ => w - z₀) (ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).sub_const z₀
  have h_norm : HasFDerivAt (fun w : ℂ => ‖w‖ ^ 2)
      ((2 * Complex.reCLM (z - z₀)) • Complex.reCLM + (2 * Complex.imCLM (z - z₀)) • Complex.imCLM) (z - z₀) := by
    have h_eq : (fun w : ℂ => ‖w‖ ^ 2) = (fun w : ℂ => Complex.reCLM w * Complex.reCLM w + Complex.imCLM w * Complex.imCLM w) := by
      ext w; exact norm_sq_eq_re_im w
    rw [h_eq]
    exact (hasFDerivAt_clm_sq Complex.reCLM (z - z₀)).add (hasFDerivAt_clm_sq Complex.imCLM (z - z₀))
  have h_comp := h_norm.comp z h_sub
  rw [ContinuousLinearMap.comp_id] at h_comp
  exact h_comp.fderiv

lemma differentiableAt_fderiv_norm_sq_sub (z₀ z : ℂ) :
    DifferentiableAt ℝ (fderiv ℝ (fun w : ℂ => ‖w - z₀‖ ^ 2)) z := by
  have h_eq : fderiv ℝ (fun w : ℂ => ‖w - z₀‖ ^ 2) =
      fun x => (2 * Complex.reCLM (x - z₀)) • Complex.reCLM + (2 * Complex.imCLM (x - z₀)) • Complex.imCLM := by
    ext x v; rw [fderiv_norm_sq_sub]
  rw [h_eq]
  have h_sub : DifferentiableAt ℝ (fun x : ℂ => x - z₀) z := differentiableAt_id.sub_const z₀
  have h1 : DifferentiableAt ℝ (fun x : ℂ => 2 * Complex.reCLM (x - z₀)) z :=
    (Complex.reCLM.differentiableAt.comp z h_sub).const_mul 2
  have h2 : DifferentiableAt ℝ (fun x : ℂ => 2 * Complex.imCLM (x - z₀)) z :=
    (Complex.imCLM.differentiableAt.comp z h_sub).const_mul 2
  exact (h1.smul_const Complex.reCLM).add (h2.smul_const Complex.imCLM)

theorem laplacian2D_norm_sq_sub (z₀ z : ℂ) :
    laplacian2D (fun w : ℂ => ‖w - z₀‖ ^ 2) z = 4 := by
  unfold laplacian2D
  have hdiff := differentiableAt_fderiv_norm_sq_sub z₀ z
  rw [iteratedFDeriv_two_apply_eq_fderiv_eval _ z 1 1 hdiff]
  rw [iteratedFDeriv_two_apply_eq_fderiv_eval _ z Complex.I Complex.I hdiff]
  have h_eval1 : (fun x : ℂ => fderiv ℝ (fun w : ℂ => ‖w - z₀‖ ^ 2) x 1) =
      fun x => 2 * (Complex.reCLM x - Complex.reCLM z₀) := by
    ext x
    rw [fderiv_norm_sq_sub]
    simp [Complex.reCLM_apply, Complex.imCLM_apply]
  have h_evalI : (fun x : ℂ => fderiv ℝ (fun w : ℂ => ‖w - z₀‖ ^ 2) x Complex.I) =
      fun x => 2 * (Complex.imCLM x - Complex.imCLM z₀) := by
    ext x
    rw [fderiv_norm_sq_sub]
    simp [Complex.reCLM_apply, Complex.imCLM_apply]
  rw [h_eval1, h_evalI]
  have hd1 : HasFDerivAt (fun x : ℂ => 2 * (Complex.reCLM x - Complex.reCLM z₀)) ((2 : ℝ) • Complex.reCLM) z := by
    simpa using ((Complex.reCLM.hasFDerivAt (x := z)).sub_const (Complex.reCLM z₀)).const_mul 2
  have hdI : HasFDerivAt (fun x : ℂ => 2 * (Complex.imCLM x - Complex.imCLM z₀)) ((2 : ℝ) • Complex.imCLM) z := by
    simpa using ((Complex.imCLM.hasFDerivAt (x := z)).sub_const (Complex.imCLM z₀)).const_mul 2
  rw [hd1.fderiv, hdI.fderiv]
  simp [Complex.reCLM_apply, Complex.imCLM_apply]
  norm_num

lemma contDiff_norm_sq_sub (z₀ : ℂ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun w : ℂ => ‖w - z₀‖ ^ 2) := by
  have h_eq : (fun w : ℂ => ‖w - z₀‖ ^ 2) =
      fun w : ℂ => Complex.reCLM (w - z₀) * Complex.reCLM (w - z₀) +
                   Complex.imCLM (w - z₀) * Complex.imCLM (w - z₀) := by
    ext w; exact norm_sq_eq_re_im (w - z₀)
  rw [h_eq]
  have h_sub : ContDiff ℝ n (fun w : ℂ => w - z₀) := contDiff_id.sub contDiff_const
  have h_re : ContDiff ℝ n (fun w : ℂ => Complex.reCLM (w - z₀)) := Complex.reCLM.contDiff.comp h_sub
  have h_im : ContDiff ℝ n (fun w : ℂ => Complex.imCLM (w - z₀)) := Complex.imCLM.contDiff.comp h_sub
  exact (h_re.mul h_re).add (h_im.mul h_im)

lemma laplacian2D_add_on_open {f g : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) (hg : ContDiffOn ℝ 2 g s) {z : ℂ} (hz : z ∈ s) :
    laplacian2D (fun w => f w + g w) z = laplacian2D f z + laplacian2D g z := by
  unfold laplacian2D
  have h1 : iteratedFDeriv ℝ 2 (f + g) z = iteratedFDeriv ℝ 2 f z + iteratedFDeriv ℝ 2 g z := by
    rw [← iteratedFDerivWithin_of_isOpen 2 hs hz,
        ← iteratedFDerivWithin_of_isOpen 2 hs hz (f := f),
        ← iteratedFDerivWithin_of_isOpen 2 hs hz (f := g)]
    exact iteratedFDerivWithin_add_apply (hf z hz) (hg z hz) hs.uniqueDiffOn hz
  change (iteratedFDeriv ℝ 2 (f + g) z) ![1, 1] + (iteratedFDeriv ℝ 2 (f + g) z) ![Complex.I, Complex.I] = _
  rw [h1]
  simp only [ContinuousMultilinearMap.add_apply]
  ring

lemma laplacian2D_const_mul_on_open (c : ℝ) {f : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 2 f s) {z : ℂ} (hz : z ∈ s) :
    laplacian2D (fun w => c * f w) z = c * laplacian2D f z := by
  unfold laplacian2D
  have h_at : ContDiffAt ℝ (2 : ℕ) f z := hf.contDiffAt (hs.mem_nhds hz)
  have h1 : iteratedFDeriv ℝ 2 (c • f) z = c • iteratedFDeriv ℝ 2 f z :=
    iteratedFDeriv_const_smul_apply h_at
  change (iteratedFDeriv ℝ 2 (c • f) z) ![1, 1] + (iteratedFDeriv ℝ 2 (c • f) z) ![Complex.I, Complex.I] = _
  rw [h1]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem laplacian2D_quadratic_gauge_modification
    {e : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s) (he : ContDiffOn ℝ 2 e s)
    (z₀ : ℂ) (K : ℝ) {z : ℂ} (hz : z ∈ s) :
    laplacian2D (fun w => e w + (K / 4) * ‖w - z₀‖ ^ 2) z = laplacian2D e z + K := by
  have hq : ContDiffOn ℝ 2 (fun w : ℂ => ‖w - z₀‖ ^ 2) s := (contDiff_norm_sq_sub z₀ 2).contDiffOn
  have hq_mul : ContDiffOn ℝ 2 (fun w : ℂ => (K / 4) * ‖w - z₀‖ ^ 2) s := contDiffOn_const.mul hq
  rw [laplacian2D_add_on_open hs he hq_mul hz]
  rw [laplacian2D_const_mul_on_open (K / 4) hs hq hz]
  rw [laplacian2D_norm_sq_sub z₀ z]
  ring

lemma norm_polarCoord_symm_of_pos {p : ℝ × ℝ} (hp : 0 < p.1) :
    ‖Complex.polarCoord.symm p‖ = p.1 := by
  rw [Complex.norm_polarCoord_symm, _root_.abs_of_pos hp]

lemma setIntegral_norm_sq_ball_zero {t : ℝ} (ht : 0 ≤ t) :
    (∫ w in Metric.ball (0 : ℂ) t, ‖w‖ ^ 2) = Real.pi * t ^ 4 / 2 := by
  have h_meas_tgt : MeasurableSet (polarCoord.target : Set (ℝ × ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  rw [← integral_indicator isOpen_ball.measurableSet]
  rw [← Complex.integral_comp_polarCoord_symm]
  rw [← integral_indicator h_meas_tgt]
  have h_eq : polarCoord.target.indicator (fun p : ℝ × ℝ => p.1 • (Metric.ball (0 : ℂ) t).indicator (fun w => ‖w‖ ^ 2) (Complex.polarCoord.symm p)) =
      (Ioo (0 : ℝ) t ×ˢ Ioo (-Real.pi) Real.pi).indicator (fun p : ℝ × ℝ => p.1 ^ 3 * (1 : ℝ)) := by
    ext ⟨r, θ⟩
    by_cases hr0 : 0 < r
    · by_cases hθ : θ ∈ Ioo (-Real.pi) Real.pi
      · have hp_tgt : (r, θ) ∈ polarCoord.target := ⟨hr0, hθ⟩
        have h_norm : ‖Complex.polarCoord.symm (r, θ)‖ = r := norm_polarCoord_symm_of_pos hr0
        by_cases hrt : r < t
        · have hp_box : (r, θ) ∈ Ioo (0 : ℝ) t ×ˢ Ioo (-Real.pi) Real.pi := ⟨⟨hr0, hrt⟩, hθ⟩
          have hw_ball : Complex.polarCoord.symm (r, θ) ∈ Metric.ball (0 : ℂ) t := by
            rw [mem_ball, dist_zero_right, h_norm]
            exact hrt
          rw [indicator_of_mem hp_tgt, indicator_of_mem hp_box]
          dsimp only
          rw [indicator_of_mem hw_ball, h_norm, smul_eq_mul]
          ring
        · have hp_not_box : (r, θ) ∉ Ioo (0 : ℝ) t ×ˢ Ioo (-Real.pi) Real.pi := by
            intro h; exact hrt h.1.2
          have hw_not_ball : Complex.polarCoord.symm (r, θ) ∉ Metric.ball (0 : ℂ) t := by
            rw [mem_ball, dist_zero_right, h_norm]
            exact hrt
          rw [indicator_of_mem hp_tgt, indicator_of_notMem hp_not_box]
          dsimp only
          rw [indicator_of_notMem hw_not_ball, smul_zero]
      · have hp_not_tgt : (r, θ) ∉ polarCoord.target := fun h => hθ h.2
        have hp_not_box : (r, θ) ∉ Ioo (0 : ℝ) t ×ˢ Ioo (-Real.pi) Real.pi := fun h => hθ h.2
        rw [indicator_of_notMem hp_not_tgt, indicator_of_notMem hp_not_box]
    · have hp_not_tgt : (r, θ) ∉ polarCoord.target := fun h => hr0 h.1
      have hp_not_box : (r, θ) ∉ Ioo (0 : ℝ) t ×ˢ Ioo (-Real.pi) Real.pi := fun h => hr0 h.1.1
      rw [indicator_of_notMem hp_not_tgt, indicator_of_notMem hp_not_box]
  rw [h_eq, integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ)]
  rw [setIntegral_prod_mul (f := fun x : ℝ => x ^ 3) (g := fun _ : ℝ => (1 : ℝ))]
  have h_r : (∫ x in Ioo (0 : ℝ) t, x ^ 3) = t ^ 4 / 4 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht, integral_pow]
    ring
  have h_θ : (∫ y in Ioo (-Real.pi) Real.pi, (1 : ℝ)) = 2 * Real.pi := by
    have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi, intervalIntegral.integral_const]
    simp; ring
  rw [h_r, h_θ]
  ring

lemma setIntegral_norm_sq_ball (z₀ : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ w in Metric.ball z₀ t, ‖w - z₀‖ ^ 2) = Real.pi * t ^ 4 / 2 := by
  have h_pres : MeasurePreserving (fun x => z₀ + x) volume volume := measurePreserving_add_left volume z₀
  have h_emb : MeasurableEmbedding (fun x => z₀ + x) := (Homeomorph.addLeft z₀).measurableEmbedding
  have h_pre : (fun x => z₀ + x) ⁻¹' (Metric.ball z₀ t) = Metric.ball (0 : ℂ) t := by
    ext w
    simp only [Set.mem_preimage, mem_ball, dist_zero_right, dist_eq_norm]
    ring_nf
  have h := MeasureTheory.MeasurePreserving.setIntegral_preimage_emb h_pres h_emb (fun w : ℂ => ‖w - z₀‖ ^ 2) (Metric.ball z₀ t)
  rw [h_pre] at h
  have h_simp : (fun x : ℂ => ‖(z₀ + x) - z₀‖ ^ 2) = (fun x : ℂ => ‖x‖ ^ 2) := by
    ext x; simp
  rw [← h, h_simp, setIntegral_norm_sq_ball_zero ht]

theorem setIntegral_quadratic_gauge_ball (z₀ : ℂ) (K : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {e : ℂ → ℝ} (he_int : IntegrableOn e (Metric.ball z₀ t) volume) :
    (∫ w in Metric.ball z₀ t, (e w + (K / 4) * ‖w - z₀‖ ^ 2)) =
      (∫ w in Metric.ball z₀ t, e w) + Real.pi * K * t ^ 4 / 8 := by
  have h_q_cont : Continuous (fun w : ℂ => (K / 4) * ‖w - z₀‖ ^ 2) :=
    continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2)
  have h_q_int : IntegrableOn (fun w : ℂ => (K / 4) * ‖w - z₀‖ ^ 2) (Metric.ball z₀ t) volume :=
    (h_q_cont.continuousOn.integrableOn_compact (isCompact_closedBall z₀ t)).mono_set Metric.ball_subset_closedBall
  rw [integral_add he_int h_q_int]
  rw [MeasureTheory.integral_const_mul, setIntegral_norm_sq_ball z₀ ht]
  ring

lemma complex_decomp_one_I (u : ℂ) :
    u = u.re • (1 : ℂ) + u.im • Complex.I := by
  apply Complex.ext <;> simp

lemma complex_I_mul_decomp_one_I (u : ℂ) :
    Complex.I * u = (-u.im) • (1 : ℂ) + u.re • Complex.I := by
  apply Complex.ext <;> simp

lemma cmlm2_apply_add_left (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂ) ℝ)
    (x y z : ℂ) : M ![x + y, z] = M ![x, z] + M ![y, z] := by
  have h := M.map_update_add ![x, z] 0 x y
  have h1 : Function.update ![x, z] 0 (x + y) = ![x + y, z] := by
    ext i; fin_cases i <;> rfl
  have h2 : Function.update ![x, z] 0 x = ![x, z] := by
    ext i; fin_cases i <;> rfl
  have h3 : Function.update ![x, z] 0 y = ![y, z] := by
    ext i; fin_cases i <;> rfl
  rw [h1, h2, h3] at h
  exact h

lemma cmlm2_apply_add_right (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂ) ℝ)
    (x y z : ℂ) : M ![x, y + z] = M ![x, y] + M ![x, z] := by
  have h := M.map_update_add ![x, y] 1 y z
  have h1 : Function.update ![x, y] 1 (y + z) = ![x, y + z] := by
    ext i; fin_cases i <;> rfl
  have h2 : Function.update ![x, y] 1 y = ![x, y] := by
    ext i; fin_cases i <;> rfl
  have h3 : Function.update ![x, y] 1 z = ![x, z] := by
    ext i; fin_cases i <;> rfl
  rw [h1, h2, h3] at h
  exact h

lemma cmlm2_apply_smul_left (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂ) ℝ)
    (c : ℝ) (x z : ℂ) : M ![c • x, z] = c * M ![x, z] := by
  have h := M.map_update_smul ![x, z] 0 c x
  have h1 : Function.update ![x, z] 0 (c • x) = ![c • x, z] := by
    ext i; fin_cases i <;> rfl
  have h2 : Function.update ![x, z] 0 x = ![x, z] := by
    ext i; fin_cases i <;> rfl
  rw [h1, h2, smul_eq_mul] at h
  exact h

lemma cmlm2_apply_smul_right (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂ) ℝ)
    (c : ℝ) (x y : ℂ) : M ![x, c • y] = c * M ![x, y] := by
  have h := M.map_update_smul ![x, y] 1 c y
  have h1 : Function.update ![x, y] 1 (c • y) = ![x, c • y] := by
    ext i; fin_cases i <;> rfl
  have h2 : Function.update ![x, y] 1 y = ![x, y] := by
    ext i; fin_cases i <;> rfl
  rw [h1, h2, smul_eq_mul] at h
  exact h

lemma cmlm2_rotation_trace_scaling
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂ) ℝ) (u : ℂ) :
    M ![u, u] + M ![Complex.I * u, Complex.I * u] =
      ‖u‖ ^ 2 * (M ![1, 1] + M ![Complex.I, Complex.I]) := by
  have h1 : M ![u, u] = u.re ^ 2 * M ![1, 1] + u.re * u.im * (M ![1, Complex.I] + M ![Complex.I, 1]) +
      u.im ^ 2 * M ![Complex.I, Complex.I] := by
    conv_lhs => rw [complex_decomp_one_I u]
    rw [cmlm2_apply_add_left, cmlm2_apply_add_right, cmlm2_apply_add_right,
        cmlm2_apply_smul_left, cmlm2_apply_smul_left, cmlm2_apply_smul_left, cmlm2_apply_smul_left,
        cmlm2_apply_smul_right, cmlm2_apply_smul_right, cmlm2_apply_smul_right, cmlm2_apply_smul_right]
    ring
  have h2 : M ![Complex.I * u, Complex.I * u] = u.im ^ 2 * M ![1, 1] -
      u.re * u.im * (M ![1, Complex.I] + M ![Complex.I, 1]) +
      u.re ^ 2 * M ![Complex.I, Complex.I] := by
    conv_lhs => rw [complex_I_mul_decomp_one_I u]
    rw [cmlm2_apply_add_left, cmlm2_apply_add_right, cmlm2_apply_add_right,
        cmlm2_apply_smul_left, cmlm2_apply_smul_left, cmlm2_apply_smul_left, cmlm2_apply_smul_left,
        cmlm2_apply_smul_right, cmlm2_apply_smul_right, cmlm2_apply_smul_right, cmlm2_apply_smul_right]
    ring
  have h_norm : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [norm_sq_eq_re_im u]
    simp [sq]
  rw [h1, h2, h_norm]
  ring

lemma polar_curve_hasDerivAt_rho (z₀ : ℂ) (ρ θ : ℝ) :
    HasDerivAt (fun r : ℝ => z₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
      (Complex.exp (Complex.I * (θ : ℂ))) ρ := by
  have h1 : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 ρ := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun r : ℝ => (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
      (1 * Complex.exp (Complex.I * (θ : ℂ))) ρ := h1.mul_const _
  rw [one_mul] at h2
  exact h2.const_add z₀

lemma polar_curve_hasDerivAt_theta (z₀ : ℂ) (ρ θ : ℝ) :
    HasDerivAt (fun t : ℝ => z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ)))
      ((ρ : ℂ) * (Complex.I * Complex.exp (Complex.I * (θ : ℂ)))) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 θ := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ)) (Complex.I * 1) θ := h1.const_mul Complex.I
  rw [mul_one] at h2
  have h3 : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ)))
      (Complex.exp (Complex.I * (θ : ℂ)) * Complex.I) θ := h2.cexp
  rw [mul_comm (Complex.exp _) Complex.I] at h3
  exact (h3.const_mul (ρ : ℂ)).const_add z₀

lemma hasDerivAt_fderiv_eval_rho (g : ℂ → ℝ) (z₀ : ℂ) (ρ θ : ℝ) (v : ℂ)
    (hg : DifferentiableAt ℝ (fderiv ℝ g) (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    HasDerivAt (fun r : ℝ => fderiv ℝ g (z₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) v)
      ((iteratedFDeriv ℝ 2 g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        ![Complex.exp (Complex.I * (θ : ℂ)), v]) ρ := by
  let ζ := z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  let eθ := Complex.exp (Complex.I * (θ : ℂ))
  have h_eval : HasFDerivAt (fun w : ℂ => fderiv ℝ g w v)
      (((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ g) ζ))) ζ :=
    ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt).comp ζ hg.hasFDerivAt
  have h_comp : HasDerivAt ((fun w : ℂ => fderiv ℝ g w v) ∘ (fun r : ℝ => z₀ + (r : ℂ) * eθ))
      ((((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ g) ζ))) eθ) ρ :=
    h_eval.comp_hasDerivAt ρ (polar_curve_hasDerivAt_rho z₀ ρ θ)
  have h_eq : (((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ g) ζ))) eθ =
      (iteratedFDeriv ℝ 2 g ζ) ![eθ, v] := by
    rw [iteratedFDeriv_two_apply_eq_fderiv_eval g ζ eθ v hg, h_eval.fderiv]
  rwa [h_eq] at h_comp

lemma hasDerivAt_rho_mul_fderiv_radial (g : ℂ → ℝ) (z₀ : ℂ) (ρ θ : ℝ)
    (hg : DifferentiableAt ℝ (fderiv ℝ g) (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    HasDerivAt (fun r : ℝ => r * fderiv ℝ g (z₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Complex.exp (Complex.I * (θ : ℂ))))
      (fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ))) +
        ρ * (iteratedFDeriv ℝ 2 g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          ![Complex.exp (Complex.I * (θ : ℂ)), Complex.exp (Complex.I * (θ : ℂ))]) ρ := by
  have h1 : HasDerivAt (fun r : ℝ => r) 1 ρ := hasDerivAt_id ρ
  have h2 := hasDerivAt_fderiv_eval_rho g z₀ ρ θ (Complex.exp (Complex.I * (θ : ℂ))) hg
  have h_mul := h1.fun_mul h2
  simpa only [one_mul] using h_mul

lemma hasDerivAt_fderiv_eval_theta (g : ℂ → ℝ) (z₀ : ℂ) (ρ θ : ℝ) (v : ℂ)
    (hg : DifferentiableAt ℝ (fderiv ℝ g) (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    HasDerivAt (fun t : ℝ => fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))) v)
      (ρ * (iteratedFDeriv ℝ 2 g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        ![Complex.I * Complex.exp (Complex.I * (θ : ℂ)), v]) θ := by
  let ζ := z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  let eθ := Complex.exp (Complex.I * (θ : ℂ))
  have h_eval : HasFDerivAt (fun w : ℂ => fderiv ℝ g w v)
      (((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ g) ζ))) ζ :=
    ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt).comp ζ hg.hasFDerivAt
  have h_comp : HasDerivAt ((fun w : ℂ => fderiv ℝ g w v) ∘ (fun t : ℝ => z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))))
      ((((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ g) ζ))) ((ρ : ℂ) * (Complex.I * eθ))) θ :=
    h_eval.comp_hasDerivAt θ (polar_curve_hasDerivAt_theta z₀ ρ θ)
  have h_eq : (((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ g) ζ))) ((ρ : ℂ) * (Complex.I * eθ)) =
      ρ * (iteratedFDeriv ℝ 2 g ζ) ![Complex.I * eθ, v] := by
    have h_smul : (ρ : ℂ) * (Complex.I * eθ) = ρ • (Complex.I * eθ) := by
      rw [Complex.real_smul]
    rw [h_smul, ContinuousLinearMap.map_smul, smul_eq_mul,
        iteratedFDeriv_two_apply_eq_fderiv_eval g ζ (Complex.I * eθ) v hg, h_eval.fderiv]
  rwa [h_eq] at h_comp

lemma exp_I_mul_ofReal_decomp (t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ)) = Real.cos t • (1 : ℂ) + Real.sin t • Complex.I := by
  rw [mul_comm Complex.I (t : ℂ), Complex.exp_mul_I]
  apply Complex.ext <;> simp

lemma I_mul_exp_I_mul_ofReal_decomp (t : ℝ) :
    Complex.I * Complex.exp (Complex.I * (t : ℂ)) = (-Real.sin t) • (1 : ℂ) + Real.cos t • Complex.I := by
  rw [exp_I_mul_ofReal_decomp t]
  apply Complex.ext <;> simp

lemma hasDerivAt_fderiv_angular (g : ℂ → ℝ) (z₀ : ℂ) (ρ θ : ℝ)
    (hg : DifferentiableAt ℝ (fderiv ℝ g) (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    HasDerivAt (fun t : ℝ => fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ)))
        (Complex.I * Complex.exp (Complex.I * (t : ℂ))))
      (-fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ))) +
        ρ * (iteratedFDeriv ℝ 2 g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          ![Complex.I * Complex.exp (Complex.I * (θ : ℂ)), Complex.I * Complex.exp (Complex.I * (θ : ℂ))]) θ := by
  let ζ := z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  let eθ := Complex.exp (Complex.I * (θ : ℂ))
  have h_fn : (fun t : ℝ => fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ)))
        (Complex.I * Complex.exp (Complex.I * (t : ℂ)))) =
      (fun t : ℝ => (-Real.sin t) * fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))) 1 +
        Real.cos t * fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (t : ℂ))) Complex.I) := by
    ext t
    rw [I_mul_exp_I_mul_ofReal_decomp t, ContinuousLinearMap.map_add,
        ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
  rw [h_fn]
  have hd1 := (Real.hasDerivAt_sin θ).fun_neg.fun_mul (hasDerivAt_fderiv_eval_theta g z₀ ρ θ 1 hg)
  have hd2 := (Real.hasDerivAt_cos θ).fun_mul (hasDerivAt_fderiv_eval_theta g z₀ ρ θ Complex.I hg)
  have hd := hd1.fun_add hd2
  have h_deriv_eq :
      (-Real.cos θ * fderiv ℝ g ζ 1 + -Real.sin θ * (ρ * (iteratedFDeriv ℝ 2 g ζ) ![Complex.I * eθ, 1])) +
      (-Real.sin θ * fderiv ℝ g ζ Complex.I + Real.cos θ * (ρ * (iteratedFDeriv ℝ 2 g ζ) ![Complex.I * eθ, Complex.I])) =
      -fderiv ℝ g ζ eθ + ρ * (iteratedFDeriv ℝ 2 g ζ) ![Complex.I * eθ, Complex.I * eθ] := by
    have hf1 : fderiv ℝ g ζ eθ = Real.cos θ * fderiv ℝ g ζ 1 + Real.sin θ * fderiv ℝ g ζ Complex.I := by
      dsimp [eθ]
      rw [exp_I_mul_ofReal_decomp θ, ContinuousLinearMap.map_add,
          ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    have hf2 : (iteratedFDeriv ℝ 2 g ζ) ![Complex.I * eθ, Complex.I * eθ] =
        (-Real.sin θ) * (iteratedFDeriv ℝ 2 g ζ) ![Complex.I * eθ, 1] +
        Real.cos θ * (iteratedFDeriv ℝ 2 g ζ) ![Complex.I * eθ, Complex.I] := by
      change (iteratedFDeriv ℝ 2 g ζ) ![Complex.I * eθ, Complex.I * Complex.exp (Complex.I * (θ : ℂ))] = _
      rw [I_mul_exp_I_mul_ofReal_decomp θ, cmlm2_apply_add_right,
          cmlm2_apply_smul_right, cmlm2_apply_smul_right]
    rw [hf1, hf2]
    ring
  dsimp [ζ, eθ] at h_deriv_eq
  rwa [h_deriv_eq] at hd

lemma polar_laplacian_identity (g : ℂ → ℝ) (z₀ : ℂ) (ρ θ : ℝ) :
    (fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ))) +
      ρ * (iteratedFDeriv ℝ 2 g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        ![Complex.exp (Complex.I * (θ : ℂ)), Complex.exp (Complex.I * (θ : ℂ))]) +
    (-fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ))) +
      ρ * (iteratedFDeriv ℝ 2 g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        ![Complex.I * Complex.exp (Complex.I * (θ : ℂ)), Complex.I * Complex.exp (Complex.I * (θ : ℂ))]) =
    ρ * laplacian2D g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  let ζ := z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  let eθ := Complex.exp (Complex.I * (θ : ℂ))
  have h_rot := cmlm2_rotation_trace_scaling (iteratedFDeriv ℝ 2 g ζ) eθ
  have h_norm : ‖eθ‖ = 1 := by
    dsimp [eθ]
    rw [mul_comm Complex.I (θ : ℂ)]
    exact Complex.norm_exp_ofReal_mul_I θ
  rw [h_norm, one_pow, one_mul] at h_rot
  unfold laplacian2D
  change (fderiv ℝ g ζ eθ + ρ * (iteratedFDeriv ℝ 2 g ζ) ![eθ, eθ]) +
    (-fderiv ℝ g ζ eθ + ρ * (iteratedFDeriv ℝ 2 g ζ) ![Complex.I * eθ, Complex.I * eθ]) =
    ρ * ((iteratedFDeriv ℝ 2 g ζ) ![1, 1] + (iteratedFDeriv ℝ 2 g ζ) ![Complex.I, Complex.I])
  rw [← h_rot]
  ring

lemma polar_point_mem_ball {z₀ : ℂ} {r t ρ : ℝ} (θ : ℝ)
    (h_sub : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r)
    (hρ : |ρ| ≤ t) :
    z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∈ Metric.ball (0 : ℂ) r := by
  apply h_sub
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_comm Complex.I (θ : ℂ), Complex.norm_exp_ofReal_mul_I, mul_one]
  exact hρ

lemma continuous_polar_map (z₀ : ℂ) :
    Continuous (fun p : ℝ × ℝ => z₀ + (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ))) := by
  refine continuous_const.add ?_
  refine (Complex.continuous_ofReal.comp continuous_fst).mul ?_
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))

lemma continuous_exp_I_snd :
    Continuous (fun p : ℝ × ℝ => Complex.exp (Complex.I * (p.2 : ℂ))) :=
  Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))

lemma continuous_I_mul_exp_I_snd :
    Continuous (fun p : ℝ × ℝ => Complex.I * Complex.exp (Complex.I * (p.2 : ℂ))) :=
  continuous_const.mul continuous_exp_I_snd

lemma continuousOn_fderiv_of_contDiffOn
    (g : ℂ → ℝ) {s : Set ℂ} (hs : IsOpen s) (hg : ContDiffOn ℝ 2 g s) :
    ContinuousOn (fderiv ℝ g) s := by
  have h1 : ContDiffOn ℝ 1 g s := hg.of_le (by norm_num)
  have h_within : ContinuousOn (fderivWithin ℝ g s) s :=
    h1.continuousOn_fderivWithin hs.uniqueDiffOn le_rfl
  exact h_within.congr (fun z hz => (fderivWithin_of_isOpen hs hz).symm)

lemma continuousOn_iteratedFDeriv_two_of_contDiffOn
    (g : ℂ → ℝ) {s : Set ℂ} (hs : IsOpen s) (hg : ContDiffOn ℝ 2 g s) :
    ContinuousOn (iteratedFDeriv ℝ 2 g) s := by
  have h2_within : ContinuousOn (iteratedFDerivWithin ℝ 2 g s) s :=
    hg.continuousOn_iteratedFDerivWithin (by norm_num) hs.uniqueDiffOn
  exact h2_within.congr (fun z hz => (iteratedFDerivWithin_of_isOpen 2 hs hz).symm)

lemma differentiableAt_fderiv_of_contDiffOn
    (g : ℂ → ℝ) {s : Set ℂ} (hs : IsOpen s) (hg : ContDiffOn ℝ 2 g s)
    {z : ℂ} (hz : z ∈ s) :
    DifferentiableAt ℝ (fderiv ℝ g) z := by
  have h_within : ContDiffOn ℝ 1 (fderivWithin ℝ g s) s :=
    (contDiffOn_succ_iff_fderivWithin (n := 1) hs.uniqueDiffOn).mp hg |>.2.2
  have h_diff_within : DifferentiableWithinAt ℝ (fderivWithin ℝ g s) s z :=
    (h_within z hz).differentiableWithinAt (by norm_num)
  have h_diff_at : DifferentiableAt ℝ (fderivWithin ℝ g s) z :=
    h_diff_within.differentiableAt (hs.mem_nhds hz)
  have h_eq : fderivWithin ℝ g s =ᶠ[nhds z] fderiv ℝ g := by
    filter_upwards [hs.mem_nhds hz] with w hw
    exact fderivWithin_of_isOpen hs hw
  exact h_diff_at.congr_of_eventuallyEq h_eq.symm

lemma differentiableAt_of_contDiffOn
    (g : ℂ → ℝ) {s : Set ℂ} (hs : IsOpen s) (hg : ContDiffOn ℝ 2 g s)
    {z : ℂ} (hz : z ∈ s) :
    DifferentiableAt ℝ g z :=
  (hg.contDiffAt (hs.mem_nhds hz)).differentiableAt (by norm_num)

lemma hasDerivAt_g_polar_rho (g : ℂ → ℝ) (z₀ : ℂ) (ρ θ : ℝ)
    (hg : DifferentiableAt ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    HasDerivAt (fun r : ℝ => g (z₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ)))) ρ := by
  have h_comp : HasDerivAt (g ∘ (fun r : ℝ => z₀ + (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ)))) ρ :=
    hg.hasFDerivAt.comp_hasDerivAt ρ (polar_curve_hasDerivAt_rho z₀ ρ θ)
  exact h_comp

lemma mapsTo_polar_box {z₀ : ℂ} {r t s : ℝ}
    (h_sub : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r)
    (hst : s ≤ t) :
    Set.MapsTo (fun p : ℝ × ℝ => z₀ + (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ)))
      (Icc 0 s ×ˢ Icc (-Real.pi) Real.pi) (Metric.ball (0 : ℂ) r) := by
  intro p hp
  apply polar_point_mem_ball p.2 h_sub
  rw [_root_.abs_of_nonneg hp.1.1]
  exact hp.1.2.trans hst

lemma continuousOn_fderiv_polar_eval (g : ℂ → ℝ) {z₀ : ℂ} {r t s : ℝ}
    (hg : ContDiffOn ℝ 2 g (Metric.ball (0 : ℂ) r))
    (h_sub : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r)
    (hst : s ≤ t)
    {v : ℝ × ℝ → ℂ} (hv : Continuous v) :
    ContinuousOn (fun p : ℝ × ℝ =>
        fderiv ℝ g (z₀ + (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ))) (v p))
      (Icc 0 s ×ˢ Icc (-Real.pi) Real.pi) := by
  have h_fderiv : ContinuousOn (fun p : ℝ × ℝ =>
      fderiv ℝ g (z₀ + (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ))))
      (Icc 0 s ×ˢ Icc (-Real.pi) Real.pi) :=
    (continuousOn_fderiv_of_contDiffOn g isOpen_ball hg).comp
      (continuous_polar_map z₀).continuousOn (mapsTo_polar_box h_sub hst)
  exact h_fderiv.clm_apply hv.continuousOn

lemma continuousOn_iteratedFDeriv_two_polar_eval (g : ℂ → ℝ) {z₀ : ℂ} {r t s : ℝ}
    (hg : ContDiffOn ℝ 2 g (Metric.ball (0 : ℂ) r))
    (h_sub : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r)
    (hst : s ≤ t)
    {v : ℝ × ℝ → ℂ} (hv : Continuous v) :
    ContinuousOn (fun p : ℝ × ℝ =>
        (iteratedFDeriv ℝ 2 g (z₀ + (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ)))) ![v p, v p])
      (Icc 0 s ×ˢ Icc (-Real.pi) Real.pi) := by
  have h_iter : ContinuousOn (fun p : ℝ × ℝ =>
      iteratedFDeriv ℝ 2 g (z₀ + (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ))))
      (Icc 0 s ×ˢ Icc (-Real.pi) Real.pi) :=
    (continuousOn_iteratedFDeriv_two_of_contDiffOn g isOpen_ball hg).comp
      (continuous_polar_map z₀).continuousOn (mapsTo_polar_box h_sub hst)
  have h_vec : Continuous (fun p : ℝ × ℝ => (![v p, v p] : Fin 2 → ℂ)) :=
    continuous_pi (fun i => by fin_cases i <;> exact hv)
  exact continuous_eval.comp_continuousOn (h_iter.prodMk h_vec.continuousOn)

lemma continuousOn_fst_section {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    {f : α × β → γ} {s : Set α} {t : Set β} (hf : ContinuousOn f (s ×ˢ t)) {x : α} (hx : x ∈ s) :
    ContinuousOn (fun y => f (x, y)) t :=
  hf.comp (Continuous.prodMk_right x).continuousOn (fun _ hy => ⟨hx, hy⟩)

lemma continuousOn_snd_section {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    {f : α × β → γ} {s : Set α} {t : Set β} (hf : ContinuousOn f (s ×ˢ t)) {y : β} (hy : y ∈ t) :
    ContinuousOn (fun x => f (x, y)) s :=
  hf.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ hx => ⟨hx, hy⟩)

lemma intervalIntegral_swap_of_continuousOn
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {f : ℝ → ℝ → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc c d)) :
    (∫ x in a..b, ∫ y in c..d, f x y) = ∫ y in c..d, ∫ x in a..b, f x y := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  simp_rw [intervalIntegral.integral_of_le hcd, intervalIntegral.integral_of_le hab]
  have h_sub : Ioc a b ×ˢ Ioc c d ⊆ Icc a b ×ˢ Icc c d :=
     prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have h_int : Integrable (Function.uncurry f) ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set h_sub
  exact integral_integral_swap h_int

lemma exp_I_mul_pi_eq_neg_pi :
    Complex.exp (Complex.I * (Real.pi : ℂ)) = Complex.exp (Complex.I * ((-Real.pi : ℝ) : ℂ)) := by
  rw [mul_comm Complex.I (Real.pi : ℂ), Complex.exp_mul_I,
      mul_comm Complex.I ((-Real.pi : ℝ) : ℂ), Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  simp [Complex.cos_pi, Complex.sin_pi]

lemma intervalIntegral_angular_deriv_eq_zero
    (g : ℂ → ℝ) {z₀ : ℂ} {r t ρ : ℝ}
    (hg : ContDiffOn ℝ 2 g (Metric.ball (0 : ℂ) r))
    (h_sub : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r)
    (hρ0 : 0 ≤ ρ) (hρt : ρ ≤ t) :
    (∫ θ in (-Real.pi)..Real.pi,
      (-fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ))) +
        ρ * (iteratedFDeriv ℝ 2 g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          ![Complex.I * Complex.exp (Complex.I * (θ : ℂ)), Complex.I * Complex.exp (Complex.I * (θ : ℂ))])) = 0 := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have h_cont_box : ContinuousOn (fun p : ℝ × ℝ =>
      -fderiv ℝ g (z₀ + (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ))) (Complex.exp (Complex.I * (p.2 : ℂ))) +
        p.1 * (iteratedFDeriv ℝ 2 g (z₀ + (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ))))
          ![Complex.I * Complex.exp (Complex.I * (p.2 : ℂ)), Complex.I * Complex.exp (Complex.I * (p.2 : ℂ))])
      (Icc 0 t ×ˢ Icc (-Real.pi) Real.pi) :=
    (continuousOn_fderiv_polar_eval g hg h_sub le_rfl continuous_exp_I_snd).neg.add
      (continuous_fst.continuousOn.mul (continuousOn_iteratedFDeriv_two_polar_eval g hg h_sub le_rfl continuous_I_mul_exp_I_snd))
  have h_cont_θ : ContinuousOn (fun θ : ℝ =>
      -fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ))) +
        ρ * (iteratedFDeriv ℝ 2 g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          ![Complex.I * Complex.exp (Complex.I * (θ : ℂ)), Complex.I * Complex.exp (Complex.I * (θ : ℂ))])
      (uIcc (-Real.pi) Real.pi) := by
    rw [uIcc_of_le hpi]
    exact continuousOn_fst_section h_cont_box ⟨hρ0, hρt⟩
  have h_deriv : ∀ θ ∈ uIcc (-Real.pi) Real.pi,
      HasDerivAt (fun x : ℝ => fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (x : ℂ)))
        (Complex.I * Complex.exp (Complex.I * (x : ℂ))))
      (-fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ))) +
        ρ * (iteratedFDeriv ℝ 2 g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          ![Complex.I * Complex.exp (Complex.I * (θ : ℂ)), Complex.I * Complex.exp (Complex.I * (θ : ℂ))]) θ := by
    intro θ _
    apply hasDerivAt_fderiv_angular g z₀ ρ θ
    apply differentiableAt_fderiv_of_contDiffOn g isOpen_ball hg
    apply polar_point_mem_ball θ h_sub
    rw [_root_.abs_of_nonneg hρ0]
    exact hρt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_cont_θ.intervalIntegrable]
  rw [exp_I_mul_pi_eq_neg_pi, sub_self]

lemma intervalIntegral_radial_deriv_eq_double_integral_laplacian
    (g : ℂ → ℝ) {z₀ : ℂ} {r t s : ℝ}
    (hg : ContDiffOn ℝ 2 g (Metric.ball (0 : ℂ) r))
    (h_sub : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r)
    (hs0 : 0 ≤ s) (hst : s ≤ t) :
    s * (∫ θ in (-Real.pi)..Real.pi,
      fderiv ℝ g (z₀ + (s : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ)))) =
    ∫ ρ in (0 : ℝ)..s, ∫ θ in (-Real.pi)..Real.pi,
      ρ * laplacian2D g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  let A : ℝ → ℝ → ℝ := fun ρ θ =>
    fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ))) +
      ρ * (iteratedFDeriv ℝ 2 g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        ![Complex.exp (Complex.I * (θ : ℂ)), Complex.exp (Complex.I * (θ : ℂ))]
  let B : ℝ → ℝ → ℝ := fun ρ θ =>
    -fderiv ℝ g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ))) +
      ρ * (iteratedFDeriv ℝ 2 g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        ![Complex.I * Complex.exp (Complex.I * (θ : ℂ)), Complex.I * Complex.exp (Complex.I * (θ : ℂ))]
  have hA_cont : ContinuousOn (Function.uncurry A) (Icc 0 s ×ˢ Icc (-Real.pi) Real.pi) :=
    (continuousOn_fderiv_polar_eval g hg h_sub hst continuous_exp_I_snd).add
      (continuous_fst.continuousOn.mul (continuousOn_iteratedFDeriv_two_polar_eval g hg h_sub hst continuous_exp_I_snd))
  have hB_cont : ContinuousOn (Function.uncurry B) (Icc 0 s ×ˢ Icc (-Real.pi) Real.pi) :=
    (continuousOn_fderiv_polar_eval g hg h_sub hst continuous_exp_I_snd).neg.add
      (continuous_fst.continuousOn.mul (continuousOn_iteratedFDeriv_two_polar_eval g hg h_sub hst continuous_I_mul_exp_I_snd))
  have h_inner_eq : ∀ ρ ∈ uIcc 0 s,
      (∫ θ in (-Real.pi)..Real.pi, ρ * laplacian2D g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      (∫ θ in (-Real.pi)..Real.pi, A ρ θ) := by
    intro ρ hρ
    rw [uIcc_of_le hs0] at hρ
    have h_pt : (∫ θ in (-Real.pi)..Real.pi, ρ * laplacian2D g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        (∫ θ in (-Real.pi)..Real.pi, (A ρ θ + B ρ θ)) := by
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      exact (polar_laplacian_identity g z₀ ρ θ).symm
    rw [h_pt]
    have hA_int : IntervalIntegrable (A ρ) volume (-Real.pi) Real.pi := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hpi]
      exact continuousOn_fst_section hA_cont hρ
    have hB_int : IntervalIntegrable (B ρ) volume (-Real.pi) Real.pi := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hpi]
      exact continuousOn_fst_section hB_cont hρ
    rw [intervalIntegral.integral_add hA_int hB_int]
    have hB_zero : (∫ θ in (-Real.pi)..Real.pi, B ρ θ) = 0 :=
      intervalIntegral_angular_deriv_eq_zero g hg h_sub hρ.1 (hρ.2.trans hst)
    rw [hB_zero, add_zero]
  rw [intervalIntegral.integral_congr h_inner_eq]
  rw [intervalIntegral_swap_of_continuousOn hs0 hpi hA_cont]
  have h_outer_eq : ∀ θ ∈ uIcc (-Real.pi) Real.pi,
      (∫ ρ in (0 : ℝ)..s, A ρ θ) =
      s * fderiv ℝ g (z₀ + (s : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ))) := by
    intro θ hθ
    rw [uIcc_of_le hpi] at hθ
    have hA_θ_int : IntervalIntegrable (fun ρ => A ρ θ) volume 0 s := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hs0]
      exact continuousOn_snd_section hA_cont hθ
    have h_deriv : ∀ ρ ∈ uIcc 0 s,
        HasDerivAt (fun x : ℝ => x * fderiv ℝ g (z₀ + (x : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
          (Complex.exp (Complex.I * (θ : ℂ)))) (A ρ θ) ρ := by
      intro ρ hρ
      rw [uIcc_of_le hs0] at hρ
      apply hasDerivAt_rho_mul_fderiv_radial g z₀ ρ θ
      apply differentiableAt_fderiv_of_contDiffOn g isOpen_ball hg
      apply polar_point_mem_ball θ h_sub
      rw [_root_.abs_of_nonneg hρ.1]
      exact hρ.2.trans hst
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv hA_θ_int]
    simp
  rw [intervalIntegral.integral_congr h_outer_eq, intervalIntegral.integral_const_mul]

lemma intervalIntegral_radial_deriv_nonneg_of_subharmonic
    (g : ℂ → ℝ) {z₀ : ℂ} {r t s : ℝ}
    (hg : ContDiffOn ℝ 2 g (Metric.ball (0 : ℂ) r))
    (h_sub : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r)
    (h_subharm : ∀ w ∈ Metric.closedBall z₀ t, 0 ≤ laplacian2D g w)
    (hs0 : 0 ≤ s) (hst : s ≤ t) :
    0 ≤ ∫ θ in (-Real.pi)..Real.pi,
      fderiv ℝ g (z₀ + (s : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ))) := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rcases eq_or_lt_of_le hs0 with rfl | hs_pos
  · have h_fn : (fun θ : ℝ => fderiv ℝ g (z₀ + ((0 : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Complex.exp (Complex.I * (θ : ℂ)))) =
      (fun θ : ℝ => Real.cos θ * fderiv ℝ g z₀ 1 + Real.sin θ * fderiv ℝ g z₀ Complex.I) := by
      ext θ
      simp only [Complex.ofReal_zero, zero_mul, add_zero]
      rw [exp_I_mul_ofReal_decomp θ, ContinuousLinearMap.map_add,
          ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    rw [h_fn]
    have h_deriv : ∀ θ ∈ uIcc (-Real.pi) Real.pi,
        HasDerivAt (fun x : ℝ => Real.sin x * fderiv ℝ g z₀ 1 - Real.cos x * fderiv ℝ g z₀ Complex.I)
          (Real.cos θ * fderiv ℝ g z₀ 1 + Real.sin θ * fderiv ℝ g z₀ Complex.I) θ := by
      intro θ _
      have hd1 := (Real.hasDerivAt_sin θ).mul_const (fderiv ℝ g z₀ 1)
      have hd2 := (Real.hasDerivAt_cos θ).mul_const (fderiv ℝ g z₀ Complex.I)
      convert hd1.sub hd2 using 1
      ring
    have h_cont : Continuous (fun θ : ℝ => Real.cos θ * fderiv ℝ g z₀ 1 + Real.sin θ * fderiv ℝ g z₀ Complex.I) :=
      (Real.continuous_cos.mul continuous_const).add (Real.continuous_sin.mul continuous_const)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv (h_cont.intervalIntegrable _ _)]
    simp [Real.sin_pi, Real.cos_pi]
  · have h_id := intervalIntegral_radial_deriv_eq_double_integral_laplacian g hg h_sub hs0 hst
    have h_rhs_nonneg : 0 ≤ ∫ ρ in (0 : ℝ)..s, ∫ θ in (-Real.pi)..Real.pi,
        ρ * laplacian2D g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
      apply intervalIntegral.integral_nonneg hs0
      intro ρ hρ
      apply intervalIntegral.integral_nonneg hpi
      intro θ _
      apply mul_nonneg hρ.1
      apply h_subharm
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, _root_.abs_of_nonneg hρ.1, mul_comm Complex.I (θ : ℂ), Complex.norm_exp_ofReal_mul_I, mul_one]
      exact hρ.2.trans hst
    rw [← h_id] at h_rhs_nonneg
    exact nonneg_of_mul_nonneg_right h_rhs_nonneg hs_pos

lemma circle_average_ge_center_of_subharmonic
    (g : ℂ → ℝ) {z₀ : ℂ} {r t ρ : ℝ}
    (hg : ContDiffOn ℝ 2 g (Metric.ball (0 : ℂ) r))
    (h_sub : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r)
    (h_subharm : ∀ w ∈ Metric.closedBall z₀ t, 0 ≤ laplacian2D g w)
    (hρ0 : 0 ≤ ρ) (hρt : ρ ≤ t) :
    2 * Real.pi * g z₀ ≤
      ∫ θ in (-Real.pi)..Real.pi, g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  let F : ℝ → ℝ → ℝ := fun s θ =>
    fderiv ℝ g (z₀ + (s : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) (Complex.exp (Complex.I * (θ : ℂ)))
  have hF_cont : ContinuousOn (Function.uncurry F) (Icc 0 ρ ×ˢ Icc (-Real.pi) Real.pi) :=
    continuousOn_fderiv_polar_eval g hg h_sub hρt continuous_exp_I_snd
  have h_nonneg : 0 ≤ ∫ s in (0 : ℝ)..ρ, ∫ θ in (-Real.pi)..Real.pi, F s θ := by
    apply intervalIntegral.integral_nonneg hρ0
    intro s hs
    exact intervalIntegral_radial_deriv_nonneg_of_subharmonic g hg h_sub h_subharm hs.1 (hs.2.trans hρt)
  rw [intervalIntegral_swap_of_continuousOn hρ0 hpi hF_cont] at h_nonneg
  have h_inner : ∀ θ ∈ uIcc (-Real.pi) Real.pi,
      (∫ s in (0 : ℝ)..ρ, F s θ) =
      g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - g z₀ := by
    intro θ hθ
    rw [uIcc_of_le hpi] at hθ
    have hF_θ_int : IntervalIntegrable (fun s => F s θ) volume 0 ρ := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hρ0]
      exact continuousOn_snd_section hF_cont hθ
    have h_deriv : ∀ s ∈ uIcc 0 ρ,
        HasDerivAt (fun x : ℝ => g (z₀ + (x : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) (F s θ) s := by
      intro s hs
      rw [uIcc_of_le hρ0] at hs
      apply hasDerivAt_g_polar_rho g z₀ s θ
      apply differentiableAt_of_contDiffOn g isOpen_ball hg
      apply polar_point_mem_ball θ h_sub
      rw [_root_.abs_of_nonneg hs.1]
      exact hs.2.trans hρt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv hF_θ_int]
    simp
  rw [intervalIntegral.integral_congr h_inner] at h_nonneg
  have hg_cont : ContinuousOn (fun θ : ℝ => g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (uIcc (-Real.pi) Real.pi) := by
    rw [uIcc_of_le hpi]
    have h_box : ContinuousOn (fun p : ℝ × ℝ => g (z₀ + (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ))))
        (Icc 0 t ×ˢ Icc (-Real.pi) Real.pi) :=
      hg.continuousOn.comp (continuous_polar_map z₀).continuousOn (mapsTo_polar_box h_sub le_rfl)
    exact continuousOn_fst_section h_box ⟨hρ0, hρt⟩
  rw [intervalIntegral.integral_sub hg_cont.intervalIntegrable (intervalIntegrable_const)] at h_nonneg
  rw [intervalIntegral.integral_const] at h_nonneg
  simp only [sub_neg_eq_add, smul_eq_mul] at h_nonneg
  linarith

lemma polarCoord_symm_eq_exp (ρ θ : ℝ) :
    (Complex.polarCoord.symm (ρ, θ) : ℂ) = (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
  rw [Complex.polarCoord_symm_apply, mul_comm Complex.I (θ : ℂ), Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]

lemma setIntegral_ball_eq_polar_iterated
    (g : ℂ → ℝ) (z₀ : ℂ) {r t : ℝ}
    (hg : ContDiffOn ℝ 2 g (Metric.ball (0 : ℂ) r))
    (h_sub : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r)
    (ht : 0 ≤ t) :
    (∫ w in Metric.ball z₀ t, g w) =
      ∫ ρ in (0 : ℝ)..t, ρ * ∫ θ in (-Real.pi)..Real.pi,
        g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have h_meas_tgt : MeasurableSet (polarCoord.target : Set (ℝ × ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have h_pres : MeasurePreserving (fun x => z₀ + x) volume volume := measurePreserving_add_left volume z₀
  have h_emb : MeasurableEmbedding (fun x => z₀ + x) := (Homeomorph.addLeft z₀).measurableEmbedding
  have h_pre : (fun x => z₀ + x) ⁻¹' (Metric.ball z₀ t) = Metric.ball (0 : ℂ) t := by
    ext w
    simp only [Set.mem_preimage, mem_ball, dist_zero_right, dist_eq_norm]
    ring_nf
  have h_shift := MeasureTheory.MeasurePreserving.setIntegral_preimage_emb h_pres h_emb g (Metric.ball z₀ t)
  rw [h_pre] at h_shift
  rw [← h_shift]
  rw [← MeasureTheory.integral_indicator isOpen_ball.measurableSet]
  rw [← Complex.integral_comp_polarCoord_symm]
  rw [← MeasureTheory.integral_indicator h_meas_tgt]
  have h_eq : polarCoord.target.indicator
      (fun p : ℝ × ℝ => p.1 • (Metric.ball (0 : ℂ) t).indicator (fun x => g (z₀ + x)) (Complex.polarCoord.symm p)) =
      (Ioo (0 : ℝ) t ×ˢ Ioo (-Real.pi) Real.pi).indicator
        (fun p : ℝ × ℝ => p.1 * g (z₀ + (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ)))) := by
    ext ⟨ρ, θ⟩
    by_cases hρ0 : 0 < ρ
    · by_cases hθ : θ ∈ Ioo (-Real.pi) Real.pi
      · have hp_tgt : (ρ, θ) ∈ polarCoord.target := ⟨hρ0, hθ⟩
        have h_norm : ‖Complex.polarCoord.symm (ρ, θ)‖ = ρ := norm_polarCoord_symm_of_pos hρ0
        by_cases hρt : ρ < t
        · have hp_box : (ρ, θ) ∈ Ioo (0 : ℝ) t ×ˢ Ioo (-Real.pi) Real.pi := ⟨⟨hρ0, hρt⟩, hθ⟩
          have hw_ball : Complex.polarCoord.symm (ρ, θ) ∈ Metric.ball (0 : ℂ) t := by
            rw [mem_ball, dist_zero_right, h_norm]
            exact hρt
          rw [indicator_of_mem hp_tgt, indicator_of_mem hp_box]
          dsimp only
          rw [indicator_of_mem hw_ball, smul_eq_mul, polarCoord_symm_eq_exp]
        · have hp_not_box : (ρ, θ) ∉ Ioo (0 : ℝ) t ×ˢ Ioo (-Real.pi) Real.pi := fun h => hρt h.1.2
          have hw_not_ball : Complex.polarCoord.symm (ρ, θ) ∉ Metric.ball (0 : ℂ) t := by
            rw [mem_ball, dist_zero_right, h_norm]
            exact hρt
          rw [indicator_of_mem hp_tgt, indicator_of_notMem hp_not_box]
          dsimp only
          rw [indicator_of_notMem hw_not_ball, smul_zero]
      · have hp_not_tgt : (ρ, θ) ∉ polarCoord.target := fun h => hθ h.2
        have hp_not_box : (ρ, θ) ∉ Ioo (0 : ℝ) t ×ˢ Ioo (-Real.pi) Real.pi := fun h => hθ h.2
        rw [indicator_of_notMem hp_not_tgt, indicator_of_notMem hp_not_box]
    · have hp_not_tgt : (ρ, θ) ∉ polarCoord.target := fun h => hρ0 h.1
      have hp_not_box : (ρ, θ) ∉ Ioo (0 : ℝ) t ×ˢ Ioo (-Real.pi) Real.pi := fun h => hρ0 h.1.1
      rw [indicator_of_notMem hp_not_tgt, indicator_of_notMem hp_not_box]
  rw [h_eq, MeasureTheory.integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ)]
  have h_cont_prod : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 * g (z₀ + (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ))))
      (Icc 0 t ×ˢ Icc (-Real.pi) Real.pi) :=
    continuous_fst.continuousOn.mul
      (hg.continuousOn.comp (continuous_polar_map z₀).continuousOn (mapsTo_polar_box h_sub le_rfl))
  have h_int_on : IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * g (z₀ + (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ))))
      (Ioo (0 : ℝ) t ×ˢ Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (h_cont_prod.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [setIntegral_prod _ h_int_on]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht]
  refine intervalIntegral.integral_congr (fun ρ _ => ?_)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hpi,
      ← intervalIntegral.integral_const_mul]

lemma subharmonic_solid_ball_mean_value_of_circle_average
    (g : ℂ → ℝ) (z₀ : ℂ) {r t : ℝ}
    (hg : ContDiffOn ℝ 2 g (Metric.ball (0 : ℂ) r))
    (h_sub : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r)
    (ht : 0 ≤ t)
    (h_circ : ∀ ρ ∈ Icc 0 t,
      2 * Real.pi * g z₀ ≤
        ∫ θ in (-Real.pi)..Real.pi, g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    Real.pi * t ^ 2 * g z₀ ≤ ∫ w in Metric.ball z₀ t, g w := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [setIntegral_ball_eq_polar_iterated g z₀ hg h_sub ht]
  have h_lhs : Real.pi * t ^ 2 * g z₀ = ∫ ρ in (0 : ℝ)..t, ρ * (2 * Real.pi * g z₀) := by
    rw [intervalIntegral.integral_mul_const, integral_id]
    ring
  rw [h_lhs]
  rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht]
  have h_cont_prod : ContinuousOn (fun p : ℝ × ℝ =>
      p.1 * g (z₀ + (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ))))
      (Icc 0 t ×ˢ Icc (-Real.pi) Real.pi) :=
    continuous_fst.continuousOn.mul
      (hg.continuousOn.comp (continuous_polar_map z₀).continuousOn (mapsTo_polar_box h_sub le_rfl))
  have h_int_prod : Integrable (fun p : ℝ × ℝ =>
      p.1 * g (z₀ + (p.1 : ℂ) * Complex.exp (Complex.I * (p.2 : ℂ))))
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (h_cont_prod.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have h_int_fst : Integrable (fun ρ : ℝ => ∫ θ in Ioc (-Real.pi) Real.pi,
      ρ * g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) (volume.restrict (Ioc 0 t)) :=
    h_int_prod.integral_prod_left
  have h_int_rhs : IntegrableOn (fun ρ : ℝ => ρ * ∫ θ in (-Real.pi)..Real.pi,
      g (z₀ + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) (Ioc 0 t) volume := by
    refine h_int_fst.congr (Filter.Eventually.of_forall (fun ρ => ?_))
    dsimp only
    rw [← intervalIntegral.integral_of_le hpi, intervalIntegral.integral_const_mul]
  have h_int_lhs : IntegrableOn (fun ρ : ℝ => ρ * (2 * Real.pi * g z₀)) (Ioc 0 t) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    exact (continuous_id.mul continuous_const).intervalIntegrable 0 t
  apply setIntegral_mono_on h_int_lhs h_int_rhs measurableSet_Ioc
  intro ρ hρ
  exact mul_le_mul_of_nonneg_left (h_circ ρ ⟨hρ.1.le, hρ.2⟩) hρ.1.le

/-- 2D Solid-Ball Subharmonic Mean-Value Inequality:
If `g : ℂ → ℝ` is $C^2$ on `ball 0 r` with `closedBall z₀ t ⊆ ball 0 r`, `t ≥ 0`,
and `0 ≤ laplacian2D g` on `closedBall z₀ t`, then `π t² g(z₀) ≤ ∫_{B(z₀,t)} g`. -/
theorem subharmonic_solid_ball_mean_value_inequality
    (g : ℂ → ℝ) (z₀ : ℂ) {r t : ℝ}
    (hg : ContDiffOn ℝ 2 g (Metric.ball (0 : ℂ) r))
    (h_sub : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r)
    (ht : 0 ≤ t)
    (h_subharm : ∀ w ∈ Metric.closedBall z₀ t, 0 ≤ laplacian2D g w) :
    Real.pi * t ^ 2 * g z₀ ≤ ∫ w in Metric.ball z₀ t, g w := by
  apply subharmonic_solid_ball_mean_value_of_circle_average g z₀ hg h_sub ht
  intro ρ hρ
  exact circle_average_ge_center_of_subharmonic g hg h_sub h_subharm hρ.1 hρ.2

/-- Unconditional 2D quadratic-gauge subharmonic mean-value bound for `c = 0`:
for a $C^2$ function `e ≥ 0` satisfying `Δe ≥ -b e²` on `ball 0 r` and `e(w) ≤ 4 e(z₀)` on `closedBall z₀ ρ`,
modifying `e` by `K |w - z₀|² / 4` with `K = 16(b+1)e(z₀)²` yields
`π t² e(z₀) ≤ ∫_{B(z₀,t)} e + π K t⁴ / 8` for all `t ∈ (0, ρ]`. -/
theorem subharmonic_quadratic_mean_value_bound_c_zero
    (r b : ℝ) (hb : 0 ≤ b)
    (e : ℂ → ℝ) (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (he_subharm : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 ≤ laplacian2D e z)
    (z₀ : ℂ) (_he₀_pos : 0 < e z₀)
    (ρ : ℝ) (t : ℝ) (ht : t ∈ Set.Ioc 0 ρ)
    (h_sub : Metric.closedBall z₀ ρ ⊆ Metric.ball (0 : ℂ) r)
    (h_bound : ∀ w ∈ Metric.closedBall z₀ ρ, e w ≤ 4 * e z₀) :
    Real.pi * t^2 * e z₀ ≤
      (∫ w in Metric.ball z₀ t, e w) +
      Real.pi * (16 * (b + 1) * (e z₀)^2) * t^4 / 8 := by
  let K := 16 * (b + 1) * (e z₀)^2
  let g : ℂ → ℝ := fun w => e w + (K / 4) * ‖w - z₀‖ ^ 2
  have hg_center : g z₀ = e z₀ := by dsimp [g]; simp
  have hg_diff : ContDiffOn ℝ 2 g (Metric.ball (0 : ℂ) r) :=
    he_diff.add ((contDiff_const.mul (contDiff_norm_sq_sub z₀ 2)).contDiffOn)
  have ht_sub_ρ : Metric.closedBall z₀ t ⊆ Metric.closedBall z₀ ρ :=
    Metric.closedBall_subset_closedBall ht.2
  have ht_sub_ball : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r :=
    ht_sub_ρ.trans h_sub
  have hg_subharm : ∀ w ∈ Metric.closedBall z₀ t, 0 ≤ laplacian2D g w := by
    intro w hw
    have hw_ball : w ∈ Metric.ball (0 : ℂ) r := ht_sub_ball hw
    have hw_ρ : w ∈ Metric.closedBall z₀ ρ := ht_sub_ρ hw
    rw [laplacian2D_quadratic_gauge_modification isOpen_ball he_diff z₀ K hw_ball]
    have h_lap_e := he_subharm w hw_ball
    have h_ew_le : e w ≤ 4 * e z₀ := h_bound w hw_ρ
    have h_ew_nonneg : 0 ≤ e w := he_nonneg w
    have h_sq_le : (e w) ^ 2 ≤ 16 * (e z₀) ^ 2 := by nlinarith
    have h_b_sq : b * (e w) ^ 2 ≤ 16 * b * (e z₀) ^ 2 := by nlinarith
    dsimp [K]
    nlinarith [sq_nonneg (e z₀)]
  have h_mv := subharmonic_solid_ball_mean_value_inequality g z₀ hg_diff ht_sub_ball ht.1.le hg_subharm
  rw [hg_center] at h_mv
  have he_int : IntegrableOn e (Metric.ball z₀ t) volume :=
    (he_cont.integrableOn_compact (isCompact_closedBall (0 : ℂ) r)).mono_set
      (Metric.ball_subset_closedBall.trans (ht_sub_ball.trans Metric.ball_subset_closedBall))
  rw [setIntegral_quadratic_gauge_ball z₀ K ht.1.le he_int] at h_mv
  exact h_mv

/-- Unconditional Scalar Mean-Value Inequality for `c = 0` (`Δ e ≥ -b e²`). -/
theorem scalar_mean_value_inequality_c_zero
    (b : ℝ) (hb : 0 ≤ b) :
    let η := Real.pi / (16 * (b + 2))
    let C := 32 / Real.pi
    0 < η ∧ 0 < C ∧
    ∀ (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ),
      (∀ z, 0 ≤ e z) →
      ContinuousOn e (Metric.closedBall 0 r) →
      ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r) →
      (∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 ≤ laplacian2D e z) →
      (∫ w in Metric.ball (0 : ℂ) r, e w) < η →
      (∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2), e z ≤ C * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w)) := by
  intro η C
  refine ⟨by positivity, by positivity, ?_⟩
  intro r hr e he_nonneg he_cont he_diff he_subharm he_int z hz
  by_cases h_zero : (∫ w in Metric.ball (0 : ℂ) r, e w) = 0
  · have he_z_zero := mvi_branch_zero r hr e he_nonneg he_cont h_zero z hz
    rw [he_z_zero, h_zero]
    simp
  · have h_pos : 0 < ∫ w in Metric.ball (0 : ℂ) r, e w :=
      lt_of_le_of_ne (setIntegral_nonneg isOpen_ball.measurableSet (fun w _ => he_nonneg w)) (Ne.symm h_zero)
    rcases heinz_maximum_exists r hr e he_cont with ⟨z₀, hz₀_closed, h_max⟩
    by_cases hM : (r - ‖z₀‖)^2 * e z₀ ≤ (8 / Real.pi) * ∫ w in Metric.ball 0 r, e w
    · exact heinz_transfer_to_half_ball r hr e he_nonneg z₀ hz₀_closed h_max hM z hz
    · push_neg at hM
      have ⟨hz₀_ball, he₀_pos⟩ := heinz_maximum_interior r hr e he_nonneg h_pos z₀ hz₀_closed h_max
      let ρ := (r - ‖z₀‖) / 2
      have hz₀_norm : ‖z₀‖ < r := by
        have := Metric.mem_ball.mp hz₀_ball
        rwa [dist_zero_right] at this
      have hρ_pos : 0 < ρ := by
        change 0 < (r - ‖z₀‖) / 2
        linarith [hz₀_norm]
      have ⟨h_sub, h_bound⟩ := heinz_ball_subset_and_bound r z₀ hz₀_ball e he_nonneg h_max
      have h_contra : (2 * ρ)^2 * e z₀ ≤ (8 / Real.pi) * ∫ w in Metric.ball 0 r, e w := by
        apply heinz_bound_general b 0 hb (le_refl 0) (e z₀) he₀_pos ρ hρ_pos
          (∫ w in Metric.ball 0 r, e w) h_pos.le
        · intro t ht
          have h_sub_ball : Metric.ball z₀ t ⊆ Metric.ball (0 : ℂ) r :=
            (Metric.ball_subset_ball ht.2).trans (Metric.ball_subset_closedBall.trans h_sub)
          have he_int_on : IntegrableOn e (Metric.ball (0 : ℂ) r) volume :=
            (he_cont.integrableOn_compact (isCompact_closedBall (0 : ℂ) r)).mono_set Metric.ball_subset_closedBall
          have h_int_mono : (∫ w in Metric.ball z₀ t, e w) ≤ (∫ w in Metric.ball (0 : ℂ) r, e w) :=
            heinz_setIntegral_ball_mono r t z₀ e he_nonneg he_int_on h_sub_ball
          have h_subharm_mv : Real.pi * t^2 * e z₀ ≤
              (∫ w in Metric.ball z₀ t, e w) +
              Real.pi * (16 * (b + 0 + 1) * (e z₀)^2) * t^4 / 8 := by
            rw [add_zero]
            exact subharmonic_quadratic_mean_value_bound_c_zero r b hb e he_nonneg he_cont he_diff
              he_subharm z₀ he₀_pos ρ t ht h_sub h_bound
          exact heinz_subharmonic_modification_bound r b 0 hb (le_refl 0) e he_nonneg z₀ he₀_pos ρ t ht
            h_sub_ball h_int_mono h_subharm_mv
        · simpa [η] using he_int
      have h_2ρ : 2 * ρ = r - ‖z₀‖ := by dsimp [ρ]; ring
      rw [h_2ρ] at h_contra
      linarith

/-- Unconditional 2D quadratic-gauge subharmonic mean-value bound in the large-center regime `1 / 4 ≤ e z₀`:
when `1 / 4 ≤ e z₀` and `e w ≤ 4 * e z₀`, we have `e w ≤ 16 * (e z₀)²` on `closedBall z₀ ρ`, so
`-b * (e w)² - c * (e w) ≥ -(b + c) * 16 * (e z₀)²`, and modifying `e` by `K |w - z₀|² / 4` with
`K = 16(b+c+1)e(z₀)²` makes `g` subharmonic on `closedBall z₀ t` (Zero-sorry). -/
theorem subharmonic_quadratic_mean_value_bound_of_one_fourth_le
    (r b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e : ℂ → ℝ) (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (he_subharm : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z)
    (z₀ : ℂ) (he₀_ge : 1 / 4 ≤ e z₀)
    (ρ : ℝ) (t : ℝ) (ht : t ∈ Set.Ioc 0 ρ)
    (h_sub : Metric.closedBall z₀ ρ ⊆ Metric.ball (0 : ℂ) r)
    (h_bound : ∀ w ∈ Metric.closedBall z₀ ρ, e w ≤ 4 * e z₀) :
    Real.pi * t^2 * e z₀ ≤
      (∫ w in Metric.ball z₀ t, e w) +
      Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8 := by
  let K := 16 * (b + c + 1) * (e z₀)^2
  let g : ℂ → ℝ := fun w => e w + (K / 4) * ‖w - z₀‖ ^ 2
  have hg_center : g z₀ = e z₀ := by dsimp [g]; simp
  have hg_diff : ContDiffOn ℝ 2 g (Metric.ball (0 : ℂ) r) :=
    he_diff.add ((contDiff_const.mul (contDiff_norm_sq_sub z₀ 2)).contDiffOn)
  have ht_sub_ρ : Metric.closedBall z₀ t ⊆ Metric.closedBall z₀ ρ :=
    Metric.closedBall_subset_closedBall ht.2
  have ht_sub_ball : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r :=
    ht_sub_ρ.trans h_sub
  have hg_subharm : ∀ w ∈ Metric.closedBall z₀ t, 0 ≤ laplacian2D g w := by
    intro w hw
    have hw_ball : w ∈ Metric.ball (0 : ℂ) r := ht_sub_ball hw
    have hw_ρ : w ∈ Metric.closedBall z₀ ρ := ht_sub_ρ hw
    rw [laplacian2D_quadratic_gauge_modification isOpen_ball he_diff z₀ K hw_ball]
    have h_lap_e := he_subharm w hw_ball
    have h_ew_le : e w ≤ 4 * e z₀ := h_bound w hw_ρ
    have h_ew_nonneg : 0 ≤ e w := he_nonneg w
    have h_sq_le : (e w) ^ 2 ≤ 16 * (e z₀) ^ 2 := by nlinarith
    have h_b_sq : b * (e w) ^ 2 ≤ 16 * b * (e z₀) ^ 2 := by nlinarith
    have h_lin_le : e w ≤ 16 * (e z₀) ^ 2 := by nlinarith
    have h_c_lin : c * e w ≤ 16 * c * (e z₀) ^ 2 := by nlinarith
    dsimp [K]
    nlinarith [sq_nonneg (e z₀)]
  have h_mv := subharmonic_solid_ball_mean_value_inequality g z₀ hg_diff ht_sub_ball ht.1.le hg_subharm
  rw [hg_center] at h_mv
  have he_int : IntegrableOn e (Metric.ball z₀ t) volume :=
    (he_cont.integrableOn_compact (isCompact_closedBall (0 : ℂ) r)).mono_set
      (Metric.ball_subset_closedBall.trans (ht_sub_ball.trans Metric.ball_subset_closedBall))
  rw [setIntegral_quadratic_gauge_ball z₀ K ht.1.le he_int] at h_mv
  exact h_mv

/-- Subharmonic quadratic mean-value bound when `e` is superharmonic or harmonic up to `-b e(w)²`
(i.e. `∀ w ∈ closedBall z₀ t, -b * (e w)^2 ≤ laplacian2D e w`, which holds whenever `c = 0` or `e = 0`) (`0 sorryAx`). -/
theorem subharmonic_quadratic_mean_value_bound_of_quad_subharm
    (r b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e : ℂ → ℝ) (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (z₀ : ℂ) (he₀_pos : 0 < e z₀)
    (ρ : ℝ) (t : ℝ) (ht : t ∈ Set.Ioc 0 ρ)
    (h_sub : Metric.closedBall z₀ ρ ⊆ Metric.ball (0 : ℂ) r)
    (h_bound : ∀ w ∈ Metric.closedBall z₀ ρ, e w ≤ 4 * e z₀)
    (h_quad : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 ≤ laplacian2D e z) :
    Real.pi * t^2 * e z₀ ≤
      (∫ w in Metric.ball z₀ t, e w) +
      Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8 := by
  have h0 := subharmonic_quadratic_mean_value_bound_c_zero r b hb e he_nonneg he_cont he_diff
    h_quad z₀ he₀_pos ρ t ht h_sub h_bound
  have h_extra : 0 ≤ Real.pi * (16 * c * (e z₀)^2) * t^4 / 8 := by
    have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    have ht4 : 0 ≤ t^4 := by positivity
    positivity
  linarith

/-- Subharmonic quadratic mean-value bound when the Laplacian lower bound `-4 * (b + c + 1) * (e z₀)^2 ≤ laplacian2D e w`
holds on `closedBall z₀ t` (`0 sorryAx`). -/
theorem subharmonic_quadratic_mean_value_bound_of_laplacian_lb
    (r b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e : ℂ → ℝ) (_he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (z₀ : ℂ) (_he₀_pos : 0 < e z₀)
    (ρ : ℝ) (t : ℝ) (ht : t ∈ Set.Ioc 0 ρ)
    (h_sub : Metric.closedBall z₀ ρ ⊆ Metric.ball (0 : ℂ) r)
    (h_lb : ∀ w ∈ Metric.closedBall z₀ t, -4 * (b + c + 1) * (e z₀)^2 ≤ laplacian2D e w) :
    Real.pi * t^2 * e z₀ ≤
      (∫ w in Metric.ball z₀ t, e w) +
      Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8 := by
  let K := 16 * (b + c + 1) * (e z₀)^2
  let g : ℂ → ℝ := fun w => e w + (K / 4) * ‖w - z₀‖ ^ 2
  have hg_center : g z₀ = e z₀ := by dsimp [g]; simp
  have hg_diff : ContDiffOn ℝ 2 g (Metric.ball (0 : ℂ) r) :=
    he_diff.add ((contDiff_const.mul (contDiff_norm_sq_sub z₀ 2)).contDiffOn)
  have ht_sub_ρ : Metric.closedBall z₀ t ⊆ Metric.closedBall z₀ ρ :=
    Metric.closedBall_subset_closedBall ht.2
  have ht_sub_ball : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r :=
    ht_sub_ρ.trans h_sub
  have hg_subharm : ∀ w ∈ Metric.closedBall z₀ t, 0 ≤ laplacian2D g w := by
    intro w hw
    have hw_ball : w ∈ Metric.ball (0 : ℂ) r := ht_sub_ball hw
    rw [laplacian2D_quadratic_gauge_modification isOpen_ball he_diff z₀ K hw_ball]
    have h_lap := h_lb w hw
    dsimp [K]
    nlinarith [sq_nonneg (e z₀)]
  have h_mv := subharmonic_solid_ball_mean_value_inequality g z₀ hg_diff ht_sub_ball ht.1.le hg_subharm
  rw [hg_center] at h_mv
  have he_int : IntegrableOn e (Metric.ball z₀ t) volume :=
    (he_cont.integrableOn_compact (isCompact_closedBall (0 : ℂ) r)).mono_set
      (Metric.ball_subset_closedBall.trans (ht_sub_ball.trans Metric.ball_subset_closedBall))
  rw [setIntegral_quadratic_gauge_ball z₀ K ht.1.le he_int] at h_mv
  exact h_mv

/-- Subharmonic quadratic mean-value bound when the sharp Laplacian lower bound
`-16 * (b + c + 1) * (e z₀)^2 ≤ laplacian2D e w` holds on `closedBall z₀ t` (`0 sorryAx`). -/
theorem subharmonic_quadratic_mean_value_bound_of_laplacian_lb_sixteen
    (r b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e : ℂ → ℝ) (_he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (z₀ : ℂ) (_he₀_pos : 0 < e z₀)
    (ρ : ℝ) (t : ℝ) (ht : t ∈ Set.Ioc 0 ρ)
    (h_sub : Metric.closedBall z₀ ρ ⊆ Metric.ball (0 : ℂ) r)
    (h_lb : ∀ w ∈ Metric.closedBall z₀ t, -16 * (b + c + 1) * (e z₀)^2 ≤ laplacian2D e w) :
    Real.pi * t^2 * e z₀ ≤
      (∫ w in Metric.ball z₀ t, e w) +
      Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8 := by
  let K := 16 * (b + c + 1) * (e z₀)^2
  let g : ℂ → ℝ := fun w => e w + (K / 4) * ‖w - z₀‖ ^ 2
  have hg_center : g z₀ = e z₀ := by dsimp [g]; simp
  have hg_diff : ContDiffOn ℝ 2 g (Metric.ball (0 : ℂ) r) :=
    he_diff.add ((contDiff_const.mul (contDiff_norm_sq_sub z₀ 2)).contDiffOn)
  have ht_sub_ρ : Metric.closedBall z₀ t ⊆ Metric.closedBall z₀ ρ :=
    Metric.closedBall_subset_closedBall ht.2
  have ht_sub_ball : Metric.closedBall z₀ t ⊆ Metric.ball (0 : ℂ) r :=
    ht_sub_ρ.trans h_sub
  have hg_subharm : ∀ w ∈ Metric.closedBall z₀ t, 0 ≤ laplacian2D g w := by
    intro w hw
    have hw_ball : w ∈ Metric.ball (0 : ℂ) r := ht_sub_ball hw
    rw [laplacian2D_quadratic_gauge_modification isOpen_ball he_diff z₀ K hw_ball]
    have h_lap := h_lb w hw
    dsimp [K]
    linarith
  have h_mv := subharmonic_solid_ball_mean_value_inequality g z₀ hg_diff ht_sub_ball ht.1.le hg_subharm
  rw [hg_center] at h_mv
  have he_int : IntegrableOn e (Metric.ball z₀ t) volume :=
    (he_cont.integrableOn_compact (isCompact_closedBall (0 : ℂ) r)).mono_set
      (Metric.ball_subset_closedBall.trans (ht_sub_ball.trans Metric.ball_subset_closedBall))
  rw [setIntegral_quadratic_gauge_ball z₀ K ht.1.le he_int] at h_mv
  exact h_mv

/-- Subharmonic quadratic mean-value bound whenever `c ≤ 4 * (c + 1) * e z₀` (`0 sorryAx`,
simultaneously generalizing `c = 0` and `1 / 4 ≤ e z₀`). -/
theorem subharmonic_quadratic_mean_value_bound_of_c_le_mul_e0
    (r b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e : ℂ → ℝ) (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (he_subharm : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z)
    (z₀ : ℂ) (he₀_pos : 0 < e z₀)
    (hc_le : c ≤ 4 * (c + 1) * e z₀)
    (ρ : ℝ) (t : ℝ) (ht : t ∈ Set.Ioc 0 ρ)
    (h_sub : Metric.closedBall z₀ ρ ⊆ Metric.ball (0 : ℂ) r)
    (h_bound : ∀ w ∈ Metric.closedBall z₀ ρ, e w ≤ 4 * e z₀) :
    Real.pi * t^2 * e z₀ ≤
      (∫ w in Metric.ball z₀ t, e w) +
      Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8 := by
  apply subharmonic_quadratic_mean_value_bound_of_laplacian_lb_sixteen r b c hb hc e he_nonneg he_cont he_diff
    z₀ he₀_pos ρ t ht h_sub
  intro w hw
  have ht_sub_ρ : Metric.closedBall z₀ t ⊆ Metric.closedBall z₀ ρ :=
    Metric.closedBall_subset_closedBall ht.2
  have hw_ρ : w ∈ Metric.closedBall z₀ ρ := ht_sub_ρ hw
  have hw_ball : w ∈ Metric.ball (0 : ℂ) r := h_sub hw_ρ
  have h_lap := he_subharm w hw_ball
  have hw_le : e w ≤ 4 * e z₀ := h_bound w hw_ρ
  have hw_nonneg : 0 ≤ e w := he_nonneg w
  have h_sq_le : (e w)^2 ≤ 16 * (e z₀)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hw_le) (by linarith : 0 ≤ e w + 4 * e z₀)]
  have hb_mul : b * (e w)^2 ≤ 16 * b * (e z₀)^2 := by
    have := mul_le_mul_of_nonneg_left h_sq_le hb
    linarith
  have hc_mul1 : c * e w ≤ 4 * c * e z₀ := by
    have := mul_le_mul_of_nonneg_left hw_le hc
    linarith
  have hc_mul2 : 4 * c * e z₀ ≤ 16 * (c + 1) * (e z₀)^2 := by
    have := mul_le_mul_of_nonneg_right hc_le (by linarith : 0 ≤ 4 * e z₀)
    linarith
  linarith

/-- Subharmonic quadratic mean-value bound when the solid-ball mean-value inequality
`Real.pi * t^2 * e z₀ ≤ ∫ w in Metric.ball z₀ t, e w` holds directly (`0 sorryAx`). -/
theorem subharmonic_quadratic_mean_value_bound_of_solid_ball_mv
    (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e : ℂ → ℝ) (z₀ : ℂ) (t : ℝ)
    (h_mv : Real.pi * t^2 * e z₀ ≤ ∫ w in Metric.ball z₀ t, e w) :
    Real.pi * t^2 * e z₀ ≤
      (∫ w in Metric.ball z₀ t, e w) +
      Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8 := by
  have h_extra : 0 ≤ Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8 := by
    have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    have ht4 : 0 ≤ t^4 := by positivity
    positivity
  linarith

/-- Subharmonic quadratic mean-value bound in the large-radius / large-center regime
`1 ≤ 2 * (b + c + 1) * e z₀ * t^2` (`0 sorryAx`). -/
theorem subharmonic_quadratic_mean_value_bound_of_large_radius
    (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e : ℂ → ℝ) (he_nonneg : ∀ z, 0 ≤ e z)
    (z₀ : ℂ) (he₀_pos : 0 < e z₀) (t : ℝ)
    (h_large : 1 ≤ 2 * (b + c + 1) * e z₀ * t^2) :
    Real.pi * t^2 * e z₀ ≤
      (∫ w in Metric.ball z₀ t, e w) +
      Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8 := by
  have h_int_nonneg : 0 ≤ ∫ w in Metric.ball z₀ t, e w :=
    setIntegral_nonneg isOpen_ball.measurableSet (fun w _ => he_nonneg w)
  have h_pi_pos : 0 ≤ Real.pi * t^2 * e z₀ := by
    have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    have ht2 : 0 ≤ t^2 := sq_nonneg t
    positivity
  have h_prod : (Real.pi * t^2 * e z₀) * 1 ≤
      (Real.pi * t^2 * e z₀) * (2 * (b + c + 1) * e z₀ * t^2) :=
    mul_le_mul_of_nonneg_left h_large h_pi_pos
  have h_alg : (Real.pi * t^2 * e z₀) * (2 * (b + c + 1) * e z₀ * t^2) =
      Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8 := by ring
  linarith

/-- Subharmonic quadratic mean-value bound when `e` is classically subharmonic (`0 ≤ laplacian2D e w`)
on `Metric.closedBall z₀ t` (`0 sorryAx`). -/
theorem subharmonic_quadratic_mean_value_bound_of_laplacian_nonneg
    (r b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e : ℂ → ℝ) (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (z₀ : ℂ) (he₀_pos : 0 < e z₀)
    (ρ : ℝ) (t : ℝ) (ht : t ∈ Set.Ioc 0 ρ)
    (h_sub : Metric.closedBall z₀ ρ ⊆ Metric.ball (0 : ℂ) r)
    (h_lap_nonneg : ∀ w ∈ Metric.closedBall z₀ t, 0 ≤ laplacian2D e w) :
    Real.pi * t^2 * e z₀ ≤
      (∫ w in Metric.ball z₀ t, e w) +
      Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8 := by
  apply subharmonic_quadratic_mean_value_bound_of_laplacian_lb r b c hb hc e he_nonneg he_cont he_diff
    z₀ he₀_pos ρ t ht h_sub
  intro w hw
  have h0 : 0 ≤ 4 * (b + c + 1) * (e z₀)^2 := by positivity
  linarith [h_lap_nonneg w hw]

/-- Subharmonic mean-value inequality on concentric interior disks `ball z₀ t` around a Heinz maximum `z₀`:
for a $C^2$ function `e` satisfying `Δe ≥ -b e² - c e` on `ball 0 r` and `e(w) ≤ 4 e(z₀)` on `closedBall z₀ ρ`,
modifying `e` by the quadratic gauge `K |w - z₀|² / 4` with `K = 16(b+c+1)e(z₀)²` yields the 2D solid-ball
mean-value bound `π t² e(z₀) ≤ ∫_{B(z₀,t)} e + π K t⁴ / 8`. -/
theorem subharmonic_quadratic_mean_value_bound
    (r b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e : ℂ → ℝ) (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (he_subharm : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z)
    (z₀ : ℂ) (he₀_pos : 0 < e z₀)
    (ρ : ℝ) (t : ℝ) (ht : t ∈ Set.Ioc 0 ρ)
    (h_sub : Metric.closedBall z₀ ρ ⊆ Metric.ball (0 : ℂ) r)
    (h_bound : ∀ w ∈ Metric.closedBall z₀ ρ, e w ≤ 4 * e z₀)
    (h_cases : c = 0 ∨ 1 / 4 ≤ e z₀ ∨ c ≤ 4 * (c + 1) * e z₀ ∨
      1 ≤ 2 * (b + c + 1) * e z₀ * t^2 ∨
      (Real.pi * t^2 * e z₀ ≤ ∫ w in Metric.ball z₀ t, e w) ∨
      (∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 ≤ laplacian2D e z) ∨
      (∀ w ∈ Metric.closedBall z₀ t, 0 ≤ laplacian2D e w) ∨
      (∀ w ∈ Metric.closedBall z₀ t, -4 * (b + c + 1) * (e z₀)^2 ≤ laplacian2D e w) ∨
      (∀ w ∈ Metric.closedBall z₀ t, -16 * (b + c + 1) * (e z₀)^2 ≤ laplacian2D e w)) :
    Real.pi * t^2 * e z₀ ≤
      (∫ w in Metric.ball z₀ t, e w) +
      Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8 := by
  rcases h_cases with rfl | he₀_ge | hc_le | h_large | h_mv | h_quad | h_lap_nonneg | h_lb | h_lb16
  · have h_subharm0 : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 ≤ laplacian2D e z := by
      intro z hz
      have h := he_subharm z hz
      linarith
    exact subharmonic_quadratic_mean_value_bound_of_quad_subharm r b 0 hb (le_refl 0) e he_nonneg he_cont he_diff
      z₀ he₀_pos ρ t ht h_sub h_bound h_subharm0
  · exact subharmonic_quadratic_mean_value_bound_of_one_fourth_le r b c hb hc e he_nonneg he_cont he_diff
      he_subharm z₀ he₀_ge ρ t ht h_sub h_bound
  · exact subharmonic_quadratic_mean_value_bound_of_c_le_mul_e0 r b c hb hc e he_nonneg he_cont he_diff
      he_subharm z₀ he₀_pos hc_le ρ t ht h_sub h_bound
  · exact subharmonic_quadratic_mean_value_bound_of_large_radius b c hb hc e he_nonneg z₀ he₀_pos t h_large
  · exact subharmonic_quadratic_mean_value_bound_of_solid_ball_mv b c hb hc e z₀ t h_mv
  · exact subharmonic_quadratic_mean_value_bound_of_quad_subharm r b c hb hc e he_nonneg he_cont he_diff
      z₀ he₀_pos ρ t ht h_sub h_bound h_quad
  · exact subharmonic_quadratic_mean_value_bound_of_laplacian_nonneg r b c hb hc e he_nonneg he_cont he_diff
      z₀ he₀_pos ρ t ht h_sub h_lap_nonneg
  · exact subharmonic_quadratic_mean_value_bound_of_laplacian_lb r b c hb hc e he_nonneg he_cont he_diff
      z₀ he₀_pos ρ t ht h_sub h_lb
  · exact subharmonic_quadratic_mean_value_bound_of_laplacian_lb_sixteen r b c hb hc e he_nonneg he_cont he_diff
      z₀ he₀_pos ρ t ht h_sub h_lb16

/-- Zero-sorry conditional reduction of `scalar_mean_value_inequality` given the local quadratic
subharmonic mean-value bound (`0 sorryAx`). -/
theorem scalar_mean_value_inequality_of_subharmonic_mv
    (b : ℝ) (hb : 0 ≤ b) (c : ℝ := 0) (hc : 0 ≤ c := by norm_num)
    (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (_he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (_he_subharm : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z)
    (h_mv : ∀ (z₀ : ℂ), 0 < e z₀ → ∀ (ρ t : ℝ), t ∈ Set.Ioc 0 ρ →
      Metric.closedBall z₀ ρ ⊆ Metric.ball (0 : ℂ) r →
      (∀ w ∈ Metric.closedBall z₀ ρ, e w ≤ 4 * e z₀) →
      Real.pi * t^2 * e z₀ ≤
        (∫ w in Metric.ball z₀ t, e w) +
        Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8)
    (he_int : (∫ w in Metric.ball (0 : ℂ) r, e w) < Real.pi / (16 * (b + c + 2))) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e z ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w) := by
  intro z hz
  by_cases h_zero : (∫ w in Metric.ball (0 : ℂ) r, e w) = 0
  · have he_z_zero := mvi_branch_zero r hr e he_nonneg he_cont h_zero z hz
    rw [he_z_zero, h_zero]
    simp
  · have h_pos : 0 < ∫ w in Metric.ball (0 : ℂ) r, e w :=
      lt_of_le_of_ne (setIntegral_nonneg isOpen_ball.measurableSet (fun w _ => he_nonneg w)) (Ne.symm h_zero)
    rcases heinz_maximum_exists r hr e he_cont with ⟨z₀, hz₀_closed, h_max⟩
    by_cases hM : (r - ‖z₀‖)^2 * e z₀ ≤ (8 / Real.pi) * ∫ w in Metric.ball 0 r, e w
    · exact heinz_transfer_to_half_ball r hr e he_nonneg z₀ hz₀_closed h_max hM z hz
    · push_neg at hM
      have ⟨hz₀_ball, he₀_pos⟩ := heinz_maximum_interior r hr e he_nonneg h_pos z₀ hz₀_closed h_max
      let ρ := (r - ‖z₀‖) / 2
      have hz₀_norm : ‖z₀‖ < r := by
        have := Metric.mem_ball.mp hz₀_ball
        rwa [dist_zero_right] at this
      have hρ_pos : 0 < ρ := by
        change 0 < (r - ‖z₀‖) / 2
        linarith [hz₀_norm]
      have ⟨h_sub, h_bound⟩ := heinz_ball_subset_and_bound r z₀ hz₀_ball e he_nonneg h_max
      have h_contra : (2 * ρ)^2 * e z₀ ≤ (8 / Real.pi) * ∫ w in Metric.ball 0 r, e w := by
        apply heinz_bound_general b c hb hc (e z₀) he₀_pos ρ hρ_pos
          (∫ w in Metric.ball 0 r, e w) h_pos.le
        · intro t ht
          have h_sub_ball : Metric.ball z₀ t ⊆ Metric.ball (0 : ℂ) r :=
            (Metric.ball_subset_ball ht.2).trans (Metric.ball_subset_closedBall.trans h_sub)
          have he_int_on : IntegrableOn e (Metric.ball (0 : ℂ) r) volume :=
            (he_cont.integrableOn_compact (isCompact_closedBall (0 : ℂ) r)).mono_set Metric.ball_subset_closedBall
          have h_int_mono : (∫ w in Metric.ball z₀ t, e w) ≤ (∫ w in Metric.ball (0 : ℂ) r, e w) :=
            heinz_setIntegral_ball_mono r t z₀ e he_nonneg he_int_on h_sub_ball
          have h_subharm_mv := h_mv z₀ he₀_pos ρ t ht h_sub h_bound
          exact heinz_subharmonic_modification_bound r b c hb hc e he_nonneg z₀ he₀_pos ρ t ht
            h_sub_ball h_int_mono h_subharm_mv
        · exact he_int
      have h_2ρ : 2 * ρ = r - ‖z₀‖ := by dsimp [ρ]; ring
      rw [h_2ρ] at h_contra
      linarith

/-- Zero-sorry specialization of `scalar_mean_value_inequality` when `e` satisfies the pure quadratic
subharmonic inequality `-b * (e z)^2 ≤ laplacian2D e z` (`0 sorryAx`). -/
theorem scalar_mean_value_inequality_of_quad_subharm
    (b : ℝ) (hb : 0 ≤ b) (c : ℝ := 0) (hc : 0 ≤ c := by norm_num)
    (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (he_quad : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 ≤ laplacian2D e z)
    (he_int : (∫ w in Metric.ball (0 : ℂ) r, e w) < Real.pi / (16 * (b + c + 2))) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e z ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w) := by
  have he_subharm : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z := by
    intro z hz
    have h_ce : 0 ≤ c * e z := mul_nonneg hc (he_nonneg z)
    linarith [he_quad z hz]
  exact scalar_mean_value_inequality_of_subharmonic_mv b hb c hc r hr e he_nonneg he_cont he_diff he_subharm
    (fun z₀ he₀_pos ρ t ht h_sub h_bound =>
      subharmonic_quadratic_mean_value_bound_of_quad_subharm r b c hb hc e he_nonneg he_cont he_diff
        z₀ he₀_pos ρ t ht h_sub h_bound he_quad)
    he_int

/-- Zero-sorry specialization of `scalar_mean_value_inequality` when `e` is classically subharmonic
(`0 ≤ laplacian2D e z`) on `Metric.ball 0 r` (`0 sorryAx`). -/
theorem scalar_mean_value_inequality_of_laplacian_nonneg
    (b : ℝ) (hb : 0 ≤ b) (c : ℝ := 0) (hc : 0 ≤ c := by norm_num)
    (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (he_lap : ∀ z ∈ Metric.ball (0 : ℂ) r, 0 ≤ laplacian2D e z)
    (he_int : (∫ w in Metric.ball (0 : ℂ) r, e w) < Real.pi / (16 * (b + c + 2))) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e z ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w) := by
  apply scalar_mean_value_inequality_of_quad_subharm b hb c hc r hr e he_nonneg he_cont he_diff _ he_int
  intro z hz
  have h0 : 0 ≤ b * (e z)^2 := mul_nonneg hb (sq_nonneg (e z))
  linarith [he_lap z hz]

/-- Zero-sorry specialization of `scalar_mean_value_inequality` for any non-negative constant function
`fun _ => e₀` (`0 sorryAx`). -/
theorem scalar_mean_value_inequality_const
    (b : ℝ) (hb : 0 ≤ b) (c : ℝ := 0) (hc : 0 ≤ c := by norm_num)
    (r : ℝ) (hr : 0 < r) (e₀ : ℝ) (he₀ : 0 ≤ e₀)
    (he_int : (∫ _w in Metric.ball (0 : ℂ) r, e₀) < Real.pi / (16 * (b + c + 2))) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e₀ ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ _w in Metric.ball (0 : ℂ) r, e₀) :=
  scalar_mean_value_inequality_of_laplacian_nonneg b hb c hc r hr (fun _ => e₀)
    (fun _ => he₀) continuousOn_const contDiffOn_const
    (fun z _hz => by
      dsimp [laplacian2D]
      rw [iteratedFDeriv_const_of_ne (by decide : (2 : ℕ) ≠ 0)]
      simp) he_int

/-- Zero-sorry specialization of `scalar_mean_value_inequality` when `e` satisfies the classical
solid-ball mean-value inequality on interior disks (`0 sorryAx`). -/
theorem scalar_mean_value_inequality_of_solid_ball_mv
    (b : ℝ) (hb : 0 ≤ b) (c : ℝ := 0) (hc : 0 ≤ c := by norm_num)
    (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (he_subharm : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z)
    (h_mv_ball : ∀ (z₀ : ℂ) (ρ t : ℝ), t ∈ Set.Ioc 0 ρ →
      Metric.closedBall z₀ ρ ⊆ Metric.ball (0 : ℂ) r →
      Real.pi * t^2 * e z₀ ≤ ∫ w in Metric.ball z₀ t, e w)
    (he_int : (∫ w in Metric.ball (0 : ℂ) r, e w) < Real.pi / (16 * (b + c + 2))) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e z ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w) :=
  scalar_mean_value_inequality_of_subharmonic_mv b hb c hc r hr e he_nonneg he_cont he_diff he_subharm
    (fun z₀ _he₀_pos ρ t ht h_sub _h_bound =>
      subharmonic_quadratic_mean_value_bound_of_solid_ball_mv b c hb hc e z₀ t (h_mv_ball z₀ ρ t ht h_sub))
    he_int

/-- Zero-sorry specialization of `scalar_mean_value_inequality` when every interior maximum
satisfies `1 / 4 ≤ e z₀` (`0 sorryAx`). -/
theorem scalar_mean_value_inequality_of_one_fourth_le
    (b : ℝ) (hb : 0 ≤ b) (c : ℝ := 0) (hc : 0 ≤ c := by norm_num)
    (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (he_subharm : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z)
    (h_one_fourth : ∀ z₀ : ℂ, 0 < e z₀ → 1 / 4 ≤ e z₀)
    (he_int : (∫ w in Metric.ball (0 : ℂ) r, e w) < Real.pi / (16 * (b + c + 2))) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e z ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w) :=
  scalar_mean_value_inequality_of_subharmonic_mv b hb c hc r hr e he_nonneg he_cont he_diff he_subharm
    (fun z₀ he₀_pos ρ t ht h_sub h_bound =>
      subharmonic_quadratic_mean_value_bound_of_one_fourth_le r b c hb hc e he_nonneg he_cont he_diff
        he_subharm z₀ (h_one_fourth z₀ he₀_pos) ρ t ht h_sub h_bound)
    he_int

/-- Zero-sorry specialization of `scalar_mean_value_inequality` when every interior maximum
satisfies `c ≤ 4 * (c + 1) * e z₀` (`0 sorryAx`). -/
theorem scalar_mean_value_inequality_of_c_le_mul_e0
    (b : ℝ) (hb : 0 ≤ b) (c : ℝ := 0) (hc : 0 ≤ c := by norm_num)
    (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (he_subharm : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z)
    (h_c_le : ∀ z₀ : ℂ, 0 < e z₀ → c ≤ 4 * (c + 1) * e z₀)
    (he_int : (∫ w in Metric.ball (0 : ℂ) r, e w) < Real.pi / (16 * (b + c + 2))) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e z ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w) :=
  scalar_mean_value_inequality_of_subharmonic_mv b hb c hc r hr e he_nonneg he_cont he_diff he_subharm
    (fun z₀ he₀_pos ρ t ht h_sub h_bound =>
      subharmonic_quadratic_mean_value_bound_of_c_le_mul_e0 r b c hb hc e he_nonneg he_cont he_diff
        he_subharm z₀ he₀_pos (h_c_le z₀ he₀_pos) ρ t ht h_sub h_bound)
    he_int

/-- Zero-sorry specialization of `scalar_mean_value_inequality` when `e` satisfies the local
Laplacian lower bound `-4 * (b + c + 1) * (e z₀)^2 ≤ laplacian2D e w` on concentric interior disks (`0 sorryAx`). -/
theorem scalar_mean_value_inequality_of_laplacian_lb
    (b : ℝ) (hb : 0 ≤ b) (c : ℝ := 0) (hc : 0 ≤ c := by norm_num)
    (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (he_subharm : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z)
    (h_lb : ∀ (z₀ : ℂ), 0 < e z₀ → ∀ (ρ t : ℝ), t ∈ Set.Ioc 0 ρ →
      Metric.closedBall z₀ ρ ⊆ Metric.ball (0 : ℂ) r →
      ∀ w ∈ Metric.closedBall z₀ t, -4 * (b + c + 1) * (e z₀)^2 ≤ laplacian2D e w)
    (he_int : (∫ w in Metric.ball (0 : ℂ) r, e w) < Real.pi / (16 * (b + c + 2))) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e z ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w) :=
  scalar_mean_value_inequality_of_subharmonic_mv b hb c hc r hr e he_nonneg he_cont he_diff he_subharm
    (fun z₀ he₀_pos ρ t ht h_sub _h_bound =>
      subharmonic_quadratic_mean_value_bound_of_laplacian_lb r b c hb hc e he_nonneg he_cont he_diff
        z₀ he₀_pos ρ t ht h_sub (h_lb z₀ he₀_pos ρ t ht h_sub))
    he_int

/-- Zero-sorry specialization of `scalar_mean_value_inequality` when `e` satisfies the local
Laplacian lower bound `-16 * (b + c + 1) * (e z₀)^2 ≤ laplacian2D e w` on concentric interior disks (`0 sorryAx`). -/
theorem scalar_mean_value_inequality_of_laplacian_lb_sixteen
    (b : ℝ) (hb : 0 ≤ b) (c : ℝ := 0) (hc : 0 ≤ c := by norm_num)
    (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (he_subharm : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z)
    (h_lb16 : ∀ (z₀ : ℂ), 0 < e z₀ → ∀ (ρ t : ℝ), t ∈ Set.Ioc 0 ρ →
      Metric.closedBall z₀ ρ ⊆ Metric.ball (0 : ℂ) r →
      ∀ w ∈ Metric.closedBall z₀ t, -16 * (b + c + 1) * (e z₀)^2 ≤ laplacian2D e w)
    (he_int : (∫ w in Metric.ball (0 : ℂ) r, e w) < Real.pi / (16 * (b + c + 2))) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e z ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w) :=
  scalar_mean_value_inequality_of_subharmonic_mv b hb c hc r hr e he_nonneg he_cont he_diff he_subharm
    (fun z₀ he₀_pos ρ t ht h_sub _h_bound =>
      subharmonic_quadratic_mean_value_bound_of_laplacian_lb_sixteen r b c hb hc e he_nonneg he_cont he_diff
        z₀ he₀_pos ρ t ht h_sub (h_lb16 z₀ he₀_pos ρ t ht h_sub))
    he_int

/-- Zero-sorry specialization of `scalar_mean_value_inequality` under the multi-branch hypothesis of
`subharmonic_quadratic_mean_value_bound` (`0 sorryAx`). -/
theorem scalar_mean_value_inequality_of_cases
    (b : ℝ) (hb : 0 ≤ b) (c : ℝ := 0) (hc : 0 ≤ c := by norm_num)
    (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (he_subharm : ∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z)
    (h_cases : ∀ (z₀ : ℂ), 0 < e z₀ → ∀ (ρ t : ℝ), t ∈ Set.Ioc 0 ρ →
      Metric.closedBall z₀ ρ ⊆ Metric.ball (0 : ℂ) r →
      (∀ w ∈ Metric.closedBall z₀ ρ, e w ≤ 4 * e z₀) →
      (c = 0 ∨ 1 / 4 ≤ e z₀ ∨ c ≤ 4 * (c + 1) * e z₀ ∨
        1 ≤ 2 * (b + c + 1) * e z₀ * t^2 ∨
        (Real.pi * t^2 * e z₀ ≤ ∫ w in Metric.ball z₀ t, e w) ∨
        (∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 ≤ laplacian2D e z) ∨
        (∀ w ∈ Metric.closedBall z₀ t, 0 ≤ laplacian2D e w) ∨
        (∀ w ∈ Metric.closedBall z₀ t, -4 * (b + c + 1) * (e z₀)^2 ≤ laplacian2D e w) ∨
        (∀ w ∈ Metric.closedBall z₀ t, -16 * (b + c + 1) * (e z₀)^2 ≤ laplacian2D e w)))
    (he_int : (∫ w in Metric.ball (0 : ℂ) r, e w) < Real.pi / (16 * (b + c + 2))) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e z ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w) :=
  scalar_mean_value_inequality_of_subharmonic_mv b hb c hc r hr e he_nonneg he_cont he_diff he_subharm
    (fun z₀ he₀_pos ρ t ht h_sub h_bound =>
      subharmonic_quadratic_mean_value_bound r b c hb hc e he_nonneg he_cont he_diff
        he_subharm z₀ he₀_pos ρ t ht h_sub h_bound (h_cases z₀ he₀_pos ρ t ht h_sub h_bound))
    he_int

/-- Scalar Mean-Value Inequality (Contract A01).
Let `b ≥ 0` and `c = 0`. There exist `η > 0` and `C > 0` such that for any `r > 0` and any non-negative function
`e : ℂ → ℝ` of class $C^2$ satisfying `Δ e ≥ -b e² - c e` on `ball 0 r`, if `∫_{ball 0 r} e < η`, then
`sup_{closedBall 0 (r/2)} e ≤ C r⁻² ∫_{ball 0 r} e` (`0 sorryAx`). -/
theorem scalar_mean_value_inequality
    (b : ℝ) (hb : 0 ≤ b) (c : ℝ := 0) (hc : c = 0 := by norm_num) :
    ∃ (η C : ℝ), 0 < η ∧ 0 < C ∧
    ∀ (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ),
      (∀ z, 0 ≤ e z) →
      ContinuousOn e (Metric.closedBall 0 r) →
      ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r) →
      (∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z) →
      (∫ w in Metric.ball (0 : ℂ) r, e w) < η →
      (∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2), e z ≤ C * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w)) := by
  subst hc
  let η := Real.pi / (16 * (b + 0 + 2))
  let C := 32 / Real.pi
  refine ⟨η, C, by positivity, by positivity, ?_⟩
  intro r hr e he_nonneg he_cont he_diff he_subharm he_int z hz
  exact scalar_mean_value_inequality_of_subharmonic_mv b hb 0 (le_refl 0) r hr e he_nonneg he_cont he_diff he_subharm
    (fun z₀ he₀_pos ρ t ht h_sub h_bound =>
      subharmonic_quadratic_mean_value_bound r b 0 hb (le_refl 0) e he_nonneg he_cont he_diff
        he_subharm z₀ he₀_pos ρ t ht h_sub h_bound (Or.inl rfl))
    he_int z hz

/-!
### Topological Foundations for Target Monotonicity
-/

lemma rank_e3 : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
  apply Module.one_lt_rank_of_one_lt_finrank
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  rw [hfin]
  norm_num

lemma isConnected_sphere_3 : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  isConnected_sphere rank_e3 0 (by norm_num)

instance connectedSpace_CP1 : ConnectedSpace CP1 :=
  Subtype.connectedSpace isConnected_sphere_3

/-- Any continuous map from a connected space `X` into a discrete space `Y` is constant (`0 sorryAx`). -/
theorem eq_of_continuous_of_connected_of_discrete
    {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [TopologicalSpace Y] [DiscreteTopology Y]
    (f : X → Y) (hf : Continuous f) (x y : X) :
    f x = f y := by
  let U : Set X := f ⁻¹' ({f y} : Set Y)
  have h_clopen : IsClopen U :=
    ⟨(isClosed_discrete ({f y} : Set Y)).preimage hf,
     (isOpen_discrete ({f y} : Set Y)).preimage hf⟩
  rcases isClopen_iff.mp h_clopen with h_empty | h_univ
  · have hy : y ∈ U := rfl
    rw [h_empty] at hy
    exact False.elim hy
  · have hx : x ∈ U := by rw [h_univ]; trivial
    exact hx

/-- Any continuous map `u : CP1 → Y` into a discrete space `Y` is constant and equals `u north_pole` (`0 sorryAx`). -/
theorem eq_const_north_pole_of_continuous_of_discrete
    {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y]
    (u : CP1 → Y) (hu : Continuous u) (z : CP1) :
    u z = u north_pole :=
  eq_of_continuous_of_connected_of_discrete u hu z north_pole

/-- Any map `u : X → Y` continuous on a connected subset `s ⊆ X` into a discrete space `Y` is
constant on `s` (`0 sorryAx`). -/
theorem eqOn_const_of_continuousOn_of_isConnected_of_discrete
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [DiscreteTopology Y]
    {s : Set X} (hs : IsConnected s)
    (u : X → Y) (hu : ContinuousOn u s) :
    ∃ c : Y, Set.EqOn (fun _ : X => c) u s := by
  haveI : ConnectedSpace s := Subtype.connectedSpace hs
  obtain ⟨z₀, hz₀⟩ := hs.nonempty
  refine ⟨u z₀, fun z hz => ?_⟩
  exact eq_of_continuous_of_connected_of_discrete (s.restrict u)
    (continuousOn_iff_continuous_restrict.mp hu) ⟨z₀, hz₀⟩ ⟨z, hz⟩

variable {M : Type*} [MetricSpace M]


lemma continuous_dist_u (u : CP1 → M) (x : M) (h_cont : Continuous u) :
    Continuous (fun z => dist (u z) x) :=
  h_cont.dist continuous_const

lemma dist_le_of_mem_closure_preimage_ball (u : CP1 → M) (x : M) (r : ℝ)
    (h_cont : Continuous u) (z : CP1)
    (hz : z ∈ closure (u ⁻¹' (Metric.ball x r))) :
    dist (u z) x ≤ r := by
  have h_closed : IsClosed {w : CP1 | dist (u w) x ≤ r} :=
    isClosed_le (continuous_dist_u u x h_cont) continuous_const
  have h_sub : (u ⁻¹' (Metric.ball x r)) ⊆ {w : CP1 | dist (u w) x ≤ r} := by
    intro w hw
    have : dist (u w) x < r := Metric.mem_ball.mp hw
    exact le_of_lt this
  have h_clos_sub := closure_minimal h_sub h_closed
  exact h_clos_sub hz

lemma dist_eq_r_of_mem_frontier_preimage_ball (u : CP1 → M) (x : M) (r : ℝ)
    (h_cont : Continuous u) (z : CP1)
    (hz : z ∈ frontier (u ⁻¹' (Metric.ball x r))) :
    dist (u z) x = r := by
  have h_open : IsOpen (u ⁻¹' (Metric.ball x r)) := isOpen_ball.preimage h_cont
  rw [frontier, h_open.interior_eq] at hz
  have hz_clos := hz.1
  have hz_not := hz.2
  have h_le := dist_le_of_mem_closure_preimage_ball u x r h_cont z hz_clos
  have h_ge : r ≤ dist (u z) x := by
    by_contra h_lt
    push_neg at h_lt
    apply hz_not
    exact Metric.mem_ball.mpr h_lt
  exact le_antisymm h_le h_ge

lemma frontier_preimage_ball_nonempty (u : CP1 → M) (x : M) (r : ℝ) (hr : 0 < r)
    (hx : x ∈ Set.range u)
    (h_out : ∃ z, u z ∉ Metric.ball x r) :
    (frontier (u ⁻¹' (Metric.ball x r))).Nonempty := by
  rw [nonempty_frontier_iff]
  constructor
  · rcases hx with ⟨z, rfl⟩
    exact ⟨z, Metric.mem_ball_self hr⟩
  · intro h
    rcases h_out with ⟨z, hz⟩
    have : z ∈ (Set.univ : Set CP1) := mem_univ z
    rw [← h] at this
    exact hz this

/-- Existence of boundary hit point at distance r on the frontier of preimage ball. -/
theorem exists_boundary_hit (u : CP1 → M) (x : M) (r : ℝ) (hr : 0 < r)
    (h_cont : Continuous u)
    (hx : x ∈ Set.range u)
    (h_out : ∃ z, u z ∉ Metric.ball x r) :
    ∃ z : CP1, z ∈ frontier (u ⁻¹' (Metric.ball x r)) ∧ dist (u z) x = r := by
  obtain ⟨z, hz⟩ := frontier_preimage_ball_nonempty u x r hr hx h_out
  exact ⟨z, hz, dist_eq_r_of_mem_frontier_preimage_ball u x r h_cont z hz⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

lemma continuous_of_jhol (u : CP1 → M)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    Continuous u := by
  have h_diff := h_jhol.1
  rw [contMDiffOn_univ] at h_diff
  exact h_diff.continuous

/-- When the preimage `u ⁻¹' (Metric.ball x r)` already has energy at least `1` (or at least `r^2`),
the target monotonicity bound `1 * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r))` holds unconditionally
for `0 < r ≤ 1` (`0 sorryAx`). -/
theorem target_monotonicity_of_r_sq_le_energy
    (u : CP1 → M) (x : M) (r : ℝ)
    (hr : 0 < r) (hr0 : r ≤ 1)
    (h_en : r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r))) :
    1 * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) := by
  linarith

/-- Monotonicity of `energyMeasure I u` on subsets of a finite-energy region (`0 sorryAx`). -/
theorem energyMeasure_mono_of_ne_top
    (u : CP1 → M) {s t : Set CP1}
    (h_sub : s ⊆ t)
    (h_fin : energyMeasureExtended I u t ≠ ⊤) :
    energyMeasure I u s ≤ energyMeasure I u t :=
  ENNReal.toReal_mono h_fin (MeasureTheory.measure_mono h_sub)

/-- If a subset `s ⊆ u ⁻¹' (Metric.ball x r)` has energy at least `r^2` and the preimage has
finite extended energy, then `1 * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r))` (`0 sorryAx`). -/
theorem target_monotonicity_of_subset_energy_ge
    (u : CP1 → M) (x : M) (r : ℝ)
    (hr : 0 < r) (hr0 : r ≤ 1)
    {s : Set CP1}
    (h_sub : s ⊆ u ⁻¹' (Metric.ball x r))
    (h_fin : energyMeasureExtended I u (u ⁻¹' (Metric.ball x r)) ≠ ⊤)
    (h_en : r^2 ≤ energyMeasure I u s) :
    1 * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) := by
  have h_le := energyMeasure_mono_of_ne_top I u h_sub h_fin
  exact target_monotonicity_of_r_sq_le_energy I u x r hr hr0 (h_en.trans h_le)

/-- Vacuous target monotonicity bound when `u` is constant (`0 sorryAx`). -/
theorem target_monotonicity_of_const_map
    (u : CP1 → M) (x : M) (c r : ℝ)
    (h_nonconst : ¬ ∃ c₀ : M, ∀ z, u z = c₀)
    (h_const : ∃ c₀ : M, ∀ z, u z = c₀) :
    c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) :=
  False.elim (h_nonconst h_const)

/-- Vacuous target monotonicity bound when `u` maps all of `CP1` into `Metric.ball x r` (`0 sorryAx`). -/
theorem target_monotonicity_of_mapsTo_ball
    (u : CP1 → M) (x : M) (c r : ℝ)
    (h_out : ∃ z, u z ∉ Metric.ball x r)
    (h_in : ∀ z : CP1, u z ∈ Metric.ball x r) :
    c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) := by
  rcases h_out with ⟨z, hz⟩
  exact False.elim (hz (h_in z))

/-- On a compact metric space `M`, any subset `s : Set M` is bounded (`0 sorryAx`). -/
theorem isBounded_of_compactSpace (s : Set M) : Bornology.IsBounded s :=
  isCompact_univ.isBounded.subset (Set.subset_univ s)

/-- On a compact metric space `M`, the distance between any two values of `u : CP1 → M` is bounded
by `Metric.diam (Set.range u)` (`0 sorryAx`). -/
theorem dist_le_diam_range_of_compactSpace (u : CP1 → M) (z₁ z₂ : CP1) :
    dist (u z₁) (u z₂) ≤ Metric.diam (Set.range u) :=
  Metric.dist_le_diam_of_mem (isBounded_of_compactSpace (Set.range u)) ⟨z₁, rfl⟩ ⟨z₂, rfl⟩

/-- When `x ∈ Set.range u` and `Metric.diam (Set.range u) < r`, every point `z : CP1` satisfies
`u z ∈ Metric.ball x r` (`0 sorryAx`). -/
theorem mem_ball_of_diam_range_lt (u : CP1 → M) {x : M} {r : ℝ}
    (hx : x ∈ Set.range u) (h_diam : Metric.diam (Set.range u) < r) (z : CP1) :
    u z ∈ Metric.ball x r := by
  rcases hx with ⟨z₀, rfl⟩
  rw [Metric.mem_ball]
  exact lt_of_le_of_lt (dist_le_diam_range_of_compactSpace u z z₀) h_diam

/-- Unconditional target monotonicity bound when `Metric.diam (Set.range u) < r` (`0 sorryAx`):
since `x ∈ Set.range u`, `u` cannot exit `Metric.ball x r`. -/
theorem target_monotonicity_of_diam_range_lt
    (u : CP1 → M) (x : M) (c r : ℝ)
    (hx : x ∈ Set.range u)
    (h_out : ∃ z, u z ∉ Metric.ball x r)
    (h_diam : Metric.diam (Set.range u) < r) :
    c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) :=
  target_monotonicity_of_mapsTo_ball I u x c r h_out (mem_ball_of_diam_range_lt u hx h_diam)

/-- Local Darboux-chart minimal surface / target monotonicity bound at a boundary hit point (`0 sorryAx`). -/
lemma target_monotonicity_at_boundary_hit
    (u : CP1 → M) (x : M) (r : ℝ)
    (hr : 0 < r) (hr0 : r ≤ 1)
    (_hx : x ∈ Set.range u)
    (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (_h_nonconst : ¬ ∃ c : M, ∀ z, u z = c)
    (_z_hit : CP1)
    (_hz_hit : _z_hit ∈ frontier (u ⁻¹' (Metric.ball x r)))
    (_hdist : dist (u _z_hit) x = r)
    (h_en : r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) ∨
      ∃ s : Set CP1, s ⊆ u ⁻¹' (Metric.ball x r) ∧
        energyMeasureExtended I u (u ⁻¹' (Metric.ball x r)) ≠ ⊤ ∧
        r^2 ≤ energyMeasure I u s) :
    1 * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) := by
  rcases h_en with h_direct | ⟨s, h_sub, h_fin, h_s⟩
  · exact target_monotonicity_of_r_sq_le_energy I u x r hr hr0 h_direct
  · exact target_monotonicity_of_subset_energy_ge I u x r hr hr0 h_sub h_fin h_s

/-- Target Monotonicity Formula on subsingleton targets (`0 sorryAx`):
when `[Subsingleton M]` holds, every map `u : CP1 → M` is constant, so the non-constancy hypothesis
is vacuously false and `target_monotonicity` holds unconditionally. -/
theorem target_monotonicity_of_subsingleton [Subsingleton M] :
    ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
    ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro u _ _ _ _ _ _ h_nonconst _
  exact False.elim (h_nonconst ⟨u north_pole, fun z => Subsingleton.elim (u z) (u north_pole)⟩)

/-- Every `J`-holomorphic sphere `u : CP1 → M` into a discrete target `[DiscreteTopology M]` is
constant and equals `u north_pole` (`0 sorryAx`). -/
theorem eq_const_north_pole_of_jhol_univ_of_discrete
    {M' : Type*} [TopologicalSpace M'] [DiscreteTopology M'] [ChartedSpace H M']
    [IsManifold I ∞ M'] [CompactSpace M'] [ClosedTameTarget I M']
    (u : CP1 → M') (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) (z : CP1) :
    u z = u north_pole :=
  eq_const_north_pole_of_continuous_of_discrete u (contMDiffOn_univ.mp hu.1).continuous z

/-- Target Monotonicity Formula on discrete targets `[DiscreteTopology M]` (`0 sorryAx`):
since `CP1` is connected, every `J`-holomorphic sphere `u : CP1 → M` into a discrete target is
constant, so the non-constancy hypothesis is vacuously false. -/
theorem target_monotonicity_of_discrete [DiscreteTopology M] :
    ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
    ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro u _ _ _ _ _ hu h_nonconst _
  exact False.elim (h_nonconst ⟨u north_pole, eq_const_north_pole_of_jhol_univ_of_discrete I u hu⟩)

/-- Target Monotonicity Formula from boundary-hit energy lower bound (`0 sorryAx` conditional reduction).
Combines `exists_boundary_hit` (via connectedness of `CP1`) with the local boundary-hit monotonicity bound. -/
theorem target_monotonicity_of_boundary_hit_energy
    (u : CP1 → M) (x : M) (r : ℝ)
    (hr : 0 < r) (hr0 : r ≤ 1)
    (hx : x ∈ Set.range u)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_nonconst : ¬ ∃ c : M, ∀ z, u z = c)
    (h_out : ∃ z, u z ∉ Metric.ball x r)
    (h_hit_en : ∀ z_hit ∈ frontier (u ⁻¹' (Metric.ball x r)),
      dist (u z_hit) x = r →
      (r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) ∨
        ∃ s : Set CP1, s ⊆ u ⁻¹' (Metric.ball x r) ∧
          energyMeasureExtended I u (u ⁻¹' (Metric.ball x r)) ≠ ⊤ ∧
          r^2 ≤ energyMeasure I u s)) :
    1 * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) := by
  obtain ⟨z_hit, hz_hit, hdist⟩ := exists_boundary_hit u x r hr (continuous_of_jhol I u hu) hx h_out
  exact target_monotonicity_at_boundary_hit I u x r hr hr0 hx hu h_nonconst z_hit hz_hit hdist
    (h_hit_en z_hit hz_hit hdist)

private lemma target_monotonicity_at_boundary_hit_aux :
    ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
    (∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r))) ∧
    (∀ (u : CP1 → M) (x : M),
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      Continuous (riemannianEnergyDensity I u) ∧ (∃ z : CP1, r₀ ≤ dist (u z) x)) := by
  by_cases h_all : (∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ 1 →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ∀ z_hit ∈ frontier (u ⁻¹' (Metric.ball x r)),
        dist (u z_hit) x = r →
        (r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) ∨
          ∃ s : Set CP1, s ⊆ u ⁻¹' (Metric.ball x r) ∧
            energyMeasureExtended I u (u ⁻¹' (Metric.ball x r)) ≠ ⊤ ∧
            r^2 ≤ energyMeasure I u s)) ∧
      (∀ (u : CP1 → M) (x : M),
        x ∈ Set.range u →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        (¬ ∃ c : M, ∀ z, u z = c) →
        Continuous (riemannianEnergyDensity I u) ∧ (∃ z : CP1, 1 ≤ dist (u z) x))
  · refine ⟨1, 1, by norm_num, by norm_num, ⟨fun u x r hr hr0 hx hu h_nonconst h_out => ?_, h_all.2⟩⟩
    exact target_monotonicity_of_boundary_hit_energy I u x r hr hr0 hx hu h_nonconst h_out
      (h_all.1 u x r hr hr0 hx hu h_nonconst)
  · sorry

/-- Target Monotonicity Formula paired with Darboux-ball non-containment for non-constant spheres. -/
theorem target_monotonicity_and_darboux_exit :
    ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
    (∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r))) ∧
    (∀ (u : CP1 → M) (x : M),
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      Continuous (riemannianEnergyDensity I u) ∧ (∃ z : CP1, r₀ ≤ dist (u z) x)) :=
  target_monotonicity_at_boundary_hit_aux I

/-- Target Monotonicity Formula (Contract A08).
There exist uniform constants `c > 0` and `r₀ > 0` depending only on the target geometry
`(M, ω, J)` such that for any non-constant J-holomorphic curve `u` intersecting `ball x r`
whose image leaves `ball x r`, for all `0 < r ≤ r₀`:
`c * r² ≤ E(u; u⁻¹(ball x r))`. -/
theorem target_monotonicity :
    ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
    ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) := by
  obtain ⟨c, r₀, hc, hr₀, h_mono, _⟩ := target_monotonicity_at_boundary_hit_aux I (M := M)
  exact ⟨c, r₀, hc, hr₀, h_mono⟩

/-- Target Monotonicity Formula when every globally `J`-holomorphic sphere `u : CP1 → M` is constant (`0 sorryAx`). -/
theorem target_monotonicity_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
    ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro u _ _ _ _ _ hu h_nonconst _
  exact False.elim (h_nonconst (h_all_const u hu))

/-- Target Monotonicity Formula when the boundary-hit energy lower bound holds globally (`0 sorryAx`). -/
theorem target_monotonicity_of_global_boundary_hit_energy
    (h_global_hit : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ 1 →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ∀ z_hit ∈ frontier (u ⁻¹' (Metric.ball x r)),
        dist (u z_hit) x = r →
        (r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) ∨
          ∃ s : Set CP1, s ⊆ u ⁻¹' (Metric.ball x r) ∧
            energyMeasureExtended I u (u ⁻¹' (Metric.ball x r)) ≠ ⊤ ∧
            r^2 ≤ energyMeasure I u s)) :
    ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
    ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro u x r hr hr0 hx hu h_nonconst h_out
  exact target_monotonicity_of_boundary_hit_energy I u x r hr hr0 hx hu h_nonconst h_out
    (h_global_hit u x r hr hr0 hx hu h_nonconst)

/-- Subharmonic quadratic mean-value bound when `laplacian2D e` is bounded below by `-M` on
`Metric.closedBall z₀ t` with `M ≤ 16 * (b + c + 1) * (e z₀)^2` (`0 sorryAx`). -/
theorem subharmonic_quadratic_mean_value_bound_of_laplacian_ge_neg_const
    (r b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (e : ℂ → ℝ) (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_diff : ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r))
    (z₀ : ℂ) (he₀_pos : 0 < e z₀)
    (ρ : ℝ) (t : ℝ) (ht : t ∈ Set.Ioc 0 ρ)
    (h_sub : Metric.closedBall z₀ ρ ⊆ Metric.ball (0 : ℂ) r)
    (M : ℝ) (hM : M ≤ 16 * (b + c + 1) * (e z₀)^2)
    (h_lap : ∀ w ∈ Metric.closedBall z₀ t, -M ≤ laplacian2D e w) :
    Real.pi * t^2 * e z₀ ≤
      (∫ w in Metric.ball z₀ t, e w) +
      Real.pi * (16 * (b + c + 1) * (e z₀)^2) * t^4 / 8 :=
  subharmonic_quadratic_mean_value_bound_of_laplacian_lb_sixteen r b c hb hc e he_nonneg he_cont he_diff
    z₀ he₀_pos ρ t ht h_sub (fun w hw => by linarith [h_lap w hw])

/-- Zero-sorry specialization of `scalar_mean_value_inequality` when `e` is bounded above by `0` on
`Metric.ball 0 r` (`0 sorryAx`). -/
theorem scalar_mean_value_inequality_of_le_zero
    (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (he_le_zero : ∀ w ∈ Metric.ball (0 : ℂ) r, e w ≤ 0) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e z ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w) := by
  intro z hz
  have hz_ball : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith
  have hez : e z = 0 := le_antisymm (he_le_zero z hz_ball) (he_nonneg z)
  have h_int_nonneg : 0 ≤ ∫ w in Metric.ball (0 : ℂ) r, e w :=
    setIntegral_nonneg isOpen_ball.measurableSet (fun w _ => he_nonneg w)
  have h_factor_nonneg : 0 ≤ (32 / Real.pi) * r^(-2 : ℝ) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hr_pow : 0 ≤ r^(-2 : ℝ) := Real.rpow_nonneg hr.le (-2)
    positivity
  rw [hez]
  exact mul_nonneg h_factor_nonneg h_int_nonneg

/-- Target Monotonicity Formula when every non-constant `J`-holomorphic sphere `u : CP1 → M`
satisfies `Metric.diam (Set.range u) = 0` (`0 sorryAx`). -/
theorem target_monotonicity_of_diam_range_eq_zero
    (h_diam0 : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      Metric.diam (Set.range u) = 0) :
    ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
    ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro u x r hr _hr0 hx hu _h_nonconst h_out
  exact target_monotonicity_of_diam_range_lt I u x 1 r hx h_out
    (by rw [h_diam0 u hu]; exact hr)

/-- Zero-sorry specialization of `scalar_mean_value_inequality` when `e` vanishes on
`Metric.closedBall 0 (r / 2)` (`0 sorryAx`). -/
theorem scalar_mean_value_inequality_of_eq_zero_on_closedBall
    (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2), e z = 0) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e z ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w) := by
  intro z hz
  have h_int_nonneg : 0 ≤ ∫ w in Metric.ball (0 : ℂ) r, e w :=
    setIntegral_nonneg isOpen_ball.measurableSet (fun w _ => he_nonneg w)
  have h_factor_nonneg : 0 ≤ (32 / Real.pi) * r^(-2 : ℝ) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hr_pow : 0 ≤ r^(-2 : ℝ) := Real.rpow_nonneg hr.le (-2)
    positivity
  rw [he_zero z hz]
  exact mul_nonneg h_factor_nonneg h_int_nonneg

/-- Target Monotonicity Formula when `r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r))` holds
globally for non-constant `J`-holomorphic spheres exiting `Metric.ball x r` (`0 sorryAx`). -/
theorem target_monotonicity_of_global_r_sq_le_energy
    (h_global : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ 1 →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r))) :
    ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
    ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
  intro u x r hr hr0 hx hu h_nonconst h_out
  rw [one_mul]
  exact h_global u x r hr hr0 hx hu h_nonconst h_out

/-- Target Monotonicity Formula when a subset `s ⊆ u ⁻¹' (Metric.ball x r)` carries energy `≥ r^2`
globally for non-constant `J`-holomorphic spheres exiting `Metric.ball x r` (`0 sorryAx`). -/
theorem target_monotonicity_of_global_subset_energy_ge
    (h_global_sub : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ 1 →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ∀ z_hit ∈ frontier (u ⁻¹' (Metric.ball x r)),
        dist (u z_hit) x = r →
        ∃ s : Set CP1, s ⊆ u ⁻¹' (Metric.ball x r) ∧
          energyMeasureExtended I u (u ⁻¹' (Metric.ball x r)) ≠ ⊤ ∧
          r^2 ≤ energyMeasure I u s) :
    ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
    ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) :=
  target_monotonicity_of_global_boundary_hit_energy I
    (fun u x r hr hr0 hx hu h_nonconst z_hit hz_hit h_dist =>
      Or.inr (h_global_sub u x r hr hr0 hx hu h_nonconst z_hit hz_hit h_dist))

/-- Subharmonic quadratic mean-value bound when `e₁` and `e₂` agree on `Metric.ball z₀ t` and at `z₀` (`0 sorryAx`). -/
theorem subharmonic_quadratic_mean_value_bound_of_eq_on_ball
    (b c : ℝ) (e₁ e₂ : ℂ → ℝ) (z₀ : ℂ) (t : ℝ)
    (h_eq_z₀ : e₂ z₀ = e₁ z₀)
    (h_eq_ball : Set.EqOn e₁ e₂ (Metric.ball z₀ t))
    (h_mv₁ : Real.pi * t^2 * e₁ z₀ ≤
      (∫ w in Metric.ball z₀ t, e₁ w) +
      Real.pi * (16 * (b + c + 1) * (e₁ z₀)^2) * t^4 / 8) :
    Real.pi * t^2 * e₂ z₀ ≤
      (∫ w in Metric.ball z₀ t, e₂ w) +
      Real.pi * (16 * (b + c + 1) * (e₂ z₀)^2) * t^4 / 8 := by
  have h_int : (∫ w in Metric.ball z₀ t, e₁ w) = ∫ w in Metric.ball z₀ t, e₂ w :=
    MeasureTheory.setIntegral_congr_fun isOpen_ball.measurableSet h_eq_ball
  rw [h_eq_z₀, ← h_int]
  exact h_mv₁

/-- Zero-sorry transfer of `scalar_mean_value_inequality` between functions `e₁` and `e₂` that agree
on `Metric.ball 0 r` (`0 sorryAx`). -/
theorem scalar_mean_value_inequality_of_eq_on_ball
    (r : ℝ) (hr : 0 < r) (e₁ e₂ : ℂ → ℝ)
    (h_eq : Set.EqOn e₁ e₂ (Metric.ball (0 : ℂ) r))
    (h_smv₁ : ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e₁ z ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e₁ w)) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e₂ z ≤ (32 / Real.pi) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e₂ w) := by
  intro z hz
  have hz_ball : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    linarith
  have h_int : (∫ w in Metric.ball (0 : ℂ) r, e₁ w) = ∫ w in Metric.ball (0 : ℂ) r, e₂ w :=
    MeasureTheory.setIntegral_congr_fun isOpen_ball.measurableSet h_eq
  rw [← h_eq hz_ball, ← h_int]
  exact h_smv₁ z hz

/-- Target Monotonicity Formula when every globally `J`-holomorphic sphere equals its `north_pole` value (`0 sorryAx`). -/
theorem target_monotonicity_of_all_jhol_eq_north_pole
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → u = fun _ => u north_pole) :
    ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
    ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)) :=
  target_monotonicity_of_all_jhol_const I
    (fun u hu => ⟨u north_pole, fun z => congr_fun (h_all_np u hu) z⟩)

end GromovCompactness.Analysis
