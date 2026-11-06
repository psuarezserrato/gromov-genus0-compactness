import Mathlib
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Analysis.Bochner
import GromovCompactness.Analysis.EpsilonRegularity

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness GromovCompactness.Analysis

lemma fderiv_add_left (a z : ℂ) :
    fderiv ℝ (fun w : ℂ => a + w) z = ContinuousLinearMap.id ℝ ℂ :=
  ((hasFDerivAt_id z).const_add a).fderiv

lemma fderiv_comp_add_const (g : ℂ → ℝ) (a : ℂ) (z : ℂ) :
    fderiv ℝ (fun w => g (a + w)) z = (fderiv ℝ g (a + z)) := by
  have h_trans : (fun w : ℂ => g (a + w)) = g ∘ (fun w => a + w) := rfl
  rw [h_trans]
  by_cases hg : DifferentiableAt ℝ g (a + z)
  · have h_lin : DifferentiableAt ℝ (fun w : ℂ => a + w) z := (differentiableAt_id).const_add a
    rw [fderiv_comp z hg h_lin]
    rw [fderiv_add_left a z, ContinuousLinearMap.comp_id]
  · have h_not : ¬ DifferentiableAt ℝ (g ∘ (fun w => a + w)) z := by
      intro h_comp
      have h_inv : g = (g ∘ (fun w => a + w)) ∘ (fun w => -a + w) := by
        ext w
        simp
      have h_diff_inv : DifferentiableAt ℝ (fun w => -a + w) (a + z) := (differentiableAt_id).const_add (-a)
      have : DifferentiableAt ℝ g (a + z) := by
        rw [h_inv]
        have h_pt : (-a + (a + z)) = z := by ring
        apply DifferentiableAt.comp (x := a + z)
        · rw [h_pt]; exact h_comp
        · exact h_diff_inv
      exact hg this
    rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt h_not]

lemma iteratedFDeriv_one_comp_add_const (g : ℂ → ℝ) (a : ℂ) (z : ℂ) :
    iteratedFDeriv ℝ 1 (fun w => g (a + w)) z = iteratedFDeriv ℝ 1 g (a + z) := by
  ext m
  rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply, fderiv_comp_add_const]

lemma fderiv_iteratedFDeriv_one_comp_add_const (g : ℂ → ℝ) (a : ℂ) (z : ℂ) :
    fderiv ℝ (iteratedFDeriv ℝ 1 (fun w => g (a + w))) z =
      fderiv ℝ (iteratedFDeriv ℝ 1 g) (a + z) := by
  have h_eq : (iteratedFDeriv ℝ 1 (fun w => g (a + w))) =
      (fun w => iteratedFDeriv ℝ 1 g (a + w)) :=
    funext (fun w => iteratedFDeriv_one_comp_add_const g a w)
  rw [h_eq]
  have h_trans : (fun w => iteratedFDeriv ℝ 1 g (a + w)) = (iteratedFDeriv ℝ 1 g) ∘ (fun w => a + w) := rfl
  rw [h_trans]
  by_cases hg : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 g) (a + z)
  · have h_lin : DifferentiableAt ℝ (fun w : ℂ => a + w) z := (differentiableAt_id).const_add a
    rw [fderiv_comp z hg h_lin]
    rw [fderiv_add_left a z, ContinuousLinearMap.comp_id]
  · have h_not : ¬ DifferentiableAt ℝ ((iteratedFDeriv ℝ 1 g) ∘ (fun w => a + w)) z := by
      intro h_comp
      have h_inv : (iteratedFDeriv ℝ 1 g) = ((iteratedFDeriv ℝ 1 g) ∘ (fun w => a + w)) ∘ (fun w => -a + w) := by
        ext w
        simp
      have h_diff_inv : DifferentiableAt ℝ (fun w => -a + w) (a + z) := (differentiableAt_id).const_add (-a)
      have : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 g) (a + z) := by
        rw [h_inv]
        have h_pt : (-a + (a + z)) = z := by ring
        apply DifferentiableAt.comp (x := a + z)
        · rw [h_pt]; exact h_comp
        · exact h_diff_inv
      exact hg this
    rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt h_not]

lemma iteratedFDeriv_two_comp_add_const (g : ℂ → ℝ) (a : ℂ) (z : ℂ) :
    iteratedFDeriv ℝ 2 (fun w => g (a + w)) z = iteratedFDeriv ℝ 2 g (a + z) := by
  ext m
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
  rw [fderiv_iteratedFDeriv_one_comp_add_const]

/-- 1. Invariance of 2D Euclidean Laplacian on ℂ under spatial translation. -/
theorem laplacian2D_comp_add_left (g : ℂ → ℝ) (a : ℂ) (z : ℂ) :
    laplacian2D (fun w => g (a + w)) z = laplacian2D g (a + z) := by
  dsimp [laplacian2D]
  rw [iteratedFDeriv_two_comp_add_const g a z]

lemma bochner_differential_inequality_translated
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (b c : ℝ)
    (h_boch : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w)
    (u : CP1 → M) (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (a : ℂ) (z : ℂ) :
    -b * (riemannianEnergyDensity I u (stereo_chart.symm (a + z)))^2 -
      c * (riemannianEnergyDensity I u (stereo_chart.symm (a + z))) ≤
    laplacian2D (fun w => riemannianEnergyDensity I u (stereo_chart.symm (a + w))) z := by
  rw [laplacian2D_comp_add_left (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) a z]
  exact h_boch u hu (a + z)

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

lemma heinz_maximum_interior (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
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

#print axioms heinz_maximum_interior

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

#print axioms heinz_ball_subset_and_bound

lemma heinz_transfer_to_half_ball (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z) (z₀ : ℂ) (_hz₀ : z₀ ∈ Metric.closedBall 0 r)
    (h_max : ∀ w ∈ Metric.closedBall 0 r, (r - ‖w‖)^2 * e w ≤ (r - ‖z₀‖)^2 * e z₀)
    (M_bound : (r - ‖z₀‖)^2 * e z₀ ≤ (8 / π) * ∫ w in Metric.ball 0 r, e w) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
      e z ≤ (32 / π) * r^(-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w) := by
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
  have h_chain : (r / 2)^2 * e z ≤ (8 / π) * ∫ w in Metric.ball 0 r, e w :=
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
       _ ≤ (r^2 / 4)⁻¹ * ((8 / π) * E_val) := mul_le_mul_of_nonneg_left h_chain (by positivity)
       _ = (4 / r^2) * (8 / π) * E_val := by ring
       _ = (32 / π) * (r^2)⁻¹ * E_val := by ring
       _ = (32 / π) * r^(-2 : ℝ) * E_val := by rw [← hr_pow_eq]

#print axioms heinz_transfer_to_half_ball

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
    have h_half_bound : e₀ ≤ (Real.pi * ρ^2)⁻¹ * E + (1 / 2) * e₀ := le_trans h_bound (add_le_add_left h_le_half _)
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
        ring
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

#print axioms heinz_central_value_bound_c_zero

#print axioms laplacian2D_comp_add_left
#print axioms bochner_differential_inequality_translated
