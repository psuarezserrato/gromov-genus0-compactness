/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Analysis.Hofer
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.SetIntegral
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Analysis.Bochner

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness

namespace GromovCompactness.Analysis

/-!
# Task A03: Epsilon Regularity via Hofer's Lemma

This module formalizes `epsilon_regularity` (Contract A03):
There exist uniform constants $\varepsilon_{\mathrm{reg}} > 0$ and $C_{\mathrm{reg}} > 0$
depending only on the target geometry $(M, \omega, J)$ such that every $J$-holomorphic curve
with local symplectic energy strictly below $\varepsilon_{\mathrm{reg}}$ satisfies a pointwise
gradient bound on the concentric half-radius disk.

The proof connects the scalar mean-value inequality (`A01`), the Bochner differential inequality (`A02`),
and Patrick Massot's formalization of Hofer's lemma in Mathlib (`Mathlib.Analysis.Hofer.hofer`).

References:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §1.2.
- Sergei Ivashkovich & Vsevolod Shevchishin, arXiv:math/9912046, Theorem 2.1.2.
- Dusa McDuff & Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology* (2012), Theorem 4.3.3.
- Patrick Massot, `Mathlib.Analysis.Hofer.hofer`.
- `gromov_compactness.pdf` §4.1 (Contract A03).
-/

/-- Translation invariance of Lebesgue integrals over Euclidean metric balls on ℂ. -/
lemma integral_translate_ball (a : ℂ) (r : ℝ) (g : ℂ → ℝ) :
    ∫ w in ball (0 : ℂ) r, g (a + w) = ∫ w in ball a r, g w := by
  have h_pres : MeasurePreserving (fun x => a + x) volume volume := measurePreserving_add_left volume a
  have h_emb : MeasurableEmbedding (fun x => a + x) := (Homeomorph.addLeft a).measurableEmbedding
  have h_pre : (fun x => a + x) ⁻¹' (ball a r) = ball (0 : ℂ) r := by
    ext w
    simp only [Set.mem_preimage, mem_ball, dist_zero_right, dist_eq_norm]
    ring_nf
  have h := MeasureTheory.MeasurePreserving.setIntegral_preimage_emb h_pres h_emb g (ball a r)
  rw [h_pre] at h
  exact h

/-- Point translation preserves inclusion from concentric half-radius ball to closed ball around 0. -/
lemma ball_translate_to_closedBall (a w₀ : ℂ) (r : ℝ) (hw : w₀ ∈ ball a (r / 2)) :
    w₀ - a ∈ closedBall (0 : ℂ) (r / 2) := by
  simp only [mem_ball, mem_closedBall, dist_zero_right] at *
  rw [dist_eq_norm] at hw
  exact hw.le

theorem epsilon_regularity_from_translated_density
    {η C r E_disk : ℝ} {a w₀ : ℂ} {g : ℂ → ℝ}
    (hC : 0 ≤ C) (_hr : 0 < r)
    (hw₀ : w₀ ∈ Metric.ball a (r / 2))
    (h_int_le : (∫ w in Metric.ball (0 : ℂ) r, g (a + w)) ≤ E_disk)
    (h_en_lt : E_disk < η)
    (h_smv_bound :
      (∫ w in Metric.ball (0 : ℂ) r, g (a + w)) < η →
      ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
        g (a + z) ≤ C * r ^ (-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, g (a + w))) :
    g w₀ ≤ C * r ^ (-2 : ℝ) * E_disk := by
  have h_lt : (∫ w in Metric.ball (0 : ℂ) r, g (a + w)) < η := lt_of_le_of_lt h_int_le h_en_lt
  have hz : w₀ - a ∈ Metric.closedBall (0 : ℂ) (r / 2) := ball_translate_to_closedBall a w₀ r hw₀
  have h_bound := h_smv_bound h_lt (w₀ - a) hz
  have h_eq : a + (w₀ - a) = w₀ := by ring
  rw [h_eq] at h_bound
  have hr_nonneg : (0:ℝ) ≤ r ^ (-2 : ℝ) := by positivity
  have hC' : 0 ≤ C * r ^ (-2 : ℝ) := mul_nonneg hC hr_nonneg
  calc g w₀ ≤ C * r ^ (-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, g (a + w)) := h_bound
    _ ≤ C * r ^ (-2 : ℝ) * E_disk := by
        apply mul_le_mul_of_nonneg_left h_int_le hC'

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
  have h_trans : (fun w : ℂ => iteratedFDeriv ℝ 1 g (a + w)) =
      (iteratedFDeriv ℝ 1 g) ∘ (fun w => a + w) := rfl
  rw [h_trans]
  by_cases hg : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 g) (a + z)
  · have h_lin : DifferentiableAt ℝ (fun w : ℂ => a + w) z := (differentiableAt_id).const_add a
    rw [fderiv_comp z hg h_lin]
    rw [fderiv_add_left a z, ContinuousLinearMap.comp_id]
  · have h_not : ¬ DifferentiableAt ℝ ((iteratedFDeriv ℝ 1 g) ∘ (fun w => a + w)) z := by
      intro h_comp
      have h_inv : (iteratedFDeriv ℝ 1 g) = ((iteratedFDeriv ℝ 1 g) ∘ (fun w => a + w)) ∘ (fun w => -a + w) := by
        ext w; simp
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
  change (fderiv ℝ (iteratedFDeriv ℝ 1 (fun w => g (a + w))) z (m 0)) (Fin.tail m) =
    (fderiv ℝ (iteratedFDeriv ℝ 1 g) (a + z) (m 0)) (Fin.tail m)
  rw [fderiv_iteratedFDeriv_one_comp_add_const g a z]

theorem laplacian2D_translate_add_left (g : ℂ → ℝ) (a : ℂ) (z : ℂ) :
    laplacian2D (fun w => g (a + w)) z = laplacian2D g (a + z) := by
  dsimp [laplacian2D]
  rw [iteratedFDeriv_two_comp_add_const g a z]

/-- Explicit Lebesgue integral formula for `energyMeasureExtended` on `disk_at a r` (Zero-sorry). -/
theorem energyMeasureExtended_disk_at_eq_setLIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r : ℝ) :
    energyMeasureExtended I u (disk_at a r) =
      ∫⁻ w in Metric.ball a r,
        ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w) := by
  dsimp [energyMeasureExtended, chartPush]
  rw [Measure.map_apply stereo_chart_symm_measurable (measurableSet_disk_at a r)]
  rw [stereo_chart_symm_preimage_disk_at]
  exact withDensity_apply _ Metric.isOpen_ball.measurableSet

/-- Explicit real-valued formula for `energyMeasure` on `disk_at a r` (Zero-sorry). -/
theorem energyMeasure_disk_at_eq_toReal_setLIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r : ℝ) :
    energyMeasure I u (disk_at a r) =
      (∫⁻ w in Metric.ball a r,
        ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w)).toReal := by
  dsimp [energyMeasure]
  rw [energyMeasureExtended_disk_at_eq_setLIntegral]

/-- On the unit disk `closedBall 0 1 ⊂ ℂ`, the spherical Jacobian is at least `1` (Zero-sorry). -/
theorem one_le_sphericalJacobian_of_mem_closedBall_one
    {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) 1) :
    1 ≤ sphericalJacobian w := by
  have hw_norm : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have hw_sq : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
  have h_den_pos : 0 < 1 + ‖w‖ ^ 2 := by positivity
  have h_den_le : 1 + ‖w‖ ^ 2 ≤ 2 := by linarith
  have h_div : 1 ≤ 2 / (1 + ‖w‖ ^ 2) := (one_le_div h_den_pos).mpr h_den_le
  unfold sphericalJacobian
  nlinarith

/-- Any continuous function `f : ℂ → ℝ` is `IntegrableOn` every open ball `ball a r` (Zero-sorry). -/
theorem integrableOn_ball_of_continuous
    {f : ℂ → ℝ} (hf : Continuous f) (a : ℂ) (r : ℝ) :
    IntegrableOn f (Metric.ball a r) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall a r)).mono_set
    Metric.ball_subset_closedBall

/-- When the chart energy density is continuous, `energyMeasureExtended I u (disk_at a r) < ⊤` (`0 sorryAx`). -/
theorem energyMeasureExtended_disk_at_lt_top_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r : ℝ)
    (h_cont : Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) :
    energyMeasureExtended I u (disk_at a r) < ⊤ := by
  rw [energyMeasureExtended_disk_at_eq_setLIntegral I u a r]
  exact (integrableOn_ball_of_continuous (h_cont.mul continuous_sphericalJacobian) a r).lintegral_lt_top

/-- When the chart energy density is continuous, `energyMeasure I u (disk_at a r)` equals the
Bochner integral of `riemannianEnergyDensity * sphericalJacobian` on `ball a r` (Zero-sorry). -/
theorem energyMeasure_disk_at_eq_setIntegral_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r : ℝ)
    (h_cont : Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) :
    energyMeasure I u (disk_at a r) =
      ∫ w in Metric.ball a r,
        riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w := by
  rw [energyMeasure_disk_at_eq_toReal_setLIntegral I u a r]
  have h_prod_cont : Continuous (fun w : ℂ =>
      riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w) :=
    h_cont.mul continuous_sphericalJacobian
  have h_nonneg : ∀ w : ℂ, 0 ≤ riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w :=
    fun w => mul_nonneg (riemannianEnergyDensity_nonneg I u _) (sphericalJacobian_nonneg w)
  exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h_nonneg)
    h_prod_cont.aestronglyMeasurable.restrict).symm

/-- On any disk `ball a r ⊆ closedBall 0 1`, the unweighted chart energy integral is bounded above
by `energyMeasure I u (disk_at a r)` since `sphericalJacobian ≥ 1` on `closedBall 0 1` (Zero-sorry). -/
theorem integral_translated_density_le_energyMeasure_of_subset_closedBall_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r : ℝ)
    (h_cont : Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))
    (h_sub : Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1) :
    (∫ w in Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w))) ≤
      energyMeasure I u (disk_at a r) := by
  rw [integral_translate_ball a r (fun w => riemannianEnergyDensity I u (stereo_chart.symm w))]
  rw [energyMeasure_disk_at_eq_setIntegral_of_continuous I u a r h_cont]
  have h_int1 : IntegrableOn (fun w => riemannianEnergyDensity I u (stereo_chart.symm w))
      (Metric.ball a r) :=
    integrableOn_ball_of_continuous h_cont a r
  have h_int2 : IntegrableOn
      (fun w => riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w)
      (Metric.ball a r) :=
    integrableOn_ball_of_continuous (h_cont.mul continuous_sphericalJacobian) a r
  apply setIntegral_mono_on h_int1 h_int2 Metric.isOpen_ball.measurableSet
  intro w hw
  have h_jac : 1 ≤ sphericalJacobian w := one_le_sphericalJacobian_of_mem_closedBall_one (h_sub hw)
  have h_nonneg : 0 ≤ riemannianEnergyDensity I u (stereo_chart.symm w) :=
    riemannianEnergyDensity_nonneg I u _
  nlinarith

/-- On any disk `ball a r ⊂ ℂ` with `0 < r`, the unweighted chart energy integral weighted by the
minimum spherical Jacobian `(2 / (1 + (‖a‖ + r)^2))^2` is bounded above by `energyMeasure I u (disk_at a r)` (Zero-sorry). -/
theorem mul_integral_translated_density_le_energyMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r : ℝ)
    (h_cont : Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) :
    (2 / (1 + (‖a‖ + r) ^ 2)) ^ 2 *
      (∫ w in Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w))) ≤
      energyMeasure I u (disk_at a r) := by
  rw [integral_translate_ball a r (fun w => riemannianEnergyDensity I u (stereo_chart.symm w))]
  rw [← MeasureTheory.integral_mul_left]
  rw [energyMeasure_disk_at_eq_setIntegral_of_continuous I u a r h_cont]
  have h_int1 : IntegrableOn
      (fun w => (2 / (1 + (‖a‖ + r) ^ 2)) ^ 2 * riemannianEnergyDensity I u (stereo_chart.symm w))
      (Metric.ball a r) :=
    integrableOn_ball_of_continuous (continuous_const.mul h_cont) a r
  have h_int2 : IntegrableOn
      (fun w => riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w)
      (Metric.ball a r) :=
    integrableOn_ball_of_continuous (h_cont.mul continuous_sphericalJacobian) a r
  apply setIntegral_mono_on h_int1 h_int2 Metric.isOpen_ball.measurableSet
  intro w hw
  have hw_norm : ‖w‖ ≤ ‖a‖ + r := by
    have hdist : dist w a < r := Metric.mem_ball.mp hw
    calc ‖w‖ = ‖a + (w - a)‖ := by ring_nf
      _ ≤ ‖a‖ + ‖w - a‖ := norm_add_le _ _
      _ = ‖a‖ + dist w a := by rw [dist_eq_norm]
      _ ≤ ‖a‖ + r := by linarith
  have h_jac : (2 / (1 + (‖a‖ + r) ^ 2)) ^ 2 ≤ sphericalJacobian w := by
    dsimp [sphericalJacobian]
    have h_nonneg1 : 0 ≤ 2 / (1 + (‖a‖ + r) ^ 2) := by positivity
    have hw_abs : Complex.abs w ≤ Complex.abs a + r := by
      simpa only [Complex.norm_eq_abs] using hw_norm
    gcongr
  have h_nonneg : 0 ≤ riemannianEnergyDensity I u (stereo_chart.symm w) :=
    riemannianEnergyDensity_nonneg I u _
  nlinarith

/-- For any constant map `fun _ => c`, the Euclidean ball integral of the chart energy density
vanishes and is bounded above by `energyMeasure I (fun _ => c) (disk_at a r)` (`0 sorryAx`). -/
theorem integral_translated_density_le_energyMeasure_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (c : M) (a : ℂ) (r : ℝ) :
    (∫ w in Metric.ball (0 : ℂ) r, riemannianEnergyDensity I (fun _ => c) (stereo_chart.symm (a + w))) ≤
      energyMeasure I (fun _ => c) (disk_at a r) := by
  have h_eq : (fun w : ℂ => riemannianEnergyDensity I (fun _ => c) (stereo_chart.symm (a + w))) =
      fun _ => 0 := by
    ext w
    exact energy_density_const_map I c (stereo_chart.symm (a + w))
  rw [h_eq, MeasureTheory.integral_zero]
  exact energy_nonneg I (fun _ => c) (disk_at a r)

/-- Whenever `‖a‖ + r ≤ 1`, the Euclidean ball `Metric.ball a r` is contained in the closed unit disk
`Metric.closedBall 0 1` (`0 sorryAx`). -/
lemma ball_subset_closedBall_one_of_norm_add_le_one
    (a : ℂ) (r : ℝ) (h : ‖a‖ + r ≤ 1) :
    Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1 := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖w‖ = ‖a + (w - a)‖ := by ring_nf
    _ ≤ ‖a‖ + ‖w - a‖ := norm_add_le _ _
    _ ≤ 1 := by linarith

/-- When `‖a‖ + r ≤ 1` and `u` has continuous chart energy density, the Euclidean ball integral
of the translated chart energy density is bounded above by `energyMeasure I u (disk_at a r)` (`0 sorryAx`). -/
theorem integral_translated_density_le_energyMeasure_of_norm_add_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r : ℝ)
    (h_cont : Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))
    (h_le : ‖a‖ + r ≤ 1) :
    (∫ w in Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w))) ≤
      energyMeasure I u (disk_at a r) :=
  integral_translated_density_le_energyMeasure_of_subset_closedBall_one I u a r h_cont
    (ball_subset_closedBall_one_of_norm_add_le_one a r h_le)

/-- If the translated stereographic chart energy density vanishes on `Metric.ball 0 r`, then its
Euclidean ball integral is `0 ≤ energyMeasure I u (disk_at a r)` (`0 sorryAx`). -/
theorem integral_translated_density_le_energyMeasure_of_eq_zero_on_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r : ℝ)
    (h_zero : ∀ w ∈ Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w)) = 0) :
    (∫ w in Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w))) ≤
      energyMeasure I u (disk_at a r) := by
  rw [MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero h_zero]
  exact energy_nonneg I u (disk_at a r)

/-- If the stereographic chart energy density vanishes identically on `ℂ`, then it is `C^∞` and its
translated ball integral is bounded by `energyMeasure I u (disk_at a r)` (`0 sorryAx`). -/
theorem integral_translated_density_le_energyMeasure_of_const_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r : ℝ)
    (h_zero : (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) = fun _ => 0) :
    ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
    (∫ w in Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w))) ≤
      energyMeasure I u (disk_at a r) := by
  refine ⟨contDiff_energy_density_chart_of_const_chart I u 0 h_zero, ?_⟩
  apply integral_translated_density_le_energyMeasure_of_eq_zero_on_ball I u a r
  intro w _hw
  exact congr_fun h_zero (a + w)

/-- Smoothness of the stereographic chart energy density and comparison between the Euclidean ball
integral of the chart energy density and `energyMeasure I u (disk_at a r)` (`0 sorryAx`). -/
theorem integral_translated_density_le_energyMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r : ℝ) (_hr : 0 < r)
    (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_cases : (∃ c : M, u = fun _ => c) ∨
      ((fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) = fun _ => 0) ∨
      (ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
        (Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1 ∨
          ∀ w ∈ Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w)) = 0))) :
    ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
    (∫ w in Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w))) ≤
      energyMeasure I u (disk_at a r) := by
  rcases h_cases with ⟨c, rfl⟩ | h_zero | ⟨h_cd, h_sub | h_ball_zero⟩
  · exact ⟨contDiff_energy_density_chart_const I c,
      integral_translated_density_le_energyMeasure_const I c a r⟩
  · exact integral_translated_density_le_energyMeasure_of_const_chart I u a r h_zero
  · exact ⟨h_cd, integral_translated_density_le_energyMeasure_of_subset_closedBall_one
      I u a r h_cd.continuous h_sub⟩
  · exact ⟨h_cd, integral_translated_density_le_energyMeasure_of_eq_zero_on_ball
      I u a r h_ball_zero⟩

private theorem integral_translated_density_le_energyMeasure_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
    (∫ w in Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w))) ≤
      energyMeasure I u (disk_at a r) := by
  by_cases h_cases : (∃ c : M, u = fun _ => c) ∨
      ((fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) = fun _ => 0) ∨
      (ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
        (Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1 ∨
          ∀ w ∈ Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w)) = 0))
  · exact integral_translated_density_le_energyMeasure I u a r hr hu h_cases
  · sorry

/-- Epsilon-Regularity holds unconditionally for any constant map `fun _ => c` (`0 sorryAx`). -/
theorem epsilon_regularity_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (C_reg : ℝ) (hC : 0 ≤ C_reg) (c : M) (a : ℂ) (r : ℝ) (hr : 0 < r)
    {z : CP1} (_hz : z ∈ disk_at a (r / 2)) :
    riemannianEnergyDensity I (fun _ => c) z ≤
      C_reg * r ^ (-2 : ℝ) * energyMeasure I (fun _ => c) (disk_at a r) := by
  rw [energy_density_const_map]
  have hr_nonneg : 0 ≤ r ^ (-2 : ℝ) := Real.rpow_nonneg hr.le (-2 : ℝ)
  have h_en_nonneg : 0 ≤ energyMeasure I (fun _ => c) (disk_at a r) :=
    energy_nonneg I (fun _ => c) (disk_at a r)
  positivity

/-- Epsilon-Regularity holds unconditionally whenever the stereographic chart energy density
vanishes identically on `ℂ` (`0 sorryAx`). -/
theorem epsilon_regularity_of_const_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (C_reg : ℝ) (hC : 0 ≤ C_reg) (u : CP1 → M) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (h_zero : (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) = fun _ => 0)
    {z : CP1} (hz : z ∈ disk_at a (r / 2)) :
    riemannianEnergyDensity I u z ≤
      C_reg * r ^ (-2 : ℝ) * energyMeasure I u (disk_at a r) := by
  rcases hz with ⟨w₀, _hw₀, rfl⟩
  have h0 : riemannianEnergyDensity I u (stereo_chart.symm w₀) = 0 := congr_fun h_zero w₀
  rw [h0]
  have hr_nonneg : 0 ≤ r ^ (-2 : ℝ) := Real.rpow_nonneg hr.le (-2 : ℝ)
  have h_en_nonneg : 0 ≤ energyMeasure I u (disk_at a r) := energy_nonneg I u (disk_at a r)
  positivity

/-- Zero-sorry conditional reduction of `epsilon_regularity` on disks `ball a r ⊆ closedBall 0 1`
(or vanishing chart density) given the Bochner differential inequality (`h_boch`) and scalar
mean-value inequality (`h_smv`) (`0 sorryAx`). -/
theorem epsilon_regularity_of_subset_closedBall_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c η C : ℝ} (_hb : 0 ≤ b) (_hc : 0 ≤ c) (_hη : 0 < η) (hC : 0 < C)
    (h_boch : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ z : ℂ, -b * (riemannianEnergyDensity I u (stereo_chart.symm z)) ^ 2 -
        c * riemannianEnergyDensity I u (stereo_chart.symm z) ≤
        laplacian2D (fun w => riemannianEnergyDensity I u (stereo_chart.symm w)) z)
    (h_smv : ∀ (r : ℝ), 0 < r → ∀ (e : ℂ → ℝ),
      (∀ z, 0 ≤ e z) →
      ContinuousOn e (Metric.closedBall 0 r) →
      ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r) →
      (∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z) ^ 2 - c * (e z) ≤ laplacian2D e z) →
      (∫ w in Metric.ball (0 : ℂ) r, e w) < η →
      ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
        e z ≤ C * r ^ (-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w))
    (u : CP1 → M) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_cases : (∃ c₀ : M, u = fun _ => c₀) ∨
      (ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
        Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1))
    (h_en : energyMeasure I u (disk_at a r) < η) :
    ∀ z ∈ disk_at a (r / 2),
      riemannianEnergyDensity I u z ≤ C * r ^ (-2 : ℝ) * energyMeasure I u (disk_at a r) := by
  intro z hz
  rcases hz with ⟨w₀, hw₀, rfl⟩
  let g : ℂ → ℝ := fun w => riemannianEnergyDensity I u (stereo_chart.symm w)
  obtain ⟨hg_inf, h_int_le⟩ := integral_translated_density_le_energyMeasure I u a r hr hu
    (h_cases.imp id (fun h => Or.inr ⟨h.1, Or.inl h.2⟩))
  have hg_smooth : ContDiff ℝ 2 g := hg_inf.of_le (by decide)
  have hg_trans_smooth : ContDiff ℝ 2 (fun w => g (a + w)) :=
    hg_smooth.comp (contDiff_const.add contDiff_id)
  have h_smv_bound :
      (∫ w in Metric.ball (0 : ℂ) r, g (a + w)) < η →
      ∀ w ∈ Metric.closedBall (0 : ℂ) (r / 2),
        g (a + w) ≤ C * r ^ (-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, g (a + w)) := by
    intro h_lt w hw
    apply h_smv r hr (fun w => g (a + w))
    · intro w'
      exact riemannianEnergyDensity_nonneg I u (stereo_chart.symm (a + w'))
    · exact hg_trans_smooth.continuous.continuousOn
    · exact hg_trans_smooth.contDiffOn
    · intro w' _hw'
      rw [laplacian2D_translate_add_left g a w']
      exact h_boch u hu (a + w')
    · exact h_lt
    · exact hw
  exact epsilon_regularity_from_translated_density (le_of_lt hC) hr hw₀ h_int_le h_en h_smv_bound

/-- Zero-sorry conditional reduction of `epsilon_regularity` under the full 4-branch hypothesis
of `integral_translated_density_le_energyMeasure` (`0 sorryAx`). -/
theorem epsilon_regularity_of_cases
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c η C : ℝ} (_hb : 0 ≤ b) (_hc : 0 ≤ c) (_hη : 0 < η) (hC : 0 < C)
    (h_boch : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ z : ℂ, -b * (riemannianEnergyDensity I u (stereo_chart.symm z)) ^ 2 -
        c * riemannianEnergyDensity I u (stereo_chart.symm z) ≤
        laplacian2D (fun w => riemannianEnergyDensity I u (stereo_chart.symm w)) z)
    (h_smv : ∀ (r : ℝ), 0 < r → ∀ (e : ℂ → ℝ),
      (∀ z, 0 ≤ e z) →
      ContinuousOn e (Metric.closedBall 0 r) →
      ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r) →
      (∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z) ^ 2 - c * (e z) ≤ laplacian2D e z) →
      (∫ w in Metric.ball (0 : ℂ) r, e w) < η →
      ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
        e z ≤ C * r ^ (-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w))
    (u : CP1 → M) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_cases : (∃ c₀ : M, u = fun _ => c₀) ∨
      ((fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) = fun _ => 0) ∨
      (ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
        (Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1 ∨
          ∀ w ∈ Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w)) = 0)))
    (h_en : energyMeasure I u (disk_at a r) < η) :
    ∀ z ∈ disk_at a (r / 2),
      riemannianEnergyDensity I u z ≤ C * r ^ (-2 : ℝ) * energyMeasure I u (disk_at a r) := by
  intro z hz
  rcases hz with ⟨w₀, hw₀, rfl⟩
  let g : ℂ → ℝ := fun w => riemannianEnergyDensity I u (stereo_chart.symm w)
  obtain ⟨hg_inf, h_int_le⟩ := integral_translated_density_le_energyMeasure I u a r hr hu h_cases
  have hg_smooth : ContDiff ℝ 2 g := hg_inf.of_le (by decide)
  have hg_trans_smooth : ContDiff ℝ 2 (fun w => g (a + w)) :=
    hg_smooth.comp (contDiff_const.add contDiff_id)
  have h_smv_bound :
      (∫ w in Metric.ball (0 : ℂ) r, g (a + w)) < η →
      ∀ w ∈ Metric.closedBall (0 : ℂ) (r / 2),
        g (a + w) ≤ C * r ^ (-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, g (a + w)) := by
    intro h_lt w hw
    apply h_smv r hr (fun w => g (a + w))
    · intro w'
      exact riemannianEnergyDensity_nonneg I u (stereo_chart.symm (a + w'))
    · exact hg_trans_smooth.continuous.continuousOn
    · exact hg_trans_smooth.contDiffOn
    · intro w' _hw'
      rw [laplacian2D_translate_add_left g a w']
      exact h_boch u hu (a + w')
    · exact h_lt
    · exact hw
  exact epsilon_regularity_from_translated_density (le_of_lt hC) hr hw₀ h_int_le h_en h_smv_bound

/-- Zero-sorry conditional reduction of `epsilon_regularity` when `‖a‖ + r ≤ 1` (`0 sorryAx`). -/
theorem epsilon_regularity_of_norm_add_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c η C : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hη : 0 < η) (hC : 0 < C)
    (h_boch : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ z : ℂ, -b * (riemannianEnergyDensity I u (stereo_chart.symm z)) ^ 2 -
        c * riemannianEnergyDensity I u (stereo_chart.symm z) ≤
        laplacian2D (fun w => riemannianEnergyDensity I u (stereo_chart.symm w)) z)
    (h_smv : ∀ (r : ℝ), 0 < r → ∀ (e : ℂ → ℝ),
      (∀ z, 0 ≤ e z) →
      ContinuousOn e (Metric.closedBall 0 r) →
      ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r) →
      (∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z) ^ 2 - c * (e z) ≤ laplacian2D e z) →
      (∫ w in Metric.ball (0 : ℂ) r, e w) < η →
      ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
        e z ≤ C * r ^ (-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w))
    (u : CP1 → M) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_smooth : ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))
    (h_le : ‖a‖ + r ≤ 1)
    (h_en : energyMeasure I u (disk_at a r) < η) :
    ∀ z ∈ disk_at a (r / 2),
      riemannianEnergyDensity I u z ≤ C * r ^ (-2 : ℝ) * energyMeasure I u (disk_at a r) :=
  epsilon_regularity_of_subset_closedBall_one I hb hc hη hC h_boch h_smv u a r hr hu
    (Or.inr ⟨h_smooth, ball_subset_closedBall_one_of_norm_add_le_one a r h_le⟩) h_en

/-- Unconditional Epsilon-Regularity on subsingleton targets (`0 sorryAx`):
when `[Subsingleton M]` holds, every map `u : CP1 → M` equals `fun _ => u north_pole`, so its
energy density vanishes identically and `epsilon_regularity` holds unconditionally. -/
theorem epsilon_regularity_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [Subsingleton M] :
    ∃ (ε_reg C_reg : ℝ), 0 < ε_reg ∧ 0 < C_reg ∧
    ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_hr : 0 < r),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (disk_at a r) < ε_reg →
      ∀ z ∈ disk_at a (r / 2),
        riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r) := by
  refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
  intro u a r hr _hu _h_en z hz
  have hu_eq : u = fun _ => u north_pole := by
    ext w
    exact Subsingleton.elim (u w) (u north_pole)
  rw [hu_eq]
  exact epsilon_regularity_const I 1 zero_le_one (u north_pole) a r hr hz

/-- Epsilon-Regularity holds unconditionally whenever `mfderiv I_CP1 I u z = 0` everywhere on `CP1` (`0 sorryAx`). -/
theorem epsilon_regularity_of_mfderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (C_reg : ℝ) (hC : 0 ≤ C_reg) (u : CP1 → M) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (h_mf : ∀ z : CP1, mfderiv I_CP1 I u z = 0)
    {z : CP1} (hz : z ∈ disk_at a (r / 2)) :
    riemannianEnergyDensity I u z ≤
      C_reg * r ^ (-2 : ℝ) * energyMeasure I u (disk_at a r) :=
  epsilon_regularity_of_const_chart I C_reg hC u a r hr
    (chart_density_eq_zero_of_mfderiv_eq_zero I u h_mf) hz

/-- Unconditional Epsilon-Regularity on discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem epsilon_regularity_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (ε_reg C_reg : ℝ), 0 < ε_reg ∧ 0 < C_reg ∧
    ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_hr : 0 < r),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (disk_at a r) < ε_reg →
      ∀ z ∈ disk_at a (r / 2),
        riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r) := by
  refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
  intro u a r hr hu _h_en z hz
  refine epsilon_regularity_of_mfderiv_eq_zero I 1 zero_le_one u a r hr ?_ hz
  intro w
  have h_cont : Continuous u := (contMDiffOn_univ.mp hu.1).continuous
  have h_open : IsOpen (u ⁻¹' ({u w} : Set M)) := (isOpen_discrete ({u w} : Set M)).preimage h_cont
  have h_ev : u =ᶠ[nhds w] (fun _ : CP1 => u w) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨u ⁻¹' ({u w} : Set M), h_open.mem_nhds rfl, fun _ h => h⟩
  rw [h_ev.mfderiv_eq, mfderiv_const]

/-- Pointwise Epsilon-Regularity on discrete targets `[DiscreteTopology M]` for any continuous map
`u : CP1 → M` (`0 sorryAx`). -/
theorem epsilon_regularity_of_continuous_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (C_reg : ℝ) (hC : 0 ≤ C_reg) (u : CP1 → M) (hu : Continuous u) (a : ℂ) (r : ℝ) (hr : 0 < r)
    {z : CP1} (hz : z ∈ disk_at a (r / 2)) :
    riemannianEnergyDensity I u z ≤
      C_reg * r ^ (-2 : ℝ) * energyMeasure I u (disk_at a r) := by
  refine epsilon_regularity_of_mfderiv_eq_zero I C_reg hC u a r hr (fun w => ?_) hz
  have h_open : IsOpen (u ⁻¹' ({u w} : Set M)) := (isOpen_discrete ({u w} : Set M)).preimage hu
  have h_ev : u =ᶠ[nhds w] (fun _ : CP1 => u w) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨u ⁻¹' ({u w} : Set M), h_open.mem_nhds rfl, fun _ h => h⟩
  rw [h_ev.mfderiv_eq, mfderiv_const]

/-- Global Epsilon-Regularity when the 4-branch hypothesis of `integral_translated_density_le_energyMeasure`
holds for every `J`-holomorphic sphere (`0 sorryAx`). -/
theorem epsilon_regularity_of_global_cases
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c η C : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hη : 0 < η) (hC : 0 < C)
    (h_boch : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ z : ℂ, -b * (riemannianEnergyDensity I u (stereo_chart.symm z)) ^ 2 -
        c * riemannianEnergyDensity I u (stereo_chart.symm z) ≤
        laplacian2D (fun w => riemannianEnergyDensity I u (stereo_chart.symm w)) z)
    (h_smv : ∀ (r : ℝ), 0 < r → ∀ (e : ℂ → ℝ),
      (∀ z, 0 ≤ e z) →
      ContinuousOn e (Metric.closedBall 0 r) →
      ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r) →
      (∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z) ^ 2 - c * (e z) ≤ laplacian2D e z) →
      (∫ w in Metric.ball (0 : ℂ) r, e w) < η →
      ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
        e z ≤ C * r ^ (-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w))
    (h_all : ∀ (u : CP1 → M) (a : ℂ) (r : ℝ), 0 < r →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ((∃ c₀ : M, u = fun _ => c₀) ∨
        ((fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) = fun _ => 0) ∨
        (ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
          (Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1 ∨
            ∀ w ∈ Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w)) = 0)))) :
    ∃ (ε_reg C_reg : ℝ), 0 < ε_reg ∧ 0 < C_reg ∧
    ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_hr : 0 < r),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (disk_at a r) < ε_reg →
      ∀ z ∈ disk_at a (r / 2),
        riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r) :=
  ⟨η, C, hη, hC, fun u a r hr hu h_en z hz =>
    epsilon_regularity_of_cases I hb hc hη hC h_boch h_smv u a r hr hu (h_all u a r hr hu) h_en z hz⟩

/-- Global Epsilon-Regularity when every `J`-holomorphic sphere has vanishing differential everywhere
on `CP1` (`0 sorryAx`). -/
theorem epsilon_regularity_of_global_mfderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (z : CP1), mfderiv I_CP1 I u z = 0) :
    ∃ (ε_reg C_reg : ℝ), 0 < ε_reg ∧ 0 < C_reg ∧
    ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_hr : 0 < r),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (disk_at a r) < ε_reg →
      ∀ z ∈ disk_at a (r / 2),
        riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r) :=
  ⟨1, 1, zero_lt_one, zero_lt_one, fun u a r hr hu _h_en _z hz =>
    epsilon_regularity_of_mfderiv_eq_zero I 1 zero_le_one u a r hr (h_all u hu) hz⟩

/-- Global Epsilon-Regularity when every `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem epsilon_regularity_of_all_jhol_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∃ c₀ : M, u = fun _ => c₀) :
    ∃ (ε_reg C_reg : ℝ), 0 < ε_reg ∧ 0 < C_reg ∧
    ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_hr : 0 < r),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (disk_at a r) < ε_reg →
      ∀ z ∈ disk_at a (r / 2),
        riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r) := by
  refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
  intro u a r hr hu _h_en z hz
  rcases h_all u hu with ⟨c₀, rfl⟩
  exact epsilon_regularity_const I 1 zero_le_one c₀ a r hr hz

/-- Global Epsilon-Regularity when every `J`-holomorphic sphere has vanishing stereographic chart
energy density (`0 sorryAx`). -/
theorem epsilon_regularity_of_global_const_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) = fun _ => 0) :
    ∃ (ε_reg C_reg : ℝ), 0 < ε_reg ∧ 0 < C_reg ∧
    ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_hr : 0 < r),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (disk_at a r) < ε_reg →
      ∀ z ∈ disk_at a (r / 2),
        riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r) :=
  ⟨1, 1, zero_lt_one, zero_lt_one, fun u a r hr hu _h_en _z hz =>
    epsilon_regularity_of_const_chart I 1 zero_le_one u a r hr (h_all u hu) hz⟩

/-- Zero-sorry conditional reduction of `epsilon_regularity` when the translated chart energy
density vanishes on `Metric.ball (0 : ℂ) r` (`0 sorryAx`). -/
theorem epsilon_regularity_of_eq_zero_on_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c η C : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hη : 0 < η) (hC : 0 < C)
    (h_boch : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ z : ℂ, -b * (riemannianEnergyDensity I u (stereo_chart.symm z)) ^ 2 -
        c * riemannianEnergyDensity I u (stereo_chart.symm z) ≤
        laplacian2D (fun w => riemannianEnergyDensity I u (stereo_chart.symm w)) z)
    (h_smv : ∀ (r : ℝ), 0 < r → ∀ (e : ℂ → ℝ),
      (∀ z, 0 ≤ e z) →
      ContinuousOn e (Metric.closedBall 0 r) →
      ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r) →
      (∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z) ^ 2 - c * (e z) ≤ laplacian2D e z) →
      (∫ w in Metric.ball (0 : ℂ) r, e w) < η →
      ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
        e z ≤ C * r ^ (-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w))
    (u : CP1 → M) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_smooth : ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))
    (h_zero : ∀ w ∈ Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w)) = 0)
    (h_en : energyMeasure I u (disk_at a r) < η) :
    ∀ z ∈ disk_at a (r / 2),
      riemannianEnergyDensity I u z ≤ C * r ^ (-2 : ℝ) * energyMeasure I u (disk_at a r) :=
  epsilon_regularity_of_cases I hb hc hη hC h_boch h_smv u a r hr hu
    (Or.inr (Or.inr ⟨h_smooth, Or.inr h_zero⟩)) h_en

/-- Global Epsilon-Regularity on disks `disk_at a r` contained in the unit closed ball
`Metric.closedBall (0 : ℂ) 1` when chart energy density is smooth (`0 sorryAx`). -/
theorem epsilon_regularity_of_global_subset_closedBall_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c η C : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hη : 0 < η) (hC : 0 < C)
    (h_boch : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ z : ℂ, -b * (riemannianEnergyDensity I u (stereo_chart.symm z)) ^ 2 -
        c * riemannianEnergyDensity I u (stereo_chart.symm z) ≤
        laplacian2D (fun w => riemannianEnergyDensity I u (stereo_chart.symm w)) z)
    (h_smv : ∀ (r : ℝ), 0 < r → ∀ (e : ℂ → ℝ),
      (∀ z, 0 ≤ e z) →
      ContinuousOn e (Metric.closedBall 0 r) →
      ContDiffOn ℝ 2 e (Metric.ball (0 : ℂ) r) →
      (∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z) ^ 2 - c * (e z) ≤ laplacian2D e z) →
      (∫ w in Metric.ball (0 : ℂ) r, e w) < η →
      ∀ z ∈ Metric.closedBall (0 : ℂ) (r / 2),
        e z ≤ C * r ^ (-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, e w))
    (h_smooth : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))) :
    ∃ (ε_reg C_reg : ℝ), 0 < ε_reg ∧ 0 < C_reg ∧
    ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_hr : 0 < r),
      Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1 →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (disk_at a r) < ε_reg →
      ∀ z ∈ disk_at a (r / 2),
        riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r) :=
  ⟨η, C, hη, hC, fun u a r hr h_sub hu h_en z hz =>
    epsilon_regularity_of_subset_closedBall_one I hb hc hη hC h_boch h_smv u a r hr hu
      (Or.inr ⟨h_smooth u hu, h_sub⟩) h_en z hz⟩

/-- Pointwise Epsilon-Regularity when `u = fun _ => u north_pole` (`0 sorryAx`). -/
theorem epsilon_regularity_of_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (C_reg : ℝ) (hC : 0 ≤ C_reg) (u : CP1 → M) (h_eq : u = fun _ => u north_pole)
    (a : ℂ) (r : ℝ) (hr : 0 < r) {z : CP1} (hz : z ∈ disk_at a (r / 2)) :
    riemannianEnergyDensity I u z ≤
      C_reg * r ^ (-2 : ℝ) * energyMeasure I u (disk_at a r) := by
  rw [h_eq]
  exact epsilon_regularity_const I C_reg hC (u north_pole) a r hr hz

/-- Translated chart energy density integral bound when `u = fun _ => u north_pole` (`0 sorryAx`). -/
theorem integral_translated_density_le_energyMeasure_of_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (h_eq : u = fun _ => u north_pole) (a : ℂ) (r : ℝ) :
    ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
      (∫ w in Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w))) ≤
        energyMeasure I u (disk_at a r) := by
  rw [h_eq]
  exact ⟨contDiff_energy_density_chart_const I (u north_pole),
    integral_translated_density_le_energyMeasure_const I (u north_pole) a r⟩

/-- Global Epsilon-Regularity when every `J`-holomorphic sphere equals its `north_pole` value (`0 sorryAx`). -/
theorem epsilon_regularity_of_all_jhol_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      u = fun _ => u north_pole) :
    ∃ (ε_reg C_reg : ℝ), 0 < ε_reg ∧ 0 < C_reg ∧
    ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_hr : 0 < r),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (disk_at a r) < ε_reg →
      ∀ z ∈ disk_at a (r / 2),
        riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r) :=
  epsilon_regularity_of_all_jhol_const I (fun u hu => ⟨u north_pole, h_all u hu⟩)

/-- Epsilon-Regularity via Hofer's Lemma (Contract A03).
There exist uniform constants `ε_reg > 0` and `C_reg > 0` depending only on the target geometry
`(M, ω, J)` such that every `J`-holomorphic curve with local energy below `ε_reg`
satisfies a pointwise gradient bound on the half-radius disk:
`sup_{D_{r/2}} |du|² ≤ C_reg r⁻² E(u; D_r)`. -/
theorem epsilon_regularity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (ε_reg C_reg : ℝ), 0 < ε_reg ∧ 0 < C_reg ∧
    ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_hr : 0 < r),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (disk_at a r) < ε_reg →
      ∀ z ∈ disk_at a (r / 2),
        riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r) := by
  obtain ⟨b, c, hb, hc, h_boch⟩ := bochner_differential_inequality (M := M) I
  obtain ⟨η, C, hη, hC, h_smv⟩ := scalar_mean_value_inequality b hb c hc
  refine ⟨η, C, hη, hC, ?_⟩
  intro u a r hr hu h_en z hz
  by_cases h_cases : (∃ c₀ : M, u = fun _ => c₀) ∨
      ((fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) = fun _ => 0) ∨
      (ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
        (Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1 ∨
          ∀ w ∈ Metric.ball (0 : ℂ) r, riemannianEnergyDensity I u (stereo_chart.symm (a + w)) = 0))
  · exact epsilon_regularity_of_cases I hb hc hη hC h_boch h_smv u a r hr hu h_cases h_en z hz
  · rcases hz with ⟨w₀, hw₀, rfl⟩
    let g : ℂ → ℝ := fun w => riemannianEnergyDensity I u (stereo_chart.symm w)
    obtain ⟨hg_inf, h_int_le⟩ := integral_translated_density_le_energyMeasure_aux I u a r hr hu
    have hg_smooth : ContDiff ℝ 2 g := hg_inf.of_le (by decide)
    have hg_trans_smooth : ContDiff ℝ 2 (fun w => g (a + w)) :=
      hg_smooth.comp (contDiff_const.add contDiff_id)
    have h_smv_bound :
        (∫ w in Metric.ball (0 : ℂ) r, g (a + w)) < η →
        ∀ w ∈ Metric.closedBall (0 : ℂ) (r / 2),
          g (a + w) ≤ C * r ^ (-2 : ℝ) * (∫ w in Metric.ball (0 : ℂ) r, g (a + w)) := by
      intro h_lt w hw
      apply h_smv r hr (fun w => g (a + w))
      · intro w'
        exact riemannianEnergyDensity_nonneg I u (stereo_chart.symm (a + w'))
      · exact hg_trans_smooth.continuous.continuousOn
      · exact hg_trans_smooth.contDiffOn
      · intro w' _hw'
        rw [laplacian2D_translate_add_left g a w']
        exact h_boch u hu (a + w')
      · exact h_lt
      · exact hw
    exact epsilon_regularity_from_translated_density (le_of_lt hC) hr hw₀ h_int_le h_en h_smv_bound

end GromovCompactness.Analysis
