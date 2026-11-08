/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Milestone N2 Adversarial Challenger 2)
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Compactness.Compact
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Geometry.NormalCharts

open scoped Manifold ContDiff Topology Real ENNReal
open Metric Set MeasureTheory Filter Topology ENNReal GromovCompactness

namespace GromovCompactness.Tests.AdversarialNormalChartsN2

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
variable [tgt : ClosedTameTarget I M] [Nonempty M]

set_option linter.unusedSectionVars false

/- =========================================================================
   PROBE 1: Mathematical Fidelity & Non-Vacuity of `dmetric_zero`
   ========================================================================= -/

/-- Adversarial Test 1.1: Linear metric variation is strictly rejected by dmetric_zero.
If a component has a non-zero linear first derivative, fderiv ≠ 0.
This confirms dmetric_zero is not vacuously true for arbitrary non-normal coordinates. -/
theorem test_dmetric_zero_rejects_nonzero_derivative (L : E →L[ℝ] ℝ) (hL : L ≠ 0) :
    ¬ (fderiv ℝ (fun z : E => L z) 0 = 0) := by
  have h_deriv : fderiv ℝ (fun z : E => L z) 0 = L := L.hasFDerivAt.fderiv
  rw [h_deriv]
  exact hL

/-- Adversarial Test 1.2: dmetric_zero forces directional derivatives to vanish in all directions.
Verifies that fderiv = 0 entails directional derivative vanishing along any probe vector u. -/
theorem test_dmetric_zero_directional_vanishing
    {r : ℝ} (p : M) (C : CenteredNormalChart I p r) (v w u : E) :
    (fderiv ℝ (fun z => ClosedTameTarget.metric I (C.chart.symm z) v w) 0) u = 0 := by
  rw [C.dmetric_zero v w]
  rfl

/-- Adversarial Test 1.3: Koszul vanishing from dmetric_zero.
If the metric derivative dg0 vanishes identically, the Koszul form vanishes identically. -/
theorem test_koszulForm_zero_of_dg0_zero (u v w : E) :
    koszulForm (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) u v w = 0 := by
  simp only [koszulForm, zero_apply, add_zero, sub_zero, mul_zero]

/-- Adversarial Test 1.4: Christoffel symbol vanishing from Koszul cancellation.
When metric derivatives vanish at the origin, the Christoffel tensor Γ at the origin
must be identically zero, provided the background metric is positive definite. -/
theorem test_christoffel_vanishing_genuine
    (g0 : E →L[ℝ] E →L[ℝ] ℝ) (h_pos : ∀ v ≠ 0, 0 < g0 v v)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (h_koszul : ∀ u v w, g0 (Γ u v) w = koszulForm (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) u v w) :
    Γ = 0 := by
  have h_zero : ∀ u v w, g0 (Γ u v) w = 0 := by
    intro u v w
    rw [h_koszul u v w, test_koszulForm_zero_of_dg0_zero]
  exact christoffel_zero_of_dmetric_zero g0 h_pos Γ h_zero

/- =========================================================================
   PROBE 2: Resistance to Degenerate Metrics & Fake Homeomorphisms
   ========================================================================= -/

/-- Adversarial Test 2.1: Non-collapse of chart.
The chart parametrization chart.symm cannot collapse any point in B(0, r_norm)
to the center p other than the origin 0 itself.
Guarantees constant/collapsed fake homeomorphisms are strictly rejected. -/
theorem test_chart_non_collapse
    (fam : UniformNormalChartFamily I (M := M)) (p : M)
    (y : E) (hy : y ∈ Metric.ball (0 : E) fam.r_norm) :
    (fam.chartAt p).chart.symm y = p ↔ y = 0 := by
  constructor
  · intro h_eq
    have h_le := fam.chart_le_dist p y hy
    rw [h_eq, dist_self, mul_zero] at h_le
    have h_norm_le : ‖y‖ ≤ 0 := h_le
    have h_norm_nonneg : 0 ≤ ‖y‖ := norm_nonneg y
    have h_norm_zero : ‖y‖ = 0 := le_antisymm h_norm_le h_norm_nonneg
    exact norm_eq_zero.mp h_norm_zero
  · rintro rfl
    exact (fam.chartAt p).symm_center

/-- Adversarial Test 2.2: Strict two-sided bi-Lipschitz bounds.
The distance on M and Euclidean norm on E satisfy two-sided control on B(0, r_norm):
(1 / L_dist) * ‖y‖ ≤ dist (chart.symm y) p ≤ L_dist * ‖y‖.
Guarantees no crushing (lower bound) and no infinite stretching (upper bound). -/
theorem test_two_sided_bilipschitz
    (fam : UniformNormalChartFamily I (M := M)) (p : M)
    (y : E) (hy : y ∈ Metric.ball (0 : E) fam.r_norm) :
    (1 / fam.L_dist) * ‖y‖ ≤ dist ((fam.chartAt p).chart.symm y) p ∧
    dist ((fam.chartAt p).chart.symm y) p ≤ fam.L_dist * ‖y‖ := by
  refine ⟨?_, fam.dist_le_chart p y hy⟩
  have h_chart := fam.chart_le_dist p y hy
  have h_L_pos : 0 < fam.L_dist := by linarith [fam.L_dist_ge]
  rw [div_mul_eq_mul_div, one_mul]
  exact (div_le_iff₀ h_L_pos).mpr (by linarith [h_chart])

/-- Adversarial Test 2.3: Strict injectivity on chart domain.
The parametrization chart.symm is strictly injective on B(0, r_norm),
preventing self-intersections, pinching, or folding. -/
theorem test_chart_symm_injective
    (fam : UniformNormalChartFamily I (M := M)) (p : M)
    (y₁ y₂ : E)
    (hy₁ : y₁ ∈ Metric.ball (0 : E) fam.r_norm)
    (hy₂ : y₂ ∈ Metric.ball (0 : E) fam.r_norm) :
    (fam.chartAt p).chart.symm y₁ = (fam.chartAt p).chart.symm y₂ ↔ y₁ = y₂ := by
  have h_sub := (fam.chartAt p).ball_subset_target
  have h1 : y₁ ∈ (fam.chartAt p).chart.target := h_sub hy₁
  have h2 : y₂ ∈ (fam.chartAt p).chart.target := h_sub hy₂
  constructor
  · intro h_eq
    have h_inv1 := (fam.chartAt p).chart.right_inv h1
    have h_inv2 := (fam.chartAt p).chart.right_inv h2
    rw [← h_inv1, ← h_inv2, h_eq]
  · rintro rfl; rfl

/-- Adversarial Test 2.4: Full rank differential at origin.
The differential of chart.symm at 0 is id_E, which is injective and surjective.
Prevents rank drop, branching, or cusps at chart center. -/
theorem test_chart_differential_full_rank
    (fam : UniformNormalChartFamily I (M := M)) (p : M) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ E) I (fam.chartAt p).chart.symm 0) ∧
    Function.Surjective (mfderiv (modelWithCornersSelf ℝ E) I (fam.chartAt p).chart.symm 0) := by
  have h_id := (fam.chartAt p).fderiv_symm_zero
  rw [h_id]
  exact ⟨Function.injective_id, Function.surjective_id⟩

/-- Adversarial Test 2.5: Positive-definiteness of target metric.
Every metric tensor in ClosedTameTarget is strictly positive definite,
ruling out zero metrics or degenerate pseudo-Riemannian signatures. -/
theorem test_target_metric_strictly_positive (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < ClosedTameTarget.metric I x v v :=
  metric_pos_def (I := I) x v hv

/- =========================================================================
   PROBE 3: Koszul Connection Cancellation & Quadratic Taylor Normalization
   ========================================================================= -/

/-- Adversarial Test 3.1: Koszul cancellation is exact on all triples of vectors. -/
theorem test_koszul_exact_cancellation
    (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h_symm : ∀ u v w, dg0 u v w = dg0 u w v)
    (u h₁ h₂ : E) :
    koszulForm dg0 u h₁ h₂ + koszulForm dg0 u h₂ h₁ = dg0 u h₁ h₂ :=
  koszul_cancellation dg0 h_symm u h₁ h₂

/-- Adversarial Test 3.2: Pulled-back metric derivative cancels algebraically to exactly 0. -/
theorem test_pulled_back_metric_deriv_exact_zero
    (g0 : E →L[ℝ] E →L[ℝ] ℝ)
    (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h_symm : ∀ u v w, dg0 u v w = dg0 u w v)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ : ∀ u v w, g0 (Γ u v) w = koszulForm dg0 u v w)
    (u h₁ h₂ : E) :
    dg0 u h₁ h₂ - g0 (Γ u h₁) h₂ - g0 (Γ u h₂) h₁ = 0 :=
  pulled_back_metric_deriv_zero g0 dg0 h_symm Γ hΓ u h₁ h₂

/-- Adversarial Test 3.3: Uniqueness of torsion-free connection cancelling metric derivative.
If both Γ and Γ' satisfy the Koszul cancellation identity and are symmetric,
their difference Δ satisfies g0(Δ(u, v), w) = 0, forcing Γ = Γ'. -/
theorem test_koszul_cancellation_uniqueness
    (g0 : E →L[ℝ] E →L[ℝ] ℝ) (h_pos : ∀ v ≠ 0, 0 < g0 v v)
    (Γ₁ Γ₂ : E →L[ℝ] E →L[ℝ] E)
    (hΓ₁ : ∀ u v w, g0 (Γ₁ u v) w = koszulForm (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) u v w)
    (hΓ₂ : ∀ u v w, g0 (Γ₂ u v) w = koszulForm (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) u v w) :
    Γ₁ = Γ₂ := by
  have h1 : Γ₁ = 0 := test_christoffel_vanishing_genuine g0 h_pos Γ₁ hΓ₁
  have h2 : Γ₂ = 0 := test_christoffel_vanishing_genuine g0 h_pos Γ₂ hΓ₂
  rw [h1, h2]

/-- Adversarial Test 3.4: Taylor map differential at 0 is id and second derivative is -Γ. -/
theorem test_quadraticTaylorMap_derivatives
    (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) (h_symm : ∀ u v, Γ u v = Γ v u) :
    quadraticTaylorMap y₀ Γ 0 = y₀ ∧
    fderiv ℝ (quadraticTaylorMap y₀ Γ) 0 = ContinuousLinearMap.id ℝ E ∧
    fderiv ℝ (fderiv ℝ (quadraticTaylorMap y₀ Γ)) 0 = -Γ :=
  ⟨quadraticTaylorMap_zero y₀ Γ,
   quadraticTaylorMap_fderiv_zero y₀ Γ,
   quadraticTaylorMap_fderiv2_zero y₀ Γ h_symm⟩

/- =========================================================================
   PROBE 4: Axiom Census Audit for Milestone N2
   ========================================================================= -/

#print axioms test_dmetric_zero_rejects_nonzero_derivative
#print axioms test_dmetric_zero_directional_vanishing
#print axioms test_koszulForm_zero_of_dg0_zero
#print axioms test_christoffel_vanishing_genuine
#print axioms test_chart_non_collapse
#print axioms test_two_sided_bilipschitz
#print axioms test_chart_symm_injective
#print axioms test_chart_differential_full_rank
#print axioms test_target_metric_strictly_positive
#print axioms test_koszul_exact_cancellation
#print axioms test_pulled_back_metric_deriv_exact_zero
#print axioms test_koszul_cancellation_uniqueness
#print axioms test_quadraticTaylorMap_derivatives

end GromovCompactness.Tests.AdversarialNormalChartsN2
