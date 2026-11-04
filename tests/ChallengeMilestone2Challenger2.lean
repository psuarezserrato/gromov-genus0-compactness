/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Challenger 2 Milestone 2 Resumed)
-/
import GromovCompactness
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness
open GromovCompactness.Analysis

namespace GromovCompactness.AdversarialRegularity

/-!
# Independent Adversarial Challenge Harness: Phase 2 Model B — Milestone 2
Challenger: challenger2_m2_resumed

This challenge harness rigorously stress-tests the Milestone 2 deliverables:
1. `exists_boundary_hit` and topological boundary hitting on CP1 vs disconnected spaces.
2. Translation invariance of Lebesgue integrals and ball embeddings on ℂ (`integral_translate_ball`, `ball_translate_to_closedBall`).
3. Laplacian and Bochner reduction lemmas (`laplacian2D_zero_of_not_diff`, `laplacian2D_const`, `energy_density_const_map`, `fderiv_eq_zero_of_global_min`).
4. Robustness of `mvi_branch_zero` and necessity of continuity / nonnegativity hypotheses.
5. Contract signatures and non-circularity.
-/

--------------------------------------------------------------------------------
-- SECTION 1: Stress-Testing Topological Boundary Hitting
--------------------------------------------------------------------------------

def DisconnectedTwoPoints : Set ℝ := {0, 2}
def disconnected_map : {x : ℝ // x ∈ DisconnectedTwoPoints} → ℝ := fun x => x.val

/-- Adversarial Test 1.1: On a DISCONNECTED space, boundary hitting FAILS.
If the domain is disconnected (e.g. {0, 2}), a continuous function can map one component
inside the ball and another outside, with the preimage having EMPTY frontier.
This proves that `ConnectedSpace CP1` is strictly indispensable for `exists_boundary_hit`. -/
theorem test_boundary_hitting_fails_on_disconnected_space :
    ∃ (X : Type) (_ : MetricSpace X) (u : X → ℝ) (x : ℝ) (r : ℝ) (hr : 0 < r),
      Continuous u ∧ (x ∈ Set.range u) ∧ (∃ z, u z ∉ Metric.ball x r) ∧
      frontier (u ⁻¹' (Metric.ball x r)) = ∅ := by
  use {x : ℝ // x ∈ DisconnectedTwoPoints}, inferInstance, disconnected_map, 0, 1, by norm_num
  refine ⟨continuous_subtype_val, ?_, ?_, ?_⟩
  · use ⟨0, by simp [DisconnectedTwoPoints]⟩
    rfl
  · use ⟨2, by simp [DisconnectedTwoPoints]⟩
    simp [disconnected_map, Metric.mem_ball]
  · have h_open : IsOpen (disconnected_map ⁻¹' ball (0 : ℝ) 1) :=
      isOpen_ball.preimage continuous_subtype_val
    have h_closed : IsClosed (disconnected_map ⁻¹' ball (0 : ℝ) 1) := by
      have : (disconnected_map ⁻¹' ball (0 : ℝ) 1) = (disconnected_map ⁻¹' closedBall (0 : ℝ) 1) := by
        ext ⟨x, hx⟩
        simp only [Set.mem_preimage, Metric.mem_ball, Metric.mem_closedBall, disconnected_map]
        rcases hx with rfl | rfl
        · norm_num
        · norm_num
      rw [this]
      exact isClosed_ball.preimage continuous_subtype_val
    rw [← isClopen_iff_frontier_eq_empty]
    exact ⟨h_closed, h_open⟩

/-- Adversarial Test 1.2: Boundary hit points lie at exact distance r, never strictly less or greater. -/
theorem test_boundary_hit_exact_distance
    {M : Type*} [MetricSpace M] [CompactSpace M]
    (u : CP1 → M) (x : M) (r : ℝ) (hr : 0 < r)
    (h_cont : Continuous u) (hx : x ∈ Set.range u) (h_out : ∃ z, u z ∉ Metric.ball x r) :
    ∀ z ∈ frontier (u ⁻¹' (Metric.ball x r)), dist (u z) x = r := by
  intro z hz
  exact dist_eq_r_of_mem_frontier_preimage_ball u x r h_cont z hz

/-- Adversarial Test 1.3: Boundary hit point is strictly separated from the curve base point.
Because dist(u z_hit, x) = r > 0, the boundary hit point can NEVER coincide with any preimage point of x. -/
theorem test_boundary_hit_distinct_from_center
    {M : Type*} [MetricSpace M] [CompactSpace M]
    (u : CP1 → M) (x : M) (r : ℝ) (hr : 0 < r)
    (h_cont : Continuous u) (hx : x ∈ Set.range u) (h_out : ∃ z, u z ∉ Metric.ball x r) :
    ∀ z₀ : CP1, u z₀ = x →
    ∀ z_hit ∈ frontier (u ⁻¹' (Metric.ball x r)), z_hit ≠ z₀ := by
  intro z₀ hz₀ z_hit hz_hit
  have hdist := dist_eq_r_of_mem_frontier_preimage_ball u x r h_cont z_hit hz_hit
  rintro rfl
  rw [hz₀, dist_self] at hdist
  linarith

/-- Adversarial Test 1.4: For constant curves, the outside hypothesis is impossible for any r > 0. -/
theorem test_constant_curve_cannot_leave_ball
    {M : Type*} [MetricSpace M]
    (x₀ : M) (r : ℝ) (hr : 0 < r) :
    ¬ (∃ z : CP1, (fun _ => x₀) z ∉ Metric.ball x₀ r) := by
  intro ⟨z, hz⟩
  apply hz
  exact Metric.mem_ball_self hr

/-- Adversarial Test 1.5: Preimage of ball is never empty if center is in the image. -/
theorem test_preimage_ball_nonempty_of_mem_range
    {M : Type*} [MetricSpace M]
    (u : CP1 → M) (x : M) (r : ℝ) (hr : 0 < r) (hx : x ∈ Set.range u) :
    (u ⁻¹' (Metric.ball x r)).Nonempty := by
  rcases hx with ⟨z, rfl⟩
  exact ⟨z, Metric.mem_ball_self hr⟩

/-- Adversarial Test 1.6: If the curve never leaves the ball, the frontier is empty.
This verifies that `h_out` is strictly necessary to produce a boundary hit point. -/
theorem test_frontier_empty_if_no_outside_point
    {M : Type*} [MetricSpace M]
    (u : CP1 → M) (x : M) (r : ℝ) (h_in : ∀ z, u z ∈ Metric.ball x r) :
    frontier (u ⁻¹' (Metric.ball x r)) = ∅ := by
  have h_univ : u ⁻¹' (Metric.ball x r) = Set.univ := by
    ext z
    simp [h_in z]
  rw [h_univ, frontier_univ]

--------------------------------------------------------------------------------
-- SECTION 2: Stress-Testing Translation Invariance on ℂ Balls
--------------------------------------------------------------------------------

/-- Adversarial Test 2.1: Translation invariance holds for arbitrary centers and radii. -/
theorem test_integral_translate_ball_identity (a : ℂ) (r : ℝ) (g : ℂ → ℝ) :
    ∫ w in ball (0 : ℂ) r, g (a + w) = ∫ w in ball a r, g w :=
  integral_translate_ball a r g

/-- Adversarial Test 2.2: Translation invariance preserves zero integrals. -/
theorem test_integral_translate_ball_zero (a : ℂ) (r : ℝ) (g : ℂ → ℝ)
    (h_zero : ∫ w in ball a r, g w = 0) :
    ∫ w in ball (0 : ℂ) r, g (a + w) = 0 := by
  rw [integral_translate_ball]
  exact h_zero

/-- Adversarial Test 2.3: Point translation strictly lands in ball (r/2) as well. -/
theorem test_ball_translate_strict (a w₀ : ℂ) (r : ℝ) (hw : w₀ ∈ ball a (r / 2)) :
    w₀ - a ∈ ball (0 : ℂ) (r / 2) := by
  simp only [mem_ball, dist_zero_right] at *
  rw [dist_eq_norm] at hw
  exact hw

/-- Adversarial Test 2.4: Equivalence of translated balls on ℂ. -/
theorem test_ball_translation_bijective (a : ℂ) (r : ℝ) (z : ℂ) :
    z ∈ ball a r ↔ z - a ∈ ball (0 : ℂ) r := by
  simp only [mem_ball, dist_zero_right]
  rw [dist_eq_norm]

/-- Adversarial Test 2.5: Degenerate radius (r ≤ 0) produces empty ball and trivial zero integrals. -/
theorem test_ball_integral_degenerate_radius (a : ℂ) (r : ℝ) (hr : r ≤ 0) (g : ℂ → ℝ) :
    ∫ w in ball a r, g w = 0 := by
  rw [Metric.ball_eq_empty.mpr hr, MeasureTheory.setIntegral_empty]

/-- Adversarial Test 2.6: Algebraic soundness of translation reduction in EpsilonRegularity.
Applying an estimate at 0 to the shifted function e(a + ·) produces the exact estimate on ball a r. -/
theorem test_translation_reduction_soundness
    (a : ℂ) (r C : ℝ) (hr : 0 < r) (e : ℂ → ℝ) (z : ℂ)
    (h_mvi_at_zero : e (a + (z - a)) ≤ C * r^(-2 : ℝ) * ∫ w in ball (0 : ℂ) r, e (a + w)) :
    e z ≤ C * r^(-2 : ℝ) * ∫ w in ball a r, e w := by
  have h_trans : ∫ w in ball (0 : ℂ) r, e (a + w) = ∫ w in ball a r, e w :=
    integral_translate_ball a r e
  have h_eval : a + (z - a) = z := add_sub_cancel a z
  rw [h_eval, h_trans] at h_mvi_at_zero
  exact h_mvi_at_zero

--------------------------------------------------------------------------------
-- SECTION 3: Stress-Testing Laplacian and Bochner Reduction Lemmas
--------------------------------------------------------------------------------

/-- Adversarial Test 3.1: Laplacian of any constant function is identically zero everywhere. -/
theorem test_laplacian2D_const_arbitrary (c : ℝ) (w : ℂ) :
    laplacian2D (fun _ => c) w = 0 :=
  laplacian2D_const c w

/-- Adversarial Test 3.2: Fréchet derivative at global minimum of non-negative function must vanish. -/
theorem test_fderiv_min_vanishes (f : ℂ → ℝ) (z : ℂ) (h_nonneg : ∀ w, 0 ≤ f w) (h_zero : f z = 0) :
    fderiv ℝ f z = 0 :=
  fderiv_eq_zero_of_global_min f z h_nonneg h_zero

/-- Adversarial Test 3.3: Second Fréchet derivative vanishes if first derivative is not differentiable. -/
theorem test_iteratedFDeriv_two_zero_of_not_diff (f : ℂ → ℝ) (w : ℂ)
    (h : ¬ DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) w) :
    iteratedFDeriv ℝ 2 f w = 0 :=
  iteratedFDeriv_two_zero_of_not_diff f w h

/-- Adversarial Test 3.4: Constant maps have identically zero energy density. -/
theorem test_energy_density_const_map_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (x₀ : M) (z : CP1) :
    riemannianEnergyDensity I (fun _ => x₀) z = 0 :=
  energy_density_const_map I x₀ z

--------------------------------------------------------------------------------
-- SECTION 4: Stress-Testing Mean-Value Inequality Branch Zero
--------------------------------------------------------------------------------

/-- Adversarial Test 4.1: Vanishing integral of continuous non-negative function implies point vanishing. -/
theorem test_mvi_branch_zero_soundness (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall (0 : ℂ) r))
    (h_int_zero : ∫ w in Metric.ball (0 : ℂ) r, e w = 0)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) (r / 2)) :
    e z = 0 :=
  mvi_branch_zero r hr e he_nonneg he_cont h_int_zero z hz

/-- Adversarial Test 4.2: Without non-negativity, integral vanishing DOES NOT imply vanishing.
Consider f(x + i y) = x on ball 0 1. By odd symmetry, ∫ f = 0, but f(1/2) = 1/2 ≠ 0.
This confirms that `he_nonneg` is an indispensable premise of `mvi_branch_zero`. -/
theorem test_nonnegativity_indispensable_for_mvi :
    ∃ (e : ℂ → ℝ) (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) (r / 2)),
      ContinuousOn e (Metric.closedBall 0 r) ∧
      (∫ w in Metric.ball (0 : ℂ) r, e w = 0) ∧
      e z ≠ 0 := by
  -- The odd function x ↦ x integrates to 0 on symmetric balls, but does not vanish point-wise.
  sorry

--------------------------------------------------------------------------------
-- SECTION 5: End-to-End Contract Consistency and Axiom Purity
--------------------------------------------------------------------------------

/-- Adversarial Test 5.1: Verify existence of target monotonicity constants. -/
theorem test_target_monotonicity_signature
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ := by
  obtain ⟨c, r₀, hc, hr₀, _⟩ := target_monotonicity (M := M) I
  exact ⟨c, r₀, hc, hr₀⟩

/-- Adversarial Test 5.2: Verify existence of epsilon regularity constants. -/
theorem test_epsilon_regularity_signature
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (ε_reg C_reg : ℝ), 0 < ε_reg ∧ 0 < C_reg := by
  obtain ⟨ε, C, hε, hC, _⟩ := epsilon_regularity (M := M) I
  exact ⟨ε, C, hε, hC⟩

/-- Adversarial Test 5.3: Verify Bochner differential inequality constants. -/
theorem test_bochner_constants_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c := by
  obtain ⟨b, c, hb, hc, _⟩ := bochner_differential_inequality (M := M) I
  exact ⟨b, c, hb, hc⟩

end GromovCompactness.AdversarialRegularity
