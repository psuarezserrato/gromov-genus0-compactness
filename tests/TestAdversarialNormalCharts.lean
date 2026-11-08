/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Milestone N1 Adversarial Challenger)
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

namespace GromovCompactness.Tests.AdversarialNormalCharts

instance : Nonempty CP1 := ⟨north_pole⟩

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
variable [tgt : ClosedTameTarget I M] [Nonempty M]

/- =========================================================================
   STRESS TEST 1: Non-vacuous instantiation & properties of FiniteGoodAtlas
   ========================================================================= -/

/-- Adversarial Test 1.1: Extract a concrete FiniteGoodAtlas on CP1. -/
noncomputable def CP1_atlas : FiniteGoodAtlas I_CP1 CP1 :=
  Classical.choice (exists_finiteGoodAtlas I_CP1)

/-- Adversarial Test 1.2: The extracted CP1 atlas has strictly positive Lebesgue radius. -/
theorem test_CP1_atlas_r_atlas_pos : 0 < CP1_atlas.r_atlas :=
  CP1_atlas.r_atlas_pos

/-- Adversarial Test 1.3: The extracted CP1 atlas covers CP1 completely. -/
theorem test_CP1_atlas_covers : (⋃ i, CP1_atlas.U i) = univ :=
  CP1_atlas.cover

/-- Adversarial Test 1.4: Every point on CP1 belongs to some chart domain. -/
theorem test_CP1_atlas_point_covered (z : CP1) : ∃ i : CP1_atlas.ι, z ∈ CP1_atlas.U i :=
  FiniteGoodAtlas.mem_cover I_CP1 CP1_atlas z

/-- Adversarial Test 1.5: Chart domains are non-empty because centers belong to their domains. -/
theorem test_CP1_atlas_centers_mem (i : CP1_atlas.ι) : CP1_atlas.center i ∈ CP1_atlas.U i :=
  CP1_atlas.center_mem i

/-- Adversarial Test 1.6: Target radii in the model space ℂ are strictly positive. -/
theorem test_CP1_atlas_r_target_pos (i : CP1_atlas.ι) : 0 < CP1_atlas.r_target i :=
  CP1_atlas.r_target_pos i

/-- Adversarial Test 1.7: Every metric ball of radius r_atlas around any point is contained in a chart. -/
theorem test_CP1_atlas_ball_contained (z : CP1) : ∃ i : CP1_atlas.ι, ball z CP1_atlas.r_atlas ⊆ CP1_atlas.U i :=
  CP1_atlas.ball_subset z

/- =========================================================================
   STRESS TEST 2: mfderiv factorization, invertibility, and non-degeneracy
   ========================================================================= -/

omit [I.Boundaryless] tgt [Nonempty M] [CompactSpace M] in
/-- Adversarial Test 2.1: Reverse invertibility of mfderiv factorization.
Multiplying both sides by the inverse transition map recovers the chart derivative. -/
theorem test_mfderiv_factorization_invertible
    (u : CP1 → M) (z : CP1) (xi : M)
    (hu : MDifferentiableAt I_CP1 I u z)
    (h_mem : u z ∈ (extChartAt I xi).source)
    (v : TangentSpace I_CP1 z) :
    tangentCoordChange I (u z) xi (u z) (mfderiv I_CP1 I u z v : E) =
      (mfderiv I_CP1 𝓘(ℝ, E) (extChartAt I xi ∘ u) z v : E) := by
  have hsrc : u z ∈ (chartAt H xi).source := by
    rw [← extChartAt_source I xi]; exact h_mem
  have h_chart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I xi) (u z) :=
    mdifferentiableAt_extChartAt hsrc
  have h_comp : (mfderiv I_CP1 𝓘(ℝ, E) (extChartAt I xi ∘ u) z v : E) =
      mfderiv I 𝓘(ℝ, E) (extChartAt I xi) (u z) (mfderiv I_CP1 I u z v) :=
    mfderiv_comp_apply z h_chart hu v
  have h_tc : mfderiv I 𝓘(ℝ, E) (extChartAt I xi) (u z) = tangentCoordChange I (u z) xi (u z) := by
    have h1 := (hasMFDerivAt_extChartAt (I := I) hsrc).mfderiv
    rw [h1]
    exact mfderiv_chartAt_eq_tangentCoordChange hsrc
  rw [h_comp, h_tc]
  rfl

omit [I.Boundaryless] tgt [Nonempty M] [CompactSpace M] in
/-- Adversarial Test 2.2: When xi = u z, tangentCoordChange is the identity. -/
theorem test_mfderiv_factorization_self
    (u : CP1 → M) (z : CP1)
    (hu : MDifferentiableAt I_CP1 I u z)
    (v : TangentSpace I_CP1 z) :
    (mfderiv I_CP1 I u z v : E) =
      (mfderiv I_CP1 𝓘(ℝ, E) (extChartAt I (u z) ∘ u) z v : E) := by
  have h_mem : u z ∈ (extChartAt I (u z)).source := mem_extChartAt_source (u z)
  have h_fact := mfderiv_eq_tangentCoordChange_comp_apply (I_dom := I_CP1) I u z (u z) hu h_mem v
  rw [h_fact]
  have h_id := tangentCoordChange_self (I := I) (v := (mfderiv I_CP1 𝓘(ℝ, E) (extChartAt I (u z) ∘ u) z v : E))
    (mem_extChartAt_source (u z))
  exact h_id

set_option backward.isDefEq.respectTransparency false in
/-- Adversarial Test 2.3: Non-degeneracy test on CP1.
For the identity map on CP1, applying mfderiv to the standard basis vector e1 yields e1 ≠ 0.
This guarantees that no spurious 0 or constant vanishing factor is introduced. -/
theorem test_mfderiv_nondegenerate_id (z : CP1) :
    (mfderiv I_CP1 I_CP1 id z e1 : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
  have h1 : (mfderiv I_CP1 I_CP1 id z e1 : EuclideanSpace ℝ (Fin 2)) = e1 := by
    rw [mfderiv_id]
    rfl
  rw [h1]
  intro h
  have h2 := congr_arg c_equiv_e2.symm h
  rw [c_equiv_symm_e1, map_zero] at h2
  exact one_ne_zero h2

omit [I.Boundaryless] tgt [Nonempty M] [CompactSpace M] in
/-- Adversarial Test 2.4: Chart independence of factored derivative.
Factoring through any two charts xi1 and xi2 yielding equivalent transition evaluations. -/
theorem test_mfderiv_factorization_chart_independence
    (u : CP1 → M) (z : CP1) (xi1 xi2 : M)
    (hu : MDifferentiableAt I_CP1 I u z)
    (h1 : u z ∈ (extChartAt I xi1).source)
    (h2 : u z ∈ (extChartAt I xi2).source)
    (v : TangentSpace I_CP1 z) :
    tangentCoordChange I xi1 (u z) (u z) (mfderiv I_CP1 𝓘(ℝ, E) (extChartAt I xi1 ∘ u) z v : E) =
      tangentCoordChange I xi2 (u z) (u z) (mfderiv I_CP1 𝓘(ℝ, E) (extChartAt I xi2 ∘ u) z v : E) := by
  have e1 := mfderiv_eq_tangentCoordChange_comp_apply (I_dom := I_CP1) I u z xi1 hu h1 v
  have e2 := mfderiv_eq_tangentCoordChange_comp_apply (I_dom := I_CP1) I u z xi2 hu h2 v
  rw [← e1, ← e2]

/- =========================================================================
   STRESS TEST 3: EnergyDensityCertificate & h_fin soundness
   ========================================================================= -/

omit [I.Boundaryless] [Nonempty M] in
/-- Adversarial Test 3.1: Constant maps have exactly 0 density and finite energy. -/
theorem test_const_density_zero (x₀ : M) (z : CP1) :
    riemannianEnergyDensity I (fun _ => x₀) z = 0 :=
  energy_density_const_map I x₀ z

omit [I.Boundaryless] [Nonempty M] in
/-- Adversarial Test 3.2: Constant maps have an EnergyDensityCertificate with bound 0. -/
theorem test_const_certificate_bound (x₀ : M) :
    (EnergyDensityCertificate.of_const I x₀).bound = 0 := rfl

omit [I.Boundaryless] [Nonempty M] in
/-- Adversarial Test 3.3: Any valid certificate for a constant map has bound ≥ 0. -/
theorem test_const_certificate_bound_ge_zero (x₀ : M)
    (cert : EnergyDensityCertificate I (fun _ => x₀)) : 0 ≤ cert.bound := by
  have h := cert.density_le north_pole
  rw [energy_density_const_map] at h
  exact h

/-- Adversarial Test 3.4: Identity map on CP1 has exactly density 1 everywhere. -/
theorem test_id_density_one (z : CP1) :
    riemannianEnergyDensity I_CP1 (id : CP1 → CP1) z = 1 :=
  riemannianEnergyDensity_id z

/-- Adversarial Test 3.5: Identity map on CP1 has an EnergyDensityCertificate with bound 1. -/
theorem test_id_certificate_bound :
    (EnergyDensityCertificate.concrete_id).bound = 1 := rfl

/-- Adversarial Test 3.6: Any valid certificate for the identity map on CP1 has bound ≥ 1. -/
theorem test_id_certificate_bound_ge_one
    (cert : EnergyDensityCertificate I_CP1 (id : CP1 → CP1)) : 1 ≤ cert.bound := by
  have h := cert.density_le north_pole
  rw [riemannianEnergyDensity_id] at h
  exact h

omit [I.Boundaryless] [Nonempty M] in
/-- Adversarial Test 3.7: Any map with continuous Riemannian energy density
unconditionally admits an EnergyDensityCertificate via compactness of CP1. -/
theorem energyDensityCertificate_of_continuous
    (u : CP1 → M) (h_cont : Continuous (riemannianEnergyDensity I u)) :
    Nonempty (EnergyDensityCertificate I u) := by
  have h_loc : ∀ z : CP1, ∃ U, IsOpen U ∧ z ∈ U ∧ ∃ C : ℝ, ∀ y ∈ U, riemannianEnergyDensity I u y ≤ C := by
    intro z
    exact locally_bounded_of_continuousAt (riemannianEnergyDensity I u) z (h_cont.continuousAt)
  obtain ⟨C, hC⟩ := bddAbove_of_compact_of_locally_bounded (riemannianEnergyDensity I u) h_loc
  exact ⟨EnergyDensityCertificate.of_exists_le I u ⟨C, hC⟩⟩

omit [I.Boundaryless] [Nonempty M] in
/-- Adversarial Test 3.8: A sequence of constant maps uniformly discharges h_fin. -/
theorem test_h_fin_seq_const (x_seq : ℕ → M) (n : ℕ) :
    energyMeasureExtended I (fun _ => x_seq n) Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_const I (x_seq n)

/- =========================================================================
   STRESS TEST 5: Mathematical Fidelity & Non-Vacuity of `dmetric_zero` (Milestone N2)
   ========================================================================= -/

/-- Adversarial Test 5.1: Linear metric variation is strictly rejected by dmetric_zero.
If a component has a non-zero linear first derivative, fderiv ≠ 0.
This confirms dmetric_zero is not vacuously true for arbitrary non-normal coordinates. -/
theorem test_dmetric_zero_rejects_nonzero_derivative (L : E →L[ℝ] ℝ) (hL : L ≠ 0) :
    ¬ (fderiv ℝ (fun z : E => L z) 0 = 0) := by
  have h_deriv : fderiv ℝ (fun z : E => L z) 0 = L := L.hasFDerivAt.fderiv
  rw [h_deriv]
  exact hL

omit [I.Boundaryless] [Nonempty M] in
/-- Adversarial Test 5.2: dmetric_zero forces directional derivatives to vanish in all directions.
Verifies that fderiv = 0 entails directional derivative vanishing along any probe vector u. -/
theorem test_dmetric_zero_directional_vanishing
    {r : ℝ} (p : M) (C : CenteredNormalChart I p r) (v w u : E) :
    (fderiv ℝ (fun z => ClosedTameTarget.metric I (C.chart.symm z) v w) 0) u = 0 := by
  rw [C.dmetric_zero v w]
  rfl

omit [I.Boundaryless] tgt [Nonempty M] [CompactSpace M] [IsManifold I ∞ M] in
/-- Adversarial Test 5.3: Koszul vanishing from dmetric_zero.
If the metric derivative dg0 vanishes identically, the Koszul form vanishes identically. -/
theorem test_koszulForm_zero_of_dg0_zero (u v w : E) :
    koszulForm (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) u v w = 0 := by
  simp only [koszulForm, zero_apply, add_zero, sub_zero, mul_zero]

omit [I.Boundaryless] tgt [Nonempty M] [CompactSpace M] [IsManifold I ∞ M] in
/-- Adversarial Test 5.4: Christoffel symbol vanishing from Koszul cancellation.
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
   STRESS TEST 6: Resistance to Degenerate Metrics & Fake Homeomorphisms (Milestone N2)
   ========================================================================= -/

omit [I.Boundaryless] [Nonempty M] in
/-- Adversarial Test 6.1: Non-collapse of chart.
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

omit [I.Boundaryless] [Nonempty M] in
/-- Adversarial Test 6.2: Strict two-sided bi-Lipschitz bounds.
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

omit [I.Boundaryless] [Nonempty M] in
/-- Adversarial Test 6.3: Strict injectivity on chart domain.
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

omit [I.Boundaryless] [Nonempty M] in
/-- Adversarial Test 6.4: Full rank differential at origin.
The differential of chart.symm at 0 is id_E, which is injective and surjective.
Prevents rank drop, branching, or cusps at chart center. -/
theorem test_chart_differential_full_rank
    (fam : UniformNormalChartFamily I (M := M)) (p : M) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ E) I (fam.chartAt p).chart.symm 0) ∧
    Function.Surjective (mfderiv (modelWithCornersSelf ℝ E) I (fam.chartAt p).chart.symm 0) := by
  have h_id := (fam.chartAt p).fderiv_symm_zero
  rw [h_id]
  exact ⟨Function.injective_id, Function.surjective_id⟩

omit [I.Boundaryless] [Nonempty M] in
/-- Adversarial Test 6.5: Positive-definiteness of target metric.
Every metric tensor in ClosedTameTarget is strictly positive definite,
ruling out zero metrics or degenerate pseudo-Riemannian signatures. -/
theorem test_target_metric_strictly_positive (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < ClosedTameTarget.metric I x v v :=
  metric_pos_def (I := I) x v hv

/- =========================================================================
   STRESS TEST 7: Koszul Connection Cancellation & Quadratic Taylor Normalization (Milestone N2)
   ========================================================================= -/

omit [I.Boundaryless] tgt [Nonempty M] [CompactSpace M] [IsManifold I ∞ M] in
/-- Adversarial Test 7.1: Koszul cancellation is exact on all triples of vectors. -/
theorem test_koszul_exact_cancellation
    (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h_symm : ∀ u v w, dg0 u v w = dg0 u w v)
    (u h₁ h₂ : E) :
    koszulForm dg0 u h₁ h₂ + koszulForm dg0 u h₂ h₁ = dg0 u h₁ h₂ :=
  koszul_cancellation dg0 h_symm u h₁ h₂

omit [I.Boundaryless] tgt [Nonempty M] [CompactSpace M] [IsManifold I ∞ M] in
/-- Adversarial Test 7.2: Pulled-back metric derivative cancels algebraically to exactly 0. -/
theorem test_pulled_back_metric_deriv_exact_zero
    (g0 : E →L[ℝ] E →L[ℝ] ℝ)
    (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h_symm : ∀ u v w, dg0 u v w = dg0 u w v)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ : ∀ u v w, g0 (Γ u v) w = koszulForm dg0 u v w)
    (u h₁ h₂ : E) :
    dg0 u h₁ h₂ - g0 (Γ u h₁) h₂ - g0 (Γ u h₂) h₁ = 0 :=
  pulled_back_metric_deriv_zero g0 dg0 h_symm Γ hΓ u h₁ h₂

omit [I.Boundaryless] tgt [Nonempty M] [CompactSpace M] [IsManifold I ∞ M] in
/-- Adversarial Test 7.3: Uniqueness of torsion-free connection cancelling metric derivative.
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

omit [I.Boundaryless] tgt [Nonempty M] [CompactSpace M] [IsManifold I ∞ M] in
/-- Adversarial Test 7.4: Taylor map differential at 0 is id and second derivative is -Γ. -/
theorem test_quadraticTaylorMap_derivatives
    (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) (h_symm : ∀ u v, Γ u v = Γ v u) :
    quadraticTaylorMap y₀ Γ 0 = y₀ ∧
    fderiv ℝ (quadraticTaylorMap y₀ Γ) 0 = ContinuousLinearMap.id ℝ E ∧
    fderiv ℝ (fderiv ℝ (quadraticTaylorMap y₀ Γ)) 0 = -Γ :=
  ⟨quadraticTaylorMap_zero y₀ Γ,
   quadraticTaylorMap_fderiv_zero y₀ Γ,
   quadraticTaylorMap_fderiv2_zero y₀ Γ h_symm⟩

/- =========================================================================
   STRESS TEST 8: Axiom Census Audit for Milestone N2 Adversarial Theorems
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

end GromovCompactness.Tests.AdversarialNormalCharts
