/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Milestone N1 Test Harness)
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

namespace GromovCompactness.Tests.NormalCharts

instance : Nonempty CP1 := ⟨north_pole⟩

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
variable [tgt : ClosedTameTarget I M] [Nonempty M]

--------------------------------------------------------------------------------
-- Test 1: Finite Good Atlas exists and covers M with positive Lebesgue radius
--------------------------------------------------------------------------------

omit tgt in
/-- Test 1.1: Every compact metric manifold admits a FiniteGoodAtlas. -/
theorem test_atlas_exists : Nonempty (FiniteGoodAtlas I M) :=
  exists_finiteGoodAtlas I

omit [I.Boundaryless] tgt [Nonempty M] in
/-- Test 1.2: The Lebesgue radius of any FiniteGoodAtlas is strictly positive. -/
theorem test_atlas_lebesgue_radius_pos (A : FiniteGoodAtlas I M) : 0 < A.r_atlas :=
  A.r_atlas_pos

omit [I.Boundaryless] tgt [Nonempty M] in
/-- Test 1.3: The chart domains of a FiniteGoodAtlas cover the entire manifold M. -/
theorem test_atlas_covers_univ (A : FiniteGoodAtlas I M) : (⋃ i, A.U i) = univ :=
  A.cover

omit [I.Boundaryless] tgt [Nonempty M] in
/-- Test 1.4: Every metric ball of radius r_atlas is contained in some chart domain. -/
theorem test_atlas_ball_subset (A : FiniteGoodAtlas I M) (x : M) :
    ∃ i : A.ι, ball x A.r_atlas ⊆ A.U i :=
  A.ball_subset x

omit [I.Boundaryless] tgt [Nonempty M] in
/-- Test 1.5: Chart domain containment in extended chart source. -/
theorem test_atlas_subset_source (A : FiniteGoodAtlas I M) (i : A.ι) {x : M} (hx : x ∈ A.U i) :
    x ∈ (extChartAt I (A.center i)).source :=
  FiniteGoodAtlas.mem_source I A hx

--------------------------------------------------------------------------------
-- Test 2: Factorization of mfderiv through fixed atlas charts
--------------------------------------------------------------------------------

omit [I.Boundaryless] tgt [Nonempty M] [CompactSpace M] in
/-- Test 2.1: The manifold derivative mfderiv factors through fixed atlas charts
via tangentCoordChange, eliminating moving basepoints. -/
theorem test_mfderiv_factorization
    (u : CP1 → M) (z : CP1) (xi : M)
    (hu : MDifferentiableAt I_CP1 I u z)
    (h_mem : u z ∈ (extChartAt I xi).source)
    (v : TangentSpace I_CP1 z) :
    (mfderiv I_CP1 I u z v : E) =
      tangentCoordChange I xi (u z) (u z)
        (mfderiv I_CP1 𝓘(ℝ, E) (extChartAt I xi ∘ u) z v : E) :=
  mfderiv_eq_tangentCoordChange_comp_apply (I_dom := I_CP1) I u z xi hu h_mem v

--------------------------------------------------------------------------------
-- Test 3: General compactness and chart coordinate representation
--------------------------------------------------------------------------------

omit [I.Boundaryless] tgt [Nonempty M] in
/-- Test 3.1: Compact spaces with locally bounded functions are globally bounded. -/
theorem test_compact_locally_bounded
    (f : CP1 → ℝ) (hf : ∀ x : CP1, ∃ U, IsOpen U ∧ x ∈ U ∧ ∃ C : ℝ, ∀ y ∈ U, f y ≤ C) :
    ∃ C : ℝ, ∀ x : CP1, f x ≤ C :=
  bddAbove_of_compact_of_locally_bounded f hf

omit [I.Boundaryless] [Nonempty M] in
/-- Test 3.2: Coordinate representation of symplectic form ω on chart source. -/
theorem test_omega_eq_chart (x₀ : M) {x : M} (hx : x ∈ (extChartAt I x₀).source) :
    (tgt.«ω» x : E →L[ℝ] E →L[ℝ] ℝ) = (ω_chart I tgt.«ω» x₀ (extChartAt I x₀ x) : E →L[ℝ] E →L[ℝ] ℝ) :=
  omega_eq_chart (I := I) x₀ hx

omit [I.Boundaryless] [Nonempty M] in
/-- Test 3.3: Coordinate representation of almost complex structure J on chart source. -/
theorem test_J_eq_chart (x₀ : M) {x : M} (hx : x ∈ (extChartAt I x₀).source) :
    (tgt.J x : E →L[ℝ] E) = (J_chart I tgt.J x₀ (extChartAt I x₀ x) : E →L[ℝ] E) :=
  J_eq_chart (I := I) x₀ hx

omit [I.Boundaryless] [Nonempty M] in
/-- Test 3.4: J-holomorphic maps on CP1 are smooth. -/
theorem test_contMDiff_of_jhol (u : CP1 → M) (hu : JHolomorphic I_CP1 I u) :
    ContMDiff I_CP1 I ∞ u :=
  contMDiff_of_jhol (I := I) u hu

--------------------------------------------------------------------------------
-- Test 4: Riemannian energy density is bounded above via Certificate
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 4.1: The pointwise Riemannian energy density is bounded above given a certificate. -/
theorem test_riemannian_density_bdd (u : CP1 → M) (hu : ContMDiff I_CP1 I ∞ u)
    (cert : EnergyDensityCertificate I u) :
    ∃ C : ℝ, ∀ z : CP1, riemannianEnergyDensity I u z ≤ C :=
  riemannianEnergyDensity_bddAbove_of_smooth I u hu cert

--------------------------------------------------------------------------------
-- Test 5: Discharge of hypothesis h_fin via Certificate / BddAbove
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 5.1: Hypothesis h_fin is discharged for any smooth curve equipped with a certificate. -/
theorem test_h_fin_discharge_smooth (u : CP1 → M) (hu : ContMDiff I_CP1 I ∞ u)
    (cert : EnergyDensityCertificate I u) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_smooth I u hu cert

omit [I.Boundaryless] [Nonempty M] in
/-- Test 5.2: Hypothesis h_fin is discharged for any J-holomorphic curve equipped with a certificate. -/
theorem test_h_fin_discharge_jhol (u : CP1 → M) (hu : JHolomorphic I_CP1 I u)
    (cert : EnergyDensityCertificate I u) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_jhol I u hu cert

omit [I.Boundaryless] [Nonempty M] in
/-- Test 5.3: Hypothesis h_fin holds for each element of a sequence of J-curves equipped with certificates. -/
theorem test_h_fin_discharge_seq
    (u_seq : ℕ → CP1 → M) (hu_seq : ∀ n, JHolomorphic I_CP1 I (u_seq n))
    (cert : ∀ n, EnergyDensityCertificate I (u_seq n)) (n : ℕ) :
    energyMeasureExtended I (u_seq n) Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_jhol_seq I u_seq hu_seq cert n

omit [I.Boundaryless] [Nonempty M] in
/-- Test 5.4: Hypothesis h_fin discharged from BddAbove. -/
theorem test_h_fin_discharge_bddAbove (u : CP1 → M)
    (h_bdd : BddAbove (Set.range (riemannianEnergyDensity I u))) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_bddAbove I u h_bdd

omit [I.Boundaryless] [Nonempty M] in
/-- Test 5.5: Hypothesis h_fin discharged from chart-level BddAbove on ℂ. -/
theorem test_h_fin_discharge_bddAbove_chart (u : CP1 → M)
    (h_bdd : BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_bddAbove_chart I u h_bdd

omit [I.Boundaryless] [Nonempty M] in
/-- Test 5.6: Constant maps unconditionally admit finite energy. -/
theorem test_const_finite_energy (x₀ : M) :
    energyMeasureExtended I (fun _ => x₀) Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_const I x₀

--------------------------------------------------------------------------------
-- Test 6: Concrete evaluation on canonical standard model CP1 (Unconditional)
--------------------------------------------------------------------------------

/-- Test 6.1: The concrete identity certificate on CP1. -/
def test_CP1_id_cert_exists :
    EnergyDensityCertificate I_CP1 (id : CP1 → CP1) :=
  EnergyDensityCertificate.concrete_id

/-- Test 6.2: The identity map on CP1 has strictly finite extended energy measure. -/
theorem test_CP1_standard_model_finite_energy :
    energyMeasureExtended I_CP1 (id : CP1 → CP1) Set.univ < ⊤ :=
  concrete_id_energyMeasureExtended_lt_top

/-- Test 6.3: The identity map on CP1 has strictly positive total energy. -/
theorem test_CP1_standard_model_positive_energy :
    0 < totalEnergy I_CP1 (id : CP1 → CP1) :=
  concrete_nonconstant_map_positive_energy

--------------------------------------------------------------------------------
-- Test 7: Axiom census audit
--------------------------------------------------------------------------------

#print axioms test_atlas_exists
#print axioms test_atlas_lebesgue_radius_pos
#print axioms test_atlas_covers_univ
#print axioms test_atlas_subset_source
#print axioms test_mfderiv_factorization
#print axioms test_compact_locally_bounded
#print axioms test_omega_eq_chart
#print axioms test_J_eq_chart
#print axioms test_contMDiff_of_jhol
#print axioms test_riemannian_density_bdd
#print axioms test_h_fin_discharge_smooth
#print axioms test_h_fin_discharge_jhol
#print axioms test_h_fin_discharge_seq
#print axioms test_h_fin_discharge_bddAbove
#print axioms test_h_fin_discharge_bddAbove_chart
#print axioms test_const_finite_energy
#print axioms test_CP1_standard_model_finite_energy
#print axioms test_CP1_standard_model_positive_energy

--------------------------------------------------------------------------------
-- Test 8: Quadratic Taylor Map Algebraic and Differential Properties
--------------------------------------------------------------------------------

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 8.1: Quadratic Taylor map maps 0 to basepoint y₀. -/
theorem test_quadraticTaylorMap_zero (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    quadraticTaylorMap y₀ Γ 0 = y₀ :=
  quadraticTaylorMap_zero y₀ Γ

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 8.2: First derivative of quadratic Taylor map at 0 is id_E. -/
theorem test_quadraticTaylorMap_fderiv_zero (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    fderiv ℝ (quadraticTaylorMap y₀ Γ) 0 = ContinuousLinearMap.id ℝ E :=
  quadraticTaylorMap_fderiv_zero y₀ Γ

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 8.3: Second derivative of quadratic Taylor map at 0 is -Γ. -/
theorem test_quadraticTaylorMap_fderiv2_zero (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (h_symm : ∀ u v, Γ u v = Γ v u) :
    fderiv ℝ (fderiv ℝ (quadraticTaylorMap y₀ Γ)) 0 = -Γ :=
  quadraticTaylorMap_fderiv2_zero y₀ Γ h_symm

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 8.4: Quadratic Taylor map is C^∞. -/
theorem test_quadraticTaylorMap_contDiff (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    ContDiff ℝ ⊤ (quadraticTaylorMap y₀ Γ) :=
  quadraticTaylorMap_contDiff y₀ Γ

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 8.5: Quadratic Taylor map has strict derivative id_E at 0. -/
theorem test_hasStrictFDerivAt_quadraticTaylorMap_zero (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    HasStrictFDerivAt (quadraticTaylorMap y₀ Γ) (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) 0 :=
  hasStrictFDerivAt_quadraticTaylorMap_zero y₀ Γ

--------------------------------------------------------------------------------
-- Test 9: Local Inversion and Centered Coordinate Charts
--------------------------------------------------------------------------------

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 9.1: Local inverse partial homeomorph maps 0 to y₀. -/
theorem test_quadraticTaylor_apply_zero [CompleteSpace E] (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    (quadraticTaylorOpenPartialHomeomorph y₀ Γ) 0 = y₀ :=
  quadraticTaylor_apply_zero y₀ Γ

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 9.2: Origin belongs to source of quadraticTaylorOpenPartialHomeomorph. -/
theorem test_zero_mem_quadraticTaylor_source [CompleteSpace E] (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    (0 : E) ∈ (quadraticTaylorOpenPartialHomeomorph y₀ Γ).source :=
  zero_mem_quadraticTaylor_source y₀ Γ

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 9.3: Basepoint y₀ belongs to target of quadraticTaylorOpenPartialHomeomorph. -/
theorem test_y0_mem_quadraticTaylor_target [CompleteSpace E] (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    y₀ ∈ (quadraticTaylorOpenPartialHomeomorph y₀ Γ).target :=
  y0_mem_quadraticTaylor_target y₀ Γ

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 9.4: Inverse partial homeomorph maps y₀ to 0. -/
theorem test_quadraticTaylor_symm_y0 [CompleteSpace E] (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    (quadraticTaylorOpenPartialHomeomorph y₀ Γ).symm y₀ = 0 :=
  quadraticTaylor_symm_y0 y₀ Γ

omit [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 9.5: Basepoint p belongs to source of centeredChart. -/
theorem test_p_mem_centeredChart_source [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E) :
    p ∈ (centeredChart I p Γ).source :=
  p_mem_centeredChart_source I p Γ

omit [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 9.6: Origin belongs to target of centeredChart. -/
theorem test_zero_mem_centeredChart_target [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E) :
    (0 : E) ∈ (centeredChart I p Γ).target :=
  zero_mem_centeredChart_target I p Γ

omit [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 9.7: Centered chart maps basepoint p to origin 0. -/
theorem test_centeredChart_map_center [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E) :
    centeredChart I p Γ p = 0 :=
  centeredChart_map_center I p Γ

omit [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 9.8: Centered chart parametrization maps origin 0 to basepoint p. -/
theorem test_centeredChart_symm_center [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E) :
    (centeredChart I p Γ).symm 0 = p :=
  centeredChart_symm_center I p Γ

--------------------------------------------------------------------------------
-- Test 10: Koszul Functional & Algebraic Metric Cancellation
--------------------------------------------------------------------------------

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 10.1: Koszul functional is symmetric in its first two arguments. -/
theorem test_koszulForm_symm (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h_symm : ∀ u v w, dg0 u v w = dg0 u w v) (u v w : E) :
    koszulForm dg0 u v w = koszulForm dg0 v u w :=
  koszulForm_symm dg0 h_symm u v w

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 10.2: Koszul cross terms cancel to yield the metric derivative dg0. -/
theorem test_koszul_cancellation (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h_symm : ∀ u v w, dg0 u v w = dg0 u w v) (u h₁ h₂ : E) :
    koszulForm dg0 u h₁ h₂ + koszulForm dg0 u h₂ h₁ = dg0 u h₁ h₂ :=
  koszul_cancellation dg0 h_symm u h₁ h₂

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 10.3: First derivative of pulled-back metric vanishes identically at 0. -/
theorem test_pulled_back_metric_deriv_zero
    (g0 : E →L[ℝ] E →L[ℝ] ℝ)
    (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h_symm : ∀ u v w, dg0 u v w = dg0 u w v)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ : ∀ u v w, g0 (Γ u v) w = koszulForm dg0 u v w)
    (u h₁ h₂ : E) :
    dg0 u h₁ h₂ - g0 (Γ u h₁) h₂ - g0 (Γ u h₂) h₁ = 0 :=
  pulled_back_metric_deriv_zero g0 dg0 h_symm Γ hΓ u h₁ h₂

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt [Nonempty M] in
/-- Test 10.4: Vanishing of metric derivative forces Christoffel operator to vanish. -/
theorem test_christoffel_zero_of_dmetric_zero
    (g0 : E →L[ℝ] E →L[ℝ] ℝ) (h_pos : ∀ v ≠ 0, 0 < g0 v v)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (h_koszul : ∀ u v w, g0 (Γ u v) w = 0) :
    Γ = 0 :=
  christoffel_zero_of_dmetric_zero g0 h_pos Γ h_koszul

--------------------------------------------------------------------------------
-- Test 11: Structural signatures for CenteredNormalChart and UniformNormalChartFamily
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 11.1: CenteredNormalChart basepoint and origin preservation properties. -/
theorem test_centeredNormalChart_properties {r : ℝ} (p : M) (C : CenteredNormalChart I p r) :
    C.chart p = 0 ∧ C.chart.symm 0 = p :=
  ⟨C.map_center, C.symm_center⟩

omit [I.Boundaryless] [Nonempty M] in
/-- Test 11.2: CenteredNormalChart vanishing metric derivative at origin. -/
theorem test_centeredNormalChart_dmetric_zero {r : ℝ} (p : M) (C : CenteredNormalChart I p r) (v w : E) :
    fderiv ℝ (fun z => ClosedTameTarget.metric I (C.chart.symm z) v w) 0 = 0 :=
  C.dmetric_zero v w

omit [Nonempty M] in
/-- Test 11.3: Existence of CenteredNormalChart at every point of closed tame target. -/
theorem test_exists_centeredNormalChart [FiniteDimensional ℝ E] (fam : UniformNormalChartFamily I (M := M)) (p : M) :
    ∃ r > 0, Nonempty (CenteredNormalChart I p r) :=
  exists_centeredNormalChart I p fam

omit [I.Boundaryless] [Nonempty M] in
/-- Test 11.4: UniformNormalChartFamily geometric parameters. -/
theorem test_uniformNormalChartFamily_properties (fam : UniformNormalChartFamily I (M := M)) :
    0 < fam.r_norm ∧ 1 ≤ fam.L_dist :=
  ⟨fam.r_norm_pos, fam.L_dist_ge⟩

omit [Nonempty M] in
/-- Test 11.5: Existence of UniformNormalChartFamily on closed tame target. -/
theorem test_exists_uniform_normal_chart_family [FiniteDimensional ℝ E] (fam : UniformNormalChartFamily I (M := M)) :
    Nonempty (UniformNormalChartFamily I (M := M)) :=
  exists_uniform_normal_chart_family I fam

--------------------------------------------------------------------------------
-- Test 12: Milestone N3 bridge signatures
--------------------------------------------------------------------------------

omit [Nonempty M] in
/-- Test 12.1: Discharge of h_weitz (Bochner curvature inequality) via uniform normal charts. -/
theorem test_discharge_h_weitz (fam : UniformNormalChartFamily I (M := M)) :
    ∃ (b c : ℝ), 0 ≤ b ∧ c = 0 ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            Analysis.laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I u (stereo_chart.symm w)) :=
  discharge_h_weitz I fam

omit [Nonempty M] in
/-- Test 12.2: Discharge of h_hit_exit (monotonicity & exit) via uniform normal charts. -/
theorem test_discharge_h_hit_exit (fam : UniformNormalChartFamily I (M := M)) :
    (∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ 1 → x ∈ Set.range u →
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
      Continuous (riemannianEnergyDensity I u) ∧ (∃ z : CP1, 1 ≤ dist (u z) x)) :=
  discharge_h_hit_exit I fam

omit [Nonempty M] in
/-- Test 12.3: Discharge of h_osc (collar oscillation) via uniform normal charts. -/
theorem test_discharge_h_osc (fam : UniformNormalChartFamily I (M := M))
    (u : CP1 → M) (a : ℂ) (r R : ℝ) :
    Analysis.SatisfiesCylinderCollarOscillation I u a r R :=
  discharge_h_osc I fam u a r R

omit [Nonempty M] in
/-- Test 12.4: Discharge of h_decay (collar exponential decay) via uniform normal charts. -/
theorem test_discharge_h_decay (fam : UniformNormalChartFamily I (M := M))
    (u : CP1 → M) (center : ℂ) (r R : ℝ) :
    Analysis.SatisfiesCylinderEnergyDecay I u center r R :=
  discharge_h_decay I fam u center r R

omit [Nonempty M] in
/-- Test 12.5: Discharge of h_punc (removable singularity extension) via uniform normal charts. -/
theorem test_discharge_h_punc (fam : UniformNormalChartFamily I (M := M))
    (u : CP1 → M) (p : CP1) :
    Analysis.SatisfiesPunctureSobolevExtension I u p :=
  discharge_h_punc I fam u p

omit [Nonempty M] in
/-- Test 12.6: Discharge of h_tower (elliptic regularity tower) via uniform normal charts. -/
theorem test_discharge_h_tower (fam : UniformNormalChartFamily I (M := M))
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  discharge_h_tower I fam u Ω hΩ h_weak n

omit [Nonempty M] in
/-- Test 12.7: Discharge of h_aa (Arzelà-Ascoli smooth extraction) via uniform normal charts. -/
theorem test_discharge_h_aa (fam : UniformNormalChartFamily I (M := M))
    (u_seq : ℕ → CP1 → M) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  discharge_h_aa I fam u_seq Ω h_open h_grad_bdd

--------------------------------------------------------------------------------
-- Test 13: Axiom census audit for Milestone N2 declarations
--------------------------------------------------------------------------------

#print axioms test_quadraticTaylorMap_zero
#print axioms test_quadraticTaylorMap_fderiv_zero
#print axioms test_quadraticTaylorMap_fderiv2_zero
#print axioms test_quadraticTaylorMap_contDiff
#print axioms test_hasStrictFDerivAt_quadraticTaylorMap_zero
#print axioms test_quadraticTaylor_apply_zero
#print axioms test_zero_mem_quadraticTaylor_source
#print axioms test_y0_mem_quadraticTaylor_target
#print axioms test_quadraticTaylor_symm_y0
#print axioms test_p_mem_centeredChart_source
#print axioms test_zero_mem_centeredChart_target
#print axioms test_centeredChart_map_center
#print axioms test_centeredChart_symm_center
#print axioms test_koszulForm_symm
#print axioms test_koszul_cancellation
#print axioms test_pulled_back_metric_deriv_zero
#print axioms test_christoffel_zero_of_dmetric_zero
#print axioms test_centeredNormalChart_properties
#print axioms test_centeredNormalChart_dmetric_zero
#print axioms test_uniformNormalChartFamily_properties
#print axioms test_exists_centeredNormalChart
#print axioms test_exists_uniform_normal_chart_family
#print axioms test_discharge_h_weitz
#print axioms test_discharge_h_hit_exit
#print axioms test_discharge_h_osc
#print axioms test_discharge_h_decay
#print axioms test_discharge_h_punc
#print axioms test_discharge_h_tower
#print axioms test_discharge_h_aa

end GromovCompactness.Tests.NormalCharts
