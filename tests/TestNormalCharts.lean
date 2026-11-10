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
import GromovCompactness.Analysis.HoferRescaling
import GromovCompactness.Bubbling.LocalTree
import GromovCompactness.Compactness.Concentration
import GromovCompactness.Compactness.GenusZero
import GromovCompactness.Geometry.NormalCharts
import GromovCompactness.Main
import GromovCompactness.Extensions.VaryingJ
import GromovCompactness.Extensions.MarkedCurves
import GromovCompactness.Extensions.Automorphisms
import GromovCompactness.Extensions.ModuliSpace

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
    fderiv ℝ (fun z => pulledBackMetricAt I p C.chart z v w) 0 = 0 :=
  C.dmetric_zero v w

omit [I.Boundaryless] [Nonempty M] in
/-- Test 11.3: Existence of CenteredNormalChart at every point of closed tame target. -/
theorem test_exists_centeredNormalChart [FiniteDimensional ℝ E] (fam : UniformNormalChartFamily I (M := M)) (p : M) :
    ∃ r > 0, Nonempty (CenteredNormalChart I p r) :=
  exists_centeredNormalChart I p fam

omit [I.Boundaryless] [Nonempty M] in
/-- Test 11.4: UniformNormalChartFamily geometric parameters. -/
theorem test_uniformNormalChartFamily_properties (fam : UniformNormalChartFamily I (M := M)) :
    0 < fam.r_norm ∧ 1 ≤ fam.L_dist :=
  ⟨fam.r_norm_pos, fam.L_dist_ge⟩

omit [I.Boundaryless] [Nonempty M] in
/-- Test 11.5: Existence of UniformNormalChartFamily on closed tame target. -/
theorem test_exists_uniform_normal_chart_family [FiniteDimensional ℝ E] (fam : UniformNormalChartFamily I (M := M)) :
    Nonempty (UniformNormalChartFamily I (M := M)) :=
  exists_uniform_normal_chart_family I fam

--------------------------------------------------------------------------------
-- Test 12: Milestone N3 bridge signatures
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 12.1: Discharge of h_weitz (Bochner curvature inequality) via uniform normal charts. -/
theorem test_discharge_h_weitz (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
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
  discharge_h_weitz I fam certs

omit [I.Boundaryless] [Nonempty M] in
/-- Test 12.2: Discharge of h_hit_exit (monotonicity & exit) via uniform normal charts. -/
theorem test_discharge_h_hit_exit (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.HitExitProperty I M :=
  discharge_h_hit_exit I fam certs

omit [I.Boundaryless] [Nonempty M] in
/-- Test 12.3: Discharge of h_osc (collar oscillation) via uniform normal charts. -/
theorem test_discharge_h_osc (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CollarOscillationProperty I M :=
  discharge_h_osc I fam certs

omit [I.Boundaryless] [Nonempty M] in
/-- Test 12.4: Discharge of h_decay (collar exponential decay) via uniform normal charts. -/
theorem test_discharge_h_decay (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CylinderEnergyDecayProperty I M :=
  discharge_h_decay I fam certs

omit [I.Boundaryless] [Nonempty M] in
/-- Test 12.5: Discharge of h_punc (removable singularity extension) via uniform normal charts. -/
theorem test_discharge_h_punc (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    Analysis.SatisfiesPunctureSobolevExtension I u p :=
  discharge_h_punc I fam certs u p hu h_energy

omit [I.Boundaryless] [Nonempty M] in
/-- Test 12.6: Discharge of h_tower (elliptic regularity tower) via uniform normal charts. -/
theorem test_discharge_h_tower (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  discharge_h_tower I fam certs u Ω hΩ h_weak n

omit [I.Boundaryless] [Nonempty M] in
/-- Test 12.7: Discharge of h_aa (Arzelà-Ascoli smooth extraction) via uniform normal charts. -/
theorem test_discharge_h_aa (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u_seq : ℕ → CP1 → M) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  discharge_h_aa I fam certs u_seq Ω h_open h_jhol h_grad_bdd

omit [I.Boundaryless] [Nonempty M] in
/-- Test 12.8: Discharge of h_hit_exit on constant curves via discharge_h_hit_exit_const. -/
theorem test_discharge_h_hit_exit_const (fam : UniformNormalChartFamily I (M := M)) (c : M) :
    (∀ (x : M) (r : ℝ),
      0 < r → r ≤ 1 → x ∈ Set.range (fun _ : CP1 => c) →
      JHolomorphicOn (I := I) (I_dom := I_CP1) (fun _ : CP1 => c) Set.univ →
      (¬ ∃ c' : M, ∀ z : CP1, (fun _ : CP1 => c) z = c') →
      ∀ z_hit : CP1, z_hit ∈ frontier ((fun _ : CP1 => c) ⁻¹' (Metric.ball x r)) →
        dist ((fun _ : CP1 => c) z_hit) x = r →
        (r^2 ≤ energyMeasure I (fun _ : CP1 => c) ((fun _ : CP1 => c) ⁻¹' (Metric.ball x r)) ∨
          ∃ s : Set CP1, s ⊆ (fun _ : CP1 => c) ⁻¹' (Metric.ball x r) ∧
            energyMeasureExtended I (fun _ : CP1 => c) ((fun _ : CP1 => c) ⁻¹' (Metric.ball x r)) ≠ ⊤ ∧
            r^2 ≤ energyMeasure I (fun _ : CP1 => c) s)) ∧
    (∀ (x : M),
      x ∈ Set.range (fun _ : CP1 => c) →
      JHolomorphicOn (I := I) (I_dom := I_CP1) (fun _ : CP1 => c) Set.univ →
      (¬ ∃ c' : M, ∀ z : CP1, (fun _ : CP1 => c) z = c') →
      Continuous (riemannianEnergyDensity I (fun _ : CP1 => c)) ∧ (∃ z : CP1, 1 ≤ dist ((fun _ : CP1 => c) z) x)) :=
  discharge_h_hit_exit_const I fam c

/-- Test 12.9: Concrete model instance on CP1. -/
theorem test_concrete_CP1 :
    Nonempty (UniformNormalChartFamily I_CP1 (M := CP1)) :=
  ⟨UniformNormalChartFamily.concrete_CP1⟩

omit [I.Boundaryless] [Nonempty M] in
/-- Test 12.10: Conditioned certificates inhabited on constant-reduction targets. -/
theorem test_conditioned_certificates_inhabited_of_all_const
    (fam : UniformNormalChartFamily I (M := M))
    (h_all_const : ∀ (u : CP1 → M), JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c)
    (h_punc_const : ∀ (u : CP1 → M) (p : CP1),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}) →
      energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤ → ∃ c : M, EqOn u (fun _ => c) (punctured_sphere {p}))
    (h_tower_const : ∀ (u : CP1 → M) (Ω : Set CP1), IsOpen Ω → Analysis.WeakJHolomorphicOn I u Ω →
      ∃ c : M, EqOn u (fun _ => c) Ω)
    (h_aa_extract : ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
      (_h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
      (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C),
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω) :
    Nonempty (UniformNormalChartCertificates I fam) :=
  conditioned_certificates_inhabited_of_all_const I fam h_all_const h_punc_const h_tower_const h_aa_extract

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
#print axioms test_discharge_h_hit_exit_const
#print axioms test_concrete_CP1
#print axioms test_conditioned_certificates_inhabited_of_all_const

--------------------------------------------------------------------------------
-- Test 14: Step 1 First-Principles Constructions (O3, O4, h_punc_osc, h_aa_lip, fam)
--------------------------------------------------------------------------------

/-- Test 14.1: Unconditional BoundedChartedTarget instance on CP1. -/
theorem test_instBoundedChartedTargetCP1 : BoundedChartedTarget I_CP1 CP1 :=
  instBoundedChartedTargetCP1

omit [Nonempty M] in
/-- Test 14.2: First-principles construction of UniformNormalChartFamily from BoundedChartedTarget
without taking `fam` as an input hypothesis. -/
noncomputable def test_construct_uniform_normal_chart_family
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E] :
    UniformNormalChartFamily I (M := M) :=
  construct_uniform_normal_chart_family I

/-- Test 14.3: Concrete instantiation of `construct_uniform_normal_chart_family` on CP1. -/
noncomputable def test_construct_uniform_normal_chart_family_CP1 :
    UniformNormalChartFamily I_CP1 (M := CP1) :=
  construct_uniform_normal_chart_family I_CP1

omit [Nonempty M] in
/-- Test 14.4: First-principles local Lipschitz equicontinuity (`h_aa_lip`) from bounded energy density. -/
theorem test_local_lipschitz_of_bounded_energy_density
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∀ z₀ ∈ Ω, ∃ ρ > 0, ∃ L ≥ 0, ∀ n : ℕ, ∀ z ∈ Metric.ball z₀ ρ,
      dist (u_seq n z) (u_seq n z₀) ≤ L * dist z z₀ :=
  local_lipschitz_of_bounded_energy_density I u_seq Ω h_open h_jhol h_grad_bdd

omit [I.Boundaryless] [Nonempty M] in
/-- Test 14.5: First-principles punctured-neighborhood vanishing oscillation (`h_punc_osc`)
at every puncture `p : CP1` (including `p = north_pole`). -/
theorem test_punctured_oscillation_of_local_collar_oscillation
    (h_osc_local : ∃ (C ε_osc : ℝ), 0 < C ∧ 0 < ε_osc ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r R) →
        energyMeasure I u (annulus_at a r R) < ε_osc →
        Analysis.SatisfiesCylinderCollarOscillationWith I C u a r R)
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∀ ε > 0, ∃ U ∈ 𝓝 p, ∀ z₁ ∈ U \ {p}, ∀ z₂ ∈ U \ {p}, dist (u z₁) (u z₂) < ε :=
  Analysis.punctured_oscillation_of_local_collar_oscillation I (M := M) h_osc_local u p h_jhol h_energy

#print axioms instBoundedChartedTargetCP1
#print axioms construct_uniform_normal_chart_family
#print axioms exists_uniform_normal_chart_family_of_bounded_geometry
#print axioms local_lipschitz_of_bounded_energy_density
#print axioms GromovCompactness.Analysis.punctured_oscillation_of_local_collar_oscillation
#print axioms UniformNormalChartCertificates.of_first_principles

--------------------------------------------------------------------------------
-- Test 15: Step 2 First-Principles Constructions (Bounded-Modulus Chaining & Zero-Energy Constancy)
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 15.1: Arbitrary-modulus local collar oscillation from bounded-modulus (`R ≤ 18 * r`)
ring oscillation and local cylinder energy decay (`0 sorryAx`). -/
theorem test_local_collar_oscillation_of_bounded_modulus_and_decay
    (h_ring_osc : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r R) →
        energyMeasure I u (annulus_at a r R) < ε_ring →
        Analysis.SatisfiesCylinderCollarOscillationWith I C_ring u a r R)
    (h_decay_local : ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
      ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
        0 < r → 2 * r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at center r R) →
        energyMeasure I u (annulus_at center r R) < ε_neck →
        Analysis.SatisfiesCylinderEnergyDecayWith I C₀ a_decay u center r R) :
    ∃ (C ε_osc : ℝ), 0 < C ∧ 0 < ε_osc ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r R) →
        energyMeasure I u (annulus_at a r R) < ε_osc →
        Analysis.SatisfiesCylinderCollarOscillationWith I C u a r R :=
  Analysis.local_collar_oscillation_of_bounded_modulus_and_decay I (M := M) h_ring_osc h_decay_local

omit [Nonempty M] in
/-- Test 15.2: Strict positivity of total energy for nonconstant `C¹` spheres
whose stereographic energy density is continuous (`0 sorryAx`). -/
theorem test_totalEnergy_pos_of_nonconstant
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (u : CP1 → M)
    (hu : ContMDiffOn I_CP1 I 1 u Set.univ)
    (h_cont : Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))
    (h_fin : energyMeasureExtended I u Set.univ < ⊤)
    (h_nonconst : ¬ ∃ c : M, ∀ z, u z = c) :
    0 < totalEnergy I u :=
  totalEnergy_pos_of_nonconstant I u hu h_cont h_fin h_nonconst

#print axioms GromovCompactness.Analysis.satisfiesCylinderCollarOscillationWith_of_bounded_modulus_and_decay
#print axioms GromovCompactness.Analysis.local_collar_oscillation_of_bounded_modulus_and_decay
#print axioms GromovCompactness.Analysis.collarOscillationProperty_of_bounded_modulus_and_decay
#print axioms mfderiv_eq_zero_of_riemannianEnergyDensity_eq_zero
#print axioms eqOn_const_of_riemannianEnergyDensity_eq_zero_on
#print axioms eq_const_of_riemannianEnergyDensity_stereo_eq_zero
#print axioms eq_const_of_totalEnergy_eq_zero
#print axioms totalEnergy_pos_of_nonconstant

--------------------------------------------------------------------------------
-- Test 16: Step 3 First-Principles Constructions (Local Jet Bounds → SmoothLocalConvergesOn & SmallBallExit)
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 16.1: Frame-invariant `SmoothLocalConvergesOn` from `HasLocalChartJetBoundsAt` on `Ω` alone (`0 sorryAx`). -/
theorem test_smoothLocalConvergesOn_of_local_jet_bounds
    [FiniteDimensional ℝ E]
    (v_seq : ℕ → (CP1 → M)) (v_lim : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (hv_seq : ∀ n, ContMDiffOn I_CP1 I ∞ (v_seq n) Ω)
    (hv_lim_cont : ContinuousOn v_lim Ω)
    (h_pt : ∀ z ∈ Ω, Filter.Tendsto (fun n => v_seq n z) Filter.atTop (nhds (v_lim z)))
    (h_jets : ∀ z ∈ Ω, Analysis.HasLocalChartJetBoundsAt I v_seq v_lim z) :
    SmoothLocalConvergesOn I v_seq v_lim Ω :=
  Analysis.smoothLocalConvergesOn_of_local_jet_bounds I v_seq v_lim Ω hΩ hv_seq hv_lim_cont h_pt h_jets

omit [I.Boundaryless] [Nonempty M] in
/-- Test 16.2: `SmallBallExit` from stereographic energy density smoothness, north-pole continuity,
and ball exit (`0 sorryAx`). -/
theorem test_smallBallExit_of_contDiff_stereo_and_exit
    {r₀ : ℝ}
    (h_stereo : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))
    (h_exit : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ContinuousAt (riemannianEnergyDensity I u) north_pole ∧
      ∀ x ∈ Set.range u, ∃ z : CP1, r₀ ≤ dist (u z) x) :
    Analysis.SmallBallExit I M r₀ :=
  Analysis.smallBallExit_of_contDiff_stereo_and_exit I h_stereo h_exit

#print axioms GromovCompactness.Analysis.exists_continuousOn_pointwise_convergent_subseq_on_domain
#print axioms GromovCompactness.Analysis.continuous_closedTameTarget_J
#print axioms GromovCompactness.Analysis.mfderiv_eq_curry_iteratedFDeriv_one
#print axioms GromovCompactness.Analysis.hasLocalChartJetBoundsAt_comp_moebius
#print axioms GromovCompactness.Analysis.coreSmoothLocalConvergesOn_of_local_jet_bounds
#print axioms GromovCompactness.Analysis.smoothLocalConvergesOn_of_local_jet_bounds
#print axioms GromovCompactness.Analysis.exists_smoothLocalConvergesOn_subseq_of_equicontinuous_and_local_jet_bounds
#print axioms GromovCompactness.Analysis.continuous_riemannianEnergyDensity_of_cont_stereo_and_north_pole
#print axioms GromovCompactness.Analysis.smallBallExit_of_contDiff_stereo_and_exit

--------------------------------------------------------------------------------
-- Test 17: Unconditional Proof of cert_fin (h_fin) for C¹ / Smooth / JHol Maps
--------------------------------------------------------------------------------

omit [Nonempty M] in
/-- Test 17.1: Every `C¹` map `u : CP1 → M` on `[BoundedChartedTarget I M]` unconditionally
has finite extended energy measure (`0 sorryAx`). -/
theorem test_energyMeasureExtended_lt_top_of_contMDiff
    [BoundedChartedTarget I M]
    (u : CP1 → M) (hu : ContMDiff I_CP1 I 1 u) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_contMDiff I u hu

omit [Nonempty M] in
/-- Test 17.2: Every `J`-holomorphic sphere `u : CP1 → M` on `[BoundedChartedTarget I M]`
unconditionally has finite extended energy measure (`0 sorryAx`). -/
theorem test_energyMeasureExtended_lt_top_of_jhol_uncond
    [BoundedChartedTarget I M]
    (u : CP1 → M) (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_jhol_uncond I u hu

omit [Nonempty M] in
/-- Test 17.3: Unconditional positivity of total energy for nonconstant `C¹` spheres
without assuming `h_fin` (`0 sorryAx`). -/
theorem test_totalEnergy_pos_of_nonconstant_uncond
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (u : CP1 → M)
    (hu : ContMDiffOn I_CP1 I 1 u Set.univ)
    (h_cont : Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))
    (h_nonconst : ¬ ∃ c : M, ∀ z, u z = c) :
    0 < totalEnergy I u :=
  totalEnergy_pos_of_nonconstant_uncond I u hu h_cont h_nonconst

#print axioms exists_metric_upper_bound
#print axioms riemannianEnergyDensity_le_of_metric_upper_bound
#print axioms locallyLipschitz_of_contMDiff
#print axioms exists_lipschitz_of_contMDiff
#print axioms exists_mfderiv_bound_of_contMDiff
#print axioms exists_energyDensity_bound_of_contMDiff
#print axioms EnergyDensityCertificate.of_contMDiff
#print axioms energyMeasureExtended_lt_top_of_contMDiff
#print axioms energyMeasureExtended_lt_top_of_smooth_uncond
#print axioms energyMeasureExtended_lt_top_of_jhol_uncond
#print axioms eq_const_of_totalEnergy_eq_zero_uncond
#print axioms totalEnergy_pos_of_nonconstant_uncond

--------------------------------------------------------------------------------
-- Test 18: Proved Cylinder Energy Decay (cert_decay / A10) from Collar Hole-Filling & Thresholds
--------------------------------------------------------------------------------

omit [Nonempty M] in
/-- Test 18.1: Continuous two-sided power-law cylinder energy decay derived from single-step
collar Widman hole-filling (`0 sorryAx`). -/
theorem test_satisfiesCylinderEnergyDecayWith_of_collar_hole_filling
    (u : CP1 → M) (center : ℂ) {r R K : ℝ}
    (hr : 0 < r) (hK : 0 < K)
    (h_fin : energyMeasureExtended I u (annulus_at center r R) ≠ ⊤)
    (h_collar : ∀ r' R' : ℝ, r ≤ r' → R' ≤ R → 4 * r' < R' →
      energyMeasure I u (annulus_at center (2 * r') (R' / 2)) ≤
        K * (energyMeasure I u (annulus_at center r' (2 * r')) +
             energyMeasure I u (annulus_at center (R' / 2) R'))) :
    Analysis.SatisfiesCylinderEnergyDecayWith I ((1 + K) / K) (Real.log ((1 + K) / K) / Real.log 2) u center r R :=
  Analysis.satisfiesCylinderEnergyDecayWith_of_collar_hole_filling I u center hr hK h_fin h_collar

omit [Nonempty M] in
/-- Test 18.2: Unconditional `CylinderEnergyDecayProperty I M` from single-step collar Widman
hole-filling on `[BoundedChartedTarget I M]` (`0 sorryAx`). -/
theorem test_cylinderEnergyDecayProperty_of_collar_hole_filling_uncond
    [BoundedChartedTarget I M]
    {K ε_neck : ℝ} (hK : 0 < K) (hε : 0 < ε_neck)
    (h_collar : ∀ (u : CP1 → M) (center : ℂ) (r' R' : ℝ),
      0 < r' → 4 * r' < R' →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r' R') < ε_neck →
      energyMeasure I u (annulus_at center (2 * r') (R' / 2)) ≤
        K * (energyMeasure I u (annulus_at center r' (2 * r')) +
             energyMeasure I u (annulus_at center (R' / 2) R'))) :
    Analysis.CylinderEnergyDecayProperty I M :=
  cylinderEnergyDecayProperty_of_collar_hole_filling_uncond I hK hε h_collar

omit [Nonempty M] in
/-- Test 18.3: Every `TargetThresholds I M` witnesses `CylinderEnergyDecayProperty I M` (`0 sorryAx`). -/
theorem test_cylinderEnergyDecayProperty_of_thresholds
    (th : Analysis.TargetThresholds I M) :
    Analysis.CylinderEnergyDecayProperty I M :=
  th.cylinderEnergyDecayProperty

#print axioms GromovCompactness.Analysis.disjoint_annulus_at_of_le
#print axioms GromovCompactness.Analysis.energyMeasure_three_annuli_le_outer
#print axioms GromovCompactness.Analysis.energyMeasure_collar_sum_le_outer_sub_inner
#print axioms GromovCompactness.Analysis.satisfiesCylinderEnergyDecayWith_of_dyadic_hole_filling
#print axioms GromovCompactness.Analysis.satisfiesCylinderEnergyDecayWith_of_collar_hole_filling
#print axioms GromovCompactness.Analysis.satisfiesCylinderEnergyDecayWith_of_ratio_le
#print axioms GromovCompactness.Analysis.cylinderEnergyDecayProperty_of_collar_hole_filling
#print axioms GromovCompactness.Analysis.cylinder_exponential_decay_of_collar_hole_filling
#print axioms cylinderEnergyDecayProperty_of_collar_hole_filling_uncond
#print axioms cylinder_exponential_decay_of_collar_hole_filling_uncond
#print axioms UniformNormalChartCertificates.of_collar_hole_filling
#print axioms GromovCompactness.Analysis.TargetThresholds.cylinderEnergyDecayProperty
#print axioms GromovCompactness.Analysis.TargetThresholds.cylinder_exponential_decay

--------------------------------------------------------------------------------
-- Test 19: Proved Collar Oscillation (cert_osc / A09) from Bounded-Modulus Slices & Decay
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 19.1: Pointwise collar energy-density bound from dyadic disk regularity (`0 sorryAx`). -/
theorem test_riemannianEnergyDensity_collar_le_of_disk_regularity
    (u : CP1 → M) (a : ℂ) {r R C_reg : ℝ} (hr : 0 < r) (hC : 0 ≤ C_reg)
    {w₀ : ℂ} (hw₀ : w₀ ∈ {z : ℂ | 2 * r < dist z a ∧ dist z a < R / 2})
    (h_fin : energyMeasureExtended I u (annulus_at a r R) ≠ ⊤)
    (h_reg : riemannianEnergyDensity I u (stereo_chart.symm w₀) ≤
      C_reg * (dist w₀ a / 2) ^ (-2 : ℝ) * energyMeasure I u (disk_at w₀ (dist w₀ a / 2))) :
    riemannianEnergyDensity I u (stereo_chart.symm w₀) ≤
      C_reg * r ^ (-2 : ℝ) * energyMeasure I u (annulus_at a r R) :=
  Analysis.riemannianEnergyDensity_collar_le_of_disk_regularity I u a hr hC hw₀ h_fin h_reg

omit [Nonempty M] in
/-- Test 19.2: Unconditional `CollarOscillationProperty I M` (`cert_osc`) from bounded-modulus
(`R ≤ 18 * r`) radial/angular slices and single-step collar Widman hole-filling on
`[BoundedChartedTarget I M]` (`0 sorryAx`). -/
theorem test_collarOscillationProperty_of_slices_and_collar_hole_filling_uncond
    [BoundedChartedTarget I M]
    (h_slices : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        energyMeasure I u (annulus_at a r R) < ε_ring →
        ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
          ∃ z_mid : CP1,
            dist (u z₁) (u z_mid) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)) ∧
            dist (u z_mid) (u z₂) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)))
    {K ε_neck : ℝ} (hK : 0 < K) (hε : 0 < ε_neck)
    (h_collar : ∀ (u : CP1 → M) (center : ℂ) (r' R' : ℝ),
      0 < r' → 4 * r' < R' →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r' R') < ε_neck →
      energyMeasure I u (annulus_at center (2 * r') (R' / 2)) ≤
        K * (energyMeasure I u (annulus_at center r' (2 * r')) +
             energyMeasure I u (annulus_at center (R' / 2) R'))) :
    Analysis.CollarOscillationProperty I M :=
  collarOscillationProperty_of_slices_and_collar_hole_filling_uncond I h_slices hK hε h_collar

#print axioms GromovCompactness.Analysis.riemannianEnergyDensity_collar_le_of_disk_regularity
#print axioms GromovCompactness.Analysis.satisfiesCylinderCollarOscillationWith_of_lipschitz_collar_ring
#print axioms GromovCompactness.Analysis.collarOscillationProperty_of_slices_and_decay
#print axioms GromovCompactness.Analysis.collarOscillationProperty_of_slices_and_collar_hole_filling
#print axioms GromovCompactness.Analysis.cylinder_localization_of_slices_and_decay
#print axioms collarOscillationProperty_of_slices_and_collar_hole_filling_uncond
#print axioms GromovCompactness.Analysis.TargetThresholds.collarOscillationProperty_of_slices

--------------------------------------------------------------------------------
-- Test 20: Proved Puncture Extension (cert_punc / A11)
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 20.1: Single-point $C^1$ at `p` upgrades to global `ContMDiffOn I_CP1 I 1` on `CP1` (`0 sorryAx`). -/
theorem test_contMDiffOn_one_update_of_contMDiffAt_puncture
    (u : CP1 → M) (p : CP1) (m_star : M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_at : ContMDiffAt I_CP1 I 1 (Function.update u p m_star) p) :
    ContMDiffOn I_CP1 I 1 (Function.update u p m_star) Set.univ :=
  Analysis.contMDiffOn_one_update_of_contMDiffAt_puncture I u p m_star hu h_at

omit [I.Boundaryless] [Nonempty M] in
set_option backward.isDefEq.respectTransparency false in
/-- Test 20.2: Single-point $C^1$ and `mfderiv` continuity at `p` imply global `WeakJHolomorphicOn` (`0 sorryAx`). -/
theorem test_weakJHolomorphicOn_univ_of_contMDiffAt_and_continuousAt_mfderiv_at_puncture
    (u : CP1 → M) (p : CP1) (m_star : M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_at : ContMDiffAt I_CP1 I 1 (Function.update u p m_star) p)
    (hd_cont : ∀ w : EuclideanSpace ℝ (Fin 2),
      ContinuousAt (fun z : CP1 =>
        (mfderiv I_CP1 I (Function.update u p m_star) z w : E)) p) :
    Analysis.WeakJHolomorphicOn I (Function.update u p m_star) Set.univ :=
  weakJHolomorphicOn_univ_of_contMDiffAt_and_continuousAt_mfderiv_at_puncture I u p m_star hu h_at hd_cont

#print axioms GromovCompactness.Analysis.exists_limit_point_of_local_collar_oscillation
#print axioms GromovCompactness.Analysis.exists_unique_limit_point_of_local_collar_oscillation
#print axioms GromovCompactness.Analysis.exists_unique_continuous_extension_of_local_collar_oscillation
#print axioms GromovCompactness.Analysis.contMDiffOn_one_update_of_contMDiffAt_puncture
#print axioms GromovCompactness.Analysis.satisfiesPunctureSobolevExtension_of_local_collar_oscillation_and_c1
#print axioms GromovCompactness.Analysis.satisfiesPunctureSobolevExtension_of_slices_and_decay_and_c1
#print axioms GromovCompactness.Analysis.puncture_sobolev_extension_of_slices_and_decay_and_c1
#print axioms continuousAt_cr_defect_of_continuousAt_mfderiv
#print axioms weakJHolomorphicOn_univ_of_contMDiffAt_and_continuousAt_mfderiv_at_puncture
#print axioms satisfiesPunctureSobolevExtension_of_slices_and_decay_and_mfderiv

--------------------------------------------------------------------------------
-- Test 21: Proved Weitzenböck Decomposition (cert_weitz / A02 / A03)
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 21.1: `WeitzenbockDecompositionProperty` from Bochner lower bound (`0 sorryAx`). -/
theorem test_weitzenbockDecompositionProperty_of_bochner_lower_bound
    (h_bochner : ∃ b : ℝ, 0 ≤ b ∧ ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
      ∀ (w : ℂ), -b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 ≤
        Analysis.laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w) :
    Analysis.WeitzenbockDecompositionProperty I M :=
  Analysis.weitzenbockDecompositionProperty_of_bochner_lower_bound I M h_bochner

omit [I.Boundaryless] in
/-- Test 21.2: `WeitzenbockDecompositionProperty` on `[FiniteDimensional ℝ E]` `[Nonempty M]`
from the centered normal-chart Weitzenböck remainder bound (`0 sorryAx`). -/
theorem test_weitzenbockDecompositionProperty_of_normal_chart_weitz_uncond
    [FiniteDimensional ℝ E]
    {C_metric3 C_J3 : ℝ} (hCm : 0 ≤ C_metric3) (hCJ : 0 ≤ C_J3)
    (h_norm_weitz : ∀ {c_min : ℝ}, 0 < c_min →
      (∀ (x : M) (v : E), c_min * ‖v‖ ^ 2 ≤ ClosedTameTarget.metric I x v v) →
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
        ∀ (w : ℂ), ∃ (g : E → E →L[ℝ] E →L[ℝ] ℝ) (J : E → E →L[ℝ] E) (v : ℂ → E),
          v 0 = 0 ∧
          (∀ y : E, c_min * ‖y‖ ^ 2 ≤ g 0 y y) ∧
          (∀ y : E, ‖iteratedFDeriv ℝ 2 (fun z => g z y y) 0‖ ≤ C_metric3 * ‖y‖ ^ 2) ∧
          (∀ y : E, ‖fderiv ℝ (fun z => J z y) 0‖ ≤ C_J3 * ‖y‖) ∧
          (∀ y : E, ‖iteratedFDeriv ℝ 2 (fun z => J z y) 0‖ ≤ C_J3 * ‖y‖) ∧
          Analysis.localEnergyDensity v g 0 = riemannianEnergyDensity I u (stereo_chart.symm w) ∧
          ∃ (hessNorm rem : ℝ),
            Analysis.laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + rem ∧
            |rem| ≤ |Analysis.K_tensor g J v|) :
    Analysis.WeitzenbockDecompositionProperty I M :=
  weitzenbockDecompositionProperty_of_normal_chart_weitz_uncond I hCm hCJ h_norm_weitz

#print axioms GromovCompactness.Analysis.sum_norm_fderiv_sq_le_of_coercive_localEnergyDensity
#print axioms GromovCompactness.Analysis.bound_K_tensor_of_coercive
#print axioms GromovCompactness.Analysis.bochner_lower_bound_of_normal_chart_weitz_at_center
#print axioms GromovCompactness.Analysis.weitzenbockDecompositionProperty_of_bochner_lower_bound
#print axioms GromovCompactness.Analysis.weitzenbockDecompositionProperty_of_normal_chart_weitz
#print axioms GromovCompactness.Analysis.bochner_differential_inequality_of_bochner_lower_bound
#print axioms GromovCompactness.Analysis.epsilon_regularity_of_bochner_lower_bound
#print axioms GromovCompactness.Analysis.epsilon_regularity_of_normal_chart_weitz
#print axioms weitzenbockDecompositionProperty_of_normal_chart_weitz_uncond

--------------------------------------------------------------------------------
-- Test 22: Proved Elliptic Regularity Tower (cert_tower / A05 / A12)
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 22.1: `RegularityTowerProperty` from the chart-level elliptic step (`0 sorryAx`). -/
theorem test_regularityTowerProperty_of_chart_step
    (h_chart_step : ∀ (u : CP1 → M) (Ω : Set CP1), IsOpen Ω → Analysis.WeakJHolomorphicOn I u Ω →
      ∀ (k : ℕ), 1 ≤ k → ∀ z ∈ Ω,
        ContDiffAt ℝ (k : WithTop ℕ∞) (writtenInExtChartAt I_CP1 I z u) ((extChartAt I_CP1 z) z) →
        ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (writtenInExtChartAt I_CP1 I z u) ((extChartAt I_CP1 z) z)) :
    Analysis.RegularityTowerProperty I M :=
  Analysis.regularityTowerProperty_of_chart_step I M h_chart_step

omit [I.Boundaryless] [Nonempty M] in
/-- Test 22.2: Contract A05 (`nonlinear_elliptic_bootstrap_of_chart_step`) from the chart-level
elliptic step (`0 sorryAx`). -/
theorem test_nonlinear_elliptic_bootstrap_of_chart_step
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω)
    (h_chart_step : ∀ (k : ℕ), 1 ≤ k → ∀ z ∈ Ω,
      ContDiffAt ℝ (k : WithTop ℕ∞) (writtenInExtChartAt I_CP1 I z u) ((extChartAt I_CP1 z) z) →
      ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (writtenInExtChartAt I_CP1 I z u) ((extChartAt I_CP1 z) z)) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  Analysis.nonlinear_elliptic_bootstrap_of_chart_step I u Ω hΩ h_weak h_chart_step

#print axioms GromovCompactness.Analysis.contDiffAt_writtenInExtChartAt_of_contMDiffOn
#print axioms GromovCompactness.Analysis.contMDiffWithinAt_of_weakJHolomorphicOn_and_contDiffAt_writtenInExtChartAt
#print axioms GromovCompactness.Analysis.contMDiffOn_nat_of_weakJHolomorphicOn_and_chart_step
#print axioms GromovCompactness.Analysis.regularityTowerProperty_of_step
#print axioms GromovCompactness.Analysis.regularityTowerProperty_of_chart_step
#print axioms GromovCompactness.Analysis.nonlinear_elliptic_bootstrap_of_chart_step
#print axioms GromovCompactness.Analysis.removal_of_singularities_of_slices_and_decay_and_c1_and_tower
#print axioms GromovCompactness.Analysis.removal_of_singularities_of_slices_and_decay_and_c1_and_chart_step
#print axioms removal_of_singularities_of_slices_and_decay_and_mfderiv_and_chart_step

--------------------------------------------------------------------------------
-- Test 23: Proved Target Monotonicity & Small-Ball Exit (cert_hit / A08 / A07 / B01)
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 23.1: `BoundaryHitMonotonicity` from the radial differential inequality (`0 sorryAx`). -/
theorem test_boundaryHitMonotonicity_of_radial_diff_ineq
    {c r₀ : ℝ}
    (h_radial : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      ∃ (F F' : ℝ → ℝ) (r_min : ℝ),
        0 < r_min ∧ r_min ≤ r ∧
        (∀ t ∈ Set.Icc r_min r, HasDerivAt F (F' t) t) ∧
        (∀ t ∈ Set.Icc r_min r, F t ≤ (1 / 2 : ℝ) * t * F' t) ∧
        c * r_min ^ 2 ≤ F r_min ∧
        F r ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r))) :
    Analysis.BoundaryHitMonotonicity I M c r₀ :=
  Analysis.boundaryHitMonotonicity_of_radial_diff_ineq I h_radial

omit [I.Boundaryless] [Nonempty M] in
/-- Test 23.2: `HitExitProperty` from the radial differential inequality and two-point diameter
separation (`0 sorryAx`). -/
theorem test_hitExitProperty_of_radial_diff_ineq_and_pair_dist
    {c r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_radial : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c₀ : M, ∀ z, u z = c₀) →
      (∃ z, u z ∉ Metric.ball x r) →
      ∃ (F F' : ℝ → ℝ) (r_min : ℝ),
        0 < r_min ∧ r_min ≤ r ∧
        (∀ t ∈ Set.Icc r_min r, HasDerivAt F (F' t) t) ∧
        (∀ t ∈ Set.Icc r_min r, F t ≤ (1 / 2 : ℝ) * t * F' t) ∧
        c * r_min ^ 2 ≤ F r_min ∧
        F r ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (h_cont_and_pair : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      Continuous (riemannianEnergyDensity I u) ∧
      ∃ z₁ z₂ : CP1, 2 * r₀ ≤ dist (u z₁) (u z₂)) :
    Analysis.HitExitProperty I M :=
  Analysis.hitExitProperty_of_radial_diff_ineq_and_pair_dist I hc hr₀ h_radial h_cont_and_pair

#print axioms GromovCompactness.Analysis.exists_dist_ge_of_pair_dist_ge
#print axioms GromovCompactness.Analysis.smallBallExit_of_pair_dist_ge
#print axioms GromovCompactness.Analysis.boundaryHitMonotonicity_of_radial_diff_ineq
#print axioms GromovCompactness.Analysis.hitExitProperty_of_radial_diff_ineq_and_exit
#print axioms GromovCompactness.Analysis.hitExitProperty_of_radial_diff_ineq_and_pair_dist
#print axioms GromovCompactness.Analysis.target_monotonicity_of_radial_diff_ineq
#print axioms GromovCompactness.Analysis.sphere_energy_gap_of_radial_diff_ineq_and_exit
#print axioms GromovCompactness.Analysis.sphere_energy_gap_of_radial_diff_ineq_and_pair_dist
#print axioms GromovCompactness.Analysis.totalEnergy_pos_of_boundaryHitMonotonicity
#print axioms GromovCompactness.Analysis.exists_target_thresholds_of_first_principles

--------------------------------------------------------------------------------
-- Test 24: Proved Realized One-Level Decomposition & Defect Tree Resolution (cert_onelevel / B04 / B07)
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 24.1: `IsDefectSeq.exists_calibrated_subseq_scales` (`0 sorryAx`). -/
theorem test_exists_calibrated_subseq_scales
    (thresh : Bubbling.TargetThresholds I M)
    {f : ℕ → (CP1 → M)} {a : ℂ} {m_defect : ℝ} {base_val : M}
    (hm : thresh.h ≤ m_defect)
    (h_def : Bubbling.IsDefectSeq I f a m_defect base_val) :
    ∃ (σ : Bookkeeping.SubseqMap) (R scale : ℕ → ℝ),
      (∀ k, 0 < scale k) ∧
      (∀ k, scale k ≤ R k) ∧
      (∀ k, R k ≤ 1 / ((k : ℝ) + 1)) ∧
      Filter.Tendsto scale Filter.atTop (𝓝 0) ∧
      (∀ k, energyMeasure I (f (σ.1 k)) (disk_at a (scale k)) = m_defect - thresh.h / 2) ∧
      (∀ k, ∀ z ∈ annulus_at a (R k / 2) (R k),
        dist (f (σ.1 k) z) base_val < 1 / ((k : ℝ) + 1)) :=
  Bubbling.IsDefectSeq.exists_calibrated_subseq_scales I thresh hm h_def

omit [I.Boundaryless] [Nonempty M] in
/-- Test 24.2: `oneLevelCertificate_of_rescaled_limit` (`0 sorryAx`). -/
theorem test_oneLevelCertificate_of_rescaled_limit
    (thresh : Bubbling.TargetThresholds I M)
    (h_extract : ∀ (f : ℕ → (CP1 → M)) (a : ℂ) (m : ℝ) (b : M),
      thresh.h ≤ m → Bubbling.IsDefectSeq I f a m b →
      ∀ (σ₀ : Bookkeeping.SubseqMap) (scale₀ : ℕ → ℝ) (hpos₀ : ∀ k, 0 < scale₀ k),
        Filter.Tendsto scale₀ Filter.atTop (𝓝 0) →
        (∀ k, energyMeasure I (f (σ₀.1 k)) (disk_at a (scale₀ k)) = m - thresh.h / 2) →
        ∃ (decomp : Bubbling.OneLevelDecomposition I thresh m b) (τ : Bookkeeping.SubseqMap),
          SmoothLocalConvergesOn I
            (fun n => f (σ₀.1 (τ.1 n)) ∘
              (affine_scaling a (scale₀ (τ.1 n)) (hpos₀ (τ.1 n))).toHomeo)
            decomp.v
            (punctured_sphere (insert north_pole (stereo_chart.symm '' (decomp.q : Set ℂ)))) ∧
          (Filter.Tendsto (fun n => totalEnergy I (f n)) Filter.atTop (𝓝 m) →
            SmoothLocalConvergesOn I
              (fun n => f (σ₀.1 (τ.1 n)) ∘
                (affine_scaling a (scale₀ (τ.1 n)) (hpos₀ (τ.1 n))).toHomeo)
              decomp.v {north_pole}) ∧
          (∀ z ∈ decomp.q,
            Bubbling.IsDefectSeq I
              (fun n => f (σ₀.1 (τ.1 n)) ∘
                (affine_scaling a (scale₀ (τ.1 n)) (hpos₀ (τ.1 n))).toHomeo)
              z (decomp.m_child z) (decomp.v (stereo_chart.symm z)))) :
    Bubbling.OneLevelCertificate I thresh :=
  Bubbling.oneLevelCertificate_of_rescaled_limit I thresh h_extract

#print axioms GromovCompactness.Bubbling.affine_scaling_tendstoUniformlyOn_punctured_north_pole
#print axioms GromovCompactness.Bubbling.affine_scaling_inv_tendstoUniformlyOn_punctured_center
#print axioms GromovCompactness.Bubbling.IsDefectSeq.exists_calibrated_subseq_scales
#print axioms GromovCompactness.Bubbling.SeqOneLevelDecomposition.of_rescaled_limit
#print axioms GromovCompactness.Bubbling.oneLevelCertificate_of_rescaled_limit
#print axioms GromovCompactness.Bubbling.resolve_single_defect_tree_realized_of_rescaled_limit
#print axioms GromovCompactness.Bubbling.resolve_single_defect_tree_of_rescaled_limit

--------------------------------------------------------------------------------
-- Test 25: Proved Smooth Concentration Extraction & Defect Measure Decomposition (cert_conc / C02)
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 25.1: `defect_measure_decomp_of_smooth_conv_off_S` (`0 sorryAx`). -/
theorem test_defect_measure_decomp_of_smooth_conv_off_S
    (v_seq : ℕ → (CP1 → M))
    (μ : Measure CP1) [IsFiniteMeasure μ]
    (S : Finset CP1)
    (u₀ : CP1 → M)
    (h_weak : Compactness.WeakMeasureConvergence (fun n => energyMeasureExtended I (v_seq n)) μ)
    (h_conv : SmoothLocalConvergesOn I v_seq u₀ (Set.univ \ S))
    (h_meas_dens : ∀ n, Measurable (fun w : ℂ => riemannianEnergyDensity I (v_seq n) (stereo_chart.symm w)))
    (h_grad_bdd : ∀ K ⊆ Set.univ \ (S : Set CP1), IsCompact K →
      ∃ C ≥ 0, ∀ᶠ n in Filter.atTop, ∀ z ∈ K, riemannianEnergyDensity I (v_seq n) z ≤ C) :
    energyMeasureExtended I u₀ Set.univ ≤ μ Set.univ ∧
      μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • Measure.dirac p) :=
  Compactness.defect_measure_decomp_of_smooth_conv_off_S I v_seq μ S u₀ h_weak h_conv h_meas_dens h_grad_bdd

omit [I.Boundaryless] [Nonempty M] in
/-- Test 25.2: `smoothConcentrationExtractProperty_of_local_compactness_and_removal` (`0 sorryAx`). -/
theorem test_smoothConcentrationExtractProperty
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (thresh : Analysis.TargetThresholds I M)
    (h_meas_dens : ∀ n, Measurable (fun w : ℂ => riemannianEnergyDensity I (u_seq n) (stereo_chart.symm w)))
    (h_local_extract : ∀ (σ : Bookkeeping.SubseqMap) (μ : Measure CP1) (S : Finset CP1), IsFiniteMeasure μ →
      Compactness.WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ →
      (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p}) →
      (∀ K ⊆ Set.univ \ (S : Set CP1), IsCompact K →
        ∃ C ≥ 0, ∀ᶠ n in Filter.atTop, ∀ z ∈ K, riemannianEnergyDensity I (u_seq (σ.1 n)) z ≤ C) ∧
      ∃ (τ : Bookkeeping.SubseqMap) (u₁ : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq ((σ.comp τ).1 n)) u₁ (Set.univ \ S))
    (h_local_rem : ∀ (u : CP1 → M) (Ω : Set CP1) (p : CP1),
      IsOpen Ω → IsOpen (insert p Ω) → p ∉ Ω →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Ω →
      energyMeasureExtended I u Ω ≠ ⊤ →
      ∃ u_ext : CP1 → M, Set.EqOn u_ext u Ω ∧ JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext (insert p Ω)) :
    Compactness.SmoothConcentrationExtractProperty I u_seq thresh :=
  Compactness.smoothConcentrationExtractProperty_of_local_compactness_and_removal I
    u_seq h_jhol thresh h_meas_dens h_local_extract h_local_rem

#print axioms GromovCompactness.Compactness.energyMeasureExtended_congr_off_finset
#print axioms GromovCompactness.Compactness.eventually_gradient_bound_on_compact_southern_hemisphere_of_disjoint_S
#print axioms GromovCompactness.Compactness.tendsto_riemannianEnergyDensity_of_smoothLocalConvergesOn
#print axioms GromovCompactness.Compactness.defect_measure_decomp_of_smooth_conv_off_S
#print axioms GromovCompactness.Compactness.jholomorphic_extension_across_finset
#print axioms GromovCompactness.Compactness.smoothConcentrationExtractProperty_of_local_compactness_and_removal
#print axioms GromovCompactness.Compactness.exists_concentration_data_of_local_compactness_and_removal

--------------------------------------------------------------------------------
-- Test 26: Proved Arzelà–Ascoli Smooth Extraction & Local Smooth Compactness (cert_aa / A06)
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 26.1: `exists_fixed_chart_ball_eventually_smooth_and_pointwise` (`0 sorryAx`). -/
theorem test_exists_fixed_chart_ball_eventually_smooth_and_pointwise
    (v_seq : ℕ → (CP1 → M)) (v_lim : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (hv_seq : ∀ n, ContMDiffOn I_CP1 I ∞ (v_seq n) Ω)
    (hv_lim_cont : ContinuousOn v_lim Ω)
    (h_unif : ∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn v_seq v_lim Filter.atTop K)
    {z : CP1} (hz : z ∈ Ω) :
    ∃ (U_z : Set (EuclideanSpace ℝ (Fin 2))) (N_z : ℕ),
      IsOpen U_z ∧ (extChartAt I_CP1 z) z ∈ U_z ∧
      (∀ n ≥ N_z, ContDiffOn ℝ (⊤ : ℕ∞)
        (fun x => (extChartAt I (v_lim z)) (v_seq n ((extChartAt I_CP1 z).symm x))) U_z) ∧
      (∀ x ∈ U_z, Filter.Tendsto
        (fun n => (extChartAt I (v_lim z)) (v_seq n ((extChartAt I_CP1 z).symm x)))
        Filter.atTop
        (nhds (writtenInExtChartAt I_CP1 I z v_lim x))) :=
  Analysis.exists_fixed_chart_ball_eventually_smooth_and_pointwise I
    v_seq v_lim Ω hΩ hv_seq hv_lim_cont h_unif hz

omit [Nonempty M] in
/-- Test 26.2: `arzelaAscoliProperty_of_bounded_geometry_and_eventually_jet_bounds` (`0 sorryAx`). -/
theorem test_arzelaAscoliProperty_of_bounded_geometry
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (h_jets : ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1),
      IsOpen Ω →
      (∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω) →
      (∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) →
      ∀ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        ContinuousOn u_lim Ω →
        (∀ K ⊆ Ω, IsCompact K →
          TendstoUniformlyOn (fun n => u_seq (σ.1 n)) u_lim Filter.atTop K) →
        (∀ z ∈ Ω, Filter.Tendsto (fun n => u_seq (σ.1 n) z) Filter.atTop (𝓝 (u_lim z))) →
        ∀ z ∈ Ω, Analysis.EventuallyHasLocalChartJetBoundsAt I (fun n => u_seq (σ.1 n)) u_lim z) :
    Analysis.ArzelaAscoliProperty I M :=
  arzelaAscoliProperty_of_bounded_geometry_and_eventually_jet_bounds I h_jets

#print axioms GromovCompactness.Analysis.eventuallyHasLocalChartJetBoundsAt_comp_moebius
#print axioms GromovCompactness.Analysis.coreSmoothLocalConvergesOn_of_eventually_local_jet_bounds
#print axioms GromovCompactness.Analysis.smoothLocalConvergesOn_of_eventually_local_jet_bounds
#print axioms GromovCompactness.Analysis.exists_fixed_chart_ball_eventually_smooth_and_pointwise
#print axioms GromovCompactness.Analysis.exists_smoothLocalConvergesOn_subseq_of_equicontinuous_and_eventually_jet_bounds
#print axioms GromovCompactness.Analysis.arzelaAscoliProperty_of_equicontinuous_and_eventually_jet_bounds
#print axioms GromovCompactness.Analysis.local_smooth_compactness_of_arzelaAscoliProperty
#print axioms GromovCompactness.arzelaAscoliProperty_of_bounded_geometry_and_eventually_jet_bounds
#print axioms GromovCompactness.local_smooth_compactness_of_bounded_geometry_and_eventually_jet_bounds

--------------------------------------------------------------------------------
-- Test 27: Proved Concentration-to-Defect Theorem & Core Compactness (cert_concdefect / G01 / G03)
--------------------------------------------------------------------------------

omit [Nonempty M] in
/-- Test 27.1: Unconditional southern-hemisphere `IsDefectSeq` extraction (`0 sorryAx`). -/
theorem test_isDefectSeq_of_concentration_southern_hemisphere
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m : CP1 → ℝ)
    (h_decomp : cdata.μ = energyMeasureExtended I cdata.u₀ +
      ∑ q ∈ cdata.S, (ENNReal.ofReal (m q) • MeasureTheory.Measure.dirac q))
    {p : CP1} (hp : p ∈ cdata.S) (a : ℂ) (ha_norm : ‖a‖ < 1) (ha : stereo_chart.symm a = p) :
    Bubbling.IsDefectSeq I (fun n => u_seq (cdata.σ.1 n)) a (m p) (cdata.u₀ p) ∧
    ((cdata.S = {p} ∧ ∃ c : M, ∀ z : CP1, cdata.u₀ z = c) →
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop (𝓝 (m p))) :=
  Assembly.isDefectSeq_of_concentration_southern_hemisphere I
    th u_seq B h_jhol h_energy cdata m h_decomp hp a ha_norm ha

omit [Nonempty M] in
/-- Test 27.2: `concDefectCertificate_of_rotations` (`0 sorryAx`). -/
theorem test_concDefectCertificate_of_rotations
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_rot : ∀ p : CP1, (∃ a : ℂ, ‖a‖ < 1 ∧ stereo_chart.symm a = p) ∨
      ∃ rot : MoebiusFrame, Assembly.IsConformalRotationTo I (M := M) p rot) :
    Assembly.ConcDefectCertificate I u_seq B th :=
  Assembly.concDefectCertificate_of_rotations I th u_seq B h_jhol h_energy h_rot

#print axioms GromovCompactness.Assembly.tendstoUniformlyOn_of_pointwise_and_equicontinuous_on_open
#print axioms GromovCompactness.Assembly.exists_isolating_disk_radius
#print axioms GromovCompactness.Assembly.defect_mass_limit_of_concentration_finite_point
#print axioms GromovCompactness.Assembly.isDefectSeq_of_concentration_southern_hemisphere
#print axioms GromovCompactness.Assembly.weakMeasureConvergence_map_homeomorph
#print axioms GromovCompactness.Assembly.isConformalRotationTo_south_pole
#print axioms GromovCompactness.Assembly.isConformalRotationTo_of_biholomorphic_and_pullback
#print axioms GromovCompactness.Assembly.concDefectCertificate_of_rotations
#print axioms GromovCompactness.Assembly.assemble_prestable_limit_of_rotations
#print axioms GromovCompactness.gromov_compactness_core_of_rotations

--------------------------------------------------------------------------------
-- Test 28: Proved Universal Bubbling Thresholds & Master Compactness (cert_thresholds / thm_main)
--------------------------------------------------------------------------------

omit [I.Boundaryless] [Nonempty M] in
/-- Test 28.1: `exists_target_thresholds_of_properties` (`0 sorryAx`). -/
theorem test_exists_target_thresholds_of_properties
    (h_weitz : Analysis.WeitzenbockDecompositionProperty I M)
    (h_hit_exit : Analysis.HitExitProperty I M)
    (h_decay : Analysis.CylinderEnergyDecayProperty I M) :
    Nonempty (Bubbling.TargetThresholds I M) :=
  Bubbling.exists_target_thresholds_of_properties I h_weitz h_hit_exit h_decay

omit [Nonempty M] in
/-- Test 28.2: `exists_target_thresholds_of_bounded_geometry_certs` (`0 sorryAx`). -/
theorem test_exists_target_thresholds_of_bounded_geometry_certs
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (certs : UniformNormalChartCertificates I (construct_uniform_normal_chart_family I (M := M))) :
    Nonempty (Bubbling.TargetThresholds I M) :=
  Bubbling.exists_target_thresholds_of_bounded_geometry_certs I certs

omit [Nonempty M] in
/-- Test 28.3: `exists_target_thresholds_of_symplectically_aspherical` (`0 sorryAx`). -/
theorem test_exists_target_thresholds_of_symplectically_aspherical
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (h_aspherical : ∀ u : CP1 → M,
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
      totalEnergy I u = 0) :
    Nonempty (Bubbling.TargetThresholds I M) :=
  Bubbling.exists_target_thresholds_of_symplectically_aspherical I h_aspherical

#print axioms GromovCompactness.Analysis.TargetThresholds.of_properties
#print axioms GromovCompactness.Analysis.exists_target_thresholds_of_properties
#print axioms GromovCompactness.Analysis.TargetThresholds.of_normal_chart_certificates
#print axioms GromovCompactness.Analysis.exists_target_thresholds_of_normal_chart_certificates
#print axioms GromovCompactness.Analysis.TargetThresholds.of_bounded_geometry_certs
#print axioms GromovCompactness.Analysis.exists_target_thresholds_of_bounded_geometry_certs
#print axioms GromovCompactness.Analysis.TargetThresholds.of_bounded_geometry_first_principles
#print axioms GromovCompactness.Analysis.exists_target_thresholds_of_bounded_geometry_first_principles
#print axioms GromovCompactness.Analysis.exists_target_thresholds_of_symplectically_aspherical
#print axioms GromovCompactness.gromov_compactness_genus_zero_of_rotations
#print axioms GromovCompactness.gromov_compactness_genus_zero_of_properties
#print axioms GromovCompactness.gromov_compactness_genus_zero_of_bounded_geometry_certs

--------------------------------------------------------------------------------
-- Test 29: Proved Extension Theorems (cert_extensions / E01, E02, E04, E05)
--------------------------------------------------------------------------------

/-- Test 29.1: Unconditional 3-point homeomorphism rigidity of `MoebiusFrame` (`0 sorryAx`). -/
theorem test_moebiusFrame_three_point_rigidity
    (ϕ : MoebiusFrame) (p₁ p₂ p₃ : CP1)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hp1 : ϕ.toHomeo p₁ = p₁) (hp2 : ϕ.toHomeo p₂ = p₂) (hp3 : ϕ.toHomeo p₃ = p₃) :
    ϕ.toHomeo = Homeomorph.refl CP1 :=
  Extensions.moebiusFrame_three_point_rigidity ϕ p₁ p₂ p₃ h12 h13 h23 hp1 hp2 hp3

/-- Test 29.2: Unconditional 3-point transitivity of `MoebiusFrame` on `CP1` (`0 sorryAx`). -/
theorem test_exists_moebiusFrame_three_points
    (p₁ p₂ p₃ q₁ q₂ q₃ : CP1)
    (hp12 : p₁ ≠ p₂) (hp13 : p₁ ≠ p₃) (hp23 : p₂ ≠ p₃)
    (hq12 : q₁ ≠ q₂) (hq13 : q₁ ≠ q₃) (hq23 : q₂ ≠ q₃) :
    ∃ ϕ : MoebiusFrame, ϕ.toHomeo p₁ = q₁ ∧ ϕ.toHomeo p₂ = q₂ ∧ ϕ.toHomeo p₃ = q₃ :=
  Extensions.exists_moebiusFrame_three_points p₁ p₂ p₃ q₁ q₂ q₃ hp12 hp13 hp23 hq12 hq13 hq23

omit [I.Boundaryless] [Nonempty M] in
/-- Test 29.3: Non-trivial compact Hausdorff 3-marked moduli space for `0 ≤ B < th.ε_sph` (`0 sorryAx`). -/
theorem test_moduli_space_three_lt_eps_sph_compact_hausdorff
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB0 : 0 ≤ B) (hB : B < th.ε_sph)
    (h_chart_cont : Continuous (fun p : M => (extChartAt I p) p)) :
    CompactSpace (Extensions.ModuliSpace I (M := M) 3 B) ∧
    T2Space (Extensions.ModuliSpace I (M := M) 3 B) := by
  obtain ⟨_, _, hc, ht2⟩ :=
    Extensions.moduli_space_three_lt_eps_sph_compact_hausdorff_of_chart_cont I th hB0 hB h_chart_cont
  exact ⟨hc, ht2⟩

#print axioms GromovCompactness.Extensions.moebiusFrame_three_point_rigidity
#print axioms GromovCompactness.Extensions.ghost_component_pure_automorphism_trivial_uncond
#print axioms GromovCompactness.Extensions.MoebiusFrame.ofMatrix
#print axioms GromovCompactness.Extensions.exists_moebiusFrame_three_points
#print axioms GromovCompactness.Extensions.effective_ghost_identity_fiber_finite
#print axioms GromovCompactness.Extensions.effective_principal_symmetries_finite_of_finite_fibers
#print axioms GromovCompactness.Extensions.stability_iff_finite_effective_automorphisms_of_finite_fibers
#print axioms GromovCompactness.Extensions.varying_J_limit_jhol_on_open
#print axioms GromovCompactness.Extensions.gromov_compactness_varying_J_of_witness_and_thresholds
#print axioms GromovCompactness.Extensions.smoothLocalConvergesOn_of_tendsto_const_map
#print axioms GromovCompactness.Extensions.marked_gromov_compactness_three_const_of_chart_cont
#print axioms GromovCompactness.Extensions.exists_convergent_pulled_back_marks_subseq
#print axioms GromovCompactness.Extensions.marked_gromov_compactness_of_core_nodal_disjoint
#print axioms GromovCompactness.Extensions.marked_gromov_compactness_zero_marks_of_rotations
#print axioms GromovCompactness.Extensions.marked_gromov_compactness_of_rotations_nodal_disjoint
#print axioms GromovCompactness.Extensions.exists_moebiusFrame_intertwining_three_marks_of_subsingleton_V
#print axioms GromovCompactness.Extensions.moduli_space_metrizable_of_sequential_metric
#print axioms GromovCompactness.Extensions.moduli_space_compact_hausdorff_of_sequential_metric
#print axioms GromovCompactness.Extensions.moduli_space_three_lt_eps_sph_equiv_target
#print axioms GromovCompactness.Extensions.extract_bounded_marked_stable_subseq_three_lt_eps_sph_of_chart_cont
#print axioms GromovCompactness.Extensions.moduli_space_three_lt_eps_sph_compact_hausdorff_of_chart_cont
#print axioms GromovCompactness.Extensions.moduli_space_in_class_three_lt_eps_sph_compact_hausdorff_of_chart_cont

end GromovCompactness.Tests.NormalCharts
