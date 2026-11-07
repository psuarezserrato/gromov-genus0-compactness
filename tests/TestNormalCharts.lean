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

end GromovCompactness.Tests.NormalCharts
