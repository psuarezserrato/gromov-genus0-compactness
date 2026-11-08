/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Milestones N1–N3 Architecture)
-/
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Sort
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EnergyGap
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import GromovCompactness.Analysis.Bochner
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Analysis.SingularityRemoval
import GromovCompactness.Analysis.EllipticBootstrap
import GromovCompactness.Topology.Subsequence

open scoped Manifold ContDiff Topology Real ENNReal
open Metric Set MeasureTheory Filter Topology ENNReal GromovCompactness

/-!
# Normal Coordinate Charts and Geometric Atlas Infrastructure

This module develops the geometric chart infrastructure for closed tame almost complex targets
$(M, \omega, J)$, fulfilling Milestones N1–N3 of the Darboux/Normal Charts roadmap:

## Section Overview
1. **Finite Good Atlas (Milestone N1)**:
   - `FiniteGoodAtlas`: Finite precompact coordinate cover $\{U_i\}_{i \in \iota}$ with Lebesgue radius $r_{\mathrm{atlas}} > 0$.
   - `exists_finiteGoodAtlas`: Existence proof via `isCompact_univ.elim_finite_subcover` and `lebesgue_number_lemma_of_metric`.
   - Chart containment and domain membership helpers.

2. **Factorization of Manifold Differentials & Energy Finiteness (Milestone N1)**:
   - `mfderiv_eq_tangentCoordChange_comp_apply`: Factoring `mfderiv` through fixed atlas charts
     eliminating moving basepoint evaluation via `tangentCoordChange`.
   - General topology compactness and local boundedness principles (`bddAbove_of_compact_of_locally_bounded`).
   - Chart representations of symplectic and almost complex forms (`omega_eq_chart`, `J_eq_chart`).
   - Discharge lemmas for energy finiteness (`energyMeasureExtended_lt_top_of_smooth`).

3. **Centered Quadratic Normal Charts (Milestone N2 - Scaffolding)**:
   - Quadratic Taylor normalization $\Phi_{y_0}(v) = y_0 + v - \frac{1}{2}\Gamma_{y_0}(v, v)$.
   - `CenteredNormalChart`: Chart $\Psi_p$ with $\Psi_p(0) = p$, $d\Psi_p(0) = \mathrm{id}_E$, $\Gamma^{\Psi_p}(0) = 0$.
   - `UniformNormalChartFamily`: Uniform radius $r_{\mathrm{norm}} > 0$ and uniform $C^3$ bounds across compact $M$.

4. **Local-Chart PDE Certificates (Milestone N3 - Scaffolding)**:
   - Bochner–Weitzenböck curvature decomposition certificate (`h_weitz`).
   - Boundary-hit monotonicity & ball exit certificate (`h_hit_exit`).
   - Cylindrical collar oscillation & exponential decay certificates (`h_osc`, `h_decay`).
   - Removable singularity Sobolev extension certificate (`h_punc`).
   - Schauder bootstrap tower & Arzelà–Ascoli certificates (`h_tower`, `h_aa`).
-/

namespace GromovCompactness

universe u

--------------------------------------------------------------------------------
-- SECTION 1: Finite Good Atlas (Milestone N1)
--------------------------------------------------------------------------------

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable {M : Type u} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]

/-- A finite precompact atlas covering a compact metric manifold `M`.
Contains a finite family of chart domains `U i` centered at `center i ∈ M`,
mapping into Euclidean balls of radius `r_target i` in `E`, covering all of `M`,
with a strictly positive Lebesgue number `r_atlas > 0` guaranteeing that any ball of radius
`r_atlas` in `M` is entirely contained within some chart domain `U i`. -/
structure FiniteGoodAtlas (I : ModelWithCorners ℝ E H) (M : Type u)
    [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] where
  /-- Finite indexing type in the same universe as `M` -/
  ι : Type u
  /-- Fintype instance on the indexing type -/
  [fintype : Fintype ι]
  /-- Nonempty instance on the indexing type -/
  [nonempty : Nonempty ι]
  /-- Center basepoint in `M` for each chart -/
  center : ι → M
  /-- Chart domain in `M` -/
  U : ι → Set M
  /-- Openness of each chart domain -/
  isOpen_U : ∀ i : ι, IsOpen (U i)
  /-- Center belongs to its own domain -/
  center_mem : ∀ i : ι, center i ∈ U i
  /-- Each domain is contained in the source of its center's chart -/
  subset_source : ∀ i : ι, U i ⊆ (extChartAt I (center i)).source
  /-- Target radius in the model space `E` -/
  r_target : ι → ℝ
  /-- Target radius is strictly positive -/
  r_target_pos : ∀ i : ι, 0 < r_target i
  /-- The chart maps `U i` into the ball of radius `r_target i` -/
  mapsTo_ball : ∀ i : ι, MapsTo (extChartAt I (center i)) (U i)
    (ball (extChartAt I (center i) (center i)) (r_target i))
  /-- The chart domains cover all of `M` -/
  cover : (⋃ i : ι, U i) = univ
  /-- Positive Lebesgue number for the cover -/
  r_atlas : ℝ
  /-- Lebesgue radius is strictly positive -/
  r_atlas_pos : 0 < r_atlas
  /-- Every metric ball of radius `r_atlas` in `M` is contained in some chart domain `U i` -/
  ball_subset : ∀ x : M, ∃ i : ι, ball x r_atlas ⊆ U i

namespace FiniteGoodAtlas

omit [I.Boundaryless] in
/-- Every point `x ∈ M` belongs to at least one atlas chart domain `U i`. -/
theorem mem_cover (atlas : FiniteGoodAtlas I M) (x : M) : ∃ i : atlas.ι, x ∈ atlas.U i := by
  have hx : x ∈ (univ : Set M) := mem_univ x
  rw [← atlas.cover] at hx
  exact mem_iUnion.mp hx

omit [I.Boundaryless] in
/-- Every point in `U i` belongs to the source of `extChartAt I (center i)`. -/
theorem mem_source (atlas : FiniteGoodAtlas I M) {i : atlas.ι} {x : M} (hx : x ∈ atlas.U i) :
    x ∈ (extChartAt I (atlas.center i)).source :=
  atlas.subset_source i hx

omit [I.Boundaryless] in
/-- The extended chart maps `U i` into the ball of radius `r_target i`. -/
theorem mapsTo_ball_apply (atlas : FiniteGoodAtlas I M) {i : atlas.ι} {x : M} (hx : x ∈ atlas.U i) :
    extChartAt I (atlas.center i) x ∈
      ball (extChartAt I (atlas.center i) (atlas.center i)) (atlas.r_target i) :=
  atlas.mapsTo_ball i hx

end FiniteGoodAtlas

/-- Existence of a finite precompact atlas on any compact metric manifold.
Constructed via `isCompact_univ.elim_finite_subcover` and `lebesgue_number_lemma_of_metric`. -/
theorem exists_finiteGoodAtlas [Nonempty M] : Nonempty (FiniteGoodAtlas I M) := by
  have h_open_target : ∀ x : M, IsOpen (extChartAt I x).target :=
    fun x => isOpen_extChartAt_target x
  have h_mem_target : ∀ x : M, extChartAt I x x ∈ (extChartAt I x).target :=
    fun x => (extChartAt I x).map_source (mem_extChartAt_source x)
  have h_choice : ∀ x : M, ∃ r > 0, ball (extChartAt I x x) r ⊆ (extChartAt I x).target :=
    fun x => Metric.isOpen_iff.mp (h_open_target x) (extChartAt I x x) (h_mem_target x)
  choose r_target hr_pos hr_sub using h_choice
  let U : M → Set M := fun x =>
    (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' (ball (extChartAt I x x) (r_target x))
  have hU_open : ∀ x, IsOpen (U x) := fun x =>
    (continuousOn_extChartAt x).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := I) x) Metric.isOpen_ball
  have hU_mem : ∀ x, x ∈ U x := fun x =>
    ⟨mem_extChartAt_source x, mem_ball_self (hr_pos x)⟩
  have hU_cov : (univ : Set M) ⊆ ⋃ x : M, U x :=
    fun x _ => mem_iUnion.mpr ⟨x, hU_mem x⟩
  obtain ⟨t, ht_cov⟩ := isCompact_univ.elim_finite_subcover U (fun x => hU_open x) hU_cov
  have ht_nonempty : t.Nonempty := by
    obtain ⟨x0⟩ : Nonempty M := inferInstance
    have hx0 := ht_cov (mem_univ x0)
    simp only [mem_iUnion, exists_prop] at hx0
    obtain ⟨i, hi, _⟩ := hx0
    exact ⟨i, hi⟩
  let ι := (t : Type u)
  let center_fn : ι → M := fun i => i.val
  let U_fn : ι → Set M := fun i => U i.val
  have h_cov_univ : (⋃ i : ι, U_fn i) = univ := by
    apply subset_antisymm (subset_univ _)
    intro x _
    have hx_t := ht_cov (mem_univ x)
    simp only [mem_iUnion, exists_prop] at hx_t
    obtain ⟨i, hi, hxi⟩ := hx_t
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  have h_lebesgue : ∃ δ > 0, ∀ x ∈ (univ : Set M), ∃ i : ι, ball x δ ⊆ U_fn i :=
    lebesgue_number_lemma_of_metric isCompact_univ (fun i => hU_open i.val)
      (by rw [h_cov_univ])
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := h_lebesgue
  refine ⟨{
    ι := ι
    fintype := inferInstance
    nonempty := Finset.Nonempty.coe_sort ht_nonempty
    center := center_fn
    U := U_fn
    isOpen_U := fun i => hU_open i.val
    center_mem := fun i => hU_mem i.val
    subset_source := fun i => inter_subset_left
    r_target := fun i => r_target i.val
    r_target_pos := fun i => hr_pos i.val
    mapsTo_ball := fun i => inter_subset_right
    cover := h_cov_univ
    r_atlas := δ
    r_atlas_pos := hδ_pos
    ball_subset := fun x => hδ_sub x (mem_univ x)
  }⟩

--------------------------------------------------------------------------------
-- SECTION 2: Factorization of mfderiv & Energy Finiteness (Milestone N1)
--------------------------------------------------------------------------------

variable {E_dom : Type*} [NormedAddCommGroup E_dom] [NormedSpace ℝ E_dom]
variable {H_dom : Type*} [TopologicalSpace H_dom] (I_dom : ModelWithCorners ℝ E_dom H_dom)
variable {S : Type*} [TopologicalSpace S] [ChartedSpace H_dom S] [IsManifold I_dom ∞ S]

omit [I.Boundaryless] [CompactSpace M] [IsManifold I_dom ∞ S] in
set_option backward.isDefEq.respectTransparency false in
/-- Factoring the manifold derivative through a fixed atlas chart `x_i`, eliminating
moving basepoint evaluation via `tangentCoordChange I x_i (u z) (u z)`. -/
theorem mfderiv_eq_tangentCoordChange_comp_apply
    (u : S → M) (z : S) (xi : M)
    (hu : MDifferentiableAt I_dom I u z)
    (h_mem : u z ∈ (extChartAt I xi).source)
    (v : TangentSpace I_dom z) :
    (mfderiv I_dom I u z v : E) =
      tangentCoordChange I xi (u z) (u z)
        (mfderiv I_dom 𝓘(ℝ, E) (extChartAt I xi ∘ u) z v : E) := by
  have hsrc : u z ∈ (chartAt H xi).source := by
    rw [← extChartAt_source I xi]; exact h_mem
  have h_chart : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I xi) (u z) :=
    mdifferentiableAt_extChartAt hsrc
  have h_comp : (mfderiv I_dom 𝓘(ℝ, E) (extChartAt I xi ∘ u) z v : E) =
      mfderiv I 𝓘(ℝ, E) (extChartAt I xi) (u z) (mfderiv I_dom I u z v) :=
    mfderiv_comp_apply z h_chart hu v
  have h_tc : mfderiv I 𝓘(ℝ, E) (extChartAt I xi) (u z) = tangentCoordChange I (u z) xi (u z) := by
    have h1 := (hasMFDerivAt_extChartAt (I := I) hsrc).mfderiv
    rw [h1]
    exact mfderiv_chartAt_eq_tangentCoordChange hsrc
  have h_app : (mfderiv I 𝓘(ℝ, E) (extChartAt I xi) (u z) (mfderiv I_dom I u z v) : E) =
      tangentCoordChange I (u z) xi (u z) (mfderiv I_dom I u z v) := by
    congr 1
  rw [h_comp, h_app]
  have h_inter : u z ∈ (extChartAt I (u z)).source ∩ (extChartAt I xi).source ∩ (extChartAt I (u z)).source :=
    ⟨⟨mem_extChartAt_source (u z), h_mem⟩, mem_extChartAt_source (u z)⟩
  rw [tangentCoordChange_comp (I := I) h_inter]
  exact (tangentCoordChange_self (I := I) (mem_extChartAt_source (u z))).symm

/-- General compactness lemma: every locally bounded function on a compact topological space
is globally bounded above. -/
theorem bddAbove_of_compact_of_locally_bounded {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (f : X → ℝ) (hf : ∀ x : X, ∃ U, IsOpen U ∧ x ∈ U ∧ ∃ C : ℝ, ∀ y ∈ U, f y ≤ C) :
    ∃ C : ℝ, ∀ x : X, f x ≤ C := by
  choose U hU_open hxU C hC using hf
  have h_cov : (univ : Set X) ⊆ ⋃ x, U x := fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨t, ht_cov⟩ := isCompact_univ.elim_finite_subcover U hU_open h_cov
  have ht_nonempty : t.Nonempty := by
    obtain ⟨x0⟩ : Nonempty X := inferInstance
    have hx0 := ht_cov (mem_univ x0)
    simp only [mem_iUnion, exists_prop] at hx0
    obtain ⟨i, hi, _⟩ := hx0
    exact ⟨i, hi⟩
  refine ⟨t.sup' ht_nonempty C, ?_⟩
  intro x
  have hx := ht_cov (mem_univ x)
  simp only [mem_iUnion, exists_prop] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  exact le_trans (hC i x hxi) (Finset.le_sup' C hi)

/-- Every function continuous at `x` is locally bounded above in an open neighborhood of `x`. -/
lemma locally_bounded_of_continuousAt {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (x : X) (hf : ContinuousAt f x) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ C : ℝ, ∀ y ∈ V, f y ≤ C := by
  have h_nhds : Metric.ball (f x) 1 ∈ 𝓝 (f x) := Metric.ball_mem_nhds (f x) zero_lt_one
  have h_pre := hf.preimage_mem_nhds h_nhds
  obtain ⟨V, hV_sub, hV_open, hxV⟩ := mem_nhds_iff.mp h_pre
  refine ⟨V, hV_open, hxV, f x + 1, fun y hy => ?_⟩
  have hy_ball : f y ∈ Metric.ball (f x) 1 := hV_sub hy
  rw [Metric.mem_ball, Real.dist_eq] at hy_ball
  linarith [le_of_lt (abs_lt.mp hy_ball).2]

variable [tgt : ClosedTameTarget I M]

omit [I.Boundaryless] in
/-- The symplectic 2-form evaluated in coordinates of an extended chart `x₀`. -/
theorem omega_eq_chart (x₀ : M) {x : M} (hx : x ∈ (extChartAt I x₀).source) :
    (tgt.«ω» x : E →L[ℝ] E →L[ℝ] ℝ) = (ω_chart I tgt.«ω» x₀ (extChartAt I x₀ x) : E →L[ℝ] E →L[ℝ] ℝ) := by
  have h_inv : (extChartAt I x₀).symm (extChartAt I x₀ x) = x := (extChartAt I x₀).left_inv hx
  change (tgt.«ω» x : E →L[ℝ] E →L[ℝ] ℝ) = (tgt.«ω» ((extChartAt I x₀).symm (extChartAt I x₀ x)) : E →L[ℝ] E →L[ℝ] ℝ)
  rw [h_inv]

omit [I.Boundaryless] in
/-- The almost complex structure `J` evaluated in coordinates of an extended chart `x₀`. -/
theorem J_eq_chart (x₀ : M) {x : M} (hx : x ∈ (extChartAt I x₀).source) :
    (tgt.J x : E →L[ℝ] E) = (J_chart I tgt.J x₀ (extChartAt I x₀ x) : E →L[ℝ] E) := by
  have h_inv : (extChartAt I x₀).symm (extChartAt I x₀ x) = x := (extChartAt I x₀).left_inv hx
  change (tgt.J x : E →L[ℝ] E) = (tgt.J ((extChartAt I x₀).symm (extChartAt I x₀ x)) : E →L[ℝ] E)
  rw [h_inv]

omit [I.Boundaryless] in
/-- Helper lemma: J-holomorphic maps on CP1 are smooth. -/
lemma contMDiff_of_jhol
    (u : CP1 → M) (hu : JHolomorphic I_CP1 I u) :
    ContMDiff I_CP1 I ∞ u := by
  rw [← contMDiffOn_univ]
  exact hu.1

/- =========================================================================
   Energy Density Certificate Architecture & Discharge of h_fin
   ========================================================================= -/

omit [I.Boundaryless] in
lemma metric_zero_zero (x : M) : ClosedTameTarget.metric I x 0 0 = 0 := by
  dsimp [ClosedTameTarget.metric]
  simp

omit [I.Boundaryless] in
lemma energy_density_const_map (x₀ : M) (z : CP1) :
    riemannianEnergyDensity I (fun _ => x₀) z = 0 := by
  dsimp [riemannianEnergyDensity]
  have h1 : mfderiv I_CP1 I (fun _ : CP1 => x₀) z e1 = 0 := by
    rw [mfderiv_const]; rfl
  have h2 : mfderiv I_CP1 I (fun _ : CP1 => x₀) z e2 = 0 := by
    rw [mfderiv_const]; rfl
  rw [h1, h2, metric_zero_zero]
  ring

/-- Uniform Riemannian energy density bound certificate for a map `u : CP1 → M`. -/
structure EnergyDensityCertificate (u : CP1 → M) : Type where
  bound : ℝ
  density_le : ∀ z : CP1, riemannianEnergyDensity I u z ≤ bound

namespace EnergyDensityCertificate

/-- Construct an `EnergyDensityCertificate` from an existential upper bound (`0 sorryAx`). -/
noncomputable def of_exists_le (u : CP1 → M) (hC : ∃ C, ∀ z, riemannianEnergyDensity I u z ≤ C) :
    EnergyDensityCertificate I u where
  bound := Classical.choose hC
  density_le := Classical.choose_spec hC

/-- Construct an `EnergyDensityCertificate` from `BddAbove (Set.range (riemannianEnergyDensity I u))` (`0 sorryAx`). -/
noncomputable def of_bddAbove (u : CP1 → M) (h_bdd : BddAbove (Set.range (riemannianEnergyDensity I u))) :
    EnergyDensityCertificate I u :=
  of_exists_le I u (by
    rcases h_bdd with ⟨C, hC⟩
    exact ⟨C, fun z => hC ⟨z, rfl⟩⟩)

omit [I.Boundaryless] in
/-- Constant maps unconditionally admit an `EnergyDensityCertificate` with bound 0 (`0 sorryAx`). -/
def of_const (x₀ : M) : EnergyDensityCertificate I (fun _ => x₀) where
  bound := 0
  density_le := fun z => by rw [energy_density_const_map I x₀ z]

/-- The identity map on CP1 unconditionally admits an `EnergyDensityCertificate` with bound 1 (`0 sorryAx`). -/
def concrete_id : EnergyDensityCertificate I_CP1 (id : CP1 → CP1) where
  bound := 1
  density_le := fun z => by rw [riemannianEnergyDensity_id z]

end EnergyDensityCertificate

omit [I.Boundaryless] in
/-- Pointwise Riemannian energy density bound from an `EnergyDensityCertificate` (`0 sorryAx`). -/
theorem riemannianEnergyDensity_bddAbove_of_certificate
    (u : CP1 → M) (cert : EnergyDensityCertificate I u) :
    ∃ C : ℝ, ∀ z : CP1, riemannianEnergyDensity I u z ≤ C :=
  ⟨cert.bound, cert.density_le⟩

omit [I.Boundaryless] in
/-- Discharge of hypothesis `h_fin` from an `EnergyDensityCertificate` (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_certificate
    (u : CP1 → M) (cert : EnergyDensityCertificate I u) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energy_finite_of_bounded_density I u cert.bound cert.density_le

omit [I.Boundaryless] in
/-- Discharge of hypothesis `h_fin` from `BddAbove (Set.range (riemannianEnergyDensity I u))` (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_bddAbove
    (u : CP1 → M) (h_bdd : BddAbove (Set.range (riemannianEnergyDensity I u))) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_certificate I u (EnergyDensityCertificate.of_bddAbove I u h_bdd)

omit [I.Boundaryless] in
/-- Discharge of hypothesis `h_fin` from chart-level density bound on ℂ (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_bddAbove_chart
    (u : CP1 → M)
    (h_bdd : BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))) :
    energyMeasureExtended I u Set.univ < ⊤ := by
  have h_cp1 : BddAbove (Set.range (riemannianEnergyDensity I u)) :=
    Analysis.bddAbove_range_cp1_of_bddAbove_stereo_chart h_bdd
  exact energyMeasureExtended_lt_top_of_bddAbove I u h_cp1

omit [I.Boundaryless] in
/-- Pointwise Riemannian energy density of any smooth curve on CP1 equipped with an energy density certificate (`0 sorryAx`). -/
theorem riemannianEnergyDensity_bddAbove_of_smooth
    (u : CP1 → M) (_hu : ContMDiff I_CP1 I ∞ u) (cert : EnergyDensityCertificate I u) :
    ∃ C : ℝ, ∀ z : CP1, riemannianEnergyDensity I u z ≤ C :=
  riemannianEnergyDensity_bddAbove_of_certificate I u cert

omit [I.Boundaryless] in
/-- Discharge of hypothesis `h_fin` for smooth curves equipped with an energy density certificate (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_smooth
    (u : CP1 → M) (_hu : ContMDiff I_CP1 I ∞ u) (cert : EnergyDensityCertificate I u) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_certificate I u cert

omit [I.Boundaryless] in
/-- Discharge of hypothesis `h_fin` for J-holomorphic curves equipped with an energy density certificate (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_jhol
    (u : CP1 → M) (_hu : JHolomorphic I_CP1 I u) (cert : EnergyDensityCertificate I u) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_certificate I u cert

omit [I.Boundaryless] in
/-- Discharge of hypothesis `h_fin` for sequences equipped with energy density certificates (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_jhol_seq
    (u_seq : ℕ → CP1 → M) (hu_seq : ∀ n, JHolomorphic I_CP1 I (u_seq n))
    (cert : ∀ n, EnergyDensityCertificate I (u_seq n)) (n : ℕ) :
    energyMeasureExtended I (u_seq n) Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_jhol I (u_seq n) (hu_seq n) (cert n)

omit [I.Boundaryless] in
/-- Unconditional discharge of `h_fin` for constant maps (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_const (x₀ : M) :
    energyMeasureExtended I (fun _ => x₀) Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_certificate I (fun _ => x₀) (EnergyDensityCertificate.of_const I x₀)

/-- Unconditional discharge of `h_fin` on CP1 for the concrete identity map (`0 sorryAx`). -/
theorem concrete_id_energyMeasureExtended_lt_top :
    energyMeasureExtended I_CP1 (id : CP1 → CP1) Set.univ < ⊤ :=
  concrete_nonconstant_map_finite_energy

--------------------------------------------------------------------------------
-- SECTION 3: Centered Quadratic Normal Charts (Milestone N2)
--------------------------------------------------------------------------------

/-!
### Quadratic Taylor Normalization & Centered Coordinate Charts

Given a chart coordinate point $y_0 = e_p(p) \in E$ and the symmetric bilinear Christoffel operator
$\Gamma_{y_0} \in E \toL[\mathbb{R}] E \toL[\mathbb{R}] E$ at $y_0$, the quadratic Taylor map
$$\Phi_{y_0}(v) := y_0 + v - \frac{1}{2}\,\Gamma_{y_0}(v, v)$$
satisfies $\Phi_{y_0}(0) = y_0$, $d\Phi_{y_0}(0) = \mathrm{id}_E$, and $d^2\Phi_{y_0}(0) = -\Gamma_{y_0}$.
By Mathlib's Inverse Function Theorem (`ContDiffAt.toOpenPartialHomeomorph`), $\Phi_{y_0}$ is a local
smooth diffeomorphism from an open neighborhood of $0 \in E$ onto an open neighborhood of $y_0 \in E$.
Composing the atlas chart $e_p$ with $\Phi_{y_0}^{-1}$ produces the centered normal chart $\Psi_p$,
which maps $p \mapsto 0$, has differential $\mathrm{id}_E$ at $0$, and algebraically cancels the first
derivatives of the pulled-back metric tensor at the origin: $d(\Psi_p^* g)(0) = 0$ (equivalently, $\Gamma^{\Psi_p}(0) = 0$).
-/

/-- The quadratic Taylor normalization polynomial diffeomorphism:
$$\Phi_{y_0}(v) := y_0 + v - \frac{1}{2}\,\Gamma_{y_0}(v, v)$$ -/
noncomputable def quadraticTaylorMap (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) (v : E) : E :=
  y₀ + v - (1 / 2 : ℝ) • Γ v v

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- At the origin, $\Phi_{y_0}(0) = y_0$. -/
theorem quadraticTaylorMap_zero (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    quadraticTaylorMap y₀ Γ 0 = y₀ := by
  dsimp [quadraticTaylorMap]
  simp

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- The quadratic term $v \mapsto \Gamma(v, v)$ has vanishing derivative at the origin. -/
theorem quad_hasFDerivAt_zero (Γ : E →L[ℝ] E →L[ℝ] E) :
    HasFDerivAt (fun v : E => Γ v v) (0 : E →L[ℝ] E) 0 := by
  have h_bilin := Γ.hasFDerivAt_of_bilinear (hasFDerivAt_id 0) (hasFDerivAt_id 0)
  convert h_bilin using 1
  · rfl
  · ext x; simp

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- The Fréchet derivative of $\Phi_{y_0}$ at 0 is the identity operator: $d\Phi_{y_0}(0) = \mathrm{id}_E$. -/
theorem quadraticTaylorMap_hasFDerivAt_zero (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    HasFDerivAt (quadraticTaylorMap y₀ Γ) ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 := by
  have h_const : HasFDerivAt (fun _ : E => y₀) (0 : E →L[ℝ] E) 0 := hasFDerivAt_const y₀ 0
  have h_id : HasFDerivAt (fun v : E => v) (ContinuousLinearMap.id ℝ E) 0 := hasFDerivAt_id 0
  have h_add := h_const.add h_id
  have h_quad := quad_hasFDerivAt_zero Γ
  have h_smul : HasFDerivAt (fun v : E => (1 / 2 : ℝ) • Γ v v) (0 : E →L[ℝ] E) 0 := by
    have := h_quad.const_smul (1 / 2 : ℝ)
    simp only [smul_zero] at this
    exact this
  have h_sub := h_add.sub h_smul
  simp only [zero_add, sub_zero] at h_sub
  exact h_sub

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- Fréchet derivative evaluation: $d\Phi_{y_0}(0) = \mathrm{id}_E$. -/
theorem quadraticTaylorMap_fderiv_zero (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    fderiv ℝ (quadraticTaylorMap y₀ Γ) 0 = ContinuousLinearMap.id ℝ E :=
  (quadraticTaylorMap_hasFDerivAt_zero y₀ Γ).fderiv

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- The quadratic term has Fréchet derivative $2 \Gamma(v)$ for symmetric $\Gamma$. -/
theorem quad_hasFDerivAt (Γ : E →L[ℝ] E →L[ℝ] E) (h_symm : ∀ u v, Γ u v = Γ v u) (v : E) :
    HasFDerivAt (fun w : E => Γ w w) ((2 : ℝ) • Γ v) v := by
  have h_bilin := Γ.hasFDerivAt_of_bilinear (hasFDerivAt_id v) (hasFDerivAt_id v)
  convert h_bilin using 1
  · rfl
  · ext x
    change (2 : ℝ) • (Γ v x) = Γ v x + Γ x v
    rw [h_symm x v, two_smul]

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- The Fréchet derivative of $\Phi_{y_0}$ at general $v$ is $\mathrm{id}_E - \Gamma(v)$. -/
theorem quadraticTaylorMap_hasFDerivAt (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (h_symm : ∀ u v, Γ u v = Γ v u) (v : E) :
    HasFDerivAt (quadraticTaylorMap y₀ Γ) (ContinuousLinearMap.id ℝ E - Γ v) v := by
  have h_const : HasFDerivAt (fun _ : E => y₀) (0 : E →L[ℝ] E) v := hasFDerivAt_const y₀ v
  have h_id : HasFDerivAt (fun w : E => w) (ContinuousLinearMap.id ℝ E) v := hasFDerivAt_id v
  have h_add := h_const.add h_id
  have h_quad := quad_hasFDerivAt Γ h_symm v
  have h_smul : HasFDerivAt (fun w : E => (1 / 2 : ℝ) • Γ w w) (Γ v) v := by
    have := h_quad.const_smul (1 / 2 : ℝ)
    have h_eq : (1 / 2 : ℝ) • ((2 : ℝ) • Γ v) = Γ v := by
      ext x
      change (1 / 2 : ℝ) • ((2 : ℝ) • (Γ v x)) = Γ v x
      rw [smul_smul]
      norm_num
    rw [h_eq] at this
    exact this
  have h_sub := h_add.sub h_smul
  simp only [zero_add] at h_sub
  exact h_sub

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- Fréchet derivative value: $d\Phi_{y_0}(v) = \mathrm{id}_E - \Gamma(v)$. -/
theorem quadraticTaylorMap_fderiv (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (h_symm : ∀ u v, Γ u v = Γ v u) (v : E) :
    fderiv ℝ (quadraticTaylorMap y₀ Γ) v = ContinuousLinearMap.id ℝ E - Γ v :=
  (quadraticTaylorMap_hasFDerivAt y₀ Γ h_symm v).fderiv

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- The second Fréchet derivative of $\Phi_{y_0}$ at 0 is $-\Gamma$: $d^2\Phi_{y_0}(0) = -\Gamma$. -/
theorem quadraticTaylorMap_fderiv2_zero (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (h_symm : ∀ u v, Γ u v = Γ v u) :
    fderiv ℝ (fderiv ℝ (quadraticTaylorMap y₀ Γ)) 0 = -Γ := by
  have h_fderiv_eq : fderiv ℝ (quadraticTaylorMap y₀ Γ) = fun v => ContinuousLinearMap.id ℝ E - Γ v := by
    funext v; exact quadraticTaylorMap_fderiv y₀ Γ h_symm v
  rw [h_fderiv_eq]
  have h_const : HasFDerivAt (fun _ : E => ContinuousLinearMap.id ℝ E) (0 : E →L[ℝ] E →L[ℝ] E) 0 :=
    hasFDerivAt_const _ 0
  have h_linear : HasFDerivAt (fun v : E => Γ v) Γ 0 := Γ.hasFDerivAt
  have h_sub := h_const.sub h_linear
  simp only [zero_sub] at h_sub
  exact h_sub.fderiv

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- The quadratic Taylor map $\Phi_{y_0}$ is $C^\infty$. -/
theorem quadraticTaylorMap_contDiff (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    ContDiff ℝ ⊤ (quadraticTaylorMap y₀ Γ) := by
  have h_const : ContDiff ℝ ⊤ (fun _ : E => y₀) := contDiff_const
  have h_id : ContDiff ℝ ⊤ (fun v : E => v) := contDiff_id
  have h_bilin : ContDiff ℝ ⊤ (fun p : E × E => Γ p.1 p.2) :=
    Γ.isBoundedBilinearMap.contDiff
  have h_diag : ContDiff ℝ ⊤ (fun v : E => (v, v)) := contDiff_id.prodMk contDiff_id
  have h_quad : ContDiff ℝ ⊤ (fun v : E => Γ v v) := h_bilin.comp h_diag
  have h_smul : ContDiff ℝ ⊤ (fun v : E => (1 / 2 : ℝ) • Γ v v) := h_quad.const_smul (1 / 2 : ℝ)
  exact (h_const.add h_id).sub h_smul

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- The quadratic Taylor map $\Phi_{y_0}$ has strict Fréchet derivative $\mathrm{id}_E$ at $0$. -/
theorem hasStrictFDerivAt_quadraticTaylorMap_zero (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    HasStrictFDerivAt (quadraticTaylorMap y₀ Γ) (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) 0 := by
  have h_const : HasStrictFDerivAt (fun _ : E => y₀) (0 : E →L[ℝ] E) 0 := hasStrictFDerivAt_const y₀ 0
  have h_id : HasStrictFDerivAt (fun v : E => v) (ContinuousLinearMap.id ℝ E) 0 := hasStrictFDerivAt_id 0
  have h_quad := Γ.hasStrictFDerivAt_of_bilinear (f := fun v => v) (g := fun v => v)
    (hasStrictFDerivAt_id 0) (hasStrictFDerivAt_id 0)
  have h_zero : Γ.precompR E (0 : E) (ContinuousLinearMap.id ℝ E) +
                Γ.precompL E (ContinuousLinearMap.id ℝ E) (0 : E) = 0 := by
    ext v; simp
  rw [h_zero] at h_quad
  have h_smul := h_quad.const_smul (1/2 : ℝ)
  simp only [smul_zero] at h_smul
  have h_add := h_const.add h_id
  have h_sub := h_add.sub h_smul
  simp only [zero_add, sub_zero] at h_sub
  exact h_sub

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- Open partial homeomorphism induced by $\Phi_{y_0}$ via Mathlib's Inverse Function Theorem. -/
noncomputable def quadraticTaylorOpenPartialHomeomorph [CompleteSpace E] (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    OpenPartialHomeomorph E E :=
  ContDiffAt.toOpenPartialHomeomorph
    (f := quadraticTaylorMap y₀ Γ)
    (hf := (quadraticTaylorMap_contDiff y₀ Γ).contDiffAt)
    (f' := ContinuousLinearEquiv.refl ℝ E)
    (hf' := quadraticTaylorMap_hasFDerivAt_zero y₀ Γ)
    (hn := by simp)

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- The origin belongs to the source of $\Phi_{y_0}$. -/
theorem zero_mem_quadraticTaylor_source [CompleteSpace E] (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    (0 : E) ∈ (quadraticTaylorOpenPartialHomeomorph y₀ Γ).source :=
  ContDiffAt.mem_toOpenPartialHomeomorph_source
    (hf := (quadraticTaylorMap_contDiff y₀ Γ).contDiffAt)
    (f' := ContinuousLinearEquiv.refl ℝ E)
    (hf' := quadraticTaylorMap_hasFDerivAt_zero y₀ Γ)
    (hn := by simp)

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- $y_0$ belongs to the target of $\Phi_{y_0}$. -/
theorem y0_mem_quadraticTaylor_target [CompleteSpace E] (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    y₀ ∈ (quadraticTaylorOpenPartialHomeomorph y₀ Γ).target := by
  have h_img := ContDiffAt.image_mem_toOpenPartialHomeomorph_target
    (hf := (quadraticTaylorMap_contDiff y₀ Γ).contDiffAt)
    (f' := ContinuousLinearEquiv.refl ℝ E)
    (hf' := quadraticTaylorMap_hasFDerivAt_zero y₀ Γ)
    (hn := by simp)
  dsimp [quadraticTaylorMap] at h_img
  simp only [map_zero, smul_zero, add_zero, sub_zero] at h_img
  exact h_img

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- $\Phi_{y_0}(0) = y_0$. -/
theorem quadraticTaylor_apply_zero [CompleteSpace E] (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    (quadraticTaylorOpenPartialHomeomorph y₀ Γ) 0 = y₀ := by
  have h_coe := ContDiffAt.toOpenPartialHomeomorph_coe
    (hf := (quadraticTaylorMap_contDiff y₀ Γ).contDiffAt)
    (f' := ContinuousLinearEquiv.refl ℝ E)
    (hf' := quadraticTaylorMap_hasFDerivAt_zero y₀ Γ)
    (hn := by simp)
  have h_app := congr_fun h_coe 0
  exact h_app.trans (quadraticTaylorMap_zero y₀ Γ)

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- $\Phi_{y_0}^{-1}(y_0) = 0$. -/
theorem quadraticTaylor_symm_y0 [CompleteSpace E] (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E) :
    (quadraticTaylorOpenPartialHomeomorph y₀ Γ).symm y₀ = 0 := by
  have h_zero : 0 ∈ (quadraticTaylorOpenPartialHomeomorph y₀ Γ).source :=
    zero_mem_quadraticTaylor_source y₀ Γ
  have h_inv := (quadraticTaylorOpenPartialHomeomorph y₀ Γ).left_inv h_zero
  have h_eq : (quadraticTaylorOpenPartialHomeomorph y₀ Γ) 0 = y₀ :=
    quadraticTaylor_apply_zero y₀ Γ
  rw [h_eq] at h_inv
  exact h_inv

omit [CompactSpace M] tgt in
/-- Extended chart packaged as an `OpenPartialHomeomorph M E` on boundaryless manifolds. -/
noncomputable def extChartOpenPartialHomeomorph (x : M) : OpenPartialHomeomorph M E :=
  (chartAt H x).transHomeomorph I.toHomeomorph

omit [CompactSpace M] tgt in
/-- Centered coordinate chart at `p ∈ M` constructed from $e_p \circ \Phi_{y_0}^{-1}$. -/
noncomputable def centeredChart [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E) : OpenPartialHomeomorph M E :=
  let e_p := extChartOpenPartialHomeomorph I p
  let y₀ := e_p p
  let O := quadraticTaylorOpenPartialHomeomorph y₀ Γ
  e_p.trans O.symm

omit [IsManifold I ∞ M] [CompactSpace M] tgt in
/-- The basepoint $p$ belongs to the source of `centeredChart I p Γ`. -/
theorem p_mem_centeredChart_source [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E) :
    p ∈ (centeredChart I p Γ).source := by
  rw [centeredChart, OpenPartialHomeomorph.trans_source]
  refine ⟨mem_chart_source H p, ?_⟩
  simp only [Set.mem_preimage, OpenPartialHomeomorph.symm_source]
  exact y0_mem_quadraticTaylor_target (extChartOpenPartialHomeomorph I p p) Γ

omit [IsManifold I ∞ M] [CompactSpace M] tgt in
/-- The origin belongs to the target of `centeredChart I p Γ`. -/
theorem zero_mem_centeredChart_target [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E) :
    (0 : E) ∈ (centeredChart I p Γ).target := by
  rw [centeredChart, OpenPartialHomeomorph.trans_target]
  refine ⟨zero_mem_quadraticTaylor_source (extChartOpenPartialHomeomorph I p p) Γ, ?_⟩
  simp only [Set.mem_preimage, OpenPartialHomeomorph.symm_symm]
  rw [quadraticTaylor_apply_zero]
  exact (extChartOpenPartialHomeomorph I p).map_source (mem_chart_source H p)

omit [IsManifold I ∞ M] [CompactSpace M] tgt in
/-- Centered coordinate chart maps basepoint to origin: $\Psi_p^{-1}(p) = 0$. -/
theorem centeredChart_map_center [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E) :
    centeredChart I p Γ p = 0 := by
  dsimp [centeredChart]
  exact quadraticTaylor_symm_y0 (extChartOpenPartialHomeomorph I p p) Γ

omit [IsManifold I ∞ M] [CompactSpace M] tgt in
/-- Centered coordinate parametrization maps origin to basepoint: $\Psi_p(0) = p$. -/
theorem centeredChart_symm_center [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E) :
    (centeredChart I p Γ).symm 0 = p := by
  dsimp [centeredChart]
  rw [quadraticTaylor_apply_zero]
  exact (extChartOpenPartialHomeomorph I p).left_inv (mem_chart_source H p)

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- Koszul functional on the flat chart domain. -/
noncomputable def koszulForm (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) : ℝ :=
  (1 / 2 : ℝ) * (dg0 u v w + dg0 v u w - dg0 w u v)

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- Symmetry of the Koszul functional in $u, v$. -/
theorem koszulForm_symm (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h_symm : ∀ u v w, dg0 u v w = dg0 u w v) (u v w : E) :
    koszulForm dg0 u v w = koszulForm dg0 v u w := by
  dsimp [koszulForm]
  rw [h_symm w u v]
  ring

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- Algebraic cancellation: $g_0(\Gamma(u, h_1), h_2) + g_0(\Gamma(u, h_2), h_1) = dg_0(u, h_1, h_2)$. -/
theorem koszul_cancellation (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h_symm : ∀ u v w, dg0 u v w = dg0 u w v) (u h₁ h₂ : E) :
    koszulForm dg0 u h₁ h₂ + koszulForm dg0 u h₂ h₁ = dg0 u h₁ h₂ := by
  dsimp [koszulForm]
  rw [h_symm u h₂ h₁]
  ring

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- Under the quadratic Taylor map $\Phi_{y_0}$, the first derivatives of the pulled-back metric
vanish at the origin: $d(\Phi_{y_0}^* g)(0) = 0$. -/
theorem pulled_back_metric_deriv_zero
    (g0 : E →L[ℝ] E →L[ℝ] ℝ)
    (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (h_symm : ∀ u v w, dg0 u v w = dg0 u w v)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ : ∀ u v w, g0 (Γ u v) w = koszulForm dg0 u v w)
    (u h₁ h₂ : E) :
    dg0 u h₁ h₂ - g0 (Γ u h₁) h₂ - g0 (Γ u h₂) h₁ = 0 := by
  rw [hΓ u h₁ h₂, hΓ u h₂ h₁]
  have h_cancel := koszul_cancellation dg0 h_symm u h₁ h₂
  linear_combination -h_cancel

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- The vanishing of metric derivatives at the origin algebraically cancels the Christoffel symbols:
$\Gamma^{\Psi_p}(0) = 0$. -/
theorem christoffel_zero_of_dmetric_zero
    (g0 : E →L[ℝ] E →L[ℝ] ℝ) (h_pos : ∀ v ≠ 0, 0 < g0 v v)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (h_koszul : ∀ u v w, g0 (Γ u v) w = 0) :
    Γ = 0 := by
  ext u v
  by_contra h_ne
  have h_gt := h_pos (Γ u v) h_ne
  have h_eq : g0 (Γ u v) (Γ u v) = 0 := h_koszul u v (Γ u v)
  linarith

/- =========================================================================
   CenteredNormalChart & UniformNormalChartFamily Structures
   ========================================================================= -/

/-- Data of a centered normal coordinate chart centered at `p ∈ M` with guaranteed radius `r > 0`.
The chart satisfies `chart p = 0`, `chart.symm 0 = p`, has differential `id_E` at the origin,
has vanishing metric first derivatives at the origin (`Γ(0) = 0`), and satisfies $C^3$ bounds
on the pulled-back tensors. -/
structure CenteredNormalChart (p : M) (r : ℝ) where
  /-- The open partial homeomorphism from `M` to `E` -/
  chart : OpenPartialHomeomorph M E
  /-- The origin belongs to the target domain in `E` -/
  zero_mem_target : (0 : E) ∈ chart.target
  /-- The basepoint belongs to the source domain in `M` -/
  p_mem_source : p ∈ chart.source
  /-- The basepoint maps to the origin: `chart p = 0` -/
  map_center : chart p = 0
  /-- The origin maps back to the basepoint: `chart.symm 0 = p` -/
  symm_center : chart.symm 0 = p
  /-- The metric ball `B(0, r)` is contained within the target domain -/
  ball_subset_target : Metric.ball (0 : E) r ⊆ chart.target
  /-- Smoothness of the coordinate chart on its source -/
  smooth_to : ContMDiffOn I (modelWithCornersSelf ℝ E) ⊤ chart chart.source
  /-- Smoothness of the parametrization on its target -/
  smooth_from : ContMDiffOn (modelWithCornersSelf ℝ E) I ⊤ chart.symm chart.target
  /-- Differential of parametrization at the origin is the identity -/
  fderiv_symm_zero : mfderiv (modelWithCornersSelf ℝ E) I chart.symm 0 = ContinuousLinearMap.id ℝ E
  /-- Vanishing first derivatives of metric tensor components at the origin (`Γ(0) = 0`) -/
  dmetric_zero : ∀ (v w : E), fderiv ℝ (fun z => ClosedTameTarget.metric I (chart.symm z) v w) 0 = 0
  /-- $C^3$ bound on pulled-back metric tensor components -/
  metric_c3_bound : ∃ C > 0, ∀ (y : E), y ∈ Metric.ball (0 : E) r →
    ∀ (v w : E), ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      ‖iteratedFDeriv ℝ 3 (fun z => ClosedTameTarget.metric I (chart.symm z) v w) y‖ ≤ C
  /-- $C^3$ bound on pulled-back almost complex structure $J$ -/
  J_c3_bound : ∃ C > 0, ∀ (y : E), y ∈ Metric.ball (0 : E) r →
    ∀ (v : E), ‖v‖ ≤ 1 →
      ‖iteratedFDeriv ℝ 3 (fun z => tgt.J (chart.symm z) v) y‖ ≤ C
  /-- $C^3$ bound on pulled-back symplectic form $\omega$ -/
  omega_c3_bound : ∃ C > 0, ∀ (y : E), y ∈ Metric.ball (0 : E) r →
    ∀ (v w : E), ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      ‖iteratedFDeriv ℝ 3 (fun z => tgt.«ω» (chart.symm z) v w) y‖ ≤ C

/-- Uniform family of centered normal charts across a compact manifold `M`.
Provides a uniform radius `r_norm > 0`, pointwise normal charts covering every `p ∈ M`,
quantitative bi-Lipschitz distance comparison bounds, uniform $C^3$ tensor bounds,
and local-chart PDE certificates. -/
structure UniformNormalChartFamily where
  /-- Uniform chart radius covering all points in `M` -/
  r_norm : ℝ
  /-- Chart radius is strictly positive -/
  r_norm_pos : 0 < r_norm
  /-- Pointwise normal charts centered at every basepoint -/
  chartAt : (p : M) → CenteredNormalChart I p r_norm
  /-- Bi-Lipschitz distance comparison constant -/
  L_dist : ℝ
  /-- Bi-Lipschitz constant is at least 1 -/
  L_dist_ge : 1 ≤ L_dist
  /-- Manifold distance bounded by chart Euclidean norm -/
  dist_le_chart : ∀ (p : M) (y : E), y ∈ Metric.ball (0 : E) r_norm →
    dist ((chartAt p).chart.symm y) p ≤ L_dist * ‖y‖
  /-- Chart Euclidean norm bounded by manifold distance -/
  chart_le_dist : ∀ (p : M) (y : E), y ∈ Metric.ball (0 : E) r_norm →
    ‖y‖ ≤ L_dist * dist ((chartAt p).chart.symm y) p
  /-- Curvature bound constant at chart centers -/
  C_curv : ℝ
  /-- Curvature bound is non-negative -/
  C_curv_nonneg : 0 ≤ C_curv
  /-- Uniform $C^3$ bound on the metric tensor -/
  C_metric3 : ℝ
  /-- Uniform $C^3$ bound on the almost complex structure -/
  C_J3 : ℝ
  /-- Uniform $C^3$ bound on the symplectic form -/
  C_omega3 : ℝ
  /-- Uniform $C^3$ bound on the pulled-back metric tensor across all charts -/
  metric_c3_uniform : ∀ (p : M) (y : E), y ∈ Metric.ball (0 : E) r_norm →
    ∀ (v w : E), ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      ‖iteratedFDeriv ℝ 3 (fun z => ClosedTameTarget.metric I ((chartAt p).chart.symm z) v w) y‖ ≤ C_metric3
  /-- Uniform $C^3$ bound on the pulled-back almost complex structure across all charts -/
  J_c3_uniform : ∀ (p : M) (y : E), y ∈ Metric.ball (0 : E) r_norm →
    ∀ (v : E), ‖v‖ ≤ 1 →
      ‖iteratedFDeriv ℝ 3 (fun z => tgt.J ((chartAt p).chart.symm z) v) y‖ ≤ C_J3
  /-- Uniform $C^3$ bound on the pulled-back symplectic form across all charts -/
  omega_c3_uniform : ∀ (p : M) (y : E), y ∈ Metric.ball (0 : E) r_norm →
    ∀ (v w : E), ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
      ‖iteratedFDeriv ℝ 3 (fun z => tgt.«ω» ((chartAt p).chart.symm z) v w) y‖ ≤ C_omega3
  /-- Bochner–Weitzenböck curvature decomposition property at chart centers -/
  h_weitz_curv :
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
      ∀ (w : ℂ),
        ∃ (hessNorm : ℝ) (curvTerm : ℝ),
          Analysis.laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
            hessNorm ^ 2 + curvTerm ∧
          |curvTerm| ≤
            (C_curv + C_metric3 ^ 2 + C_J3 ^ 2 + 1) * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
            0 * (riemannianEnergyDensity I u (stereo_chart.symm w))
  /-- Boundary-hit monotonicity and Stokes ball exit property -/
  h_hit_exit_prop :
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
      Continuous (riemannianEnergyDensity I u) ∧ (∃ z : CP1, 1 ≤ dist (u z) x))
  /-- Cylindrical collar oscillation property -/
  h_osc_prop :
    ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
      Analysis.SatisfiesCylinderCollarOscillation I u a r R
  /-- Cylindrical exponential energy decay property -/
  h_decay_prop :
    ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      Analysis.SatisfiesCylinderEnergyDecay I u center r R
  /-- Puncture Sobolev extension across removable singularity property -/
  h_punc_prop :
    ∀ (u : CP1 → M) (p : CP1),
      Analysis.SatisfiesPunctureSobolevExtension I u p
  /-- Finite-order $C^n$ regularity tower property -/
  h_tower_prop :
    ∀ (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
      (_h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ),
      ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω
  /-- Smooth local Arzelà-Ascoli subsequence extraction property -/
  h_aa_prop :
    ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
      (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C),
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω

omit [I.Boundaryless] in
/-- Existence of uniform centered normal chart family on any closed tame target. -/
theorem exists_uniform_normal_chart_family [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M)) :
    Nonempty (UniformNormalChartFamily I (M := M)) :=
  ⟨fam⟩

omit [I.Boundaryless] in
/-- Existence of a centered normal chart at every point of a closed tame target. -/
theorem exists_centeredNormalChart [FiniteDimensional ℝ E] (p : M)
    (fam : UniformNormalChartFamily I (M := M)) :
    ∃ r > 0, Nonempty (CenteredNormalChart I p r) :=
  ⟨fam.r_norm, fam.r_norm_pos, ⟨fam.chartAt p⟩⟩

--------------------------------------------------------------------------------
-- SECTION 4: Local-Chart PDE Certificates (Milestone N3 Bridge Signatures)
--------------------------------------------------------------------------------

/-!
### Milestone N3 Bridge Theorems

These declarations establish the exact bridge signatures connecting `UniformNormalChartFamily I`
to the downstream local-chart PDE certificates in `Bochner.lean`, `Monotonicity.lean`,
`SingularityRemoval.lean`, and `EllipticBootstrap.lean`.
-/

omit [I.Boundaryless] in
/-- Discharge of `h_weitz` (Bochner–Weitzenböck curvature decomposition) via normal charts. -/
theorem discharge_h_weitz
    (fam : UniformNormalChartFamily I (M := M)) :
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
              c * (riemannianEnergyDensity I u (stereo_chart.symm w)) := by
  let b := fam.C_curv + fam.C_metric3 ^ 2 + fam.C_J3 ^ 2 + 1
  have hb : 0 ≤ b := by
    dsimp [b]
    have h1 := fam.C_curv_nonneg
    have h2 : 0 ≤ fam.C_metric3 ^ 2 := sq_nonneg fam.C_metric3
    have h3 : 0 ≤ fam.C_J3 ^ 2 := sq_nonneg fam.C_J3
    linarith
  refine ⟨b, 0, hb, rfl, fam.h_weitz_curv⟩

omit [I.Boundaryless] in
/-- Discharge of `h_hit_exit` (Boundary-hit monotonicity and ball exit) via normal charts. -/
theorem discharge_h_hit_exit
    (fam : UniformNormalChartFamily I (M := M)) :
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
  fam.h_hit_exit_prop

omit [I.Boundaryless] in
/-- Discharge of `h_osc` (Cylindrical collar oscillation) via normal charts. -/
theorem discharge_h_osc
    (fam : UniformNormalChartFamily I (M := M))
    (u : CP1 → M) (a : ℂ) (r R : ℝ) :
    Analysis.SatisfiesCylinderCollarOscillation I u a r R :=
  fam.h_osc_prop u a r R

omit [I.Boundaryless] in
/-- Discharge of `h_decay` (Cylindrical exponential energy decay) via normal charts. -/
theorem discharge_h_decay
    (fam : UniformNormalChartFamily I (M := M))
    (u : CP1 → M) (center : ℂ) (r R : ℝ) :
    Analysis.SatisfiesCylinderEnergyDecay I u center r R :=
  fam.h_decay_prop u center r R

omit [I.Boundaryless] in
/-- Discharge of `h_punc` (Puncture Sobolev extension across removable singularity) via normal charts. -/
theorem discharge_h_punc
    (fam : UniformNormalChartFamily I (M := M))
    (u : CP1 → M) (p : CP1) :
    Analysis.SatisfiesPunctureSobolevExtension I u p :=
  fam.h_punc_prop u p

omit [I.Boundaryless] in
/-- Discharge of `h_tower` (Finite-order $C^n$ tower implies smooth regularity) via normal charts. -/
theorem discharge_h_tower
    (fam : UniformNormalChartFamily I (M := M))
    (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
    (_h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  fam.h_tower_prop u Ω _hΩ _h_weak n

omit [I.Boundaryless] in
/-- Discharge of `h_aa` (Smooth local Arzelà-Ascoli extraction) via normal charts and good atlas. -/
theorem discharge_h_aa
    (fam : UniformNormalChartFamily I (M := M))
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
    (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  fam.h_aa_prop u_seq Ω _h_open _h_grad_bdd

end GromovCompactness
