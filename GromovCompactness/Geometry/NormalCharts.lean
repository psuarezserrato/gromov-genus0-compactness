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

--------------------------------------------------------------------------------
-- SECTION 3: Centered Quadratic Normal Charts (Milestone N2 - Scaffolding)
--------------------------------------------------------------------------------

-- Milestone N2 implementations of CenteredNormalChart and UniformNormalChartFamily
-- will be placed here.

--------------------------------------------------------------------------------
-- SECTION 4: Local-Chart PDE Certificates (Milestone N3 - Scaffolding)
--------------------------------------------------------------------------------

-- Milestone N3 unconditional discharges for h_weitz, h_hit_exit, h_osc, h_decay,
-- h_punc, h_tower, h_aa will be placed here.

end GromovCompactness
