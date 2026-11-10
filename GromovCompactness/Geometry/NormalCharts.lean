/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Milestones N1–N3 Architecture)
-/
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
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
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Topology.Algebra.Module.FiniteDimension
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
/-- Global continuity of `tgt.ω : M → E →L[ℝ] E →L[ℝ] ℝ` deduced from chartwise smoothness. -/
theorem continuous_omega_global : Continuous (fun x : M => id (α := E →L[ℝ] E →L[ℝ] ℝ) (tgt.«ω» x)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have h_cont_chart : ContinuousOn (ω_chart I tgt.«ω» x₀) (extChartAt I x₀).target :=
    (tgt.ω_smooth x₀).continuousOn
  have h_comp : ContinuousOn (fun x => ω_chart I tgt.«ω» x₀ (extChartAt I x₀ x)) (extChartAt I x₀).source :=
    h_cont_chart.comp (continuousOn_extChartAt x₀) (extChartAt I x₀).mapsTo
  have h_congr : ContinuousOn (fun x : M => id (α := E →L[ℝ] E →L[ℝ] ℝ) (tgt.«ω» x)) (extChartAt I x₀).source :=
    h_comp.congr (fun x hx => omega_eq_chart I x₀ hx)
  exact h_congr.continuousAt ((isOpen_extChartAt_source x₀).mem_nhds (mem_extChartAt_source x₀))

omit [I.Boundaryless] in
/-- Global continuity of `tgt.J : M → E →L[ℝ] E` deduced from chartwise smoothness. -/
theorem continuous_J_global : Continuous (fun x : M => id (α := E →L[ℝ] E) (tgt.J x)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have h_cont_chart : ContinuousOn (J_chart I tgt.J x₀) (extChartAt I x₀).target :=
    (tgt.J_smooth x₀).continuousOn
  have h_comp : ContinuousOn (fun x => J_chart I tgt.J x₀ (extChartAt I x₀ x)) (extChartAt I x₀).source :=
    h_cont_chart.comp (continuousOn_extChartAt x₀) (extChartAt I x₀).mapsTo
  have h_congr : ContinuousOn (fun x : M => id (α := E →L[ℝ] E) (tgt.J x)) (extChartAt I x₀).source :=
    h_comp.congr (fun x hx => J_eq_chart I x₀ hx)
  exact h_congr.continuousAt ((isOpen_extChartAt_source x₀).mem_nhds (mem_extChartAt_source x₀))

omit [I.Boundaryless] in
/-- Bundled continuous bilinear representation of `ClosedTameTarget.metric I x` at `x ∈ M`. -/
noncomputable def metricCLM (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  let J₀ : E →L[ℝ] E := tgt.J x
  let ω₀ : E →L[ℝ] E →L[ℝ] ℝ := tgt.«ω» x
  (1 / 2 : ℝ) • (ω₀.bilinearComp (.id ℝ E) J₀ + (ω₀.bilinearComp (.id ℝ E) J₀).flip)

omit [I.Boundaryless] in
@[simp]
theorem metricCLM_apply (x : M) (v w : E) :
    metricCLM I x v w = ClosedTameTarget.metric I x v w :=
  rfl

omit [I.Boundaryless] in
/-- Uniform positive-definiteness (coercivity) of `ClosedTameTarget.metric` across a compact
target `M` with finite-dimensional model space `E`: there exists `c_min > 0` such that
`c_min * ‖v‖^2 ≤ g_x(v, v)` for all `x ∈ M` and `v ∈ E`. -/
theorem exists_metric_coercive [FiniteDimensional ℝ E] :
    ∃ c_min : ℝ, 0 < c_min ∧ ∀ (x : M) (v : E),
      c_min * ‖v‖ ^ 2 ≤ ClosedTameTarget.metric I x v v := by
  by_cases hM : IsEmpty M
  · exact ⟨1, one_pos, fun x => False.elim (hM.false x)⟩
  rw [not_isEmpty_iff] at hM
  by_cases hE : Subsingleton E
  · refine ⟨1, one_pos, fun x v => ?_⟩
    have hv : v = 0 := Subsingleton.elim v 0
    subst hv
    rw [← metricCLM_apply]
    simp
  · have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have : ProperSpace E := FiniteDimensional.proper ℝ E
    let K : Set (M × E) := (Set.univ : Set M) ×ˢ Metric.sphere (0 : E) 1
    have hK_compact : IsCompact K := isCompact_univ.prod (isCompact_sphere (0 : E) 1)
    have hS_ne : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hK_ne : K.Nonempty := Set.univ_nonempty.prod hS_ne
    let f : M × E → ℝ := fun p => ClosedTameTarget.metric I p.1 p.2 p.2
    have hf_cont : Continuous f := by
      have hJ_app : Continuous (fun p : M × E => (id (α := E →L[ℝ] E) (tgt.J p.1)) p.2) :=
        isBoundedBilinearMap_apply.continuous.comp
          (((continuous_J_global I).comp continuous_fst).prodMk continuous_snd)
      have hω_app1 : Continuous (fun p : M × E => (id (α := E →L[ℝ] E →L[ℝ] ℝ) (tgt.«ω» p.1)) p.2) :=
        isBoundedBilinearMap_apply.continuous.comp
          (((continuous_omega_global I).comp continuous_fst).prodMk continuous_snd)
      have hω_app2 : Continuous (fun p : M × E => (id (α := E →L[ℝ] E →L[ℝ] ℝ) (tgt.«ω» p.1)) p.2
          ((id (α := E →L[ℝ] E) (tgt.J p.1)) p.2)) :=
        isBoundedBilinearMap_apply.continuous.comp (hω_app1.prodMk hJ_app)
      exact continuous_const.mul (hω_app2.add hω_app2)
    obtain ⟨p₀, hp₀K, hp₀_min⟩ := hK_compact.exists_isMinOn hK_ne hf_cont.continuousOn
    have hv₀_norm : ‖p₀.2‖ = 1 := mem_sphere_zero_iff_norm.mp hp₀K.2
    have hv₀_ne : p₀.2 ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hv₀_norm; norm_num at hv₀_norm
    have hc_pos : 0 < f p₀ := metric_pos_def I p₀.1 p₀.2 hv₀_ne
    refine ⟨f p₀, hc_pos, fun x v => ?_⟩
    by_cases hv : v = 0
    · subst hv
      rw [← metricCLM_apply]
      simp
    · have h_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      let u : E := (‖v‖⁻¹ : ℝ) • v
      have hu_sphere : u ∈ Metric.sphere (0 : E) 1 := by
        rw [mem_sphere_zero_iff_norm]
        exact norm_smul_inv_norm hv
      have h_le : f p₀ ≤ ClosedTameTarget.metric I x u u :=
        isMinOn_iff.mp hp₀_min (x, u) ⟨Set.mem_univ x, hu_sphere⟩
      have h_scale : ClosedTameTarget.metric I x u u = (‖v‖⁻¹) ^ 2 * ClosedTameTarget.metric I x v v := by
        rw [← metricCLM_apply, ← metricCLM_apply]
        simp only [u, map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
        ring
      rw [h_scale] at h_le
      have h_mul := mul_le_mul_of_nonneg_right h_le (sq_nonneg ‖v‖)
      have h_cancel : (‖v‖⁻¹) ^ 2 * ClosedTameTarget.metric I x v v * ‖v‖ ^ 2 =
          ClosedTameTarget.metric I x v v := by
        have h_ne : ‖v‖ ≠ 0 := h_norm_pos.ne'
        field_simp
      linarith

omit [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
/-- Operator norm bound on `mfderiv I_CP1 I u z` from coercivity of `ClosedTameTarget.metric`
and `riemannianEnergyDensity I u z`. -/
theorem norm_mfderiv_le_of_coercive {c_min : ℝ} (hc_pos : 0 < c_min)
    (hc : ∀ (x : M) (v : E), c_min * ‖v‖ ^ 2 ≤ ClosedTameTarget.metric I x v v)
    (u : CP1 → M) (z : CP1) :
    ‖(mfderiv I_CP1 I u z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E)‖ ≤
      2 * Real.sqrt (2 * riemannianEnergyDensity I u z / c_min) := by
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] E := mfderiv I_CP1 I u z
  have he_nonneg : 0 ≤ riemannianEnergyDensity I u z := riemannianEnergyDensity_nonneg I u z
  have h_bound_vec : ∀ b : EuclideanSpace ℝ (Fin 2),
      ClosedTameTarget.metric I (u z) (L b) (L b) ≤ 2 * riemannianEnergyDensity I u z →
      ‖L b‖ ≤ Real.sqrt (2 * riemannianEnergyDensity I u z / c_min) := by
    intro b hb
    have h1 : c_min * ‖L b‖ ^ 2 ≤ 2 * riemannianEnergyDensity I u z := (hc (u z) (L b)).trans hb
    have h2 : ‖L b‖ ^ 2 ≤ 2 * riemannianEnergyDensity I u z / c_min := by
      rwa [le_div_iff₀ hc_pos, mul_comm]
    rw [← Real.sqrt_sq (norm_nonneg (L b))]
    exact Real.sqrt_le_sqrt h2
  have he1 : ‖L e1‖ ≤ Real.sqrt (2 * riemannianEnergyDensity I u z / c_min) := by
    apply h_bound_vec e1
    change ClosedTameTarget.metric I (u z) (mfderiv I_CP1 I u z e1) (mfderiv I_CP1 I u z e1) ≤
      2 * riemannianEnergyDensity I u z
    dsimp [riemannianEnergyDensity]
    linarith [metric_self_nonneg I (u z) (mfderiv I_CP1 I u z e2)]
  have he2 : ‖L e2‖ ≤ Real.sqrt (2 * riemannianEnergyDensity I u z / c_min) := by
    apply h_bound_vec e2
    change ClosedTameTarget.metric I (u z) (mfderiv I_CP1 I u z e2) (mfderiv I_CP1 I u z e2) ≤
      2 * riemannianEnergyDensity I u z
    dsimp [riemannianEnergyDensity]
    linarith [metric_self_nonneg I (u z) (mfderiv I_CP1 I u z e1)]
  refine ContinuousLinearMap.opNorm_le_bound L (by positivity) fun w => ?_
  have hw_decomp : w = (w 0) • e1 + (w 1) • e2 := by
    ext i
    fin_cases i <;> simp [e1, e2]
  have hw0 : |w 0| ≤ ‖w‖ := by
    simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le w 0)
  have hw1 : |w 1| ≤ ‖w‖ := by
    simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le w 1)
  calc ‖L w‖ = ‖L ((w 0) • e1 + (w 1) • e2)‖ := by rw [← hw_decomp]
    _ = ‖(w 0) • L e1 + (w 1) • L e2‖ := by rw [map_add, map_smul, map_smul]
    _ ≤ ‖(w 0) • L e1‖ + ‖(w 1) • L e2‖ := norm_add_le _ _
    _ = |w 0| * ‖L e1‖ + |w 1| * ‖L e2‖ := by simp [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖w‖ * Real.sqrt (2 * riemannianEnergyDensity I u z / c_min) +
        ‖w‖ * Real.sqrt (2 * riemannianEnergyDensity I u z / c_min) := by
      gcongr
    _ = 2 * Real.sqrt (2 * riemannianEnergyDensity I u z / c_min) * ‖w‖ := by ring

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

omit [I.Boundaryless] in
/-- The Riemannian metric tensor pulled back by a local coordinate chart `chart` at `p ∈ M`:
$$(\Psi_p^* g)_z(v, w) := g_{\Psi_p(z)}\big(d(e_p \circ \Psi_p)_z(v),\; d(e_p \circ \Psi_p)_z(w)\big),$$
where $\Psi_p = \mathrm{chart.symm}$ and $e_p = \mathrm{extChartAt}\; I\; p$. -/
noncomputable def pulledBackMetricAt (p : M) (chart : OpenPartialHomeomorph M E) (z v w : E) : ℝ :=
  ClosedTameTarget.metric I (chart.symm z)
    (fderiv ℝ (extChartAt I p ∘ chart.symm) z v)
    (fderiv ℝ (extChartAt I p ∘ chart.symm) z w)

/-- Data of a centered normal coordinate chart centered at `p ∈ M` with guaranteed radius `r > 0`.
The chart satisfies `chart p = 0`, `chart.symm 0 = p`, has differential `id_E` at the origin,
has vanishing pulled-back metric first derivatives at the origin (`Γ(0) = 0`), and satisfies $C^3$
bounds on the pulled-back tensors. -/
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
  smooth_to : ContMDiffOn I (modelWithCornersSelf ℝ E) ∞ chart chart.source
  /-- Smoothness of the parametrization on its target -/
  smooth_from : ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ chart.symm chart.target
  /-- Differential of parametrization at the origin is the identity -/
  fderiv_symm_zero : mfderiv (modelWithCornersSelf ℝ E) I chart.symm 0 = ContinuousLinearMap.id ℝ E
  /-- Vanishing first derivatives of pulled-back metric tensor components at the origin (`Γ(0) = 0`) -/
  dmetric_zero : ∀ (v w : E), fderiv ℝ (fun z => pulledBackMetricAt I p chart z v w) 0 = 0
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

omit [I.Boundaryless] in
/-- Restricting a centered normal chart to a smaller positive radius preserves all normal chart properties. -/
def CenteredNormalChart.shrink {p : M} {r r' : ℝ} (C : CenteredNormalChart I p r)
    (_hr' : 0 < r') (hle : r' ≤ r) : CenteredNormalChart I p r' where
  chart := C.chart
  zero_mem_target := C.zero_mem_target
  p_mem_source := C.p_mem_source
  map_center := C.map_center
  symm_center := C.symm_center
  ball_subset_target := fun y hy => C.ball_subset_target (Metric.ball_subset_ball hle hy)
  smooth_to := C.smooth_to
  smooth_from := C.smooth_from
  fderiv_symm_zero := C.fderiv_symm_zero
  dmetric_zero := C.dmetric_zero
  metric_c3_bound := by
    obtain ⟨C_m, hCm, h_bound⟩ := C.metric_c3_bound
    exact ⟨C_m, hCm, fun y hy v w hv hw => h_bound y (Metric.ball_subset_ball hle hy) v w hv hw⟩
  J_c3_bound := by
    obtain ⟨C_J, hCJ, h_bound⟩ := C.J_c3_bound
    exact ⟨C_J, hCJ, fun y hy v hv => h_bound y (Metric.ball_subset_ball hle hy) v hv⟩
  omega_c3_bound := by
    obtain ⟨C_w, hCw, h_bound⟩ := C.omega_c3_bound
    exact ⟨C_w, hCw, fun y hy v w hv hw => h_bound y (Metric.ball_subset_ball hle hy) v w hv hw⟩

/-- Strict positivity of the infimum of a positive function on a nonempty finite type. -/
theorem finset_inf'_pos {β : Type*} [Fintype β] [Nonempty β] (f : β → ℝ) (hf : ∀ b, 0 < f b) :
    0 < (Finset.univ : Finset β).inf' Finset.univ_nonempty f := by
  have H := Finset.univ_nonempty (α := β)
  obtain ⟨b, _, h_eq⟩ := Finset.exists_mem_eq_inf' H f
  rw [h_eq]
  exact hf b

/-- Inequality for the infimum of a function on a finite type at any element. -/
theorem finset_inf'_le_apply {β : Type*} [Fintype β] [Nonempty β] (f : β → ℝ) (b : β) :
    (Finset.univ : Finset β).inf' Finset.univ_nonempty f ≤ f b :=
  Finset.inf'_le f (Finset.mem_univ b)

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
omit [I.Boundaryless] in
/-- Trivial `Nonempty` wrapper given an explicit `fam : UniformNormalChartFamily I (M := M)`
(conditional on `fam`). -/
theorem exists_uniform_normal_chart_family [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M)) :
    Nonempty (UniformNormalChartFamily I (M := M)) :=
  ⟨fam⟩

omit [I.Boundaryless] in
/-- Projection of a centered normal chart at `p` from a given `fam : UniformNormalChartFamily I (M := M)`
(conditional on `fam`). -/
theorem exists_centeredNormalChart [FiniteDimensional ℝ E] (p : M)
    (fam : UniformNormalChartFamily I (M := M)) :
    ∃ r > 0, Nonempty (CenteredNormalChart I p r) :=
  ⟨fam.r_norm, fam.r_norm_pos, ⟨fam.chartAt p⟩⟩

--------------------------------------------------------------------------------
-- SECTION 3b: Concrete Model Instance on (CP1, ω_FS, J_CP1)
--------------------------------------------------------------------------------

namespace UniformNormalChartFamily

open GromovCompactness Metric

/-- The target of the stereographic chart at every point of CP1 is the entire Euclidean space. -/
lemma cp1_chartAt_target_univ (p : CP1) :
    (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).target = Set.univ := by
  change (stereographic' 2 (-p)).target = Set.univ
  exact stereographic'_target (-p)

/-- The stereographic chart at `p` maps `p` to the origin. -/
lemma cp1_chartAt_apply_self (p : CP1) :
    (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p) p = 0 := by
  change (stereographic' 2 (-p)) p = 0
  rw [stereographic']
  simp only [OpenPartialHomeomorph.trans_apply, stereographic_neg_apply]
  exact LinearEquiv.map_zero ((OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere (-p))).repr.toLinearEquiv)

/-- The inverse of the stereographic chart at `p` maps the origin back to `p`. -/
lemma cp1_chartAt_symm_zero (p : CP1) :
    (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm 0 = p := by
  have h_mem : p ∈ (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).source := mem_chart_source _ p
  have h_app := cp1_chartAt_apply_self p
  have h_left := (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).left_inv h_mem
  rw [h_app] at h_left
  exact h_left

/-- Manifold differential of the stereographic chart at its center is the identity. -/
lemma cp1_chartAt_mfderiv_self (p : CP1) :
    mfderiv I_CP1 (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p) p = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) := by
  have hsrc : p ∈ (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).source := mem_chart_source _ p
  have h1 := mfderiv_chartAt_eq_tangentCoordChange (I := I_CP1) hsrc
  rw [h1]
  apply ContinuousLinearMap.ext
  intro v
  exact tangentCoordChange_self (I := I_CP1) (mem_extChartAt_source p)

/-- Manifold differential of the chart inverse at the origin is the identity. -/
lemma cp1_chartAt_mfderiv_symm_zero (p : CP1) :
    mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) I_CP1
      (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm 0 = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) := by
  have h_univ : (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).target = Set.univ := stereographic'_target (-p)
  have h_symm_zero : (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm 0 = p := by
    have h_mem : p ∈ (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).source := mem_chart_source _ p
    have h_app : (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p) p = 0 := by
      change (stereographic' 2 (-p)) p = 0
      rw [stereographic']
      simp only [OpenPartialHomeomorph.trans_apply, stereographic_neg_apply]
      exact LinearEquiv.map_zero ((OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere (-p))).repr.toLinearEquiv)
    have h_left := (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).left_inv h_mem
    rw [h_app] at h_left
    exact h_left
  have h_mdiff : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) I_CP1
      (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm 0 := by
    have h_cont : ContMDiffOn I_CP1 I_CP1 ⊤ (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm
        (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).target := contMDiffOn_chart_symm
    rw [h_univ] at h_cont
    exact (h_cont 0 (Set.mem_univ 0)).mdifferentiableWithinAt (by decide) |>.mdifferentiableAt (isOpen_univ.mem_nhds (Set.mem_univ 0))
  dsimp [mfderiv]
  rw [h_symm_zero]
  rw [if_pos h_mdiff]
  have h_local : _root_.chartAt (EuclideanSpace ℝ (Fin 2)) p ∘ (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm =ᶠ[𝓝 0] id := by
    filter_upwards [isOpen_univ.mem_nhds (Set.mem_univ (0 : EuclideanSpace ℝ (Fin 2)))] with y _
    exact (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).right_inv (by rw [h_univ]; exact Set.mem_univ y)
  rw [range_id, fderivWithin_univ]
  rw [h_local.fderiv_eq]
  rw [fderiv_id]
  rfl

lemma cp1_dmetric_zero (p : CP1) (v w : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fun z => pulledBackMetricAt I_CP1 p (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p) z v w) 0 = 0 := by
  have h_univ : (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).target = Set.univ :=
    cp1_chartAt_target_univ p
  have h_comp_id : extChartAt I_CP1 p ∘ (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm = id := by
    funext z
    change (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p)
      ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm z) = z
    exact (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).right_inv (by rw [h_univ]; exact Set.mem_univ z)
  have h_const : (fun z : EuclideanSpace ℝ (Fin 2) =>
      pulledBackMetricAt I_CP1 p (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p) z v w) =
      Function.const (EuclideanSpace ℝ (Fin 2)) ((1 / 2 : ℝ) * (stdOmega v (J_CP1 w) + stdOmega w (J_CP1 v))) := by
    ext z
    unfold pulledBackMetricAt
    rw [h_comp_id, fderiv_id]
    rfl
  rw [h_const, fderiv_const]
  rfl

/-- Inner product orthogonality between stereographic projection and center basepoint. -/
lemma cp1_orthonormal_repr_orthogonal (p : CP1) (y : EuclideanSpace ℝ (Fin 2)) :
    let v : CP1 := -p
    let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2 (ne_zero_of_mem_unit_sphere v)).repr
    inner ℝ (U.symm y : EuclideanSpace ℝ (Fin 3)) (p.val : EuclideanSpace ℝ (Fin 3)) = (0 : ℝ) := by
  intro v U
  have h_orth : (U.symm y : EuclideanSpace ℝ (Fin 3)) ∈ (ℝ ∙ (v.val : EuclideanSpace ℝ (Fin 3)))ᗮ :=
    (U.symm y).property
  rw [Submodule.mem_orthogonal] at h_orth
  have h_inner := h_orth (v.val) (Submodule.mem_span_singleton_self v.val)
  change inner ℝ (-(p.val : EuclideanSpace ℝ (Fin 3))) (U.symm y : EuclideanSpace ℝ (Fin 3)) = 0 at h_inner
  rw [inner_neg_left, neg_eq_zero, real_inner_comm] at h_inner
  exact h_inner

/-- Norm lower bound for orthogonal sum in real inner product space. -/
lemma norm_le_norm_add_of_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (h : inner ℝ a b = 0) : ‖a‖ ≤ ‖a + b‖ := by
  have h_sq : ‖a + b‖^2 = ‖a‖^2 + ‖b‖^2 := by
    rw [norm_add_sq_real, h]
    ring
  have h_le : ‖a‖^2 ≤ ‖a + b‖^2 := by
    rw [h_sq]
    linarith [sq_nonneg ‖b‖]
  have h_sqrt := Real.sqrt_le_sqrt h_le
  rw [Real.sqrt_sq (norm_nonneg a), Real.sqrt_sq (norm_nonneg (a + b))] at h_sqrt
  exact h_sqrt

lemma scalar_le_mul (y : EuclideanSpace ℝ (Fin 2)) (hy : ‖y‖ ≤ 1) :
    (4 * ‖y‖ + 2 * ‖y‖^2) / (‖y‖^2 + 4) ≤ 2 * ‖y‖ := by
  have h_den : 0 < ‖y‖^2 + 4 := by positivity
  rw [div_le_iff₀ h_den]
  have hy_sq : ‖y‖^2 ≤ ‖y‖ := by
    nlinarith [norm_nonneg y]
  nlinarith [norm_nonneg y]

lemma y_le_scalar_mul (y : EuclideanSpace ℝ (Fin 2)) (hy : ‖y‖ ≤ 1) :
    ‖y‖ ≤ 2 * (4 * ‖y‖ / (‖y‖^2 + 4)) := by
  have h_den : 0 < ‖y‖^2 + 4 := by positivity
  have h_den_le : ‖y‖^2 + 4 ≤ 8 := by nlinarith [norm_nonneg y]
  have h_div : ‖y‖ / 2 ≤ 4 * ‖y‖ / (‖y‖^2 + 4) := by
    have h1 : ‖y‖ * (‖y‖^2 + 4) ≤ 8 * ‖y‖ := by
      nlinarith [norm_nonneg y]
    have h2 : ‖y‖ * (‖y‖^2 + 4) ≤ 2 * (4 * ‖y‖) := by linarith
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) h_den]
    linarith
  linarith

lemma dist_symm_p_le (p : CP1) (y : EuclideanSpace ℝ (Fin 2)) (hy : ‖y‖ ≤ 1) :
    dist ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y) p ≤ 2 * ‖y‖ := by
  have h_den : 0 < ‖y‖^2 + 4 := by positivity
  let v : CP1 := -p
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2 (ne_zero_of_mem_unit_sphere v)).repr
  let uy := (U.symm y : EuclideanSpace ℝ (Fin 3))
  have h_uy : ‖uy‖ = ‖y‖ := by
    change ‖(U.symm y).val‖ = ‖y‖
    rw [Submodule.norm_coe]
    exact U.symm.norm_map y
  have h_fact : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := by
    apply Fact.mk
    simp only [finrank_euclideanSpace, Fintype.card_fin]
  have h_symm := @stereographic'_symm_apply (EuclideanSpace ℝ (Fin 3)) _ _ 2 h_fact v y
  change dist ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y) p ≤ 2 * ‖y‖
  change ‖((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y).val - p.val‖ ≤ 2 * ‖y‖
  have h_chart_eq : (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y = (stereographic' 2 v).symm y := rfl
  rw [h_chart_eq, h_symm]
  have h_comb : ((‖uy‖^2 + 4)⁻¹ • (4:ℝ) • uy + (‖uy‖^2 + 4)⁻¹ • (‖uy‖^2 - 4) • (v.val : EuclideanSpace ℝ (Fin 3))) - (p.val : EuclideanSpace ℝ (Fin 3)) =
                (4 / (‖uy‖^2 + 4)) • uy - (2 * ‖uy‖^2 / (‖uy‖^2 + 4)) • (p.val : EuclideanSpace ℝ (Fin 3)) := by
    have hv : (v.val : EuclideanSpace ℝ (Fin 3)) = - (p.val : EuclideanSpace ℝ (Fin 3)) := rfl
    rw [hv]
    have h_inv : (‖uy‖^2 + 4)⁻¹ = 1 / (‖uy‖^2 + 4) := inv_eq_one_div (‖uy‖^2 + 4)
    rw [h_inv]
    ext i
    simp
    field_simp
    ring
  rw [h_comb]
  have h_tri := norm_sub_le ((4 / (‖uy‖^2 + 4)) • uy) ((2 * ‖uy‖^2 / (‖uy‖^2 + 4)) • (p.val : EuclideanSpace ℝ (Fin 3)))
  have h_term1 : ‖(4 / (‖uy‖^2 + 4)) • uy‖ = (4 / (‖uy‖^2 + 4)) * ‖uy‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have h_term2 : ‖(2 * ‖uy‖^2 / (‖uy‖^2 + 4)) • (p.val : EuclideanSpace ℝ (Fin 3))‖ = (2 * ‖uy‖^2 / (‖uy‖^2 + 4)) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), mem_sphere_zero_iff_norm.mp p.2, mul_one]
  rw [h_term1, h_term2] at h_tri
  rw [h_uy] at h_tri
  have h_sum : 4 / (‖y‖^2 + 4) * ‖y‖ + 2 * ‖y‖^2 / (‖y‖^2 + 4) = (4 * ‖y‖ + 2 * ‖y‖^2) / (‖y‖^2 + 4) := by
    ring
  rw [h_sum] at h_tri
  have h_scal := scalar_le_mul y hy
  have h_uy_y : ‖(4 / (‖uy‖^2 + 4)) • uy - (2 * ‖uy‖^2 / (‖uy‖^2 + 4)) • (p.val : EuclideanSpace ℝ (Fin 3))‖ =
                ‖(4 / (‖y‖^2 + 4)) • uy - (2 * ‖y‖^2 / (‖y‖^2 + 4)) • (p.val : EuclideanSpace ℝ (Fin 3))‖ := by
    rw [h_uy]
  rw [h_uy_y]
  linarith

lemma chart_le_dist_symm_p (p : CP1) (y : EuclideanSpace ℝ (Fin 2)) (hy : ‖y‖ ≤ 1) :
    ‖y‖ ≤ 2 * dist ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y) p := by
  have h_den : 0 < ‖y‖^2 + 4 := by positivity
  let v : CP1 := -p
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2 (ne_zero_of_mem_unit_sphere v)).repr
  let uy := (U.symm y : EuclideanSpace ℝ (Fin 3))
  have h_uy : ‖uy‖ = ‖y‖ := by
    change ‖(U.symm y).val‖ = ‖y‖
    rw [Submodule.norm_coe]
    exact U.symm.norm_map y
  have h_fact : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := by
    apply Fact.mk
    simp only [finrank_euclideanSpace, Fintype.card_fin]
  have h_symm := @stereographic'_symm_apply (EuclideanSpace ℝ (Fin 3)) _ _ 2 h_fact v y
  change ‖y‖ ≤ 2 * dist ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y) p
  change ‖y‖ ≤ 2 * ‖((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y).val - p.val‖
  have h_chart_eq : (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y = (stereographic' 2 v).symm y := rfl
  rw [h_chart_eq, h_symm]
  have h_comb : ((‖uy‖^2 + 4)⁻¹ • (4:ℝ) • uy + (‖uy‖^2 + 4)⁻¹ • (‖uy‖^2 - 4) • (v.val : EuclideanSpace ℝ (Fin 3))) - (p.val : EuclideanSpace ℝ (Fin 3)) =
                (4 / (‖uy‖^2 + 4)) • uy + (- (2 * ‖uy‖^2 / (‖uy‖^2 + 4))) • (p.val : EuclideanSpace ℝ (Fin 3)) := by
    have hv : (v.val : EuclideanSpace ℝ (Fin 3)) = - (p.val : EuclideanSpace ℝ (Fin 3)) := rfl
    rw [hv]
    have h_inv : (‖uy‖^2 + 4)⁻¹ = 1 / (‖uy‖^2 + 4) := inv_eq_one_div (‖uy‖^2 + 4)
    rw [h_inv]
    ext i
    simp
    field_simp
    ring
  rw [h_comb]
  have h_orth : inner ℝ ((4 / (‖uy‖^2 + 4)) • uy) ((- (2 * ‖uy‖^2 / (‖uy‖^2 + 4))) • (p.val : EuclideanSpace ℝ (Fin 3))) = (0:ℝ) := by
    rw [inner_smul_left, inner_smul_right]
    have h_orth0 := cp1_orthonormal_repr_orthogonal p y
    change inner ℝ uy (p.val : EuclideanSpace ℝ (Fin 3)) = 0 at h_orth0
    rw [h_orth0]
    ring
  have h_lower := norm_le_norm_add_of_orthogonal ((4 / (‖uy‖^2 + 4)) • uy) ((- (2 * ‖uy‖^2 / (‖uy‖^2 + 4))) • (p.val : EuclideanSpace ℝ (Fin 3))) h_orth
  have h_term_norm : ‖(4 / (‖uy‖^2 + 4)) • uy‖ = 4 * ‖y‖ / (‖y‖^2 + 4) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), h_uy]
    ring
  rw [h_term_norm] at h_lower
  have h_scal := y_le_scalar_mul y hy
  linarith

/-- Canonical CenteredNormalChart on CP1 centered at basepoint `p` with radius 1. -/
noncomputable def concrete_chartAt_CP1 (p : CP1) : CenteredNormalChart I_CP1 p 1 where
  chart := _root_.chartAt (EuclideanSpace ℝ (Fin 2)) p
  zero_mem_target := by rw [cp1_chartAt_target_univ]; exact Set.mem_univ 0
  p_mem_source := mem_chart_source _ p
  map_center := cp1_chartAt_apply_self p
  symm_center := cp1_chartAt_symm_zero p
  ball_subset_target := by rw [cp1_chartAt_target_univ]; exact Set.subset_univ _
  smooth_to := contMDiffOn_chart
  smooth_from := contMDiffOn_chart_symm
  fderiv_symm_zero := cp1_chartAt_mfderiv_symm_zero p
  dmetric_zero := cp1_dmetric_zero p
  metric_c3_bound := ⟨1, by norm_num, fun y _ v w _ _ => by
    have h_const : (fun z => ClosedTameTarget.metric I_CP1 ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm z) v w) =
                   fun _ => ((1 / 2 : ℝ) * (stdOmega v (J_CP1 w) + stdOmega w (J_CP1 v))) := by
      ext z; rfl
    rw [h_const, iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by decide : 3 ≠ 0)]
    simp⟩
  J_c3_bound := ⟨1, by norm_num, fun y _ v _ => by
    have h_const : (fun z => CP1_ClosedTameTarget.J ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm z) v) =
                   fun _ => J_CP1 v := by
      ext z; rfl
    rw [h_const, iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by decide : 3 ≠ 0)]
    simp⟩
  omega_c3_bound := ⟨1, by norm_num, fun y _ v w _ _ => by
    have h_const : (fun z => CP1_ClosedTameTarget.«ω» ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm z) v w) =
                   fun _ => stdOmega v w := by
      ext z; rfl
    rw [h_const, iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by decide : 3 ≠ 0)]
    simp⟩

/-- Canonical concrete model instance of `UniformNormalChartFamily` on CP1.
Proves that `UniformNormalChartFamily` is unconditionally inhabited. -/
noncomputable def concrete_CP1 : UniformNormalChartFamily I_CP1 (M := CP1) where
  r_norm := 1
  r_norm_pos := by norm_num
  chartAt := concrete_chartAt_CP1
  L_dist := 2
  L_dist_ge := by norm_num
  dist_le_chart := fun p y hy => by
    have hy_norm : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
    have hy_le : ‖y‖ ≤ 1 := le_of_lt hy_norm
    exact dist_symm_p_le p y hy_le
  chart_le_dist := fun p y hy => by
    have hy_norm : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
    have hy_le : ‖y‖ ≤ 1 := le_of_lt hy_norm
    exact chart_le_dist_symm_p p y hy_le
  C_curv := 0
  C_curv_nonneg := le_rfl
  C_metric3 := 1
  C_J3 := 1
  C_omega3 := 1
  metric_c3_uniform := fun p y _ v w _ _ => by
    have h_const : (fun z => ClosedTameTarget.metric I_CP1 ((concrete_chartAt_CP1 p).chart.symm z) v w) =
                   fun _ => ((1 / 2 : ℝ) * (stdOmega v (J_CP1 w) + stdOmega w (J_CP1 v))) := by
      ext z; rfl
    rw [h_const, iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by decide : 3 ≠ 0)]
    simp
  J_c3_uniform := fun p y _ v _ => by
    have h_const : (fun z => CP1_ClosedTameTarget.J ((concrete_chartAt_CP1 p).chart.symm z) v) =
                   fun _ => J_CP1 v := by
      ext z; rfl
    rw [h_const, iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by decide : 3 ≠ 0)]
    simp
  omega_c3_uniform := fun p y _ v w _ _ => by
    have h_const : (fun z => CP1_ClosedTameTarget.«ω» ((concrete_chartAt_CP1 p).chart.symm z) v w) =
                   fun _ => stdOmega v w := by
      ext z; rfl
    rw [h_const, iteratedFDeriv_const_of_ne (𝕜 := ℝ) (by decide : 3 ≠ 0)]
    simp

/-- Exact stereographic chordal distance identity on `CP1`:
for `σ = chartAt (EuclideanSpace ℝ (Fin 2)) p`,
$$\mathrm{dist}(\sigma^{-1}(y_1), \sigma^{-1}(y_2))^2 = \frac{16 \|y_1 - y_2\|^2}{(\|y_1\|^2 + 4)(\|y_2\|^2 + 4)}.$$ -/
lemma cp1_dist_symm_sq (p : CP1) (y₁ y₂ : EuclideanSpace ℝ (Fin 2)) :
    dist ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y₁)
         ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y₂) ^ 2 =
      16 * ‖y₁ - y₂‖ ^ 2 / ((‖y₁‖ ^ 2 + 4) * (‖y₂‖ ^ 2 + 4)) := by
  let σ := _root_.chartAt (EuclideanSpace ℝ (Fin 2)) p
  let q₁ : CP1 := σ.symm y₁
  let q₂ : CP1 := σ.symm y₂
  let v : CP1 := -p
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton
    (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2 (ne_zero_of_mem_unit_sphere v)).repr
  let u₁ : EuclideanSpace ℝ (Fin 3) := (U.symm y₁ : EuclideanSpace ℝ (Fin 3))
  let u₂ : EuclideanSpace ℝ (Fin 3) := (U.symm y₂ : EuclideanSpace ℝ (Fin 3))
  have h_u₁_norm : ‖u₁‖ = ‖y₁‖ := by
    change ‖(U.symm y₁).val‖ = ‖y₁‖
    rw [Submodule.norm_coe]
    exact U.symm.norm_map y₁
  have h_u₂_norm : ‖u₂‖ = ‖y₂‖ := by
    change ‖(U.symm y₂).val‖ = ‖y₂‖
    rw [Submodule.norm_coe]
    exact U.symm.norm_map y₂
  have h_u_inner : inner ℝ u₁ u₂ = inner ℝ y₁ y₂ := by
    change inner ℝ (U.symm y₁).val (U.symm y₂).val = inner ℝ y₁ y₂
    rw [← Submodule.coe_inner]
    exact U.symm.inner_map_map y₁ y₂
  have h_orth₁ : inner ℝ u₁ (v.val : EuclideanSpace ℝ (Fin 3)) = 0 := by
    have h0 := cp1_orthonormal_repr_orthogonal p y₁
    change inner ℝ u₁ (p.val : EuclideanSpace ℝ (Fin 3)) = 0 at h0
    change inner ℝ u₁ (-(p.val : EuclideanSpace ℝ (Fin 3))) = 0
    rw [inner_neg_right, h0, neg_zero]
  have h_orth₂ : inner ℝ u₂ (v.val : EuclideanSpace ℝ (Fin 3)) = 0 := by
    have h0 := cp1_orthonormal_repr_orthogonal p y₂
    change inner ℝ u₂ (p.val : EuclideanSpace ℝ (Fin 3)) = 0 at h0
    change inner ℝ u₂ (-(p.val : EuclideanSpace ℝ (Fin 3))) = 0
    rw [inner_neg_right, h0, neg_zero]
  have h_orth₂' : inner ℝ (v.val : EuclideanSpace ℝ (Fin 3)) u₂ = 0 := by
    rw [real_inner_comm, h_orth₂]
  have h_v_norm : ‖(v.val : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp v.2
  have h_v_inner : inner ℝ (v.val : EuclideanSpace ℝ (Fin 3)) v.val = 1 := by
    rw [real_inner_self_eq_norm_sq, h_v_norm, one_pow]
  have h_q₁_norm : ‖(q₁.val : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp q₁.2
  have h_q₂_norm : ‖(q₂.val : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp q₂.2
  have h_fact : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := by
    apply Fact.mk
    simp only [finrank_euclideanSpace, Fintype.card_fin]
  have h_symm₁ : (q₁.val : EuclideanSpace ℝ (Fin 3)) =
      (‖u₁‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • u₁ + (‖u₁‖ ^ 2 + 4)⁻¹ • (‖u₁‖ ^ 2 - 4) • (v.val : EuclideanSpace ℝ (Fin 3)) :=
    @stereographic'_symm_apply (EuclideanSpace ℝ (Fin 3)) _ _ 2 h_fact v y₁
  have h_symm₂ : (q₂.val : EuclideanSpace ℝ (Fin 3)) =
      (‖u₂‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • u₂ + (‖u₂‖ ^ 2 + 4)⁻¹ • (‖u₂‖ ^ 2 - 4) • (v.val : EuclideanSpace ℝ (Fin 3)) :=
    @stereographic'_symm_apply (EuclideanSpace ℝ (Fin 3)) _ _ 2 h_fact v y₂
  have h_dist_sq : dist q₁ q₂ ^ 2 = 2 - 2 * inner ℝ (q₁.val : EuclideanSpace ℝ (Fin 3)) q₂.val := by
    change ‖(q₁.val : EuclideanSpace ℝ (Fin 3)) - q₂.val‖ ^ 2 = _
    rw [norm_sub_sq_real, h_q₁_norm, h_q₂_norm]
    ring
  have h_y_sq : ‖y₁ - y₂‖ ^ 2 = ‖y₁‖ ^ 2 - 2 * inner ℝ y₁ y₂ + ‖y₂‖ ^ 2 :=
    norm_sub_sq_real y₁ y₂
  have h_q_inner : inner ℝ (q₁.val : EuclideanSpace ℝ (Fin 3)) q₂.val =
      (‖y₁‖ ^ 2 + 4)⁻¹ * 4 * ((‖y₂‖ ^ 2 + 4)⁻¹ * 4 * inner ℝ y₁ y₂) +
      (‖y₁‖ ^ 2 + 4)⁻¹ * (‖y₁‖ ^ 2 - 4) * ((‖y₂‖ ^ 2 + 4)⁻¹ * (‖y₂‖ ^ 2 - 4) * 1) := by
    rw [h_symm₁, h_symm₂]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, h_orth₁, h_orth₂', h_v_inner, h_u_inner,
      h_u₁_norm, h_u₂_norm, mul_zero, add_zero, zero_add]
    ring
  have hd₁ : 0 < ‖y₁‖ ^ 2 + 4 := by positivity
  have hd₂ : 0 < ‖y₂‖ ^ 2 + 4 := by positivity
  rw [h_dist_sq, h_q_inner, h_y_sq]
  field_simp
  ring

/-- Pairwise `2`-bi-Lipschitz equivalence of stereographic charts on `Metric.ball 0 1 ⊆ ℝ²`. -/
lemma cp1_dist_symm_bilipschitz (p : CP1) {y₁ y₂ : EuclideanSpace ℝ (Fin 2)}
    (hy₁ : y₁ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
    (hy₂ : y₂ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    dist ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y₁)
         ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y₂) ≤ 2 * ‖y₁ - y₂‖ ∧
    ‖y₁ - y₂‖ ≤ 2 * dist ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y₁)
                         ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y₂) := by
  have hy₁_le : ‖y₁‖ ≤ 1 := le_of_lt (mem_ball_zero_iff.mp hy₁)
  have hy₂_le : ‖y₂‖ ≤ 1 := le_of_lt (mem_ball_zero_iff.mp hy₂)
  have hy₁_sq : ‖y₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y₁]
  have hy₂_sq : ‖y₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y₂]
  have hd₁_pos : 0 < ‖y₁‖ ^ 2 + 4 := by positivity
  have hd₂_pos : 0 < ‖y₂‖ ^ 2 + 4 := by positivity
  have hd_ge : 16 ≤ (‖y₁‖ ^ 2 + 4) * (‖y₂‖ ^ 2 + 4) := by nlinarith [sq_nonneg ‖y₁‖, sq_nonneg ‖y₂‖]
  have hd_le : (‖y₁‖ ^ 2 + 4) * (‖y₂‖ ^ 2 + 4) ≤ 64 := by nlinarith [sq_nonneg ‖y₁‖, sq_nonneg ‖y₂‖]
  have h_id := cp1_dist_symm_sq p y₁ y₂
  set d := dist ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y₁)
                ((_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y₂)
  have hd_nonneg : 0 ≤ d := dist_nonneg
  constructor
  · have h_sq_le : d ^ 2 ≤ (2 * ‖y₁ - y₂‖) ^ 2 := by
      rw [h_id, div_le_iff₀ (mul_pos hd₁_pos hd₂_pos)]
      nlinarith [sq_nonneg ‖y₁ - y₂‖]
    have h_sqrt := Real.sqrt_le_sqrt h_sq_le
    rwa [Real.sqrt_sq hd_nonneg, Real.sqrt_sq (by positivity)] at h_sqrt
  · have h_sq_le : ‖y₁ - y₂‖ ^ 2 ≤ (2 * d) ^ 2 := by
      have h_mul : 16 * ‖y₁ - y₂‖ ^ 2 = d ^ 2 * ((‖y₁‖ ^ 2 + 4) * (‖y₂‖ ^ 2 + 4)) := by
        rw [h_id, div_mul_cancel₀ _ (mul_pos hd₁_pos hd₂_pos).ne']
      nlinarith [sq_nonneg d]
    have h_sqrt := Real.sqrt_le_sqrt h_sq_le
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h_sqrt

set_option backward.isDefEq.respectTransparency false in
/-- Operator norm bound on the manifold differential of the inverse stereographic chart on `B(0, 1)`. -/
lemma cp1_norm_mfderiv_symm_le (p : CP1) {y₀ : EuclideanSpace ℝ (Fin 2)}
    (hy₀ : y₀ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    ‖(mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1
        (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).symm y₀ :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))‖ ≤ 4 := by
  let ψ := _root_.chartAt (EuclideanSpace ℝ (Fin 2)) p
  by_cases h_mdiff : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1 ψ.symm y₀
  · let p₁ : CP1 := ψ.symm y₀
    let ψ₁ := _root_.chartAt (EuclideanSpace ℝ (Fin 2)) p₁
    have h_mfderiv : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1 ψ.symm y₀ :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) =
        fderiv ℝ (ψ₁ ∘ ψ.symm) y₀ := by
      dsimp [mfderiv]
      rw [if_pos h_mdiff, range_id, fderivWithin_univ]
      rfl
    rw [h_mfderiv]
    refine norm_fderiv_le_of_lip' ℝ (by norm_num : (0 : ℝ) ≤ 4) ?_
    have h_univ : ψ.target = Set.univ := cp1_chartAt_target_univ p
    have h_symm_cont : ContinuousAt ψ.symm y₀ :=
      ψ.continuousOn_symm.continuousAt (by rw [h_univ]; exact isOpen_univ.mem_nhds (Set.mem_univ y₀))
    have hp₁_src : p₁ ∈ ψ₁.source := mem_chart_source _ p₁
    have hp₁_zero : ψ₁ p₁ = 0 := cp1_chartAt_apply_self p₁
    have h_nhds₁ : ψ₁.source ∩ ψ₁ ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 ∈ 𝓝 p₁ := by
      refine Filter.inter_mem (ψ₁.open_source.mem_nhds hp₁_src) ?_
      exact (ψ₁.continuousOn.continuousAt (ψ₁.open_source.mem_nhds hp₁_src)).preimage_mem_nhds
        (by rw [hp₁_zero]; exact Metric.ball_mem_nhds 0 one_pos)
    filter_upwards [IsOpen.mem_nhds isOpen_ball hy₀,
      h_symm_cont.preimage_mem_nhds h_nhds₁] with x hx_ball hx_pre
    rcases hx_pre with ⟨hx_src₁, hx_ball₁⟩
    change ‖ψ₁ (ψ.symm x) - ψ₁ p₁‖ ≤ 4 * ‖x - y₀‖
    rw [hp₁_zero, sub_zero]
    have hx_le₁ : ‖ψ₁ (ψ.symm x)‖ ≤ 1 := le_of_lt (mem_ball_zero_iff.mp hx_ball₁)
    have h_left₁ : ψ₁.symm (ψ₁ (ψ.symm x)) = ψ.symm x := ψ₁.left_inv hx_src₁
    have h_step1 : ‖ψ₁ (ψ.symm x)‖ ≤ 2 * dist (ψ.symm x) p₁ := by
      have h := chart_le_dist_symm_p p₁ (ψ₁ (ψ.symm x)) hx_le₁
      rwa [h_left₁] at h
    have h_step2 : dist (ψ.symm x) p₁ ≤ 2 * ‖x - y₀‖ :=
      (cp1_dist_symm_bilipschitz p hx_ball hy₀).1
    linarith
  · have h_zero : (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1 ψ.symm y₀ :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) = 0 := by
      dsimp [mfderiv]; rw [if_neg h_mdiff]
    rw [h_zero, norm_zero]
    norm_num

end UniformNormalChartFamily

/- =========================================================================
   BoundedChartedTarget (Layer 0 Atlas/Metric Compatibility) & h_aa_lip
   ========================================================================= -/

/-- Compatibility between the `MetricSpace M` distance, the smooth atlas `extChartAt I p`,
and the smooth target tensors `(ω, J)` on a closed tame target `(M, ω, J)`.

Provides:
1. A uniform coordinate ball radius `r₀ > 0` contained in `(extChartAt I p).target` at every `p : M`.
2. Uniform pairwise `L₀`-bi-Lipschitz equivalence (`L₀ ≥ 1`) between Euclidean distance on
   `Metric.ball (extChartAt I p p) r₀` and manifold distance `dist` on `M`.
3. Uniform $C^3$ bounds (`0 ≤ k ≤ 3`) on the chart representations `ω_chart` and `J_chart` on
   `Metric.ball (extChartAt I p p) r₀`. -/
class BoundedChartedTarget (I : ModelWithCorners ℝ E H) [I.Boundaryless] (M : Type u)
    [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    [tgt : ClosedTameTarget I M] : Prop where
  exists_chart_bounds :
    ∃ (r₀ L₀ C_ω C_J : ℝ),
      0 < r₀ ∧ 1 ≤ L₀ ∧ 0 < C_ω ∧ 0 < C_J ∧
      (∀ p : M, Metric.ball (extChartAt I p p) r₀ ⊆ (extChartAt I p).target) ∧
      (∀ (p : M) {y₁ y₂ : E},
        y₁ ∈ Metric.ball (extChartAt I p p) r₀ →
        y₂ ∈ Metric.ball (extChartAt I p p) r₀ →
        dist ((extChartAt I p).symm y₁) ((extChartAt I p).symm y₂) ≤ L₀ * ‖y₁ - y₂‖ ∧
        ‖y₁ - y₂‖ ≤ L₀ * dist ((extChartAt I p).symm y₁) ((extChartAt I p).symm y₂)) ∧
      (∀ (p : M) {y : E}, y ∈ Metric.ball (extChartAt I p p) r₀ →
        ∀ (v : E), ∀ k ≤ 3, ‖iteratedFDeriv ℝ k (fun z => ω_chart I tgt.«ω» p z v) y‖ ≤ C_ω * ‖v‖) ∧
      (∀ (p : M) {y : E}, y ∈ Metric.ball (extChartAt I p p) r₀ →
        ∀ k ≤ 3, ‖iteratedFDeriv ℝ k (J_chart I tgt.J p) y‖ ≤ C_J)

/-- Unconditional `BoundedChartedTarget` instance on `(CP1, ω_FS, J_CP1)`. -/
instance instBoundedChartedTargetCP1 : BoundedChartedTarget I_CP1 CP1 where
  exists_chart_bounds := by
    refine ⟨1, 2,
      ‖(stdOmega : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ + 1,
      ‖(J_CP1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))‖ + 1,
      one_pos, by norm_num, by positivity, by positivity, ?_, ?_, ?_, ?_⟩
    · intro p y _
      have h_univ : (_root_.chartAt (EuclideanSpace ℝ (Fin 2)) p).target = Set.univ :=
        UniformNormalChartFamily.cp1_chartAt_target_univ p
      simp [extChartAt, h_univ]
    · intro p y₁ y₂ hy₁ hy₂
      have hp0 : extChartAt I_CP1 p p = 0 :=
        UniformNormalChartFamily.cp1_chartAt_apply_self p
      rw [hp0] at hy₁ hy₂
      exact UniformNormalChartFamily.cp1_dist_symm_bilipschitz p hy₁ hy₂
    · intro p y _ v k _
      have h_const : (fun z => ω_chart I_CP1 CP1_ClosedTameTarget.«ω» p z v) = fun _ => stdOmega v := by
        ext z; rfl
      rw [h_const]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [norm_iteratedFDeriv_zero]
        have h_op : ‖stdOmega v‖ ≤ ‖stdOmega‖ * ‖v‖ := ContinuousLinearMap.le_opNorm stdOmega v
        nlinarith [norm_nonneg v]
      · simp only [iteratedFDeriv_const_of_ne (𝕜 := ℝ) hk.ne', Pi.zero_apply, norm_zero]
        positivity
    · intro p y _ k _
      have h_const : J_chart I_CP1 CP1_ClosedTameTarget.J p = fun _ => J_CP1 := by
        ext z; rfl
      rw [h_const]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [norm_iteratedFDeriv_zero]
        linarith
      · simp only [iteratedFDeriv_const_of_ne (𝕜 := ℝ) hk.ne', Pi.zero_apply, norm_zero]
        positivity

omit [I.Boundaryless] [CompactSpace M] tgt in
/-- The manifold differential of `extChartAt I q` at its center `q` is the identity operator on `E`. -/
theorem mfderiv_extChartAt_self (q : M) :
    (mfderiv I 𝓘(ℝ, E) (extChartAt I q) q : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
  have hsrc : q ∈ (chartAt H q).source := mem_chart_source H q
  have h1 := (hasMFDerivAt_extChartAt (I := I) hsrc).mfderiv
  rw [h1, mfderiv_chartAt_eq_tangentCoordChange hsrc]
  ext v
  exact tangentCoordChange_self (I := I) (mem_extChartAt_source q)

set_option backward.isDefEq.respectTransparency false in
/-- First-principles proof of local Lipschitz equicontinuity (`h_aa_lip`) for `J`-holomorphic
sequences with locally uniformly bounded `riemannianEnergyDensity` on any `[BoundedChartedTarget I M]`
with `[FiniteDimensional ℝ E]` (`0 sorryAx`). -/
theorem local_lipschitz_of_bounded_energy_density
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∀ z₀ ∈ Ω, ∃ ρ > 0, ∃ L ≥ 0, ∀ n : ℕ, ∀ z ∈ Metric.ball z₀ ρ,
      dist (u_seq n z) (u_seq n z₀) ≤ L * dist z z₀ := by
  obtain ⟨c_min, hc_min_pos, hc_coercive⟩ := exists_metric_coercive I (M := M)
  obtain ⟨r₀, L₀, _, _, hr₀_pos, hL₀_ge, _, _, h_ball_target, h_bilip, _, _⟩ :=
    BoundedChartedTarget.exists_chart_bounds (I := I) (M := M)
  have hL₀_pos : 0 < L₀ := lt_of_lt_of_le one_pos hL₀_ge
  intro z₀ hz₀
  let ψ := _root_.chartAt (EuclideanSpace ℝ (Fin 2)) z₀
  have hψ_univ : ψ.target = Set.univ := UniformNormalChartFamily.cp1_chartAt_target_univ z₀
  have hψ_zero : ψ z₀ = 0 := UniformNormalChartFamily.cp1_chartAt_apply_self z₀
  have hψ_symm_zero : ψ.symm 0 = z₀ := UniformNormalChartFamily.cp1_chartAt_symm_zero z₀
  have hψ_symm_cont : Continuous ψ.symm := by
    rw [← continuousOn_univ, ← hψ_univ]
    exact ψ.continuousOn_symm
  have h_pre_open : IsOpen (ψ.symm ⁻¹' Ω) := h_open.preimage hψ_symm_cont
  have h_zero_mem_pre : (0 : EuclideanSpace ℝ (Fin 2)) ∈ ψ.symm ⁻¹' Ω := by
    simp [Set.mem_preimage, hψ_symm_zero, hz₀]
  obtain ⟨r₁, hr₁_pos, hr₁_sub⟩ := Metric.isOpen_iff.mp h_pre_open 0 h_zero_mem_pre
  let r_dom : ℝ := min (r₁ / 2) (1 / 2)
  have hr_dom_pos : 0 < r_dom := lt_min (half_pos hr₁_pos) (by norm_num)
  have hr_dom_lt_one : r_dom < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have h_cball_sub_pre : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r_dom ⊆ ψ.symm ⁻¹' Ω := by
    intro y hy
    apply hr₁_sub
    rw [Metric.mem_ball, dist_zero_right]
    have hy' : ‖y‖ ≤ r_dom := mem_closedBall_zero_iff.mp hy
    have hr_le : r_dom ≤ r₁ / 2 := min_le_left _ _
    linarith
  have : ProperSpace (EuclideanSpace ℝ (Fin 2)) := FiniteDimensional.proper ℝ _
  let K : Set CP1 := ψ.symm '' Metric.closedBall 0 r_dom
  have hK_compact : IsCompact K := (isCompact_closedBall 0 r_dom).image hψ_symm_cont
  have hK_sub : K ⊆ Ω := image_subset_iff.mpr h_cball_sub_pre
  obtain ⟨C_e, hCe_pos, hCe_bdd⟩ := h_grad_bdd K hK_sub hK_compact
  have h_nhds_z₀ : ψ.source ∩ ψ ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r_dom ∈ 𝓝 z₀ := by
    refine Filter.inter_mem (ψ.open_source.mem_nhds (mem_chart_source _ z₀)) ?_
    exact (ψ.continuousOn.continuousAt (ψ.open_source.mem_nhds (mem_chart_source _ z₀))).preimage_mem_nhds
      (by rw [hψ_zero]; exact Metric.ball_mem_nhds 0 hr_dom_pos)
  obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.mem_nhds_iff.mp h_nhds_z₀
  let C_grad : ℝ := 8 * Real.sqrt (2 * C_e / c_min)
  have hC_grad_nonneg : 0 ≤ C_grad := by positivity
  refine ⟨ρ, hρ_pos, 2 * L₀ * C_grad, by positivity, fun n z hz => ?_⟩
  rcases hρ_sub hz with ⟨hz_src, hz_ball⟩
  let w : EuclideanSpace ℝ (Fin 2) := ψ z
  have hw_symm : ψ.symm w = z := ψ.left_inv hz_src
  have hw_norm_lt : ‖w‖ < r_dom := mem_ball_zero_iff.mp hz_ball
  have hw_ball1 : w ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    rw [mem_ball_zero_iff]; exact lt_trans hw_norm_lt hr_dom_lt_one
  have hw_le_dist : ‖w‖ ≤ 2 * dist z z₀ := by
    have h := UniformNormalChartFamily.chart_le_dist_symm_p z₀ w (le_of_lt (lt_trans hw_norm_lt hr_dom_lt_one))
    rwa [hw_symm] at h
  let γ : ℝ → M := fun t => u_seq n (ψ.symm (t • w))
  let f : ℝ → ℝ := fun t => dist (γ t) (γ 0)
  let B : ℝ → ℝ := fun t => (L₀ * C_grad * ‖w‖) * t
  let B' : ℝ → ℝ := fun _ => L₀ * C_grad * ‖w‖
  have h_seg_mem_cball : ∀ t ∈ Icc (0 : ℝ) 1, t • w ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r_dom := by
    intro t ht
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht.1]
    calc t * ‖w‖ ≤ 1 * r_dom := mul_le_mul ht.2 (le_of_lt hw_norm_lt) (norm_nonneg w) zero_le_one
      _ = r_dom := one_mul r_dom
  have h_seg_mem_K : ∀ t ∈ Icc (0 : ℝ) 1, ψ.symm (t • w) ∈ K :=
    fun t ht => mem_image_of_mem ψ.symm (h_seg_mem_cball t ht)
  have hγ_cont : ContinuousOn γ (Icc 0 1) := by
    refine (h_jhol n).1.continuousOn.comp ?_ (fun t ht => hK_sub (h_seg_mem_K t ht))
    exact hψ_symm_cont.comp_continuousOn (continuousOn_id.smul continuousOn_const)
  have hf_cont : ContinuousOn f (Icc 0 1) :=
    Continuous.comp_continuousOn (continuous_id.dist continuous_const) hγ_cont
  have ha : f 0 ≤ B 0 := by simp [f, B]
  have hB_cont : ContinuousOn B (Icc 0 1) :=
    (continuous_const.mul continuous_id).continuousOn
  have hB_deriv : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt B (B' t) (Ici t) t := by
    intro t _
    simpa [B, B'] using ((hasDerivAt_id t).const_mul (L₀ * C_grad * ‖w‖)).hasDerivWithinAt
  have h_fencing := image_le_of_liminf_slope_right_le_deriv_boundary hf_cont ha hB_cont hB_deriv ?_
  · have h1 := h_fencing (right_mem_Icc.mpr zero_le_one)
    have hf1 : f 1 = dist (u_seq n z) (u_seq n z₀) := by
      dsimp [f, γ]
      rw [one_smul, zero_smul, hw_symm, hψ_symm_zero]
    rw [hf1] at h1
    dsimp [B] at h1
    calc dist (u_seq n z) (u_seq n z₀) ≤ L₀ * C_grad * ‖w‖ * 1 := h1
      _ ≤ L₀ * C_grad * (2 * dist z z₀) * 1 := by gcongr
      _ = 2 * L₀ * C_grad * dist z z₀ := by ring
  · intro t₀ ht₀ r hr
    let y₀ : EuclideanSpace ℝ (Fin 2) := t₀ • w
    let p_dom : CP1 := ψ.symm y₀
    let q : M := u_seq n p_dom
    have ht₀_Icc : t₀ ∈ Icc (0 : ℝ) 1 := ⟨ht₀.1, le_of_lt ht₀.2⟩
    have hy₀_cball : y₀ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r_dom := h_seg_mem_cball t₀ ht₀_Icc
    have hy₀_ball1 : y₀ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt (mem_closedBall_zero_iff.mp hy₀_cball) hr_dom_lt_one
    have hp_dom_K : p_dom ∈ K := h_seg_mem_K t₀ ht₀_Icc
    have hp_dom_Ω : p_dom ∈ Ω := hK_sub hp_dom_K
    have h_d1 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1 ψ.symm y₀
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1 ψ.symm y₀) := by
      have h_cont : ContMDiffOn I_CP1 I_CP1 ⊤ ψ.symm ψ.target := contMDiffOn_chart_symm
      rw [hψ_univ] at h_cont
      exact ((h_cont y₀ (Set.mem_univ y₀)).mdifferentiableWithinAt (by decide)
        |>.mdifferentiableAt (isOpen_univ.mem_nhds (Set.mem_univ y₀))).hasMFDerivAt
    have h_d2 : HasMFDerivAt I_CP1 I (u_seq n) p_dom (mfderiv I_CP1 I (u_seq n) p_dom) :=
      (((h_jhol n).1 p_dom hp_dom_Ω).mdifferentiableWithinAt (by decide)
        |>.mdifferentiableAt (h_open.mem_nhds hp_dom_Ω)).hasMFDerivAt
    have h_d3 : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I q) q (mfderiv I 𝓘(ℝ, E) (extChartAt I q) q) :=
      (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H q)).hasMFDerivAt
    let D_y₀ : EuclideanSpace ℝ (Fin 2) →L[ℝ] E :=
      (mfderiv I 𝓘(ℝ, E) (extChartAt I q) q).comp
        ((mfderiv I_CP1 I (u_seq n) p_dom).comp
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1 ψ.symm y₀))
    have h_G_fderiv : HasFDerivAt (extChartAt I q ∘ u_seq n ∘ ψ.symm) D_y₀ y₀ :=
      ((h_d3.comp p_dom h_d2).comp y₀ h_d1).hasFDerivAt
    let g : ℝ → E := fun t => (extChartAt I q ∘ u_seq n ∘ ψ.symm) (t • w)
    have h_seg_deriv : HasDerivAt (fun t : ℝ => t • w) w t₀ := by
      simpa using (hasDerivAt_id t₀).smul_const w
    have hg_deriv : HasDerivAt g (D_y₀ w) t₀ := h_G_fderiv.comp_hasDerivAt t₀ h_seg_deriv
    have h_D_norm : ‖D_y₀ w‖ ≤ C_grad * ‖w‖ := by
      have h_id : (mfderiv I 𝓘(ℝ, E) (extChartAt I q) q : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E :=
        mfderiv_extChartAt_self I q
      have h_u_norm : ‖mfderiv I_CP1 I (u_seq n) p_dom‖ ≤
          2 * Real.sqrt (2 * C_e / c_min) := by
        calc ‖mfderiv I_CP1 I (u_seq n) p_dom‖
            ≤ 2 * Real.sqrt (2 * riemannianEnergyDensity I (u_seq n) p_dom / c_min) :=
              norm_mfderiv_le_of_coercive I hc_min_pos hc_coercive (u_seq n) p_dom
          _ ≤ 2 * Real.sqrt (2 * C_e / c_min) := by
              gcongr
              exact hCe_bdd n p_dom hp_dom_K
      have h_ψ_norm : ‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1 ψ.symm y₀‖ ≤ 4 :=
        UniformNormalChartFamily.cp1_norm_mfderiv_symm_le z₀ hy₀_ball1
      have h_comp_eq : D_y₀ w = (mfderiv I_CP1 I (u_seq n) p_dom)
          ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1 ψ.symm y₀) w) := by
        change ((mfderiv I 𝓘(ℝ, E) (extChartAt I q) q : E →L[ℝ] E)
          ((mfderiv I_CP1 I (u_seq n) p_dom)
            ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1 ψ.symm y₀) w))) = _
        rw [h_id]
        rfl
      rw [h_comp_eq]
      calc ‖(mfderiv I_CP1 I (u_seq n) p_dom)
              ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1 ψ.symm y₀) w)‖
          ≤ ‖mfderiv I_CP1 I (u_seq n) p_dom‖ *
            (‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1 ψ.symm y₀‖ * ‖w‖) := by
            refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
            gcongr
            exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ (2 * Real.sqrt (2 * C_e / c_min)) * (4 * ‖w‖) := by
            gcongr
        _ = C_grad * ‖w‖ := by dsimp [C_grad]; ring
    have h_tendsto_slope : Filter.Tendsto (fun t => L₀ * ‖slope g t₀ t‖) (𝓝[>] t₀) (𝓝 (L₀ * ‖D_y₀ w‖)) :=
      ((hg_deriv.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t₀)).norm).const_mul L₀
    have h_lt_r : L₀ * ‖D_y₀ w‖ < r := by
      have h_le : L₀ * ‖D_y₀ w‖ ≤ B' t₀ := by
        dsimp [B']
        nlinarith [h_D_norm]
      exact lt_of_le_of_lt h_le hr
    have h_ev_lt : ∀ᶠ t in 𝓝[>] t₀, L₀ * ‖slope g t₀ t‖ < r :=
      h_tendsto_slope.eventually (gt_mem_nhds h_lt_r)
    have hγ_cont_at : ContinuousAt γ t₀ := by
      have h_u_cont : ContinuousAt (u_seq n) p_dom :=
        ((h_jhol n).1 p_dom hp_dom_Ω).continuousWithinAt.continuousAt (h_open.mem_nhds hp_dom_Ω)
      exact h_u_cont.comp (hψ_symm_cont.continuousAt.comp (continuous_id.smul continuous_const).continuousAt)
    have hq_nhds : (extChartAt I q).source ∩
        (extChartAt I q) ⁻¹' Metric.ball (extChartAt I q q) r₀ ∈ 𝓝 q := by
      refine Filter.inter_mem ((isOpen_extChartAt_source q).mem_nhds (mem_extChartAt_source q)) ?_
      exact (continuousAt_extChartAt q).preimage_mem_nhds (Metric.ball_mem_nhds _ hr₀_pos)
    have h_ev_chart : ∀ᶠ t in 𝓝[>] t₀,
        γ t ∈ (extChartAt I q).source ∧ extChartAt I q (γ t) ∈ Metric.ball (extChartAt I q q) r₀ :=
      nhdsWithin_le_nhds (hγ_cont_at.preimage_mem_nhds hq_nhds)
    have h_ev_gt : ∀ᶠ t in 𝓝[>] t₀, t₀ < t := self_mem_nhdsWithin
    have h_ev_all : ∀ᶠ t in 𝓝[>] t₀, slope f t₀ t < r := by
      filter_upwards [h_ev_lt, h_ev_chart, h_ev_gt] with t ht_lt ⟨ht_src, ht_ball⟩ ht_gt
      have h_pos : 0 < t - t₀ := sub_pos.mpr ht_gt
      have hq_ball : extChartAt I q q ∈ Metric.ball (extChartAt I q q) r₀ := mem_ball_self hr₀_pos
      have h_dist_le : dist (γ t) q ≤ L₀ * ‖g t - g t₀‖ := by
        have h_bi := (h_bilip q ht_ball hq_ball).1
        rwa [(extChartAt I q).left_inv ht_src, (extChartAt I q).left_inv (mem_extChartAt_source q)] at h_bi
      have h_f_sub : f t - f t₀ ≤ dist (γ t) q := by
        dsimp [f, q, p_dom, y₀]
        linarith [dist_triangle (γ t) (γ t₀) (γ 0)]
      have h_slope_f : slope f t₀ t ≤ L₀ * ‖slope g t₀ t‖ := by
        rw [slope_def_field, slope_def_module, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr h_pos.le),
          div_eq_inv_mul]
        calc (t - t₀)⁻¹ * (f t - f t₀) ≤ (t - t₀)⁻¹ * dist (γ t) q :=
              mul_le_mul_of_nonneg_left h_f_sub (inv_nonneg.mpr h_pos.le)
          _ ≤ (t - t₀)⁻¹ * (L₀ * ‖g t - g t₀‖) :=
              mul_le_mul_of_nonneg_left h_dist_le (inv_nonneg.mpr h_pos.le)
          _ = L₀ * ((t - t₀)⁻¹ * ‖g t - g t₀‖) := by ring
      exact lt_of_le_of_lt h_slope_f ht_lt
    have : (𝓝[>] t₀).NeBot := nhdsWithin_Ioi_neBot le_rfl
    exact h_ev_all.frequently

set_option backward.isDefEq.respectTransparency false in
/-- Uniform upper bound on `ClosedTameTarget.metric` across a compact target `M` (`0 sorryAx`). -/
theorem exists_metric_upper_bound [BoundedChartedTarget I M] :
    ∃ C_g : ℝ, 0 ≤ C_g ∧ ∀ (x : M) (v : E),
      ClosedTameTarget.metric I x v v ≤ C_g * ‖v‖ ^ 2 := by
  obtain ⟨r₀, _, C_ω, C_J, hr₀_pos, _, hCω_pos, hCJ_pos, _, _, hω_bdd, hJ_bdd⟩ :=
    BoundedChartedTarget.exists_chart_bounds (I := I) (M := M)
  refine ⟨C_ω * C_J, by positivity, fun x v => ?_⟩
  have hx_ball : extChartAt I x x ∈ Metric.ball (extChartAt I x x) r₀ := mem_ball_self hr₀_pos
  have hω0 := hω_bdd x hx_ball v 0 (Nat.zero_le 3)
  rw [norm_iteratedFDeriv_zero] at hω0
  have h_eq_ω : ω_chart I tgt.«ω» x (extChartAt I x x) v = (tgt.«ω» x : E →L[ℝ] E →L[ℝ] ℝ) v := by
    rw [← omega_eq_chart I x (mem_extChartAt_source x)]
    rfl
  rw [h_eq_ω] at hω0
  have hJ0 := hJ_bdd x hx_ball 0 (Nat.zero_le 3)
  rw [norm_iteratedFDeriv_zero, ← J_eq_chart I x (mem_extChartAt_source x)] at hJ0
  have h_met : ClosedTameTarget.metric I x v v = tgt.«ω» x v (tgt.J x v) := by
    dsimp [ClosedTameTarget.metric]
    ring
  rw [h_met]
  calc tgt.«ω» x v (tgt.J x v)
      ≤ ‖tgt.«ω» x v (tgt.J x v)‖ := le_abs_self _
    _ ≤ ‖(tgt.«ω» x : E →L[ℝ] E →L[ℝ] ℝ) v‖ * ‖(tgt.J x : E →L[ℝ] E) v‖ :=
        ContinuousLinearMap.le_opNorm ((tgt.«ω» x : E →L[ℝ] E →L[ℝ] ℝ) v) _
    _ ≤ (C_ω * ‖v‖) * (C_J * ‖v‖) := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm (tgt.J x : E →L[ℝ] E) v).trans
          (mul_le_mul_of_nonneg_right hJ0 (norm_nonneg v))
    _ = C_ω * C_J * ‖v‖ ^ 2 := by ring

omit [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
/-- Pointwise upper bound on `riemannianEnergyDensity I u z` in terms of `‖mfderiv I_CP1 I u z‖` (`0 sorryAx`). -/
theorem riemannianEnergyDensity_le_of_metric_upper_bound {C_g : ℝ} (hCg_nonneg : 0 ≤ C_g)
    (hCg : ∀ (x : M) (v : E), ClosedTameTarget.metric I x v v ≤ C_g * ‖v‖ ^ 2)
    (u : CP1 → M) (z : CP1) :
    riemannianEnergyDensity I u z ≤
      (1 / 2 : ℝ) * C_g * (‖e1‖ ^ 2 + ‖e2‖ ^ 2) *
        ‖(mfderiv I_CP1 I u z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E)‖ ^ 2 := by
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] E := mfderiv I_CP1 I u z
  have hL_e1 : ‖L e1‖ ≤ ‖L‖ * ‖e1‖ := ContinuousLinearMap.le_opNorm L e1
  have hL_e2 : ‖L e2‖ ≤ ‖L‖ * ‖e2‖ := ContinuousLinearMap.le_opNorm L e2
  have h_met1 : ClosedTameTarget.metric I (u z) (L e1) (L e1) ≤ C_g * (‖L‖ * ‖e1‖) ^ 2 := by
    calc ClosedTameTarget.metric I (u z) (L e1) (L e1)
        ≤ C_g * ‖L e1‖ ^ 2 := hCg (u z) (L e1)
      _ ≤ C_g * (‖L‖ * ‖e1‖) ^ 2 := by gcongr
  have h_met2 : ClosedTameTarget.metric I (u z) (L e2) (L e2) ≤ C_g * (‖L‖ * ‖e2‖) ^ 2 := by
    calc ClosedTameTarget.metric I (u z) (L e2) (L e2)
        ≤ C_g * ‖L e2‖ ^ 2 := hCg (u z) (L e2)
      _ ≤ C_g * (‖L‖ * ‖e2‖) ^ 2 := by gcongr
  change (1 / 2 : ℝ) * (ClosedTameTarget.metric I (u z) (L e1) (L e1) +
                        ClosedTameTarget.metric I (u z) (L e2) (L e2)) ≤ _
  linarith

set_option backward.isDefEq.respectTransparency false in
/-- Every $C^1$ map `u : CP1 → M` on `[BoundedChartedTarget I M]` is locally Lipschitz (`0 sorryAx`). -/
theorem locallyLipschitz_of_contMDiff
    [BoundedChartedTarget I M]
    (u : CP1 → M) (hu : ContMDiff I_CP1 I 1 u) :
    LocallyLipschitz u := by
  obtain ⟨r₀, L₀, _, _, hr₀_pos, hL₀_ge, _, _, _, h_bilip, _, _⟩ :=
    BoundedChartedTarget.exists_chart_bounds (I := I) (M := M)
  have hL₀_pos : 0 < L₀ := lt_of_lt_of_le one_pos hL₀_ge
  intro p
  let ψ := _root_.chartAt (EuclideanSpace ℝ (Fin 2)) p
  let q : M := u p
  let G : EuclideanSpace ℝ (Fin 2) → E := extChartAt I q ∘ u ∘ ψ.symm
  have hψ_zero : ψ p = 0 := UniformNormalChartFamily.cp1_chartAt_apply_self p
  have hG_cdiff : ContDiffAt ℝ 1 G 0 := by
    have h_within := (contMDiffAt_iff.mp (hu p)).2
    have h_eq_G : extChartAt I (u p) ∘ u ∘ (extChartAt I_CP1 p).symm = G := rfl
    have h_eq_zero : extChartAt I_CP1 p p = 0 := hψ_zero
    have h_range : Set.range I_CP1 = Set.univ := range_id
    rw [h_eq_G, h_eq_zero, h_range, contDiffWithinAt_univ] at h_within
    exact h_within
  obtain ⟨K₀, t₀, ht₀, hlip₀⟩ := hG_cdiff.exists_lipschitzOnWith
  have h_nhds_dom : ψ.source ∩ ψ ⁻¹' (t₀ ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ∈ 𝓝 p := by
    refine Filter.inter_mem (ψ.open_source.mem_nhds (mem_chart_source _ p)) ?_
    exact (ψ.continuousOn.continuousAt (ψ.open_source.mem_nhds (mem_chart_source _ p))).preimage_mem_nhds
      (by rw [hψ_zero]; exact Filter.inter_mem ht₀ (Metric.ball_mem_nhds 0 one_pos))
  have h_nhds_tgt : u ⁻¹' ((extChartAt I q).source ∩
      (extChartAt I q) ⁻¹' Metric.ball (extChartAt I q q) r₀) ∈ 𝓝 p := by
    refine (hu p).continuousAt.preimage_mem_nhds ?_
    refine Filter.inter_mem ((isOpen_extChartAt_source q).mem_nhds (mem_extChartAt_source q)) ?_
    exact (continuousAt_extChartAt q).preimage_mem_nhds (Metric.ball_mem_nhds _ hr₀_pos)
  let s : Set CP1 :=
    (ψ.source ∩ ψ ⁻¹' (t₀ ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) ∩
    u ⁻¹' ((extChartAt I q).source ∩ (extChartAt I q) ⁻¹' Metric.ball (extChartAt I q q) r₀)
  let K : NNReal := ⟨2 * L₀ * (K₀ : ℝ), by positivity⟩
  refine ⟨K, s, Filter.inter_mem h_nhds_dom h_nhds_tgt, LipschitzOnWith.of_dist_le_mul fun z₁ hz₁ z₂ hz₂ => ?_⟩
  rcases hz₁ with ⟨⟨hz₁_src, hz₁_t₀, hz₁_ball1⟩, ⟨hu₁_src, hu₁_ball⟩⟩
  rcases hz₂ with ⟨⟨hz₂_src, hz₂_t₀, hz₂_ball1⟩, ⟨hu₂_src, hu₂_ball⟩⟩
  have h_dist_u : dist (u z₁) (u z₂) ≤ L₀ * ‖G (ψ z₁) - G (ψ z₂)‖ := by
    have h_bi := (h_bilip q hu₁_ball hu₂_ball).1
    rw [(extChartAt I q).left_inv hu₁_src, (extChartAt I q).left_inv hu₂_src] at h_bi
    have hG₁ : G (ψ z₁) = extChartAt I q (u z₁) := by
      dsimp [G]; rw [ψ.left_inv hz₁_src]
    have hG₂ : G (ψ z₂) = extChartAt I q (u z₂) := by
      dsimp [G]; rw [ψ.left_inv hz₂_src]
    rwa [hG₁, hG₂]
  have h_dist_G : ‖G (ψ z₁) - G (ψ z₂)‖ ≤ (K₀ : ℝ) * ‖ψ z₁ - ψ z₂‖ := by
    simpa [dist_eq_norm] using hlip₀.dist_le_mul (ψ z₁) hz₁_t₀ (ψ z₂) hz₂_t₀
  have h_dist_ψ : ‖ψ z₁ - ψ z₂‖ ≤ 2 * dist z₁ z₂ := by
    have h_bi := (UniformNormalChartFamily.cp1_dist_symm_bilipschitz p hz₁_ball1 hz₂_ball1).2
    rwa [ψ.left_inv hz₁_src, ψ.left_inv hz₂_src] at h_bi
  calc dist (u z₁) (u z₂)
      ≤ L₀ * ‖G (ψ z₁) - G (ψ z₂)‖ := h_dist_u
    _ ≤ L₀ * ((K₀ : ℝ) * ‖ψ z₁ - ψ z₂‖) := by gcongr
    _ ≤ L₀ * ((K₀ : ℝ) * (2 * dist z₁ z₂)) := by gcongr
    _ = (K : ℝ) * dist z₁ z₂ := by
      change L₀ * ((K₀ : ℝ) * (2 * dist z₁ z₂)) = (2 * L₀ * (K₀ : ℝ)) * dist z₁ z₂
      ring

/-- Every $C^1$ map `u : CP1 → M` on `[BoundedChartedTarget I M]` is globally Lipschitz on `CP1` (`0 sorryAx`). -/
theorem exists_lipschitz_of_contMDiff
    [BoundedChartedTarget I M]
    (u : CP1 → M) (hu : ContMDiff I_CP1 I 1 u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z₁ z₂ : CP1, dist (u z₁) (u z₂) ≤ K * dist z₁ z₂ := by
  have h_loc_on : LocallyLipschitzOn Set.univ u := by
    intro p _
    simpa [nhdsWithin_univ] using locallyLipschitz_of_contMDiff I u hu p
  obtain ⟨K, hK⟩ := h_loc_on.exists_lipschitzOnWith_of_compact isCompact_univ
  exact ⟨(K : ℝ), K.coe_nonneg, fun z₁ z₂ => hK.dist_le_mul z₁ (Set.mem_univ z₁) z₂ (Set.mem_univ z₂)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every $C^1$ map `u : CP1 → M` on `[BoundedChartedTarget I M]` has uniformly bounded manifold
differential `‖mfderiv I_CP1 I u z‖` across all `z ∈ CP1` (`0 sorryAx`). -/
theorem exists_mfderiv_bound_of_contMDiff
    [BoundedChartedTarget I M]
    (u : CP1 → M) (hu : ContMDiff I_CP1 I 1 u) :
    ∃ M_d : ℝ, 0 ≤ M_d ∧ ∀ z : CP1,
      ‖(mfderiv I_CP1 I u z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E)‖ ≤ M_d := by
  obtain ⟨r₀, L₀, _, _, hr₀_pos, hL₀_ge, _, _, _, h_bilip, _, _⟩ :=
    BoundedChartedTarget.exists_chart_bounds (I := I) (M := M)
  have hL₀_pos : 0 < L₀ := lt_of_lt_of_le one_pos hL₀_ge
  obtain ⟨K, hK_nonneg, hK_lip⟩ := exists_lipschitz_of_contMDiff I u hu
  refine ⟨2 * L₀ * K, by positivity, fun z₀ => ?_⟩
  by_cases h_mdiff : MDifferentiableAt I_CP1 I u z₀
  · let ψ₀ := _root_.chartAt (EuclideanSpace ℝ (Fin 2)) z₀
    let q₀ : M := u z₀
    have hψ₀_univ : ψ₀.target = Set.univ := UniformNormalChartFamily.cp1_chartAt_target_univ z₀
    have hψ₀_zero : ψ₀ z₀ = 0 := UniformNormalChartFamily.cp1_chartAt_apply_self z₀
    have hψ₀_symm_zero : ψ₀.symm 0 = z₀ := UniformNormalChartFamily.cp1_chartAt_symm_zero z₀
    have h_mfderiv : (mfderiv I_CP1 I u z₀ : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) =
        fderiv ℝ (extChartAt I q₀ ∘ u ∘ ψ₀.symm) 0 := by
      dsimp [mfderiv]
      rw [if_pos h_mdiff, range_id, fderivWithin_univ]
      change fderiv ℝ (writtenInExtChartAt I_CP1 I z₀ u) (ψ₀ z₀) = _
      rw [hψ₀_zero]
      rfl
    rw [h_mfderiv]
    refine norm_fderiv_le_of_lip' ℝ (by positivity : (0 : ℝ) ≤ 2 * L₀ * K) ?_
    have hψ₀_symm_cont : ContinuousAt ψ₀.symm 0 :=
      ψ₀.continuousOn_symm.continuousAt (by rw [hψ₀_univ]; exact isOpen_univ.mem_nhds (Set.mem_univ 0))
    have hu_cont : ContinuousAt (u ∘ ψ₀.symm) 0 := by
      have h_u0 : ContinuousAt u (ψ₀.symm 0) := by
        rw [hψ₀_symm_zero]
        exact (hu z₀).continuousAt
      exact h_u0.comp hψ₀_symm_cont
    have hq₀_nhds : (extChartAt I q₀).source ∩
        (extChartAt I q₀) ⁻¹' Metric.ball (extChartAt I q₀ q₀) r₀ ∈ 𝓝 (u (ψ₀.symm 0)) := by
      rw [hψ₀_symm_zero]
      refine Filter.inter_mem ((isOpen_extChartAt_source q₀).mem_nhds (mem_extChartAt_source q₀)) ?_
      exact (continuousAt_extChartAt q₀).preimage_mem_nhds (Metric.ball_mem_nhds _ hr₀_pos)
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin 2)) one_pos,
      hu_cont.preimage_mem_nhds hq₀_nhds] with x hx_ball ⟨hx_src, hx_tgt_ball⟩
    change ‖extChartAt I q₀ (u (ψ₀.symm x)) - extChartAt I q₀ (u (ψ₀.symm 0))‖ ≤ (2 * L₀ * K) * ‖x - 0‖
    rw [hψ₀_symm_zero]
    have hq₀_ball : extChartAt I q₀ q₀ ∈ Metric.ball (extChartAt I q₀ q₀) r₀ := mem_ball_self hr₀_pos
    have h_step1 : ‖extChartAt I q₀ (u (ψ₀.symm x)) - extChartAt I q₀ q₀‖ ≤
        L₀ * dist (u (ψ₀.symm x)) q₀ := by
      have h_bi := (h_bilip q₀ hx_tgt_ball hq₀_ball).2
      rwa [(extChartAt I q₀).left_inv hx_src, (extChartAt I q₀).left_inv (mem_extChartAt_source q₀)] at h_bi
    have h_step2 : dist (u (ψ₀.symm x)) q₀ ≤ K * dist (ψ₀.symm x) z₀ :=
      hK_lip (ψ₀.symm x) z₀
    have h_step3 : dist (ψ₀.symm x) z₀ ≤ 2 * ‖x - 0‖ := by
      have h0_ball : (0 : EuclideanSpace ℝ (Fin 2)) ∈ Metric.ball 0 1 := mem_ball_self one_pos
      have h_bi := (UniformNormalChartFamily.cp1_dist_symm_bilipschitz z₀ hx_ball h0_ball).1
      rwa [hψ₀_symm_zero] at h_bi
    calc ‖extChartAt I q₀ (u (ψ₀.symm x)) - extChartAt I q₀ q₀‖
        ≤ L₀ * dist (u (ψ₀.symm x)) q₀ := h_step1
      _ ≤ L₀ * (K * dist (ψ₀.symm x) z₀) := by gcongr
      _ ≤ L₀ * (K * (2 * ‖x - 0‖)) := by gcongr
      _ = (2 * L₀ * K) * ‖x - 0‖ := by ring
  · have h_zero : (mfderiv I_CP1 I u z₀ : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) = 0 := by
      dsimp [mfderiv]; rw [if_neg h_mdiff]
    rw [h_zero, norm_zero]
    positivity

set_option backward.isDefEq.respectTransparency false in
/-- First-principles proof that every $C^1$ map `u : CP1 → M` on `[BoundedChartedTarget I M]`
has globally bounded `riemannianEnergyDensity` (`0 sorryAx`). -/
theorem exists_energyDensity_bound_of_contMDiff
    [BoundedChartedTarget I M]
    (u : CP1 → M) (hu : ContMDiff I_CP1 I 1 u) :
    ∃ C : ℝ, ∀ z : CP1, riemannianEnergyDensity I u z ≤ C := by
  obtain ⟨C_g, hCg_nonneg, hCg⟩ := exists_metric_upper_bound I (M := M)
  obtain ⟨M_d, hMd_nonneg, hMd⟩ := exists_mfderiv_bound_of_contMDiff I u hu
  refine ⟨(1 / 2 : ℝ) * C_g * (‖e1‖ ^ 2 + ‖e2‖ ^ 2) * M_d ^ 2, fun z => ?_⟩
  calc riemannianEnergyDensity I u z
      ≤ (1 / 2 : ℝ) * C_g * (‖e1‖ ^ 2 + ‖e2‖ ^ 2) *
          ‖(mfderiv I_CP1 I u z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E)‖ ^ 2 :=
        riemannianEnergyDensity_le_of_metric_upper_bound I hCg_nonneg hCg u z
    _ ≤ (1 / 2 : ℝ) * C_g * (‖e1‖ ^ 2 + ‖e2‖ ^ 2) * M_d ^ 2 := by
        gcongr
        exact hMd z

/-- Unconditional construction of `EnergyDensityCertificate I u` for any $C^1$ map `u : CP1 → M`
on `[BoundedChartedTarget I M]` (`0 sorryAx`). -/
noncomputable def EnergyDensityCertificate.of_contMDiff
    [BoundedChartedTarget I M]
    (u : CP1 → M) (hu : ContMDiff I_CP1 I 1 u) :
    EnergyDensityCertificate I u :=
  EnergyDensityCertificate.of_exists_le I u (exists_energyDensity_bound_of_contMDiff I u hu)

/-- First-principles unconditional proof of `h_fin` (`energyMeasureExtended I u Set.univ < ⊤`)
for any $C^1$ map `u : CP1 → M` on `[BoundedChartedTarget I M]` (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_contMDiff
    [BoundedChartedTarget I M]
    (u : CP1 → M) (hu : ContMDiff I_CP1 I 1 u) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_certificate I u (EnergyDensityCertificate.of_contMDiff I u hu)

/-- First-principles unconditional proof of `h_fin` (`energyMeasureExtended I u Set.univ < ⊤`)
for any smooth map `u : CP1 → M` on `[BoundedChartedTarget I M]` (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_smooth_uncond
    [BoundedChartedTarget I M]
    (u : CP1 → M) (hu : ContMDiff I_CP1 I ∞ u) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_contMDiff I u (hu.of_le (by decide))

/-- First-principles unconditional proof of `h_fin` (`energyMeasureExtended I u Set.univ < ⊤`)
for any `J`-holomorphic map `u : CP1 → M` on `[BoundedChartedTarget I M]` (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_jhol_uncond
    [BoundedChartedTarget I M]
    (u : CP1 → M) (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_smooth_uncond I u (contMDiffOn_univ.mp hu.1)

/-- First-principles unconditional finiteness `energyMeasureExtended I u s ≠ ⊤` on any measurable
or arbitrary subset `s : Set CP1` for a globally `J`-holomorphic map `u : CP1 → M` on
`[BoundedChartedTarget I M]` (`0 sorryAx`). -/
theorem energyMeasureExtended_ne_top_of_jhol_uncond
    [BoundedChartedTarget I M]
    (u : CP1 → M) (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) (s : Set CP1) :
    energyMeasureExtended I u s ≠ ⊤ :=
  ne_top_of_le_ne_top (energyMeasureExtended_lt_top_of_jhol_uncond I u hu).ne
    (MeasureTheory.measure_mono (Set.subset_univ s))

/-- First-principles derivation of `CylinderEnergyDecayProperty I M` (`cert_decay` / Contract A10)
from single-step collar Widman hole-filling on `[BoundedChartedTarget I M]`, discharging annular
energy finiteness automatically via `energyMeasureExtended_ne_top_of_jhol_uncond` (`0 sorryAx`). -/
theorem cylinderEnergyDecayProperty_of_collar_hole_filling_uncond
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
  Analysis.cylinderEnergyDecayProperty_of_collar_hole_filling I M hK hε
    (fun u center r R _ _ hu _ => energyMeasureExtended_ne_top_of_jhol_uncond I u hu (annulus_at center r R))
    h_collar

/-- First-principles derivation of Contract A10 (`cylinder_exponential_decay`) from single-step
collar Widman hole-filling on `[BoundedChartedTarget I M]` (`0 sorryAx`). -/
theorem cylinder_exponential_decay_of_collar_hole_filling_uncond
    [BoundedChartedTarget I M]
    {K ε_neck : ℝ} (hK : 0 < K) (hε : 0 < ε_neck)
    (h_collar : ∀ (u : CP1 → M) (center : ℂ) (r' R' : ℝ),
      0 < r' → 4 * r' < R' →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r' R') < ε_neck →
      energyMeasure I u (annulus_at center (2 * r') (R' / 2)) ≤
        K * (energyMeasure I u (annulus_at center r' (2 * r')) +
             energyMeasure I u (annulus_at center (R' / 2) R'))) :
    ∃ (C₀ a_decay ε_neck' : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck' ∧
    ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck' →
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          C₀ * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R) :=
  Analysis.cylinder_exponential_decay_of_collar_hole_filling I M hK hε
    (fun u center r R _ _ hu _ => energyMeasureExtended_ne_top_of_jhol_uncond I u hu (annulus_at center r R))
    h_collar

/-- First-principles derivation of `CollarOscillationProperty I M` (`cert_osc` / Contract A09)
from bounded-modulus (`R ≤ 18 * r`) radial/angular slice bounds and single-step collar Widman
hole-filling on `[BoundedChartedTarget I M]`, discharging annular energy finiteness automatically
via `energyMeasureExtended_ne_top_of_jhol_uncond` (`0 sorryAx`). -/
theorem collarOscillationProperty_of_slices_and_collar_hole_filling_uncond
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
  Analysis.collarOscillationProperty_of_slices_and_collar_hole_filling I M h_slices hK hε
    (fun u center r R _ _ hu _ => energyMeasureExtended_ne_top_of_jhol_uncond I u hu (annulus_at center r R))
    h_collar

omit [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
/-- Because `RiemannDomain.j z = J_CP1` is constant on `CP1` and `ClosedTameTarget.J` is globally
continuous (`continuous_J_global`), any map `u_ext : CP1 → M` continuous at `p` whose directional
manifold derivatives `z ↦ (mfderiv I_CP1 I u_ext z w : E)` are continuous at `p` automatically has
a continuous Cauchy–Riemann defect at `p` (`0 sorryAx`). -/
theorem continuousAt_cr_defect_of_continuousAt_mfderiv
    (u_ext : CP1 → M) (p : CP1)
    (hu_cont : ContinuousAt u_ext p)
    (hd_cont : ∀ w : EuclideanSpace ℝ (Fin 2),
      ContinuousAt (fun z : CP1 => (mfderiv I_CP1 I u_ext z w : E)) p)
    (v : TangentSpace I_CP1 p) :
    ContinuousAt (fun z : CP1 =>
      mfderiv I_CP1 I u_ext z (RiemannDomain.j z v) -
        (ClosedTameTarget.J (I := I) (u_ext z)) (mfderiv I_CP1 I u_ext z v)) p := by
  have h1 : ContinuousAt (fun z : CP1 =>
      (mfderiv I_CP1 I u_ext z (J_CP1 v) : E)) p :=
    hd_cont (J_CP1 v)
  have hJ : ContinuousAt (fun z : CP1 => id (α := E →L[ℝ] E) (tgt.J (u_ext z))) p :=
    (continuous_J_global I).continuousAt.comp hu_cont
  have h2 : ContinuousAt (fun z : CP1 =>
      (tgt.J (u_ext z) : E →L[ℝ] E) (mfderiv I_CP1 I u_ext z v : E)) p :=
    hJ.clm_apply (hd_cont v)
  exact h1.sub h2

omit [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
/-- Single-point criterion at `p` for `WeakJHolomorphicOn I (Function.update u p m_star) Set.univ`:
if `u` is `J`-holomorphic on `punctured_sphere {p}`, `Function.update u p m_star` is $C^1$ at `p`,
and its directional manifold derivatives `mfderiv I_CP1 I (Function.update u p m_star) · w` are
continuous at `p`, then `Function.update u p m_star` is globally `WeakJHolomorphicOn` on `CP1` (`0 sorryAx`). -/
theorem weakJHolomorphicOn_univ_of_contMDiffAt_and_continuousAt_mfderiv_at_puncture
    (u : CP1 → M) (p : CP1) (m_star : M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_at : ContMDiffAt I_CP1 I 1 (Function.update u p m_star) p)
    (hd_cont : ∀ w : EuclideanSpace ℝ (Fin 2),
      ContinuousAt (fun z : CP1 =>
        (mfderiv I_CP1 I (Function.update u p m_star) z w : E)) p) :
    Analysis.WeakJHolomorphicOn I (Function.update u p m_star) Set.univ :=
  Analysis.weakJHolomorphicOn_univ_of_c1_and_continuousAt_cr_at_puncture
    I u (Function.update u p m_star) p
    (Analysis.contMDiffOn_one_update_of_contMDiffAt_puncture I u p m_star hu h_at)
    (Analysis.eqOn_update_punctured_sphere u p m_star) hu
    (continuousAt_cr_defect_of_continuousAt_mfderiv I (Function.update u p m_star) p
      h_at.continuousAt hd_cont)

omit [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
/-- First-principles proof of `SatisfiesPunctureSobolevExtension I u p` (`cert_punc`) from
bounded-modulus (`R ≤ 18 * r`) radial/angular slice bounds, local exponential cylinder energy decay,
and single-point $C^1$ / `mfderiv` continuity at the puncture limit `m_star` (`0 sorryAx`). -/
theorem satisfiesPunctureSobolevExtension_of_slices_and_decay_and_mfderiv
    (h_slices : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
      ∀ (u' : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at a r R) →
        energyMeasure I u' (annulus_at a r R) < ε_ring →
        ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
          ∃ z_mid : CP1,
            dist (u' z₁) (u' z_mid) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u' (annulus_at a r R)) ∧
            dist (u' z_mid) (u' z₂) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u' (annulus_at a r R)))
    (h_decay : ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
      ∀ (u' : CP1 → M) (center : ℂ) (r R : ℝ),
        0 < r → 2 * r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at center r R) →
        energyMeasure I u' (annulus_at center r R) < ε_neck →
        Analysis.SatisfiesCylinderEnergyDecayWith I C₀ a_decay u' center r R)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (he : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_c1 : ∀ m_star : M, Filter.Tendsto u (𝓝[≠] p) (𝓝 m_star) →
      ContMDiffAt I_CP1 I 1 (Function.update u p m_star) p ∧
      ∀ w : EuclideanSpace ℝ (Fin 2),
        ContinuousAt (fun z : CP1 =>
          (mfderiv I_CP1 I (Function.update u p m_star) z w : E)) p) :
    Analysis.SatisfiesPunctureSobolevExtension I u p :=
  Analysis.satisfiesPunctureSobolevExtension_of_slices_and_decay_and_c1 I h_slices h_decay u p hu he
    (fun m_star hm_star => by
      obtain ⟨h_at, hd_cont⟩ := h_c1 m_star hm_star
      exact ⟨h_at, continuousAt_cr_defect_of_continuousAt_mfderiv I
        (Function.update u p m_star) p h_at.continuousAt hd_cont⟩)

omit [I.Boundaryless] in
/-- First-principles proof of `Analysis.WeitzenbockDecompositionProperty I M` (`cert_weitz`) on
`[FiniteDimensional ℝ E]` `[Nonempty M]` from the centered normal-chart Weitzenböck remainder
bound `|rem| ≤ |K_tensor g J v|`, discharging uniform metric coercivity automatically via
`exists_metric_coercive I` (`0 sorryAx`). -/
theorem weitzenbockDecompositionProperty_of_normal_chart_weitz_uncond
    [FiniteDimensional ℝ E] [Nonempty M]
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
    Analysis.WeitzenbockDecompositionProperty I M := by
  obtain ⟨c_min, hc_min_pos, hc_coercive⟩ := exists_metric_coercive I (M := M)
  exact Analysis.weitzenbockDecompositionProperty_of_normal_chart_weitz I M
    hc_min_pos hCm hCJ (h_norm_weitz hc_min_pos hc_coercive)

omit [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
/-- Contract A12 (`removal_of_singularities`) proved from bounded-modulus (`R ≤ 18 * r`)
radial/angular slice bounds, local exponential cylinder energy decay, single-point $C^1$ / `mfderiv`
continuity at `p`, and the chart-level elliptic step (`0 sorryAx`). -/
theorem removal_of_singularities_of_slices_and_decay_and_mfderiv_and_chart_step
    (h_slices : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
      ∀ (u' : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at a r R) →
        energyMeasure I u' (annulus_at a r R) < ε_ring →
        ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
          ∃ z_mid : CP1,
            dist (u' z₁) (u' z_mid) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u' (annulus_at a r R)) ∧
            dist (u' z_mid) (u' z₂) ≤ (C_ring / 2) * Real.sqrt (energyMeasure I u' (annulus_at a r R)))
    (h_decay : ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
      ∀ (u' : CP1 → M) (center : ℂ) (r R : ℝ),
        0 < r → 2 * r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at center r R) →
        energyMeasure I u' (annulus_at center r R) < ε_neck →
        Analysis.SatisfiesCylinderEnergyDecayWith I C₀ a_decay u' center r R)
    (h_chart_step : ∀ (u' : CP1 → M) (Ω : Set CP1), IsOpen Ω → Analysis.WeakJHolomorphicOn I u' Ω →
      ∀ (k : ℕ), 1 ≤ k → ∀ z ∈ Ω,
        ContDiffAt ℝ (k : WithTop ℕ∞) (writtenInExtChartAt I_CP1 I z u') ((extChartAt I_CP1 z) z) →
        ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (writtenInExtChartAt I_CP1 I z u') ((extChartAt I_CP1 z) z))
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (he : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤)
    (h_c1 : ∀ m_star : M, Filter.Tendsto u (𝓝[≠] p) (𝓝 m_star) →
      ContMDiffAt I_CP1 I 1 (Function.update u p m_star) p ∧
      ∀ w : EuclideanSpace ℝ (Fin 2),
        ContinuousAt (fun z : CP1 =>
          (mfderiv I_CP1 I (Function.update u p m_star) z w : E)) p) :
    ∃! (u_smooth : CP1 → M),
      Set.EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  Analysis.removal_of_singularities I u p hu he
    (satisfiesPunctureSobolevExtension_of_slices_and_decay_and_mfderiv I h_slices h_decay u p hu he h_c1)
    (fun u_ext hu_weak n =>
      Analysis.regularityTowerProperty_of_chart_step I M h_chart_step u_ext Set.univ isOpen_univ hu_weak n)

omit [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
/-- First-principles proof that vanishing `riemannianEnergyDensity I u z` forces the manifold
differential `mfderiv I_CP1 I u z` to vanish (`0 sorryAx`). -/
theorem mfderiv_eq_zero_of_riemannianEnergyDensity_eq_zero
    [FiniteDimensional ℝ E] (u : CP1 → M) (z : CP1)
    (he : riemannianEnergyDensity I u z = 0) :
    mfderiv I_CP1 I u z = 0 := by
  have : Nonempty M := ⟨u z⟩
  obtain ⟨c_min, hc_min_pos, hc_coercive⟩ := exists_metric_coercive I (M := M)
  have h_norm := norm_mfderiv_le_of_coercive I hc_min_pos hc_coercive u z
  rw [he, mul_zero, zero_div, Real.sqrt_zero, mul_zero] at h_norm
  exact norm_le_zero_iff.mp h_norm

set_option backward.isDefEq.respectTransparency false in
/-- First-principles proof of local constancy on an open connected domain `Ω ⊆ CP1` for any $C^1$
map `u : CP1 → M` whose `riemannianEnergyDensity` vanishes on `Ω` (`0 sorryAx`). -/
theorem eqOn_const_of_riemannianEnergyDensity_eq_zero_on
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (u : CP1 → M) {Ω : Set CP1} (h_open : IsOpen Ω) (h_conn : IsConnected Ω)
    (h_c1 : ContMDiffOn I_CP1 I 1 u Ω)
    (h_zero : ∀ z ∈ Ω, riemannianEnergyDensity I u z = 0) :
    ∃ c : M, EqOn u (fun _ => c) Ω := by
  obtain ⟨c_min, hc_min_pos, hc_coercive⟩ := exists_metric_coercive I (M := M)
  obtain ⟨r₀, L₀, _, _, hr₀_pos, hL₀_ge, _, _, _, h_bilip, _, _⟩ :=
    BoundedChartedTarget.exists_chart_bounds (I := I) (M := M)
  have h_loc_const : IsLocallyConstant (Ω.domRestrict u) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨z₀, hz₀⟩
    let ψ := _root_.chartAt (EuclideanSpace ℝ (Fin 2)) z₀
    have hψ_univ : ψ.target = Set.univ := UniformNormalChartFamily.cp1_chartAt_target_univ z₀
    have hψ_zero : ψ z₀ = 0 := UniformNormalChartFamily.cp1_chartAt_apply_self z₀
    have hψ_symm_zero : ψ.symm 0 = z₀ := UniformNormalChartFamily.cp1_chartAt_symm_zero z₀
    have hψ_symm_cont : Continuous ψ.symm := by
      rw [← continuousOn_univ, ← hψ_univ]
      exact ψ.continuousOn_symm
    have h_pre_open : IsOpen (ψ.symm ⁻¹' Ω) := h_open.preimage hψ_symm_cont
    have h_zero_mem_pre : (0 : EuclideanSpace ℝ (Fin 2)) ∈ ψ.symm ⁻¹' Ω := by
      simp [Set.mem_preimage, hψ_symm_zero, hz₀]
    obtain ⟨r₁, hr₁_pos, hr₁_sub⟩ := Metric.isOpen_iff.mp h_pre_open 0 h_zero_mem_pre
    let r_dom : ℝ := min (r₁ / 2) (1 / 2)
    have hr_dom_pos : 0 < r_dom := lt_min (half_pos hr₁_pos) (by norm_num)
    have hr_dom_lt_one : r_dom < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have h_cball_sub_pre : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r_dom ⊆ ψ.symm ⁻¹' Ω := by
      intro y hy
      apply hr₁_sub
      rw [Metric.mem_ball, dist_zero_right]
      have hy' : ‖y‖ ≤ r_dom := mem_closedBall_zero_iff.mp hy
      have hr_le : r_dom ≤ r₁ / 2 := min_le_left _ _
      linarith
    let K : Set CP1 := ψ.symm '' Metric.closedBall 0 r_dom
    have hK_sub : K ⊆ Ω := image_subset_iff.mpr h_cball_sub_pre
    have h_nhds_z₀ : ψ.source ∩ ψ ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r_dom ∈ 𝓝 z₀ := by
      refine Filter.inter_mem (ψ.open_source.mem_nhds (mem_chart_source _ z₀)) ?_
      exact (ψ.continuousOn.continuousAt (ψ.open_source.mem_nhds (mem_chart_source _ z₀))).preimage_mem_nhds
        (by rw [hψ_zero]; exact Metric.ball_mem_nhds 0 hr_dom_pos)
    obtain ⟨ρ, hρ_pos, hρ_sub⟩ := Metric.mem_nhds_iff.mp h_nhds_z₀
    have h_sub_nhds : {x : Ω | (x : CP1) ∈ Metric.ball z₀ ρ} ∈ 𝓝 (⟨z₀, hz₀⟩ : Ω) :=
      (continuous_subtype_val.tendsto _).eventually (Metric.ball_mem_nhds z₀ hρ_pos)
    filter_upwards [h_sub_nhds] with ⟨z, hz_Ω⟩ hz
    change u z = u z₀
    rcases hρ_sub hz with ⟨hz_src, hz_ball⟩
    let w : EuclideanSpace ℝ (Fin 2) := ψ z
    have hw_symm : ψ.symm w = z := ψ.left_inv hz_src
    have hw_norm_lt : ‖w‖ < r_dom := mem_ball_zero_iff.mp hz_ball
    let γ : ℝ → M := fun t => u (ψ.symm (t • w))
    let f : ℝ → ℝ := fun t => dist (γ t) (γ 0)
    let B : ℝ → ℝ := fun _ => 0
    let B' : ℝ → ℝ := fun _ => 0
    have h_seg_mem_cball : ∀ t ∈ Icc (0 : ℝ) 1, t • w ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r_dom := by
      intro t ht
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht.1]
      calc t * ‖w‖ ≤ 1 * r_dom := mul_le_mul ht.2 (le_of_lt hw_norm_lt) (norm_nonneg w) zero_le_one
        _ = r_dom := one_mul r_dom
    have h_seg_mem_K : ∀ t ∈ Icc (0 : ℝ) 1, ψ.symm (t • w) ∈ K :=
      fun t ht => mem_image_of_mem ψ.symm (h_seg_mem_cball t ht)
    have hγ_cont : ContinuousOn γ (Icc 0 1) := by
      refine h_c1.continuousOn.comp ?_ (fun t ht => hK_sub (h_seg_mem_K t ht))
      exact hψ_symm_cont.comp_continuousOn (continuousOn_id.smul continuousOn_const)
    have hf_cont : ContinuousOn f (Icc 0 1) :=
      Continuous.comp_continuousOn (continuous_id.dist continuous_const) hγ_cont
    have ha : f 0 ≤ B 0 := by simp [f, B]
    have hB_cont : ContinuousOn B (Icc 0 1) := continuousOn_const
    have hB_deriv : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt B (B' t) (Ici t) t :=
      fun t _ => hasDerivWithinAt_const t (Ici t) 0
    have h_fencing := image_le_of_liminf_slope_right_le_deriv_boundary hf_cont ha hB_cont hB_deriv ?_
    · have h1 := h_fencing (right_mem_Icc.mpr zero_le_one)
      have hf1 : f 1 = dist (u z) (u z₀) := by
        dsimp [f, γ]
        rw [one_smul, zero_smul, hw_symm, hψ_symm_zero]
      rw [hf1] at h1
      exact dist_le_zero.mp h1
    · intro t₀ ht₀ r hr
      let y₀ : EuclideanSpace ℝ (Fin 2) := t₀ • w
      let p_dom : CP1 := ψ.symm y₀
      let q : M := u p_dom
      have ht₀_Icc : t₀ ∈ Icc (0 : ℝ) 1 := ⟨ht₀.1, le_of_lt ht₀.2⟩
      have hp_dom_K : p_dom ∈ K := h_seg_mem_K t₀ ht₀_Icc
      have hp_dom_Ω : p_dom ∈ Ω := hK_sub hp_dom_K
      have h_d1 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1 ψ.symm y₀
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1 ψ.symm y₀) := by
        have h_cont : ContMDiffOn I_CP1 I_CP1 ⊤ ψ.symm ψ.target := contMDiffOn_chart_symm
        rw [hψ_univ] at h_cont
        exact ((h_cont y₀ (Set.mem_univ y₀)).mdifferentiableWithinAt (by decide)
          |>.mdifferentiableAt (isOpen_univ.mem_nhds (Set.mem_univ y₀))).hasMFDerivAt
      have h_d2 : HasMFDerivAt I_CP1 I u p_dom (mfderiv I_CP1 I u p_dom) :=
        ((h_c1 p_dom hp_dom_Ω).mdifferentiableWithinAt one_ne_zero
          |>.mdifferentiableAt (h_open.mem_nhds hp_dom_Ω)).hasMFDerivAt
      have h_d3 : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I q) q (mfderiv I 𝓘(ℝ, E) (extChartAt I q) q) :=
        (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H q)).hasMFDerivAt
      let D_y₀ : EuclideanSpace ℝ (Fin 2) →L[ℝ] E :=
        (mfderiv I 𝓘(ℝ, E) (extChartAt I q) q).comp
          ((mfderiv I_CP1 I u p_dom).comp
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) I_CP1 ψ.symm y₀))
      have h_G_fderiv : HasFDerivAt (extChartAt I q ∘ u ∘ ψ.symm) D_y₀ y₀ :=
        ((h_d3.comp p_dom h_d2).comp y₀ h_d1).hasFDerivAt
      let g : ℝ → E := fun t => (extChartAt I q ∘ u ∘ ψ.symm) (t • w)
      have h_seg_deriv : HasDerivAt (fun t : ℝ => t • w) w t₀ := by
        simpa using (hasDerivAt_id t₀).smul_const w
      have hg_deriv : HasDerivAt g (D_y₀ w) t₀ := h_G_fderiv.comp_hasDerivAt t₀ h_seg_deriv
      have h_D_zero : D_y₀ w = 0 := by
        have h_u_zero : mfderiv I_CP1 I u p_dom = 0 :=
          mfderiv_eq_zero_of_riemannianEnergyDensity_eq_zero I u p_dom (h_zero p_dom hp_dom_Ω)
        dsimp [D_y₀]
        rw [h_u_zero]
        simp
      have h_tendsto_slope : Filter.Tendsto (fun t => L₀ * ‖slope g t₀ t‖) (𝓝[>] t₀) (𝓝 0) := by
        have h_t := ((hg_deriv.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t₀)).norm).const_mul L₀
        rwa [h_D_zero, norm_zero, mul_zero] at h_t
      have hr_pos : 0 < r := hr
      have h_ev_lt : ∀ᶠ t in 𝓝[>] t₀, L₀ * ‖slope g t₀ t‖ < r :=
        h_tendsto_slope.eventually (gt_mem_nhds hr_pos)
      have hγ_cont_at : ContinuousAt γ t₀ := by
        have h_u_cont : ContinuousAt u p_dom :=
          (h_c1 p_dom hp_dom_Ω).continuousWithinAt.continuousAt (h_open.mem_nhds hp_dom_Ω)
        exact h_u_cont.comp (hψ_symm_cont.continuousAt.comp (continuous_id.smul continuous_const).continuousAt)
      have hq_nhds : (extChartAt I q).source ∩
          (extChartAt I q) ⁻¹' Metric.ball (extChartAt I q q) r₀ ∈ 𝓝 q := by
        refine Filter.inter_mem ((isOpen_extChartAt_source q).mem_nhds (mem_extChartAt_source q)) ?_
        exact (continuousAt_extChartAt q).preimage_mem_nhds (Metric.ball_mem_nhds _ hr₀_pos)
      have h_ev_chart : ∀ᶠ t in 𝓝[>] t₀,
          γ t ∈ (extChartAt I q).source ∧ extChartAt I q (γ t) ∈ Metric.ball (extChartAt I q q) r₀ :=
        nhdsWithin_le_nhds (hγ_cont_at.preimage_mem_nhds hq_nhds)
      have h_ev_gt : ∀ᶠ t in 𝓝[>] t₀, t₀ < t := self_mem_nhdsWithin
      have h_ev_all : ∀ᶠ t in 𝓝[>] t₀, slope f t₀ t < r := by
        filter_upwards [h_ev_lt, h_ev_chart, h_ev_gt] with t ht_lt ⟨ht_src, ht_ball⟩ ht_gt
        have h_pos : 0 < t - t₀ := sub_pos.mpr ht_gt
        have hq_ball : extChartAt I q q ∈ Metric.ball (extChartAt I q q) r₀ := mem_ball_self hr₀_pos
        have h_dist_le : dist (γ t) q ≤ L₀ * ‖g t - g t₀‖ := by
          have h_bi := (h_bilip q ht_ball hq_ball).1
          rwa [(extChartAt I q).left_inv ht_src, (extChartAt I q).left_inv (mem_extChartAt_source q)] at h_bi
        have h_f_sub : f t - f t₀ ≤ dist (γ t) q := by
          dsimp [f, q, p_dom, y₀]
          linarith [dist_triangle (γ t) (γ t₀) (γ 0)]
        have h_slope_f : slope f t₀ t ≤ L₀ * ‖slope g t₀ t‖ := by
          rw [slope_def_field, slope_def_module, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr h_pos.le),
            div_eq_inv_mul]
          calc (t - t₀)⁻¹ * (f t - f t₀) ≤ (t - t₀)⁻¹ * dist (γ t) q :=
                mul_le_mul_of_nonneg_left h_f_sub (inv_nonneg.mpr h_pos.le)
            _ ≤ (t - t₀)⁻¹ * (L₀ * ‖g t - g t₀‖) :=
                mul_le_mul_of_nonneg_left h_dist_le (inv_nonneg.mpr h_pos.le)
            _ = L₀ * ((t - t₀)⁻¹ * ‖g t - g t₀‖) := by ring
        exact lt_of_le_of_lt h_slope_f ht_lt
      have : (𝓝[>] t₀).NeBot := nhdsWithin_Ioi_neBot le_rfl
      exact h_ev_all.frequently
  have : PreconnectedSpace Ω := Subtype.preconnectedSpace h_conn.isPreconnected
  obtain ⟨z₀, hz₀⟩ := h_conn.nonempty
  refine ⟨u z₀, fun z hz => ?_⟩
  exact h_loc_const.apply_eq_of_preconnectedSpace ⟨z, hz⟩ ⟨z₀, hz₀⟩

/-- First-principles proof that any $C^1$ map `u : CP1 → M` whose `riemannianEnergyDensity`
vanishes on `ℂ` (via `stereo_chart.symm`) is globally constant on `CP1` (`0 sorryAx`). -/
theorem eq_const_of_riemannianEnergyDensity_stereo_eq_zero
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (u : CP1 → M) (h_c1 : ContMDiffOn I_CP1 I 1 u Set.univ)
    (h_zero : ∀ w : ℂ, riemannianEnergyDensity I u (stereo_chart.symm w) = 0) :
    ∃ c : M, ∀ z : CP1, u z = c := by
  have h_zero_punc : ∀ z ∈ punctured_sphere {north_pole}, riemannianEnergyDensity I u z = 0 := by
    intro z hz
    rw [Analysis.punctured_sphere_singleton_eq_compl, Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    have hz_src : z ∈ stereo_chart.source := by
      rw [stereo_chart_source]
      exact hz
    have h_eq := stereo_chart.left_inv hz_src
    rw [← h_eq]
    exact h_zero (stereo_chart z)
  obtain ⟨c, hc⟩ := eqOn_const_of_riemannianEnergyDensity_eq_zero_on I u
    (Analysis.isOpen_punctured_sphere north_pole)
    (Analysis.isConnected_punctured_sphere_singleton north_pole)
    (h_c1.mono (Set.subset_univ _))
    h_zero_punc
  refine ⟨c, ?_⟩
  have hu_cont : Continuous u := continuousOn_univ.mp h_c1.continuousOn
  have h_ext : u = fun _ => c :=
    Continuous.ext_on (Analysis.dense_punctured_sphere north_pole) hu_cont continuous_const hc
  intro z
  exact congr_fun h_ext z

/-- First-principles theorem: if `u : CP1 → M` is $C^1$, has continuous chart energy density
`w ↦ riemannianEnergyDensity I u (stereo_chart.symm w)`, and has `totalEnergy I u = 0`, then
`u` is constant (`0 sorryAx`, discharging `energyMeasureExtended I u Set.univ < ⊤` automatically
via `energyMeasureExtended_lt_top_of_contMDiff`). -/
theorem eq_const_of_totalEnergy_eq_zero_uncond
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (u : CP1 → M) (h_c1 : ContMDiffOn I_CP1 I 1 u Set.univ)
    (h_cont_ed : Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))
    (h_zero_en : totalEnergy I u = 0) :
    ∃ c : M, ∀ z : CP1, u z = c := by
  have h_fin : energyMeasureExtended I u Set.univ < ⊤ :=
    energyMeasureExtended_lt_top_of_contMDiff I u (contMDiffOn_univ.mp h_c1)
  apply eq_const_of_riemannianEnergyDensity_stereo_eq_zero I u h_c1
  intro w₀
  by_contra h_ne
  have h_pos : 0 < riemannianEnergyDensity I u (stereo_chart.symm w₀) :=
    lt_of_le_of_ne (riemannianEnergyDensity_nonneg I u _) (Ne.symm h_ne)
  let c₀ := riemannianEnergyDensity I u (stereo_chart.symm w₀) / 2
  have hc₀_pos : 0 < c₀ := half_pos h_pos
  have h_open : IsOpen {w : ℂ | c₀ < riemannianEnergyDensity I u (stereo_chart.symm w)} :=
    isOpen_Ioi.preimage h_cont_ed
  have hw₀_mem : w₀ ∈ {w : ℂ | c₀ < riemannianEnergyDensity I u (stereo_chart.symm w)} := by
    dsimp [c₀]; linarith
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp h_open w₀ hw₀_mem
  have h_tot_pos : 0 < totalEnergy I u :=
    totalEnergy_pos_of_exists_ball I u w₀ r hr_pos c₀ hc₀_pos
      (fun w hw => le_of_lt (show c₀ < riemannianEnergyDensity I u (stereo_chart.symm w) from hr_sub hw))
      h_fin
  linarith

/-- First-principles theorem: if `u : CP1 → M` is $C^1$, has continuous chart energy density
`w ↦ riemannianEnergyDensity I u (stereo_chart.symm w)`, and has `totalEnergy I u = 0`, then
`u` is constant (`0 sorryAx`). -/
theorem eq_const_of_totalEnergy_eq_zero
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (u : CP1 → M) (h_c1 : ContMDiffOn I_CP1 I 1 u Set.univ)
    (h_cont_ed : Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))
    (_h_fin : energyMeasureExtended I u Set.univ < ⊤)
    (h_zero_en : totalEnergy I u = 0) :
    ∃ c : M, ∀ z : CP1, u z = c :=
  eq_const_of_totalEnergy_eq_zero_uncond I u h_c1 h_cont_ed h_zero_en

/-- First-principles theorem: every non-constant $C^1$ map `u : CP1 → M` with continuous chart
energy density has strictly positive `totalEnergy I u > 0` (`0 sorryAx`, discharging `h_fin`
automatically via `energyMeasureExtended_lt_top_of_contMDiff`). -/
theorem totalEnergy_pos_of_nonconstant_uncond
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (u : CP1 → M) (h_c1 : ContMDiffOn I_CP1 I 1 u Set.univ)
    (h_cont_ed : Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))
    (h_nonconst : ¬ ∃ c : M, ∀ z : CP1, u z = c) :
    0 < totalEnergy I u := by
  have h_nonneg : 0 ≤ totalEnergy I u := energy_nonneg I u Set.univ
  rcases eq_or_lt_of_le h_nonneg with h_zero | h_pos
  · exfalso
    exact h_nonconst (eq_const_of_totalEnergy_eq_zero_uncond I u h_c1 h_cont_ed h_zero.symm)
  · exact h_pos

/-- First-principles theorem: every non-constant $C^1$ map `u : CP1 → M` with continuous chart
energy density and finite energy has strictly positive `totalEnergy I u > 0` (`0 sorryAx`). -/
theorem totalEnergy_pos_of_nonconstant
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (u : CP1 → M) (h_c1 : ContMDiffOn I_CP1 I 1 u Set.univ)
    (h_cont_ed : Continuous (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))
    (_h_fin : energyMeasureExtended I u Set.univ < ⊤)
    (h_nonconst : ¬ ∃ c : M, ∀ z : CP1, u z = c) :
    0 < totalEnergy I u :=
  totalEnergy_pos_of_nonconstant_uncond I u h_c1 h_cont_ed h_nonconst

/- =========================================================================
   First-Principles Construction of UniformNormalChartFamily
   ========================================================================= -/

section ConstructUniformNormalChartFamily

open ContinuousLinearMap
open scoped NNReal

omit [I.Boundaryless] in
lemma smooth_ω_apply (p : M) (v : E) :
    ContDiffOn ℝ ∞ (fun z => ω_chart I tgt.«ω» p z v) (extChartAt I p).target :=
  (tgt.ω_smooth p).clm_apply contDiffOn_const

omit [I.Boundaryless] in
lemma smooth_J_apply (p : M) (v : E) :
    ContDiffOn ℝ ∞ (fun z => J_chart I tgt.J p z v) (extChartAt I p).target :=
  (tgt.J_smooth p).clm_apply contDiffOn_const

omit [I.Boundaryless] in
lemma smooth_metric_apply (p : M) (v w : E) :
    ContDiffOn ℝ ∞ (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w)
      (extChartAt I p).target :=
  contDiffOn_const.mul
    (((smooth_ω_apply I p v).clm_apply (smooth_J_apply I p w)).add
      ((smooth_ω_apply I p w).clm_apply (smooth_J_apply I p v)))

lemma differentiableAt_metric_apply (p : M) (v w : E) :
    DifferentiableAt ℝ (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w)
      (extChartAt I p p) := by
  have h_mem : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source (mem_extChartAt_source p)
  exact ((smooth_metric_apply I p v w).contDiffAt
    ((isOpen_extChartAt_target p).mem_nhds h_mem)).differentiableAt (by decide)

set_option backward.isDefEq.respectTransparency false in
/-- The directional derivative of the symmetrized metric in `extChartAt I p` at `y₀ = extChartAt I p p`,
bundled as a trilinear map `E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ`. -/
noncomputable def dmetricAt [FiniteDimensional ℝ E] (p : M) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => LinearMap.toContinuousLinearMap
        { toFun := fun v => LinearMap.toContinuousLinearMap
            { toFun := fun w =>
                fderiv ℝ (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w)
                  (extChartAt I p p) u
              map_add' := fun w₁ w₂ => by
                have h_eq : (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v (w₁ + w₂)) =
                    ((fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w₁) +
                    (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w₂)) := by
                  ext z; exact map_add (metricCLM I ((extChartAt I p).symm z) v) w₁ w₂
                rw [h_eq, ((differentiableAt_metric_apply I p v w₁).hasFDerivAt.add
                  (differentiableAt_metric_apply I p v w₂).hasFDerivAt).fderiv,
                  add_apply]
              map_smul' := fun c w => by
                have h_eq : (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v (c • w)) =
                    c • (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w) := by
                  ext z; exact map_smul (metricCLM I ((extChartAt I p).symm z) v) c w
                rw [h_eq, ((differentiableAt_metric_apply I p v w).hasFDerivAt.const_smul c).fderiv,
                  smul_apply, RingHom.id_apply] }
          map_add' := fun v₁ v₂ => by
            ext w
            change fderiv ℝ (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) (v₁ + v₂) w)
                (extChartAt I p p) u =
              fderiv ℝ (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v₁ w)
                (extChartAt I p p) u +
              fderiv ℝ (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v₂ w)
                (extChartAt I p p) u
            have h_eq : (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) (v₁ + v₂) w) =
                ((fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v₁ w) +
                (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v₂ w)) := by
              ext z; simp [← metricCLM_apply]
            rw [h_eq, ((differentiableAt_metric_apply I p v₁ w).hasFDerivAt.add
              (differentiableAt_metric_apply I p v₂ w).hasFDerivAt).fderiv,
              add_apply]
          map_smul' := fun c v => by
            ext w
            change fderiv ℝ (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) (c • v) w)
                (extChartAt I p p) u =
              c * fderiv ℝ (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w)
                (extChartAt I p p) u
            have h_eq : (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) (c • v) w) =
                c • (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w) := by
              ext z; simp [← metricCLM_apply]
            rw [h_eq, ((differentiableAt_metric_apply I p v w).hasFDerivAt.const_smul c).fderiv,
              smul_apply, smul_eq_mul] }
      map_add' := fun u₁ u₂ => by
        ext v w
        exact map_add (fderiv ℝ (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w)
          (extChartAt I p p)) u₁ u₂
      map_smul' := fun c u => by
        ext v w
        exact map_smul (fderiv ℝ (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w)
          (extChartAt I p p)) c u }

lemma dmetricAt_apply [FiniteDimensional ℝ E] (p : M) (u v w : E) :
    dmetricAt I p u v w =
      fderiv ℝ (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w)
        (extChartAt I p p) u := rfl

lemma dmetricAt_symm [FiniteDimensional ℝ E] (p : M) (u v w : E) :
    dmetricAt I p u v w = dmetricAt I p u w v := by
  simp only [dmetricAt_apply]
  congr 2
  ext z
  exact metric_symm I ((extChartAt I p).symm z) v w

lemma abs_fderiv_ω_J_apply_le (p : M) {C_ω C_J : ℝ} (hC_ω : 0 ≤ C_ω) (_hC_J : 0 ≤ C_J)
    (h_ω0 : ∀ a : E, ‖ω_chart I tgt.«ω» p (extChartAt I p p) a‖ ≤ C_ω * ‖a‖)
    (h_ω1 : ∀ a : E, ‖fderiv ℝ (fun z => ω_chart I tgt.«ω» p z a) (extChartAt I p p)‖ ≤ C_ω * ‖a‖)
    (h_J0 : ‖J_chart I tgt.J p (extChartAt I p p)‖ ≤ C_J)
    (h_J1 : ‖fderiv ℝ (J_chart I tgt.J p) (extChartAt I p p)‖ ≤ C_J)
    (u a b : E) :
    |fderiv ℝ (fun z => ω_chart I tgt.«ω» p z a (J_chart I tgt.J p z b)) (extChartAt I p p) u| ≤
      2 * C_ω * C_J * ‖u‖ * ‖a‖ * ‖b‖ := by
  let y₀ := extChartAt I p p
  have h_mem : y₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source (mem_extChartAt_source p)
  have h_nhds : (extChartAt I p).target ∈ 𝓝 y₀ :=
    (isOpen_extChartAt_target p).mem_nhds h_mem
  have hf : HasFDerivAt (fun z => ω_chart I tgt.«ω» p z a)
      (fderiv ℝ (fun z => ω_chart I tgt.«ω» p z a) y₀) y₀ :=
    (((smooth_ω_apply I p a).contDiffAt h_nhds).differentiableAt (by decide)).hasFDerivAt
  have hJ : HasFDerivAt (J_chart I tgt.J p) (fderiv ℝ (J_chart I tgt.J p) y₀) y₀ :=
    (((tgt.J_smooth p).contDiffAt h_nhds).differentiableAt (by decide)).hasFDerivAt
  have hg : HasFDerivAt (fun z => J_chart I tgt.J p z b)
      ((J_chart I tgt.J p y₀).comp (0 : E →L[ℝ] E) + (fderiv ℝ (J_chart I tgt.J p) y₀).flip b) y₀ :=
    hJ.clm_apply (hasFDerivAt_const b y₀)
  have hfg := (hf.clm_apply hg).fderiv
  rw [hfg]
  simp only [comp_zero, zero_add, add_apply, flip_apply]
  rw [ContinuousLinearMap.comp_apply, flip_apply]
  have h1 : |ω_chart I tgt.«ω» p y₀ a (fderiv ℝ (J_chart I tgt.J p) y₀ u b)| ≤
      C_ω * C_J * ‖u‖ * ‖a‖ * ‖b‖ := by
    rw [← Real.norm_eq_abs]
    calc ‖ω_chart I tgt.«ω» p y₀ a (fderiv ℝ (J_chart I tgt.J p) y₀ u b)‖
        ≤ ‖ω_chart I tgt.«ω» p y₀ a‖ * ‖fderiv ℝ (J_chart I tgt.J p) y₀ u b‖ :=
          le_opNorm _ _
      _ ≤ (C_ω * ‖a‖) * (‖fderiv ℝ (J_chart I tgt.J p) y₀ u‖ * ‖b‖) := by
          gcongr
          · exact h_ω0 a
          · exact le_opNorm _ _
      _ ≤ (C_ω * ‖a‖) * ((‖fderiv ℝ (J_chart I tgt.J p) y₀‖ * ‖u‖) * ‖b‖) := by
          gcongr
          exact le_opNorm _ _
      _ ≤ (C_ω * ‖a‖) * ((C_J * ‖u‖) * ‖b‖) := by
          gcongr
      _ = C_ω * C_J * ‖u‖ * ‖a‖ * ‖b‖ := by ring
  have h2 : |fderiv ℝ (fun z => ω_chart I tgt.«ω» p z a) y₀ u (J_chart I tgt.J p y₀ b)| ≤
      C_ω * C_J * ‖u‖ * ‖a‖ * ‖b‖ := by
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (fun z => ω_chart I tgt.«ω» p z a) y₀ u (J_chart I tgt.J p y₀ b)‖
        ≤ ‖fderiv ℝ (fun z => ω_chart I tgt.«ω» p z a) y₀ u‖ * ‖J_chart I tgt.J p y₀ b‖ :=
          le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fun z => ω_chart I tgt.«ω» p z a) y₀‖ * ‖u‖) * (‖J_chart I tgt.J p y₀‖ * ‖b‖) := by
          gcongr <;> exact le_opNorm _ _
      _ ≤ ((C_ω * ‖a‖) * ‖u‖) * (C_J * ‖b‖) := by
          gcongr
          exact h_ω1 a
      _ = C_ω * C_J * ‖u‖ * ‖a‖ * ‖b‖ := by ring
  have h_tri := abs_add_le
    (ω_chart I tgt.«ω» p y₀ a (fderiv ℝ (J_chart I tgt.J p) y₀ u b))
    (fderiv ℝ (fun z => ω_chart I tgt.«ω» p z a) y₀ u (J_chart I tgt.J p y₀ b))
  linarith

lemma abs_dmetricAt_le [FiniteDimensional ℝ E] (p : M) {C_ω C_J : ℝ}
    (hC_ω : 0 ≤ C_ω) (hC_J : 0 ≤ C_J)
    (h_ω0 : ∀ a : E, ‖ω_chart I tgt.«ω» p (extChartAt I p p) a‖ ≤ C_ω * ‖a‖)
    (h_ω1 : ∀ a : E, ‖fderiv ℝ (fun z => ω_chart I tgt.«ω» p z a) (extChartAt I p p)‖ ≤ C_ω * ‖a‖)
    (h_J0 : ‖J_chart I tgt.J p (extChartAt I p p)‖ ≤ C_J)
    (h_J1 : ‖fderiv ℝ (J_chart I tgt.J p) (extChartAt I p p)‖ ≤ C_J)
    (u v w : E) :
    |dmetricAt I p u v w| ≤ 2 * C_ω * C_J * ‖u‖ * ‖v‖ * ‖w‖ := by
  let y₀ := extChartAt I p p
  have h_mem : y₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source (mem_extChartAt_source p)
  have h_nhds : (extChartAt I p).target ∈ 𝓝 y₀ :=
    (isOpen_extChartAt_target p).mem_nhds h_mem
  have hd_vw : DifferentiableAt ℝ (fun z => ω_chart I tgt.«ω» p z v (J_chart I tgt.J p z w)) y₀ :=
    (((smooth_ω_apply I p v).clm_apply (smooth_J_apply I p w)).contDiffAt h_nhds).differentiableAt (by decide)
  have hd_wv : DifferentiableAt ℝ (fun z => ω_chart I tgt.«ω» p z w (J_chart I tgt.J p z v)) y₀ :=
    (((smooth_ω_apply I p w).clm_apply (smooth_J_apply I p v)).contDiffAt h_nhds).differentiableAt (by decide)
  rw [dmetricAt_apply]
  have h_eq : (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w) =
      (1 / 2 : ℝ) • ((fun z => ω_chart I tgt.«ω» p z v (J_chart I tgt.J p z w)) +
        (fun z => ω_chart I tgt.«ω» p z w (J_chart I tgt.J p z v))) := rfl
  rw [h_eq, ((hd_vw.hasFDerivAt.add hd_wv.hasFDerivAt).const_smul (1 / 2 : ℝ)).fderiv,
    smul_apply, add_apply, smul_eq_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h1 := abs_fderiv_ω_J_apply_le I p hC_ω hC_J h_ω0 h_ω1 h_J0 h_J1 u v w
  have h2 := abs_fderiv_ω_J_apply_le I p hC_ω hC_J h_ω0 h_ω1 h_J0 h_J1 u w v
  have h_tri := abs_add_le
    (fderiv ℝ (fun z => ω_chart I tgt.«ω» p z v (J_chart I tgt.J p z w)) y₀ u)
    (fderiv ℝ (fun z => ω_chart I tgt.«ω» p z w (J_chart I tgt.J p z v)) y₀ u)
  linarith

omit [I.Boundaryless] in
lemma nondegenerate_metricBilin (p : M) :
    LinearMap.BilinForm.Nondegenerate (metricCLM I p).toLinearMap₁₂ := by
  constructor
  · intro v hv
    by_contra hv0
    have hpos : 0 < ClosedTameTarget.metric I p v v := metric_pos_def I p v hv0
    have hz : ClosedTameTarget.metric I p v v = 0 := hv v
    linarith
  · intro w hw
    by_contra hw0
    have hpos : 0 < ClosedTameTarget.metric I p w w := metric_pos_def I p w hw0
    have hz : ClosedTameTarget.metric I p w w = 0 := hw w
    linarith

/-- The Christoffel bilinear operator `Γ(p) : E →L[ℝ] E →L[ℝ] E` constructed from the Koszul
identity `g_p(Γ(u, v), w) = (1/2) (∂_u g(v, w) + ∂_v g(u, w) - ∂_w g(u, v))` via the Riesz
isomorphism of the nondegenerate symmetric bilinear form `g_p`. -/
noncomputable def christoffelFromKoszul [FiniteDimensional ℝ E] (p : M)
    (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E :=
  let B : LinearMap.BilinForm ℝ E := (metricCLM I p).toLinearMap₁₂
  let hB : B.Nondegenerate := nondegenerate_metricBilin I p
  let Φ := (LinearMap.BilinForm.toDual B hB).symm
  LinearMap.toContinuousLinearMap
    { toFun := fun u => LinearMap.toContinuousLinearMap
        { toFun := fun v => Φ
            { toFun := fun w => koszulForm dg0 u v w
              map_add' := fun w₁ w₂ => by
                dsimp [koszulForm]
                simp only [map_add, add_apply]
                ring
              map_smul' := fun c w => by
                dsimp [koszulForm]
                simp only [map_smul, smul_apply, smul_eq_mul]
                ring }
          map_add' := fun v₁ v₂ => by
            rw [← LinearEquiv.map_add]
            apply congr_arg Φ
            ext w
            change koszulForm dg0 u (v₁ + v₂) w = koszulForm dg0 u v₁ w + koszulForm dg0 u v₂ w
            dsimp [koszulForm]
            simp only [map_add, add_apply]
            ring
          map_smul' := fun c v => by
            rw [← LinearEquiv.map_smul]
            apply congr_arg Φ
            ext w
            change koszulForm dg0 u (c • v) w = c * koszulForm dg0 u v w
            dsimp [koszulForm]
            simp only [map_smul, smul_apply, smul_eq_mul]
            ring }
      map_add' := fun u₁ u₂ => by
        ext v
        change Φ _ = Φ _ + Φ _
        rw [← LinearEquiv.map_add]
        apply congr_arg Φ
        ext w
        change koszulForm dg0 (u₁ + u₂) v w = koszulForm dg0 u₁ v w + koszulForm dg0 u₂ v w
        dsimp [koszulForm]
        simp only [map_add, add_apply]
        ring
      map_smul' := fun c u => by
        ext v
        change Φ _ = c • Φ _
        rw [← LinearEquiv.map_smul]
        apply congr_arg Φ
        ext w
        change koszulForm dg0 (c • u) v w = c * koszulForm dg0 u v w
        dsimp [koszulForm]
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring }

omit [I.Boundaryless] in
lemma christoffelFromKoszul_koszul [FiniteDimensional ℝ E] (p : M)
    (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    ClosedTameTarget.metric I p (christoffelFromKoszul I p dg0 u v) w =
      koszulForm dg0 u v w := by
  change (metricCLM I p).toLinearMap₁₂ (christoffelFromKoszul I p dg0 u v) w = _
  exact LinearMap.BilinForm.apply_toDual_symm_apply (B := (metricCLM I p).toLinearMap₁₂)
    (hB := nondegenerate_metricBilin I p) _ w

omit [I.Boundaryless] in
lemma christoffelFromKoszul_symm [FiniteDimensional ℝ E] (p : M)
    (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (h_symm : ∀ u v w, dg0 u v w = dg0 u w v) (u v : E) :
    christoffelFromKoszul I p dg0 u v = christoffelFromKoszul I p dg0 v u := by
  apply sub_eq_zero.mp
  apply (nondegenerate_metricBilin I p).1
  intro w
  change ClosedTameTarget.metric I p (christoffelFromKoszul I p dg0 u v - christoffelFromKoszul I p dg0 v u) w = 0
  have h1 : ClosedTameTarget.metric I p (christoffelFromKoszul I p dg0 u v - christoffelFromKoszul I p dg0 v u) w =
      ClosedTameTarget.metric I p (christoffelFromKoszul I p dg0 u v) w -
      ClosedTameTarget.metric I p (christoffelFromKoszul I p dg0 v u) w := by
    simp [← metricCLM_apply]
  rw [h1, christoffelFromKoszul_koszul, christoffelFromKoszul_koszul, koszulForm_symm dg0 h_symm u v w, sub_self]

omit [I.Boundaryless] in
lemma norm_christoffelFromKoszul_le [FiniteDimensional ℝ E] (p : M)
    (dg0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    {c_min C_dg : ℝ} (hc_min : 0 < c_min) (hC_dg : 0 ≤ C_dg)
    (h_coercive : ∀ v : E, c_min * ‖v‖ ^ 2 ≤ ClosedTameTarget.metric I p v v)
    (h_dg_bound : ∀ u v w : E, |dg0 u v w| ≤ C_dg * ‖u‖ * ‖v‖ * ‖w‖) :
    ‖christoffelFromKoszul I p dg0‖ ≤ (3 / 2) * C_dg / c_min := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun u => ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  let Γuv := christoffelFromKoszul I p dg0 u v
  by_cases h0 : ‖Γuv‖ = 0
  · rw [h0]; positivity
  · have h_pos : 0 < ‖Γuv‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have h_coer : c_min * ‖Γuv‖ ^ 2 ≤ koszulForm dg0 u v Γuv := by
      rw [← christoffelFromKoszul_koszul I p dg0 u v Γuv]
      exact h_coercive Γuv
    have h_kosz : koszulForm dg0 u v Γuv ≤ (3 / 2) * C_dg * ‖u‖ * ‖v‖ * ‖Γuv‖ := by
      dsimp [koszulForm]
      have h1 := (le_abs_self _).trans (h_dg_bound u v Γuv)
      have h2 := (le_abs_self _).trans (h_dg_bound v u Γuv)
      have h3 := (neg_le_abs _).trans (h_dg_bound Γuv u v)
      linarith
    have h_ineq : c_min * ‖Γuv‖ * ‖Γuv‖ ≤ ((3 / 2) * C_dg * ‖u‖ * ‖v‖) * ‖Γuv‖ := by
      calc c_min * ‖Γuv‖ * ‖Γuv‖ = c_min * ‖Γuv‖ ^ 2 := by ring
        _ ≤ koszulForm dg0 u v Γuv := h_coer
        _ ≤ ((3 / 2) * C_dg * ‖u‖ * ‖v‖) * ‖Γuv‖ := by linarith
    have h_div : c_min * ‖Γuv‖ ≤ (3 / 2) * C_dg * ‖u‖ * ‖v‖ :=
      le_of_mul_le_mul_right h_ineq h_pos
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc_min]
    linarith

omit [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma extChartOpenPartialHomeomorph_source (x : M) :
    (extChartOpenPartialHomeomorph I x).source = (extChartAt I x).source := by
  simp [extChartOpenPartialHomeomorph, extChartAt]

omit [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma extChartOpenPartialHomeomorph_target (x : M) :
    (extChartOpenPartialHomeomorph I x).target = (extChartAt I x).target := by
  ext y
  simp [extChartOpenPartialHomeomorph, extChartAt, I.range_eq_univ]

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma refl_hc : Subsingleton E ∨ (1 / 2 : ℝ≥0) < ‖((ContinuousLinearEquiv.refl ℝ E).symm : E →L[ℝ] E)‖₊⁻¹ := by
  rcases subsingleton_or_nontrivial E with hSub | hNontriv
  · exact Or.inl hSub
  · right
    have h_id : ((ContinuousLinearEquiv.refl ℝ E).symm : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := rfl
    rw [h_id, ContinuousLinearMap.nnnorm_id, inv_one]
    norm_num

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma quadraticTaylorMap_sub_sub (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) (z₁ z₂ : E) :
    quadraticTaylorMap y₀ Γ z₁ - quadraticTaylorMap y₀ Γ z₂ -
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) (z₁ - z₂) =
      -((1 / 2 : ℝ) • Γ (z₁ + z₂) (z₁ - z₂)) := by
  dsimp [quadraticTaylorMap]
  have h_quad : Γ z₁ z₁ - Γ z₂ z₂ = Γ (z₁ + z₂) (z₁ - z₂) := by
    simp only [map_add, map_sub, add_apply, hΓ_symm z₂ z₁]
    abel
  rw [← h_quad, smul_sub]
  abel

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma quadraticTaylorMap_approximatesLinearOn (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R : ℝ} (hΓR : ‖Γ‖ * R ≤ 1 / 2) :
    ApproximatesLinearOn (quadraticTaylorMap y₀ Γ)
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) (Metric.ball (0 : E) R) (1 / 2) := by
  intro z₁ hz₁ z₂ hz₂
  rw [quadraticTaylorMap_sub_sub y₀ Γ hΓ_symm z₁ z₂, norm_neg, norm_smul,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hz₁_le : ‖z₁‖ ≤ R := le_of_lt (mem_ball_zero_iff.mp hz₁)
  have hz₂_le : ‖z₂‖ ≤ R := le_of_lt (mem_ball_zero_iff.mp hz₂)
  have h_sum : ‖z₁ + z₂‖ ≤ 2 * R := by
    calc ‖z₁ + z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := norm_add_le z₁ z₂
      _ ≤ R + R := add_le_add hz₁_le hz₂_le
      _ = 2 * R := by ring
  calc (1 / 2 : ℝ) * ‖Γ (z₁ + z₂) (z₁ - z₂)‖
      ≤ (1 / 2 : ℝ) * (‖Γ (z₁ + z₂)‖ * ‖z₁ - z₂‖) := by
        gcongr; exact le_opNorm _ _
    _ ≤ (1 / 2 : ℝ) * ((‖Γ‖ * ‖z₁ + z₂‖) * ‖z₁ - z₂‖) := by
        gcongr; exact le_opNorm _ _
    _ ≤ (1 / 2 : ℝ) * ((‖Γ‖ * (2 * R)) * ‖z₁ - z₂‖) := by gcongr
    _ = (‖Γ‖ * R) * ‖z₁ - z₂‖ := by ring
    _ ≤ (1 / 2 : ℝ) * ‖z₁ - z₂‖ := by gcongr
    _ = ((1 / 2 : ℝ≥0) : ℝ) * ‖z₁ - z₂‖ := by norm_num

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma quadraticTaylorMap_bilipschitz (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R : ℝ} (hΓR : ‖Γ‖ * R ≤ 1 / 2)
    {z₁ z₂ : E} (hz₁ : z₁ ∈ Metric.ball (0 : E) R) (hz₂ : z₂ ∈ Metric.ball (0 : E) R) :
    (1 / 2 : ℝ) * ‖z₁ - z₂‖ ≤ ‖quadraticTaylorMap y₀ Γ z₁ - quadraticTaylorMap y₀ Γ z₂‖ ∧
    ‖quadraticTaylorMap y₀ Γ z₁ - quadraticTaylorMap y₀ Γ z₂‖ ≤ (3 / 2 : ℝ) * ‖z₁ - z₂‖ := by
  have h_approx := quadraticTaylorMap_approximatesLinearOn y₀ Γ hΓ_symm hΓR z₁ hz₁ z₂ hz₂
  have h_coe : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  rw [h_coe] at h_approx
  change ‖quadraticTaylorMap y₀ Γ z₁ - quadraticTaylorMap y₀ Γ z₂ - (z₁ - z₂)‖ ≤
    (1 / 2 : ℝ) * ‖z₁ - z₂‖ at h_approx
  set Δ := quadraticTaylorMap y₀ Γ z₁ - quadraticTaylorMap y₀ Γ z₂
  set δ := z₁ - z₂
  constructor
  · have h_tri : ‖δ‖ ≤ ‖Δ‖ + ‖Δ - δ‖ := by
      simpa using norm_sub_le Δ (Δ - δ)
    linarith
  · have h_tri : ‖Δ‖ ≤ ‖Δ - δ‖ + ‖δ‖ := by
      simpa using norm_add_le (Δ - δ) δ
    linarith

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma quadraticTaylorMap_mapsTo_ball (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R r₀ : ℝ} (hR : 0 < R)
    (hΓR : ‖Γ‖ * R ≤ 1 / 2) (hRr₀ : (3 / 2 : ℝ) * R ≤ r₀) :
    Set.MapsTo (quadraticTaylorMap y₀ Γ) (Metric.ball (0 : E) R) (Metric.ball y₀ r₀) := by
  intro z hz
  have h0 : (0 : E) ∈ Metric.ball (0 : E) R := mem_ball_self hR
  have h_bi := (quadraticTaylorMap_bilipschitz y₀ Γ hΓ_symm hΓR hz h0).2
  rw [quadraticTaylorMap_zero, sub_zero] at h_bi
  rw [mem_ball, dist_eq_norm]
  have hz_lt : ‖z‖ < R := mem_ball_zero_iff.mp hz
  linarith

noncomputable def quantTaylorHomeomorph [CompleteSpace E] (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R : ℝ} (hΓR : ‖Γ‖ * R ≤ 1 / 2) :
    OpenPartialHomeomorph E E :=
  (quadraticTaylorMap_approximatesLinearOn y₀ Γ hΓ_symm hΓR).toOpenPartialHomeomorph
    (quadraticTaylorMap y₀ Γ) (Metric.ball (0 : E) R) refl_hc isOpen_ball

noncomputable def oneSubCLE [CompleteSpace E] (A : E →L[ℝ] E) (hA : ‖A‖ < 1) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.unitsEquiv ℝ E (Units.oneSub A hA)

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma contDiffOn_quantTaylorHomeomorph_symm [CompleteSpace E] (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R : ℝ} (hΓR : ‖Γ‖ * R ≤ 1 / 2) :
    ContDiffOn ℝ ⊤ (quantTaylorHomeomorph y₀ Γ hΓ_symm hΓR).symm
      (quantTaylorHomeomorph y₀ Γ hΓ_symm hΓR).target := by
  let O := quantTaylorHomeomorph y₀ Γ hΓ_symm hΓR
  intro y hy
  have hz : O.symm y ∈ Metric.ball (0 : E) R := O.map_target hy
  have hz_lt : ‖O.symm y‖ < R := mem_ball_zero_iff.mp hz
  have hΓz : ‖Γ (O.symm y)‖ < 1 := by
    calc ‖Γ (O.symm y)‖ ≤ ‖Γ‖ * ‖O.symm y‖ := le_opNorm _ _
      _ ≤ ‖Γ‖ * R := by gcongr
      _ ≤ 1 / 2 := hΓR
      _ < 1 := by norm_num
  have h_fderiv : HasFDerivAt O (oneSubCLE (Γ (O.symm y)) hΓz : E →L[ℝ] E) (O.symm y) :=
    quadraticTaylorMap_hasFDerivAt y₀ Γ hΓ_symm (O.symm y)
  have h_cd : ContDiffAt ℝ ⊤ O (O.symm y) :=
    (quadraticTaylorMap_contDiff y₀ Γ).contDiffAt
  exact (O.contDiffAt_symm hy h_fderiv h_cd).contDiffWithinAt

noncomputable def quantCenteredChart [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R : ℝ} (hΓR : ‖Γ‖ * R ≤ 1 / 2) :
    OpenPartialHomeomorph M E :=
  (extChartOpenPartialHomeomorph I p).trans
    (quantTaylorHomeomorph (extChartAt I p p) Γ hΓ_symm hΓR).symm

omit [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma quantCenteredChart_target [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R r₀ : ℝ} (hR : 0 < R)
    (hΓR : ‖Γ‖ * R ≤ 1 / 2) (hRr₀ : (3 / 2 : ℝ) * R ≤ r₀)
    (h_sub : Metric.ball (extChartAt I p p) r₀ ⊆ (extChartAt I p).target) :
    (quantCenteredChart I p Γ hΓ_symm hΓR).target = Metric.ball (0 : E) R := by
  rw [quantCenteredChart, OpenPartialHomeomorph.trans_target]
  have h_src : (quantTaylorHomeomorph (extChartAt I p p) Γ hΓ_symm hΓR).symm.target =
      Metric.ball (0 : E) R := rfl
  rw [h_src, extChartOpenPartialHomeomorph_target, inter_eq_left]
  intro z hz
  exact h_sub (quadraticTaylorMap_mapsTo_ball (extChartAt I p p) Γ hΓ_symm hR hΓR hRr₀ hz)

omit [CompactSpace M] tgt in
lemma quantCenteredChart_smooth_to [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R : ℝ} (hΓR : ‖Γ‖ * R ≤ 1 / 2) :
    ContMDiffOn I (modelWithCornersSelf ℝ E) ∞
      (quantCenteredChart I p Γ hΓ_symm hΓR) (quantCenteredChart I p Γ hΓ_symm hΓR).source := by
  let O := quantTaylorHomeomorph (extChartAt I p p) Γ hΓ_symm hΓR
  have h1 : ContMDiffOn (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞ O.symm O.target :=
    ((contDiffOn_quantTaylorHomeomorph_symm (extChartAt I p p) Γ hΓ_symm hΓR).of_le le_top).contMDiffOn
  have h2 : ContMDiffOn I (modelWithCornersSelf ℝ E) ∞ (extChartAt I p) (extChartAt I p).source := by
    simpa using contMDiffOn_extChartAt (I := I) (x := p)
  refine h1.comp (h2.mono ?_) ?_
  · rw [quantCenteredChart, OpenPartialHomeomorph.trans_source, extChartOpenPartialHomeomorph_source]
    exact inter_subset_left
  · intro x hx
    rw [quantCenteredChart, OpenPartialHomeomorph.trans_source] at hx
    exact hx.2

omit [CompactSpace M] tgt in
lemma quantCenteredChart_smooth_from [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R r₀ : ℝ} (hR : 0 < R)
    (hΓR : ‖Γ‖ * R ≤ 1 / 2) (hRr₀ : (3 / 2 : ℝ) * R ≤ r₀)
    (h_sub : Metric.ball (extChartAt I p p) r₀ ⊆ (extChartAt I p).target) :
    ContMDiffOn (modelWithCornersSelf ℝ E) I ∞
      (quantCenteredChart I p Γ hΓ_symm hΓR).symm (quantCenteredChart I p Γ hΓ_symm hΓR).target := by
  rw [quantCenteredChart_target I p Γ hΓ_symm hR hΓR hRr₀ h_sub]
  have h1 : ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ (extChartAt I p).symm (extChartAt I p).target :=
    contMDiffOn_extChartAt_symm p
  have h2 : ContMDiffOn (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
      (quadraticTaylorMap (extChartAt I p p) Γ) (Metric.ball (0 : E) R) :=
    ((quadraticTaylorMap_contDiff (extChartAt I p p) Γ).contDiffOn.of_le le_top).contMDiffOn
  exact h1.comp h2 ((quadraticTaylorMap_mapsTo_ball (extChartAt I p p) Γ hΓ_symm hR hΓR hRr₀).mono_right h_sub)

omit [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma quantCenteredChart_symm_center [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R : ℝ} (hΓR : ‖Γ‖ * R ≤ 1 / 2) :
    (quantCenteredChart I p Γ hΓ_symm hΓR).symm 0 = p := by
  change (extChartAt I p).symm (quadraticTaylorMap (extChartAt I p p) Γ 0) = p
  rw [quadraticTaylorMap_zero]
  exact (extChartAt I p).left_inv (mem_extChartAt_source p)

omit [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma quantCenteredChart_p_mem_source [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R : ℝ} (hR : 0 < R) (hΓR : ‖Γ‖ * R ≤ 1 / 2) :
    p ∈ (quantCenteredChart I p Γ hΓ_symm hΓR).source := by
  rw [quantCenteredChart, OpenPartialHomeomorph.trans_source, extChartOpenPartialHomeomorph_source]
  refine ⟨mem_extChartAt_source p, ?_⟩
  let O := quantTaylorHomeomorph (extChartAt I p p) Γ hΓ_symm hΓR
  change extChartAt I p p ∈ O.target
  have h0 : (0 : E) ∈ O.source := mem_ball_self hR
  have hO0 : O 0 = extChartAt I p p := quadraticTaylorMap_zero (extChartAt I p p) Γ
  rw [← hO0]
  exact O.map_source h0

omit [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma quantCenteredChart_map_center [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R : ℝ} (hR : 0 < R) (hΓR : ‖Γ‖ * R ≤ 1 / 2) :
    quantCenteredChart I p Γ hΓ_symm hΓR p = 0 := by
  let O := quantTaylorHomeomorph (extChartAt I p p) Γ hΓ_symm hΓR
  change O.symm (extChartAt I p p) = 0
  have h0 : (0 : E) ∈ O.source := mem_ball_self hR
  have hO0 : O 0 = extChartAt I p p := quadraticTaylorMap_zero (extChartAt I p p) Γ
  rw [← hO0]
  exact O.left_inv h0

omit [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma extChartAt_comp_quantCenteredChart_symm_eqOn [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R r₀ : ℝ} (hR : 0 < R)
    (hΓR : ‖Γ‖ * R ≤ 1 / 2) (hRr₀ : (3 / 2 : ℝ) * R ≤ r₀)
    (h_sub : Metric.ball (extChartAt I p p) r₀ ⊆ (extChartAt I p).target) :
    Set.EqOn (extChartAt I p ∘ (quantCenteredChart I p Γ hΓ_symm hΓR).symm)
      (quadraticTaylorMap (extChartAt I p p) Γ) (Metric.ball (0 : E) R) := by
  intro z hz
  change extChartAt I p ((extChartAt I p).symm (quadraticTaylorMap (extChartAt I p p) Γ z)) =
    quadraticTaylorMap (extChartAt I p p) Γ z
  exact (extChartAt I p).right_inv
    (h_sub (quadraticTaylorMap_mapsTo_ball (extChartAt I p p) Γ hΓ_symm hR hΓR hRr₀ hz))

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] tgt in
lemma quantCenteredChart_fderiv_symm_zero [CompleteSpace E] (p : M) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R r₀ : ℝ} (hR : 0 < R)
    (hΓR : ‖Γ‖ * R ≤ 1 / 2) (hRr₀ : (3 / 2 : ℝ) * R ≤ r₀)
    (h_sub : Metric.ball (extChartAt I p p) r₀ ⊆ (extChartAt I p).target) :
    mfderiv (modelWithCornersSelf ℝ E) I (quantCenteredChart I p Γ hΓ_symm hΓR).symm 0 =
      ContinuousLinearMap.id ℝ E := by
  let chart_p := quantCenteredChart I p Γ hΓ_symm hΓR
  have h_tgt := quantCenteredChart_target I p Γ hΓ_symm hR hΓR hRr₀ h_sub
  have h0_mem : (0 : E) ∈ chart_p.target := by rw [h_tgt]; exact mem_ball_self hR
  have h_mdiff : MDifferentiableAt (modelWithCornersSelf ℝ E) I chart_p.symm 0 := by
    have h_cont := quantCenteredChart_smooth_from I p Γ hΓ_symm hR hΓR hRr₀ h_sub 0 h0_mem
    exact (h_cont.mdifferentiableWithinAt (by decide)).mdifferentiableAt
      (by rw [h_tgt]; exact isOpen_ball.mem_nhds (mem_ball_self hR))
  dsimp [mfderiv]
  rw [if_pos h_mdiff, quantCenteredChart_symm_center I p Γ hΓ_symm hΓR]
  have h_local : (extChartAt I p ∘ chart_p.symm) =ᶠ[𝓝 0] quadraticTaylorMap (extChartAt I p p) Γ :=
    Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds (mem_ball_self hR))
      (extChartAt_comp_quantCenteredChart_symm_eqOn I p Γ hΓ_symm hR hΓR hRr₀ h_sub)
  change fderivWithin ℝ (extChartAt I p ∘ chart_p.symm) (Set.range id) 0 = ContinuousLinearMap.id ℝ E
  rw [Set.range_id, fderivWithin_univ, h_local.fderiv_eq]
  exact (quadraticTaylorMap_hasFDerivAt_zero (extChartAt I p p) Γ).fderiv

lemma hasFDerivAt_metric_zero_of_map_zero (p : M) (Γ : E →L[ℝ] E →L[ℝ] E)
    {g h : E → E} {g' : E →L[ℝ] E}
    (hg0 : g 0 = 0) (hg : HasFDerivAt g g' 0) (hh : ContDiffAt ℝ ∞ h 0) :
    HasFDerivAt
      (fun z => ClosedTameTarget.metric I
        ((extChartAt I p).symm (quadraticTaylorMap (extChartAt I p p) Γ z)) (g z) (h z))
      ((metricCLM I p (h 0)).comp g')
      0 := by
  let y₀ := extChartAt I p p
  let Φ := quadraticTaylorMap y₀ Γ
  have hΦ0 : Φ 0 = y₀ := quadraticTaylorMap_zero y₀ Γ
  have hx0 : (extChartAt I p).symm y₀ = p :=
    (extChartAt I p).left_inv (mem_extChartAt_source p)
  have h_mem : y₀ ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source (mem_extChartAt_source p)
  have h_nhds : (extChartAt I p).target ∈ 𝓝 (Φ 0) := by
    rw [hΦ0]
    exact (isOpen_extChartAt_target p).mem_nhds h_mem
  have hΦ_cd : ContDiffAt ℝ ∞ Φ 0 :=
    (quadraticTaylorMap_contDiff y₀ Γ).contDiffAt.of_le le_top
  have hω_cd : ContDiffAt ℝ ∞ (fun z => ω_chart I tgt.«ω» p (Φ z)) 0 :=
    ((tgt.ω_smooth p).contDiffAt h_nhds).comp 0 hΦ_cd
  have hJ_cd : ContDiffAt ℝ ∞ (fun z => J_chart I tgt.J p (Φ z)) 0 :=
    ((tgt.J_smooth p).contDiffAt h_nhds).comp 0 hΦ_cd
  have hc1_diff : DifferentiableAt ℝ (fun z => ω_chart I tgt.«ω» p (Φ z) (h z)) 0 :=
    (hω_cd.clm_apply hh).differentiableAt (by decide)
  have hJ_diff : DifferentiableAt ℝ (fun z => J_chart I tgt.J p (Φ z)) 0 :=
    hJ_cd.differentiableAt (by decide)
  have hJg : HasFDerivAt (fun z => J_chart I tgt.J p (Φ z) (g z))
      (J_chart I tgt.J p (Φ 0) ∘L g' + (fderiv ℝ (fun z => J_chart I tgt.J p (Φ z)) 0).flip (g 0)) 0 :=
    hJ_diff.hasFDerivAt.clm_apply hg
  have h_term1 := hc1_diff.hasFDerivAt.clm_apply hJg
  have hc2_diff : DifferentiableAt ℝ (fun z => ω_chart I tgt.«ω» p (Φ z) (J_chart I tgt.J p (Φ z) (h z))) 0 :=
    (hω_cd.clm_apply (hJ_cd.clm_apply hh)).differentiableAt (by decide)
  have h_term2 := (hc2_diff.hasFDerivAt.clm_apply hg).neg
  have h_comb := (h_term1.add h_term2).const_smul (1 / 2 : ℝ)
  have h_eq_fn : (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm (Φ z)) (g z) (h z)) =
      (1 / 2 : ℝ) • ((fun z => ω_chart I tgt.«ω» p (Φ z) (h z) (J_chart I tgt.J p (Φ z) (g z))) +
        -(fun z => ω_chart I tgt.«ω» p (Φ z) (J_chart I tgt.J p (Φ z) (h z)) (g z))) := by
    ext z
    dsimp [ClosedTameTarget.metric, ω_chart, J_chart]
    have h_skew := tgt.ω_skew ((extChartAt I p).symm (Φ z)) (g z) (tgt.J ((extChartAt I p).symm (Φ z)) (h z))
    change (1 / 2 : ℝ) * (tgt.«ω» ((extChartAt I p).symm (Φ z)) (g z) (tgt.J ((extChartAt I p).symm (Φ z)) (h z)) +
        tgt.«ω» ((extChartAt I p).symm (Φ z)) (h z) (tgt.J ((extChartAt I p).symm (Φ z)) (g z))) =
      (1 / 2 : ℝ) * (tgt.«ω» ((extChartAt I p).symm (Φ z)) (h z) (tgt.J ((extChartAt I p).symm (Φ z)) (g z)) +
        - tgt.«ω» ((extChartAt I p).symm (Φ z)) (tgt.J ((extChartAt I p).symm (Φ z)) (h z)) (g z))
    rw [h_skew]
    ring
  rw [h_eq_fn]
  refine h_comb.congr_fderiv ?_
  ext u
  simp only [hg0, map_zero, add_zero, smul_apply, add_apply, neg_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  change (1 / 2 : ℝ) * (tgt.«ω» ((extChartAt I p).symm (Φ 0)) (h 0) (tgt.J ((extChartAt I p).symm (Φ 0)) (g' u)) +
      - tgt.«ω» ((extChartAt I p).symm (Φ 0)) (tgt.J ((extChartAt I p).symm (Φ 0)) (h 0)) (g' u)) =
    ClosedTameTarget.metric I p (h 0) (g' u)
  rw [hΦ0, hx0]
  have h_skew0 := tgt.ω_skew p (g' u) (tgt.J p (h 0))
  dsimp [ClosedTameTarget.metric]
  linarith

lemma hasFDerivAt_taylor_metric_zero (p : M) (Γ : E →L[ℝ] E →L[ℝ] E) (v w : E) :
    HasFDerivAt
      (fun z => ClosedTameTarget.metric I
        ((extChartAt I p).symm (quadraticTaylorMap (extChartAt I p p) Γ z))
        (v - Γ z v) (w - Γ z w))
      (fderiv ℝ (fun y => ClosedTameTarget.metric I ((extChartAt I p).symm y) v w) (extChartAt I p p) -
        (metricCLM I p w).comp (Γ.flip v) -
        (metricCLM I p v).comp (Γ.flip w))
      0 := by
  let y₀ := extChartAt I p p
  let Φ := quadraticTaylorMap y₀ Γ
  let x : E → M := fun z => (extChartAt I p).symm (Φ z)
  have hΦ0 : Φ 0 = y₀ := quadraticTaylorMap_zero y₀ Γ
  have h1 : HasFDerivAt (fun z => ClosedTameTarget.metric I (x z) v w)
      (fderiv ℝ (fun y => ClosedTameTarget.metric I ((extChartAt I p).symm y) v w) y₀) 0 := by
    have h_base : HasFDerivAt (fun y => ClosedTameTarget.metric I ((extChartAt I p).symm y) v w)
        (fderiv ℝ (fun y => ClosedTameTarget.metric I ((extChartAt I p).symm y) v w) y₀) (Φ 0) := by
      rw [hΦ0]
      exact (differentiableAt_metric_apply I p v w).hasFDerivAt
    exact (h_base.comp 0 (quadraticTaylorMap_hasFDerivAt_zero y₀ Γ)).congr_fderiv
      (ContinuousLinearMap.comp_id _)
  have h2 : HasFDerivAt (fun z => ClosedTameTarget.metric I (x z) (Γ z v) w)
      ((metricCLM I p w).comp (Γ.flip v)) 0 :=
    hasFDerivAt_metric_zero_of_map_zero I p Γ (g := fun z => Γ z v) (h := fun _ => w)
      (by simp) (Γ.flip v).hasFDerivAt contDiffAt_const
  have h3_symm : HasFDerivAt (fun z => ClosedTameTarget.metric I (x z) (Γ z w) v)
      ((metricCLM I p v).comp (Γ.flip w)) 0 :=
    hasFDerivAt_metric_zero_of_map_zero I p Γ (g := fun z => Γ z w) (h := fun _ => v)
      (by simp) (Γ.flip w).hasFDerivAt contDiffAt_const
  have h4 : HasFDerivAt (fun z => ClosedTameTarget.metric I (x z) (Γ z v) (Γ z w)) (0 : E →L[ℝ] ℝ) 0 := by
    have h4' := hasFDerivAt_metric_zero_of_map_zero I p Γ (g := fun z => Γ z v) (h := fun z => Γ z w)
      (by simp) (Γ.flip v).hasFDerivAt ((Γ.flip w).contDiff.contDiffAt.of_le le_top)
    exact h4'.congr_fderiv (by simp)
  have h_comb := ((h1.sub h2).sub h3_symm).add h4
  rw [add_zero] at h_comb
  refine h_comb.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  change ClosedTameTarget.metric I (x z) (v - Γ z v) (w - Γ z w) =
    ClosedTameTarget.metric I (x z) v w -
      ClosedTameTarget.metric I (x z) (Γ z v) w -
      ClosedTameTarget.metric I (x z) (Γ z w) v +
      ClosedTameTarget.metric I (x z) (Γ z v) (Γ z w)
  have h_vw : ClosedTameTarget.metric I (x z) v (Γ z w) = ClosedTameTarget.metric I (x z) (Γ z w) v :=
    metric_symm I (x z) v (Γ z w)
  simp only [← metricCLM_apply] at h_vw ⊢
  simp only [map_sub, sub_apply, h_vw]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma quantCenteredChart_dmetric_zero [FiniteDimensional ℝ E] (p : M)
    {R r₀ : ℝ} (hR : 0 < R)
    (hΓR : ‖christoffelFromKoszul I p (dmetricAt I p)‖ * R ≤ 1 / 2)
    (hRr₀ : (3 / 2 : ℝ) * R ≤ r₀)
    (h_sub : Metric.ball (extChartAt I p p) r₀ ⊆ (extChartAt I p).target)
    (v w : E) :
    fderiv ℝ (fun z => pulledBackMetricAt I p
      (quantCenteredChart I p (christoffelFromKoszul I p (dmetricAt I p))
        (christoffelFromKoszul_symm I p (dmetricAt I p) (dmetricAt_symm I p)) hΓR) z v w) 0 = 0 := by
  let Γ := christoffelFromKoszul I p (dmetricAt I p)
  have hΓ_symm := christoffelFromKoszul_symm I p (dmetricAt I p) (dmetricAt_symm I p)
  let chart_p := quantCenteredChart I p Γ hΓ_symm hΓR
  let y₀ := extChartAt I p p
  let Φ := quadraticTaylorMap y₀ Γ
  have h_nhds : Metric.ball (0 : E) R ∈ 𝓝 (0 : E) := isOpen_ball.mem_nhds (mem_ball_self hR)
  have h_local_comp : (extChartAt I p ∘ chart_p.symm) =ᶠ[𝓝 0] Φ :=
    Filter.eventuallyEq_of_mem h_nhds
      (extChartAt_comp_quantCenteredChart_symm_eqOn I p Γ hΓ_symm hR hΓR hRr₀ h_sub)
  have h_ev : (fun z => pulledBackMetricAt I p chart_p z v w) =ᶠ[𝓝 0]
      (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm (Φ z)) (v - Γ z v) (w - Γ z w)) := by
    have h_fderiv_ev : ∀ᶠ z in 𝓝 (0 : E), fderiv ℝ (extChartAt I p ∘ chart_p.symm) z = fderiv ℝ Φ z :=
      h_local_comp.fderiv
    filter_upwards [h_nhds, h_fderiv_ev] with z _ hz_fd
    change ClosedTameTarget.metric I (chart_p.symm z)
        (fderiv ℝ (extChartAt I p ∘ chart_p.symm) z v)
        (fderiv ℝ (extChartAt I p ∘ chart_p.symm) z w) =
      ClosedTameTarget.metric I ((extChartAt I p).symm (Φ z)) (v - Γ z v) (w - Γ z w)
    rw [hz_fd, quadraticTaylorMap_fderiv y₀ Γ hΓ_symm z]
    rfl
  rw [h_ev.fderiv_eq, (hasFDerivAt_taylor_metric_zero I p Γ v w).fderiv]
  ext u
  simp only [sub_apply, ContinuousLinearMap.comp_apply, flip_apply, zero_apply]
  change dmetricAt I p u v w -
      ClosedTameTarget.metric I p w (Γ u v) -
      ClosedTameTarget.metric I p v (Γ u w) = 0
  rw [metric_symm I p w (Γ u v), metric_symm I p v (Γ u w)]
  dsimp [Γ]
  rw [christoffelFromKoszul_koszul, christoffelFromKoszul_koszul]
  linarith [koszul_cancellation (dmetricAt I p) (dmetricAt_symm I p) u v w]

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma fderiv_quadraticTaylorMap_eq (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) :
    fderiv ℝ (quadraticTaylorMap y₀ Γ) = fun z => ContinuousLinearMap.id ℝ E - Γ z := by
  ext z v
  rw [quadraticTaylorMap_fderiv y₀ Γ hΓ_symm z]

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma fderiv_fderiv_quadraticTaylorMap_eq (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) :
    fderiv ℝ (fderiv ℝ (quadraticTaylorMap y₀ Γ)) = fun _ => -Γ := by
  rw [fderiv_quadraticTaylorMap_eq y₀ Γ hΓ_symm]
  ext z u v
  have h_sub : HasFDerivAt (fun w : E => ContinuousLinearMap.id ℝ E - Γ w) (0 - Γ) z :=
    (hasFDerivAt_const (ContinuousLinearMap.id ℝ E) z).sub Γ.hasFDerivAt
  rw [h_sub.fderiv, zero_sub]

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma norm_iteratedFDeriv_quadraticTaylorMap_le (y₀ : E) (Γ : E →L[ℝ] E →L[ℝ] E)
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R D : ℝ} (hΓR : ‖Γ‖ * R ≤ 1 / 2)
    (hD2 : 2 ≤ D) (hDΓ : ‖Γ‖ ≤ D)
    {z : E} (hz : z ∈ Metric.ball (0 : E) R) {i : ℕ} (hi1 : 1 ≤ i) (hi3 : i ≤ 3) :
    ‖iteratedFDeriv ℝ i (quadraticTaylorMap y₀ Γ) z‖ ≤ D ^ i := by
  have hD_pos : 0 ≤ D := by linarith
  interval_cases i
  · rw [norm_iteratedFDeriv_one, fderiv_quadraticTaylorMap_eq y₀ Γ hΓ_symm, pow_one]
    have hz_le : ‖z‖ ≤ R := le_of_lt (mem_ball_zero_iff.mp hz)
    have hΓz : ‖Γ z‖ ≤ 1 / 2 := by
      calc ‖Γ z‖ ≤ ‖Γ‖ * ‖z‖ := le_opNorm _ _
        _ ≤ ‖Γ‖ * R := by gcongr
        _ ≤ 1 / 2 := hΓR
    have h_id : ‖(ContinuousLinearMap.id ℝ E : E →L[ℝ] E)‖ ≤ 1 := norm_id_le
    calc ‖ContinuousLinearMap.id ℝ E - Γ z‖
        ≤ ‖(ContinuousLinearMap.id ℝ E : E →L[ℝ] E)‖ + ‖Γ z‖ := norm_sub_le _ _
      _ ≤ 1 + 1 / 2 := add_le_add h_id hΓz
      _ ≤ 2 := by norm_num
      _ ≤ D := hD2
  · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedFDeriv_succ_eq_comp_right,
      Function.comp_apply, LinearIsometryEquiv.norm_map, norm_iteratedFDeriv_one,
      fderiv_fderiv_quadraticTaylorMap_eq y₀ Γ hΓ_symm, norm_neg]
    calc ‖Γ‖ = ‖Γ‖ * 1 := by ring
      _ ≤ D * D := mul_le_mul hDΓ (by linarith) zero_le_one hD_pos
      _ = D ^ 2 := by ring
  · rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedFDeriv_succ_eq_comp_right,
      Function.comp_apply, LinearIsometryEquiv.norm_map,
      show (2 : ℕ) = 1 + 1 from rfl, iteratedFDeriv_succ_eq_comp_right,
      Function.comp_apply, LinearIsometryEquiv.norm_map, norm_iteratedFDeriv_one,
      fderiv_fderiv_quadraticTaylorMap_eq y₀ Γ hΓ_symm, fderiv_const_apply, norm_zero]
    positivity

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma norm_iteratedFDeriv_comp_taylor_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : E → G} {y₀ : E} {Γ : E →L[ℝ] E →L[ℝ] E}
    (hΓ_symm : ∀ u v, Γ u v = Γ v u) {R r₀ C D : ℝ}
    (hΓR : ‖Γ‖ * R ≤ 1 / 2) (hD2 : 2 ≤ D) (hDΓ : ‖Γ‖ ≤ D)
    (hg : ContDiffOn ℝ ∞ g (Metric.ball y₀ r₀))
    (hst : Set.MapsTo (quadraticTaylorMap y₀ Γ) (Metric.ball (0 : E) R) (Metric.ball y₀ r₀))
    {y : E} (hy : y ∈ Metric.ball (0 : E) R)
    (hC : ∀ i ≤ 3, ‖iteratedFDeriv ℝ i g (quadraticTaylorMap y₀ Γ y)‖ ≤ C) :
    ‖iteratedFDeriv ℝ 3 (g ∘ quadraticTaylorMap y₀ Γ) y‖ ≤ 6 * C * D ^ 3 := by
  let s := Metric.ball (0 : E) R
  let t := Metric.ball y₀ r₀
  have hs_open : IsOpen s := isOpen_ball
  have ht_open : IsOpen t := isOpen_ball
  have hΦ_cd : ContDiffOn ℝ ∞ (quadraticTaylorMap y₀ Γ) s :=
    (quadraticTaylorMap_contDiff y₀ Γ).contDiffOn.of_le le_top
  rw [← iteratedFDerivWithin_of_isOpen 3 hs_open hy]
  have h_comp := norm_iteratedFDerivWithin_comp_le (N := ∞) (n := 3)
    hg hΦ_cd (by simp) ht_open.uniqueDiffOn hs_open.uniqueDiffOn hst hy
    (C := C) (D := D)
    (fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i ht_open (hst hy)]
      exact hC i hi)
    (fun i hi1 hi3 => by
      rw [iteratedFDerivWithin_of_isOpen i hs_open hy]
      exact norm_iteratedFDeriv_quadraticTaylorMap_le y₀ Γ hΓ_symm hΓR hD2 hDΓ hy hi1 hi3)
  simpa [Nat.factorial] using h_comp

omit [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M] tgt in
lemma norm_iteratedFDeriv_clm_apply_const_le {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F →L[ℝ] G} {s : Set E} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    {y : E} (hy : y ∈ s) (c : F) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun z => f z c) y‖ ≤ ‖c‖ * ‖iteratedFDeriv ℝ k f y‖ := by
  rw [← iteratedFDerivWithin_of_isOpen k hs hy, ← iteratedFDerivWithin_of_isOpen k hs hy]
  exact norm_iteratedFDerivWithin_clm_apply_const (N := ∞) (hf y hy) hs.uniqueDiffOn hy (by simp)

omit [I.Boundaryless] in
lemma norm_iteratedFDeriv_ω_J_le (p : M) {r₀ C_ω C_J : ℝ} (hC_ω : 0 ≤ C_ω) (_hC_J : 0 ≤ C_J)
    (h_sub : Metric.ball (extChartAt I p p) r₀ ⊆ (extChartAt I p).target)
    (h_ω : ∀ {y : E}, y ∈ Metric.ball (extChartAt I p p) r₀ → ∀ (a : E), ∀ k ≤ 3,
      ‖iteratedFDeriv ℝ k (fun z => ω_chart I tgt.«ω» p z a) y‖ ≤ C_ω * ‖a‖)
    (h_J : ∀ {y : E}, y ∈ Metric.ball (extChartAt I p p) r₀ → ∀ k ≤ 3,
      ‖iteratedFDeriv ℝ k (J_chart I tgt.J p) y‖ ≤ C_J)
    {y : E} (hy : y ∈ Metric.ball (extChartAt I p p) r₀)
    {a b : E} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) {k : ℕ} (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (fun z => ω_chart I tgt.«ω» p z a (J_chart I tgt.J p z b)) y‖ ≤
      8 * C_ω * C_J := by
  let t := Metric.ball (extChartAt I p p) r₀
  have ht_open : IsOpen t := isOpen_ball
  have hf_cd : ContDiffOn ℝ ∞ (fun z => ω_chart I tgt.«ω» p z a) t :=
    (smooth_ω_apply I p a).mono h_sub
  have hg_cd : ContDiffOn ℝ ∞ (fun z => J_chart I tgt.J p z b) t :=
    (smooth_J_apply I p b).mono h_sub
  have hJ_cd : ContDiffOn ℝ ∞ (J_chart I tgt.J p) t :=
    (tgt.J_smooth p).mono h_sub
  rw [← iteratedFDerivWithin_of_isOpen k ht_open hy]
  have h_le := norm_iteratedFDerivWithin_clm_apply (N := ∞) (n := k) hf_cd hg_cd ht_open.uniqueDiffOn hy (by simp)
  refine h_le.trans ?_
  have h_term : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (fun z => ω_chart I tgt.«ω» p z a) t y‖ *
        ‖iteratedFDerivWithin ℝ (k - i) (fun z => J_chart I tgt.J p z b) t y‖ ≤
      (k.choose i : ℝ) * (C_ω * C_J) := by
    intro i hi
    have hi_le : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [iteratedFDerivWithin_of_isOpen i ht_open hy, iteratedFDerivWithin_of_isOpen (k - i) ht_open hy]
    have h1 : ‖iteratedFDeriv ℝ i (fun z => ω_chart I tgt.«ω» p z a) y‖ ≤ C_ω := by
      calc ‖iteratedFDeriv ℝ i (fun z => ω_chart I tgt.«ω» p z a) y‖
          ≤ C_ω * ‖a‖ := h_ω hy a i (hi_le.trans hk)
        _ ≤ C_ω * 1 := by gcongr
        _ = C_ω := mul_one C_ω
    have h2 : ‖iteratedFDeriv ℝ (k - i) (fun z => J_chart I tgt.J p z b) y‖ ≤ C_J := by
      calc ‖iteratedFDeriv ℝ (k - i) (fun z => J_chart I tgt.J p z b) y‖
          ≤ ‖b‖ * ‖iteratedFDeriv ℝ (k - i) (J_chart I tgt.J p) y‖ :=
            norm_iteratedFDeriv_clm_apply_const_le ht_open hJ_cd hy b (k - i)
        _ ≤ 1 * C_J := mul_le_mul hb (h_J hy (k - i) (Nat.sub_le k i |>.trans hk)) (norm_nonneg _) zero_le_one
        _ = C_J := one_mul C_J
    calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z => ω_chart I tgt.«ω» p z a) y‖ *
          ‖iteratedFDeriv ℝ (k - i) (fun z => J_chart I tgt.J p z b) y‖
        = (k.choose i : ℝ) * (‖iteratedFDeriv ℝ i (fun z => ω_chart I tgt.«ω» p z a) y‖ *
            ‖iteratedFDeriv ℝ (k - i) (fun z => J_chart I tgt.J p z b) y‖) := by ring
      _ ≤ (k.choose i : ℝ) * (C_ω * C_J) := by
          gcongr
  calc ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (fun z => ω_chart I tgt.«ω» p z a) t y‖ *
          ‖iteratedFDerivWithin ℝ (k - i) (fun z => J_chart I tgt.J p z b) t y‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (C_ω * C_J) :=
        Finset.sum_le_sum h_term
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * (C_ω * C_J) := by
        rw [← Finset.sum_mul]
    _ ≤ 8 * (C_ω * C_J) := by
        gcongr
        rw [← Nat.cast_sum, Nat.sum_range_choose]
        have : 2 ^ k ≤ 8 := by interval_cases k <;> decide
        exact_mod_cast this
    _ = 8 * C_ω * C_J := by ring

omit [I.Boundaryless] in
lemma norm_iteratedFDeriv_metric_le (p : M) {r₀ C_ω C_J : ℝ} (hC_ω : 0 ≤ C_ω) (hC_J : 0 ≤ C_J)
    (h_sub : Metric.ball (extChartAt I p p) r₀ ⊆ (extChartAt I p).target)
    (h_ω : ∀ {y : E}, y ∈ Metric.ball (extChartAt I p p) r₀ → ∀ (a : E), ∀ k ≤ 3,
      ‖iteratedFDeriv ℝ k (fun z => ω_chart I tgt.«ω» p z a) y‖ ≤ C_ω * ‖a‖)
    (h_J : ∀ {y : E}, y ∈ Metric.ball (extChartAt I p p) r₀ → ∀ k ≤ 3,
      ‖iteratedFDeriv ℝ k (J_chart I tgt.J p) y‖ ≤ C_J)
    {y : E} (hy : y ∈ Metric.ball (extChartAt I p p) r₀)
    {v w : E} (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) {k : ℕ} (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w) y‖ ≤
      8 * C_ω * C_J := by
  let t := Metric.ball (extChartAt I p p) r₀
  have ht_open : IsOpen t := isOpen_ball
  let f1 : E → ℝ := fun z => ω_chart I tgt.«ω» p z v (J_chart I tgt.J p z w)
  let f2 : E → ℝ := fun z => ω_chart I tgt.«ω» p z w (J_chart I tgt.J p z v)
  have h1_cd : ContDiffOn ℝ ∞ f1 t :=
    ((smooth_ω_apply I p v).clm_apply (smooth_J_apply I p w)).mono h_sub
  have h2_cd : ContDiffOn ℝ ∞ f2 t :=
    ((smooth_ω_apply I p w).clm_apply (smooth_J_apply I p v)).mono h_sub
  have h12_cd : ContDiffWithinAt ℝ k (f1 + f2) t y :=
    ((h1_cd.add h2_cd) y hy).of_le (by simp)
  have h_eq : (fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w) =
      (1 / 2 : ℝ) • (f1 + f2) := rfl
  rw [h_eq, ← iteratedFDerivWithin_of_isOpen k ht_open hy,
    iteratedFDerivWithin_const_smul_apply h12_cd ht_open.uniqueDiffOn hy,
    iteratedFDerivWithin_add_apply ((h1_cd y hy).of_le (by simp)) ((h2_cd y hy).of_le (by simp))
      ht_open.uniqueDiffOn hy,
    iteratedFDerivWithin_of_isOpen k ht_open hy, iteratedFDerivWithin_of_isOpen k ht_open hy,
    norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hvw := norm_iteratedFDeriv_ω_J_le I p hC_ω hC_J h_sub h_ω h_J hy hv hw hk
  have hwv := norm_iteratedFDeriv_ω_J_le I p hC_ω hC_J h_sub h_ω h_J hy hw hv hk
  linarith [norm_add_le (iteratedFDeriv ℝ k f1 y) (iteratedFDeriv ℝ k f2 y)]

/-- Explicit construction of a `UniformNormalChartFamily` from explicit metric coercivity and
atlas/tensor $C^3$ bounds (`0 sorryAx`). -/
noncomputable def construct_uniform_normal_chart_family_of_bounds
    [FiniteDimensional ℝ E]
    (c_min r₀ L₀ C_ω C_J : ℝ)
    (hc_min_pos : 0 < c_min)
    (hc_coercive : ∀ (x : M) (v : E), c_min * ‖v‖ ^ 2 ≤ ClosedTameTarget.metric I x v v)
    (hr₀_pos : 0 < r₀) (hL₀_ge : 1 ≤ L₀) (hC_ω_pos : 0 < C_ω) (hC_J_pos : 0 < C_J)
    (h_ball_target : ∀ p : M, Metric.ball (extChartAt I p p) r₀ ⊆ (extChartAt I p).target)
    (h_bilip : ∀ (p : M) {y₁ y₂ : E},
      y₁ ∈ Metric.ball (extChartAt I p p) r₀ →
      y₂ ∈ Metric.ball (extChartAt I p p) r₀ →
      dist ((extChartAt I p).symm y₁) ((extChartAt I p).symm y₂) ≤ L₀ * ‖y₁ - y₂‖ ∧
      ‖y₁ - y₂‖ ≤ L₀ * dist ((extChartAt I p).symm y₁) ((extChartAt I p).symm y₂))
    (h_ω_c3 : ∀ (p : M) {y : E}, y ∈ Metric.ball (extChartAt I p p) r₀ →
      ∀ (v : E), ∀ k ≤ 3, ‖iteratedFDeriv ℝ k (fun z => ω_chart I tgt.«ω» p z v) y‖ ≤ C_ω * ‖v‖)
    (h_J_c3 : ∀ (p : M) {y : E}, y ∈ Metric.ball (extChartAt I p p) r₀ →
      ∀ k ≤ 3, ‖iteratedFDeriv ℝ k (J_chart I tgt.J p) y‖ ≤ C_J) :
    UniformNormalChartFamily I (M := M) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let C_Γ : ℝ := 3 * C_ω * C_J / c_min + 1
  have hC_Γ_pos : 0 < C_Γ := by positivity
  let r_norm : ℝ := min (r₀ / 2) (1 / (2 * C_Γ))
  have hr_norm_pos : 0 < r_norm := lt_min (half_pos hr₀_pos) (by positivity)
  have hr_norm_r₀ : (3 / 2 : ℝ) * r_norm ≤ r₀ := by
    have h1 : r_norm ≤ r₀ / 2 := min_le_left _ _
    linarith
  have hΓ_norm_le : ∀ p : M, ‖christoffelFromKoszul I p (dmetricAt I p)‖ ≤ 3 * C_ω * C_J / c_min := by
    intro p
    have hp_mem : extChartAt I p p ∈ Metric.ball (extChartAt I p p) r₀ := mem_ball_self hr₀_pos
    have h_bound := norm_christoffelFromKoszul_le I p (dmetricAt I p)
      hc_min_pos (by positivity : 0 ≤ 2 * C_ω * C_J) (hc_coercive p)
      (abs_dmetricAt_le I p hC_ω_pos.le hC_J_pos.le
        (fun a => by
          rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fun z => ω_chart I tgt.«ω» p z a)]
          exact h_ω_c3 p hp_mem a 0 (Nat.zero_le 3))
        (fun a => by
          rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (f := fun z => ω_chart I tgt.«ω» p z a)]
          exact h_ω_c3 p hp_mem a 1 (by decide))
        (by
          rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := J_chart I tgt.J p)]
          exact h_J_c3 p hp_mem 0 (Nat.zero_le 3))
        (by
          rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (f := J_chart I tgt.J p)]
          exact h_J_c3 p hp_mem 1 (by decide)))
    refine h_bound.trans (le_of_eq ?_)
    ring
  have hΓR : ∀ p : M, ‖christoffelFromKoszul I p (dmetricAt I p)‖ * r_norm ≤ 1 / 2 := by
    intro p
    have h1 : ‖christoffelFromKoszul I p (dmetricAt I p)‖ ≤ C_Γ := by
      have := hΓ_norm_le p
      dsimp [C_Γ]; linarith
    have h2 : r_norm ≤ 1 / (2 * C_Γ) := min_le_right _ _
    calc ‖christoffelFromKoszul I p (dmetricAt I p)‖ * r_norm
        ≤ C_Γ * (1 / (2 * C_Γ)) := mul_le_mul h1 h2 hr_norm_pos.le hC_Γ_pos.le
      _ = 1 / 2 := by field_simp
  let D : ℝ := max 2 C_Γ
  have hD2 : 2 ≤ D := le_max_left 2 C_Γ
  have hDΓ : ∀ p : M, ‖christoffelFromKoszul I p (dmetricAt I p)‖ ≤ D := by
    intro p
    calc ‖christoffelFromKoszul I p (dmetricAt I p)‖ ≤ C_Γ := by
          have := hΓ_norm_le p; dsimp [C_Γ]; linarith
      _ ≤ D := le_max_right 2 C_Γ
  have hD_pos : 0 < D := lt_of_lt_of_le two_pos hD2
  let C_metric3 : ℝ := 48 * C_ω * C_J * D ^ 3
  let C_J3 : ℝ := 6 * C_J * D ^ 3
  let C_omega3 : ℝ := 6 * C_ω * D ^ 3
  have h_metric_c3 : ∀ (p : M) (y : E), y ∈ Metric.ball (0 : E) r_norm →
      ∀ (v w : E), ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
        ‖iteratedFDeriv ℝ 3 (fun z => ClosedTameTarget.metric I
          ((quantCenteredChart I p (christoffelFromKoszul I p (dmetricAt I p))
            (christoffelFromKoszul_symm I p (dmetricAt I p) (dmetricAt_symm I p)) (hΓR p)).symm z) v w) y‖ ≤
          C_metric3 := by
    intro p y hy v w hv hw
    let Γ := christoffelFromKoszul I p (dmetricAt I p)
    have hΓ_symm := christoffelFromKoszul_symm I p (dmetricAt I p) (dmetricAt_symm I p)
    let y₀ := extChartAt I p p
    let g : E → ℝ := fun z => ClosedTameTarget.metric I ((extChartAt I p).symm z) v w
    have hg : ContDiffOn ℝ ∞ g (Metric.ball y₀ r₀) :=
      (smooth_metric_apply I p v w).mono (h_ball_target p)
    have hst := quadraticTaylorMap_mapsTo_ball y₀ Γ hΓ_symm hr_norm_pos (hΓR p) hr_norm_r₀
    have h_comp := norm_iteratedFDeriv_comp_taylor_le hΓ_symm (hΓR p) hD2 (hDΓ p) hg hst hy
      (C := 8 * C_ω * C_J)
      (fun i hi => norm_iteratedFDeriv_metric_le I p hC_ω_pos.le hC_J_pos.le (h_ball_target p)
        (h_ω_c3 p) (h_J_c3 p) (hst hy) hv hw hi)
    refine h_comp.trans (le_of_eq ?_)
    dsimp [C_metric3]; ring
  have h_J_c3_bound : ∀ (p : M) (y : E), y ∈ Metric.ball (0 : E) r_norm →
      ∀ (v : E), ‖v‖ ≤ 1 →
        ‖iteratedFDeriv ℝ 3 (fun z => tgt.J
          ((quantCenteredChart I p (christoffelFromKoszul I p (dmetricAt I p))
            (christoffelFromKoszul_symm I p (dmetricAt I p) (dmetricAt_symm I p)) (hΓR p)).symm z) v) y‖ ≤
          C_J3 := by
    intro p y hy v hv
    let Γ := christoffelFromKoszul I p (dmetricAt I p)
    have hΓ_symm := christoffelFromKoszul_symm I p (dmetricAt I p) (dmetricAt_symm I p)
    let y₀ := extChartAt I p p
    let g : E → E := fun z => J_chart I tgt.J p z v
    have hg : ContDiffOn ℝ ∞ g (Metric.ball y₀ r₀) :=
      (smooth_J_apply I p v).mono (h_ball_target p)
    have hJ_cd : ContDiffOn ℝ ∞ (J_chart I tgt.J p) (Metric.ball y₀ r₀) :=
      (tgt.J_smooth p).mono (h_ball_target p)
    have hst := quadraticTaylorMap_mapsTo_ball y₀ Γ hΓ_symm hr_norm_pos (hΓR p) hr_norm_r₀
    have h_comp := norm_iteratedFDeriv_comp_taylor_le hΓ_symm (hΓR p) hD2 (hDΓ p) hg hst hy
      (C := C_J)
      (fun i hi => by
        calc ‖iteratedFDeriv ℝ i g (quadraticTaylorMap y₀ Γ y)‖
            ≤ ‖v‖ * ‖iteratedFDeriv ℝ i (J_chart I tgt.J p) (quadraticTaylorMap y₀ Γ y)‖ :=
              norm_iteratedFDeriv_clm_apply_const_le isOpen_ball hJ_cd (hst hy) v i
          _ ≤ 1 * C_J := mul_le_mul hv (h_J_c3 p (hst hy) i hi) (norm_nonneg _) zero_le_one
          _ = C_J := one_mul C_J)
    exact h_comp
  have h_omega_c3_bound : ∀ (p : M) (y : E), y ∈ Metric.ball (0 : E) r_norm →
      ∀ (v w : E), ‖v‖ ≤ 1 → ‖w‖ ≤ 1 →
        ‖iteratedFDeriv ℝ 3 (fun z => tgt.«ω»
          ((quantCenteredChart I p (christoffelFromKoszul I p (dmetricAt I p))
            (christoffelFromKoszul_symm I p (dmetricAt I p) (dmetricAt_symm I p)) (hΓR p)).symm z) v w) y‖ ≤
          C_omega3 := by
    intro p y hy v w hv hw
    let Γ := christoffelFromKoszul I p (dmetricAt I p)
    have hΓ_symm := christoffelFromKoszul_symm I p (dmetricAt I p) (dmetricAt_symm I p)
    let y₀ := extChartAt I p p
    let g : E → ℝ := fun z => ω_chart I tgt.«ω» p z v w
    have hωv_cd : ContDiffOn ℝ ∞ (fun z => ω_chart I tgt.«ω» p z v) (Metric.ball y₀ r₀) :=
      (smooth_ω_apply I p v).mono (h_ball_target p)
    have hg : ContDiffOn ℝ ∞ g (Metric.ball y₀ r₀) :=
      hωv_cd.clm_apply contDiffOn_const
    have hst := quadraticTaylorMap_mapsTo_ball y₀ Γ hΓ_symm hr_norm_pos (hΓR p) hr_norm_r₀
    have h_comp := norm_iteratedFDeriv_comp_taylor_le hΓ_symm (hΓR p) hD2 (hDΓ p) hg hst hy
      (C := C_ω)
      (fun i hi => by
        have h_v : ‖iteratedFDeriv ℝ i (fun z => ω_chart I tgt.«ω» p z v) (quadraticTaylorMap y₀ Γ y)‖ ≤ C_ω := by
          calc ‖iteratedFDeriv ℝ i (fun z => ω_chart I tgt.«ω» p z v) (quadraticTaylorMap y₀ Γ y)‖
              ≤ C_ω * ‖v‖ := h_ω_c3 p (hst hy) v i hi
            _ ≤ C_ω * 1 := by gcongr
            _ = C_ω := mul_one C_ω
        calc ‖iteratedFDeriv ℝ i g (quadraticTaylorMap y₀ Γ y)‖
            ≤ ‖w‖ * ‖iteratedFDeriv ℝ i (fun z => ω_chart I tgt.«ω» p z v) (quadraticTaylorMap y₀ Γ y)‖ :=
              norm_iteratedFDeriv_clm_apply_const_le isOpen_ball hωv_cd (hst hy) w i
          _ ≤ 1 * C_ω := mul_le_mul hw h_v (norm_nonneg _) zero_le_one
          _ = C_ω := one_mul C_ω)
    exact h_comp
  exact
    { r_norm := r_norm
      r_norm_pos := hr_norm_pos
      chartAt := fun p =>
        let Γ := christoffelFromKoszul I p (dmetricAt I p)
        have hΓ_symm := christoffelFromKoszul_symm I p (dmetricAt I p) (dmetricAt_symm I p)
        { chart := quantCenteredChart I p Γ hΓ_symm (hΓR p)
          zero_mem_target := by
            rw [quantCenteredChart_target I p Γ hΓ_symm hr_norm_pos (hΓR p) hr_norm_r₀ (h_ball_target p)]
            exact mem_ball_self hr_norm_pos
          p_mem_source := quantCenteredChart_p_mem_source I p Γ hΓ_symm hr_norm_pos (hΓR p)
          map_center := quantCenteredChart_map_center I p Γ hΓ_symm hr_norm_pos (hΓR p)
          symm_center := quantCenteredChart_symm_center I p Γ hΓ_symm (hΓR p)
          ball_subset_target := by
            rw [quantCenteredChart_target I p Γ hΓ_symm hr_norm_pos (hΓR p) hr_norm_r₀ (h_ball_target p)]
          smooth_to := quantCenteredChart_smooth_to I p Γ hΓ_symm (hΓR p)
          smooth_from := quantCenteredChart_smooth_from I p Γ hΓ_symm hr_norm_pos (hΓR p) hr_norm_r₀ (h_ball_target p)
          fderiv_symm_zero := quantCenteredChart_fderiv_symm_zero I p Γ hΓ_symm hr_norm_pos (hΓR p) hr_norm_r₀ (h_ball_target p)
          dmetric_zero := quantCenteredChart_dmetric_zero I p hr_norm_pos (hΓR p) hr_norm_r₀ (h_ball_target p)
          metric_c3_bound := ⟨C_metric3, by positivity, h_metric_c3 p⟩
          J_c3_bound := ⟨C_J3, by positivity, h_J_c3_bound p⟩
          omega_c3_bound := ⟨C_omega3, by positivity, h_omega_c3_bound p⟩ }
      L_dist := 2 * L₀
      L_dist_ge := by linarith
      dist_le_chart := fun p y hy => by
        let Γ := christoffelFromKoszul I p (dmetricAt I p)
        have hΓ_symm := christoffelFromKoszul_symm I p (dmetricAt I p) (dmetricAt_symm I p)
        let y₀ := extChartAt I p p
        have hst := quadraticTaylorMap_mapsTo_ball y₀ Γ hΓ_symm hr_norm_pos (hΓR p) hr_norm_r₀
        have hy_ball : quadraticTaylorMap y₀ Γ y ∈ Metric.ball y₀ r₀ := hst hy
        have h0_ball : y₀ ∈ Metric.ball y₀ r₀ := mem_ball_self hr₀_pos
        have h_bi := (h_bilip p hy_ball h0_ball).1
        have hp_left : (extChartAt I p).symm y₀ = p :=
          (extChartAt I p).left_inv (mem_extChartAt_source p)
        rw [hp_left] at h_bi
        have h_quad := (quadraticTaylorMap_bilipschitz y₀ Γ hΓ_symm (hΓR p) hy (mem_ball_self hr_norm_pos)).2
        rw [quadraticTaylorMap_zero, sub_zero] at h_quad
        change dist ((extChartAt I p).symm (quadraticTaylorMap y₀ Γ y)) p ≤ (2 * L₀) * ‖y‖
        have hL₀_nonneg : 0 ≤ L₀ := by linarith
        calc dist ((extChartAt I p).symm (quadraticTaylorMap y₀ Γ y)) p
            ≤ L₀ * ‖quadraticTaylorMap y₀ Γ y - y₀‖ := h_bi
          _ ≤ L₀ * ((3 / 2 : ℝ) * ‖y‖) := mul_le_mul_of_nonneg_left h_quad hL₀_nonneg
          _ ≤ (2 * L₀) * ‖y‖ := by nlinarith [norm_nonneg y]
      chart_le_dist := fun p y hy => by
        let Γ := christoffelFromKoszul I p (dmetricAt I p)
        have hΓ_symm := christoffelFromKoszul_symm I p (dmetricAt I p) (dmetricAt_symm I p)
        let y₀ := extChartAt I p p
        have hst := quadraticTaylorMap_mapsTo_ball y₀ Γ hΓ_symm hr_norm_pos (hΓR p) hr_norm_r₀
        have hy_ball : quadraticTaylorMap y₀ Γ y ∈ Metric.ball y₀ r₀ := hst hy
        have h0_ball : y₀ ∈ Metric.ball y₀ r₀ := mem_ball_self hr₀_pos
        have h_bi := (h_bilip p hy_ball h0_ball).2
        have hp_left : (extChartAt I p).symm y₀ = p :=
          (extChartAt I p).left_inv (mem_extChartAt_source p)
        rw [hp_left] at h_bi
        have h_quad := (quadraticTaylorMap_bilipschitz y₀ Γ hΓ_symm (hΓR p) hy (mem_ball_self hr_norm_pos)).1
        rw [quadraticTaylorMap_zero, sub_zero] at h_quad
        change ‖y‖ ≤ (2 * L₀) * dist ((extChartAt I p).symm (quadraticTaylorMap y₀ Γ y)) p
        linarith
      C_curv := C_metric3
      C_curv_nonneg := by positivity
      C_metric3 := C_metric3
      C_J3 := C_J3
      C_omega3 := C_omega3
      metric_c3_uniform := h_metric_c3
      J_c3_uniform := h_J_c3_bound
      omega_c3_uniform := h_omega_c3_bound }

/-- First-principles construction of a `UniformNormalChartFamily` on any `[BoundedChartedTarget I M]`
with `[FiniteDimensional ℝ E]` (`0 sorryAx`). -/
noncomputable def construct_uniform_normal_chart_family
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E] :
    UniformNormalChartFamily I (M := M) := by
  have h_all : ∃ P : ℝ × ℝ × ℝ × ℝ × ℝ,
      0 < P.1 ∧
      (∀ (x : M) (v : E), P.1 * ‖v‖ ^ 2 ≤ ClosedTameTarget.metric I x v v) ∧
      0 < P.2.1 ∧ 1 ≤ P.2.2.1 ∧ 0 < P.2.2.2.1 ∧ 0 < P.2.2.2.2 ∧
      (∀ p : M, Metric.ball (extChartAt I p p) P.2.1 ⊆ (extChartAt I p).target) ∧
      (∀ (p : M) {y₁ y₂ : E},
        y₁ ∈ Metric.ball (extChartAt I p p) P.2.1 →
        y₂ ∈ Metric.ball (extChartAt I p p) P.2.1 →
        dist ((extChartAt I p).symm y₁) ((extChartAt I p).symm y₂) ≤ P.2.2.1 * ‖y₁ - y₂‖ ∧
        ‖y₁ - y₂‖ ≤ P.2.2.1 * dist ((extChartAt I p).symm y₁) ((extChartAt I p).symm y₂)) ∧
      (∀ (p : M) {y : E}, y ∈ Metric.ball (extChartAt I p p) P.2.1 →
        ∀ (v : E), ∀ k ≤ 3, ‖iteratedFDeriv ℝ k (fun z => ω_chart I tgt.«ω» p z v) y‖ ≤ P.2.2.2.1 * ‖v‖) ∧
      (∀ (p : M) {y : E}, y ∈ Metric.ball (extChartAt I p p) P.2.1 →
        ∀ k ≤ 3, ‖iteratedFDeriv ℝ k (J_chart I tgt.J p) y‖ ≤ P.2.2.2.2) := by
    obtain ⟨c_min, hc_min_pos, hc_coercive⟩ := exists_metric_coercive I (M := M)
    obtain ⟨r₀, L₀, C_ω, C_J, hr₀_pos, hL₀_ge, hC_ω_pos, hC_J_pos,
      h_ball_target, h_bilip, h_ω_c3, h_J_c3⟩ :=
      BoundedChartedTarget.exists_chart_bounds (I := I) (M := M)
    exact ⟨(c_min, r₀, L₀, C_ω, C_J), hc_min_pos, hc_coercive, hr₀_pos, hL₀_ge, hC_ω_pos, hC_J_pos,
      h_ball_target, h_bilip, h_ω_c3, h_J_c3⟩
  rcases Classical.indefiniteDescription _ h_all with
    ⟨⟨c_min, r₀, L₀, C_ω, C_J⟩, hc_min_pos, hc_coercive, hr₀_pos, hL₀_ge, hC_ω_pos, hC_J_pos,
      h_ball_target, h_bilip, h_ω_c3, h_J_c3⟩
  exact construct_uniform_normal_chart_family_of_bounds I c_min r₀ L₀ C_ω C_J
    hc_min_pos hc_coercive hr₀_pos hL₀_ge hC_ω_pos hC_J_pos h_ball_target h_bilip h_ω_c3 h_J_c3

/-- First-principles existence of a `UniformNormalChartFamily` on any `[BoundedChartedTarget I M]`
with `[FiniteDimensional ℝ E]` (`0 sorryAx`). -/
theorem exists_uniform_normal_chart_family_of_bounded_geometry
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E] :
    Nonempty (UniformNormalChartFamily I (M := M)) :=
  ⟨construct_uniform_normal_chart_family I⟩

end ConstructUniformNormalChartFamily


--------------------------------------------------------------------------------
-- SECTION 4: Local-Chart PDE Certificates (Milestone N3 Bridge Signatures)
--------------------------------------------------------------------------------

/-- Local-chart PDE certificates certified alongside a uniform normal chart family.

All seven fields are true theorems about compact tame targets (none is proved here).
Earlier versions of this structure contained statements that are false on standard targets and
have been corrected (see `certificate_free_audit.md`, items D1-D5):
* `h_weitz_curv` no longer ties the Bochner constant to the constants of `fam`;
* `h_hit_exit_prop`, `h_osc_prop`, `h_decay_prop` use target-dependent constants and, for the
  oscillation and decay bounds, a small-energy hypothesis;
* `h_aa_prop` now requires the sequence to be `J`-holomorphic (without it, a constant sequence
  of discontinuous maps, whose `mfderiv` and hence energy density vanish, is a counterexample). -/
structure UniformNormalChartCertificates (fam : UniformNormalChartFamily I (M := M)) : Prop where
  /-- Bochner–Weitzenböck decomposition with a target constant `b`
  (equivalent to the Bochner inequality `Δe ≥ -b e²`, cf. `Analysis.decomposition_of_bochner_lower_bound`). -/
  h_weitz_curv :
    ∃ b : ℝ, 0 ≤ b ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
      ∀ (w : ℂ),
        ∃ (hessNorm : ℝ) (curvTerm : ℝ),
          Analysis.laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
            hessNorm ^ 2 + curvTerm ∧
          |curvTerm| ≤
            b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
            0 * (riemannianEnergyDensity I u (stereo_chart.symm w))
  /-- Boundary-hit monotonicity and small-ball exit with target constants `c, r₀ > 0`. -/
  h_hit_exit_prop : Analysis.HitExitProperty I M
  /-- Small-energy collar oscillation bound with target constants `C, ε > 0`. -/
  h_osc_prop : Analysis.CollarOscillationProperty I M
  /-- Small-energy cylinder energy decay with target constants `C₀, a, ε > 0`. -/
  h_decay_prop : Analysis.CylinderEnergyDecayProperty I M
  /-- Puncture Sobolev extension across removable singularity for finite-energy J-holomorphic curves -/
  h_punc_prop :
    ∀ (u : CP1 → M) (p : CP1),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}) →
      energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤ →
      Analysis.SatisfiesPunctureSobolevExtension I u p
  /-- Finite-order $C^n$ regularity tower property -/
  h_tower_prop :
    ∀ (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
      (_h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ),
      ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω
  /-- Smooth local Arzelà-Ascoli subsequence extraction for `J`-holomorphic sequences with
  uniform local energy-density bounds. -/
  h_aa_prop :
    ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
      (_h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
      (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C),
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω

omit [I.Boundaryless] in
/-- Discharge of `h_weitz` (Bochner–Weitzenböck curvature decomposition) via normal charts. -/
theorem discharge_h_weitz
    (fam : UniformNormalChartFamily I (M := M))
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
              c * (riemannianEnergyDensity I u (stereo_chart.symm w)) := by
  obtain ⟨b, hb, h⟩ := certs.h_weitz_curv
  exact ⟨b, 0, hb, rfl, h⟩

omit [I.Boundaryless] in
/-- Discharge of `h_hit_exit` (boundary-hit monotonicity and small-ball exit) via normal charts. -/
theorem discharge_h_hit_exit
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.HitExitProperty I M :=
  certs.h_hit_exit_prop

omit [I.Boundaryless] in
/-- Discharge of `h_osc` (small-energy collar oscillation) via normal charts. -/
theorem discharge_h_osc
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CollarOscillationProperty I M :=
  certs.h_osc_prop

omit [I.Boundaryless] in
/-- Discharge of `h_decay` (small-energy cylindrical energy decay) via normal charts. -/
theorem discharge_h_decay
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CylinderEnergyDecayProperty I M :=
  certs.h_decay_prop

omit [I.Boundaryless] in
/-- Discharge of `h_punc` (Puncture Sobolev extension across removable singularity) via normal charts. -/
theorem discharge_h_punc
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    Analysis.SatisfiesPunctureSobolevExtension I u p :=
  certs.h_punc_prop u p hu h_energy

omit [I.Boundaryless] in
/-- Discharge of `h_tower` (Finite-order $C^n$ tower implies smooth regularity) via normal charts. -/
theorem discharge_h_tower
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
    (_h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  certs.h_tower_prop u Ω _hΩ _h_weak n

omit [I.Boundaryless] in
/-- Discharge of `h_aa` (Smooth local Arzelà-Ascoli extraction for `J`-holomorphic sequences). -/
theorem discharge_h_aa
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
    (_h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  certs.h_aa_prop u_seq Ω _h_open _h_jhol _h_grad_bdd

--------------------------------------------------------------------------------
-- SECTION 4b: Contract-named re-exports (Milestone M1/M2 names)
--------------------------------------------------------------------------------

/-! These `*_first_principles` theorems are re-exports of the projections above under the contract
names used by the milestone plans. They still take `certs` as a hypothesis. -/

omit [I.Boundaryless] in
/-- Contract-named re-export of `discharge_h_weitz`. -/
theorem discharge_h_weitz_first_principles
    (fam : UniformNormalChartFamily I (M := M))
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

omit [I.Boundaryless] in
/-- Contract-named re-export of `discharge_h_hit_exit`. -/
theorem discharge_h_hit_exit_first_principles
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.HitExitProperty I M :=
  discharge_h_hit_exit I fam certs

omit [I.Boundaryless] in
/-- Contract-named re-export of `discharge_h_osc`. -/
theorem discharge_h_osc_first_principles
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CollarOscillationProperty I M :=
  discharge_h_osc I fam certs

omit [I.Boundaryless] in
/-- Contract-named re-export of `discharge_h_decay`. -/
theorem discharge_h_decay_first_principles
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CylinderEnergyDecayProperty I M :=
  discharge_h_decay I fam certs

omit [I.Boundaryless] in
/-- Contract-named re-export of `discharge_h_punc`: a finite-energy curve on CP1 \ {p} extends
continuously and as a weak C¹ J-holomorphic curve across p. -/
theorem discharge_h_punc_first_principles
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (p : CP1)
      (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
      (_h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤),
      ∃ (u_ext : CP1 → M),
        Continuous u_ext ∧
        Analysis.WeakJHolomorphicOn I u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p}) :=
  discharge_h_punc I fam certs

omit [I.Boundaryless] in
/-- Discharge of smooth removable singularity extension (Contract A12) via coupling of `h_punc` and `h_tower`. -/
theorem discharge_removal_of_singularities
    [T2Space M]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  Analysis.removal_of_singularities I u p h_jhol h_energy
    (discharge_h_punc I fam certs u p h_jhol h_energy)
    (fun u_ext hu_weak n => discharge_h_tower I fam certs u_ext Set.univ isOpen_univ hu_weak n)

--------------------------------------------------------------------------------
-- SECTION 4c: Regularity & Compactness re-exports (Milestone M3 names)
--------------------------------------------------------------------------------

omit [I.Boundaryless] in
/-- Contract-named re-export of `discharge_h_tower`. -/
theorem discharge_h_tower_first_principles
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
      (_h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ),
      ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  discharge_h_tower I fam certs

omit [I.Boundaryless] in
/-- Contract-named re-export of `discharge_h_aa`. -/
theorem discharge_h_aa_first_principles
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
      (_h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
      (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C),
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  discharge_h_aa I fam certs

omit [I.Boundaryless] in
/-- Discharge of nonlinear elliptic bootstrap (Contract A05) via normal charts. -/
theorem discharge_nonlinear_elliptic_bootstrap
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  Analysis.nonlinear_elliptic_bootstrap I u Ω hΩ h_weak (discharge_h_tower I fam certs u Ω hΩ h_weak)

omit [I.Boundaryless] in
/-- Discharge of local smooth compactness under gradient bounds (Contract A06) via normal charts. -/
theorem discharge_local_smooth_compactness_of_arzela_ascoli
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  Analysis.local_smooth_compactness_of_arzela_ascoli I u_seq Ω h_open h_jhol h_grad_bdd
    (fun h => certs.h_aa_prop u_seq Ω h_open h_jhol h)

--------------------------------------------------------------------------------
-- SECTION 5: Companion Mathematical Limit Theorems (Tier 2 Verification)
--------------------------------------------------------------------------------

omit [I.Boundaryless] in
/-- Companion theorem: Constant curves satisfy `h_weitz` with b = 0, c = 0. -/
theorem discharge_h_weitz_const
    (_fam : UniformNormalChartFamily I (M := M)) (x₀ : M) :
    ∃ (b c : ℝ), 0 ≤ b ∧ c = 0 ∧
      ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm w)) ∧
      ∀ (w : ℂ),
        ∃ (hessNorm : ℝ) (curvTerm : ℝ),
          Analysis.laplacian2D (fun z => riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm z)) w =
            hessNorm ^ 2 + curvTerm ∧
          |curvTerm| ≤
            b * (riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm w)) ^ 2 +
            c * (riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm w)) :=
  ⟨0, 0, le_rfl, rfl, Analysis.contDiff_energy_density_chart_const I x₀,
   fun w => Analysis.bochner_curvature_decomposition_const I 0 0 x₀ w⟩

omit [I.Boundaryless] in
/-- Honest mathematical discharge of `h_hit_exit` for constant maps (`0 sorryAx`).
Constant maps vacuously satisfy the boundary-hit and ball exit conditions because
the non-constancy premise `¬ ∃ c', ∀ z, u z = c'` is identically false. -/
theorem discharge_h_hit_exit_const
    (_fam : UniformNormalChartFamily I (M := M)) (c : M) :
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
      Continuous (riemannianEnergyDensity I (fun _ : CP1 => c)) ∧ (∃ z : CP1, 1 ≤ dist ((fun _ : CP1 => c) z) x)) := by
  constructor
  · intro x r hr hr1 hx hu h_nonconst z_hit hz_front hz_dist
    exfalso
    exact h_nonconst ⟨c, fun _ => rfl⟩
  · intro x hx hu h_nonconst
    exfalso
    exact h_nonconst ⟨c, fun _ => rfl⟩

omit [I.Boundaryless] in
/-- Companion theorem: Constant curves satisfy collar oscillation `h_osc`. -/
theorem discharge_h_osc_const
    (_fam : UniformNormalChartFamily I (M := M))
    (c : M) (a : ℂ) (r R : ℝ) :
    Analysis.SatisfiesCylinderCollarOscillation I (fun _ => c) a r R :=
  Analysis.satisfiesCylinderCollarOscillation_const I c a r R

omit [I.Boundaryless] in
/-- Companion theorem: Constant curves satisfy cylinder energy decay `h_decay`. -/
theorem discharge_h_decay_const
    (_fam : UniformNormalChartFamily I (M := M))
    (c : M) (center : ℂ) (r R : ℝ) :
    Analysis.SatisfiesCylinderEnergyDecay I (fun _ => c) center r R :=
  Analysis.satisfiesCylinderEnergyDecay_const I c center r R

omit [I.Boundaryless] in
/-- Companion theorem: Constant curves satisfy puncture extension `h_punc`. -/
theorem discharge_h_punc_const
    (_fam : UniformNormalChartFamily I (M := M))
    (c : M) (p : CP1) :
    Analysis.SatisfiesPunctureSobolevExtension I (fun _ => c) p :=
  Analysis.satisfiesPunctureSobolevExtension_const I c p

omit [I.Boundaryless] in
/-- Companion theorem: Global J-holomorphic curves extend across punctures `h_punc`. -/
theorem discharge_h_punc_of_global_jhol
    (_fam : UniformNormalChartFamily I (M := M))
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    Analysis.SatisfiesPunctureSobolevExtension I u p :=
  Analysis.satisfiesPunctureSobolevExtension_of_global_jhol I u p h_jhol

omit [I.Boundaryless] in
/-- Companion theorem: Smooth maps satisfy bootstrap tower `h_tower` for all orders n. -/
theorem discharge_h_tower_smooth
    (_fam : UniformNormalChartFamily I (M := M))
    (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
    (h_smooth : ContMDiffOn I_CP1 I ∞ u Ω) (n : ℕ) :
    ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  h_smooth.of_le ENat.LEInfty.out

omit [I.Boundaryless] in
/-- Companion theorem: Constant sequences satisfy smooth local Arzelà-Ascoli `h_aa`. -/
theorem discharge_h_aa_const
    (_fam : UniformNormalChartFamily I (M := M))
    (c : M) (Ω : Set CP1) :
    ∃ (_σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun _ => (fun _ : CP1 => c)) u_lim Ω :=
  ⟨Bookkeeping.SubseqMap.id, fun _ => c, smoothLocalConvergesOn_const_map I c Ω⟩

omit [I.Boundaryless] in
/-- Satisfiability check: on targets where every `J`-holomorphic sphere is constant,
`UniformNormalChartCertificates` is inhabited, given the remaining per-target inputs
(`h_punc_const`, `h_tower_const`, `h_aa_extract`) (`0 sorryAx`). -/
theorem conditioned_certificates_inhabited_of_all_const
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
    Nonempty (UniformNormalChartCertificates I fam) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, h_aa_extract⟩⟩
  · refine ⟨0, le_rfl, fun u hu => ?_⟩
    obtain ⟨c, hc⟩ := h_all_const u hu
    have hu_eq : u = fun _ => c := funext hc
    subst hu_eq
    exact ⟨Analysis.contDiff_energy_density_chart_const I c, fun w =>
      Analysis.bochner_curvature_decomposition_const I 0 0 c w⟩
  · refine ⟨1, 1, one_pos, one_pos, ?_, ?_⟩
    · intro u x r _ _ _ hu h_nonconst _ _ _
      exfalso
      exact h_nonconst (h_all_const u hu)
    · intro u x _ hu h_nonconst
      exfalso
      exact h_nonconst (h_all_const u hu)
  · refine ⟨1, 1, one_pos, one_pos, fun u a r R _ _ hu _ => ?_⟩
    obtain ⟨c, hc⟩ := h_all_const u hu
    have hu_eq : u = fun _ => c := funext hc
    subst hu_eq
    exact Analysis.satisfiesCylinderCollarOscillationWith_const I zero_le_one c a r R
  · refine ⟨1, 1, 1, one_pos, one_pos, one_pos, fun u center r R _ _ hu _ => ?_⟩
    obtain ⟨c, hc⟩ := h_all_const u hu
    have hu_eq : u = fun _ => c := funext hc
    subst hu_eq
    exact Analysis.satisfiesCylinderEnergyDecay_const I c center r R
  · intro u p hu he
    obtain ⟨c, hc⟩ := h_punc_const u p hu he
    exact Analysis.satisfiesPunctureSobolevExtension_of_eqOn_const I u c p hc.symm
  · intro u Ω hΩ h_weak n
    obtain ⟨c, hc⟩ := h_tower_const u Ω hΩ h_weak
    have h_c_smooth : ContMDiffOn I_CP1 I (n : WithTop ℕ∞) (fun _ => c) Ω :=
      contMDiffOn_const
    exact h_c_smooth.congr hc

/-- Assembly of `UniformNormalChartCertificates I fam` from the remaining open analytic inputs,
using the coordinate-level reductions proved in Phases 1–3 and the Steps 1–3 first-principles
theorems (`Analysis.punctured_oscillation_of_local_collar_oscillation`,
`local_lipschitz_of_bounded_energy_density`, `Analysis.local_collar_oscillation_of_bounded_modulus_and_decay`,
`Analysis.smallBallExit_of_contDiff_stereo_and_exit`, and
`Analysis.exists_smoothLocalConvergesOn_subseq_of_equicontinuous_and_local_jet_bounds`) (`0 sorryAx`).

Both `h_punc_osc` (vanishing punctured oscillation for all `p : CP1`) and `h_aa_lip`
(local Lipschitz equicontinuity from bounded energy density) are proved here from first principles
rather than assumed as hypotheses, `h_osc_slices` is reduced to **bounded-modulus rings**
(`R ≤ 18 * r`) via dyadic sub-annulus chaining, and `h_aa_jets` reduces full frame-invariant
`SmoothLocalConvergesOn` (eliminating `MoebiusFrame` and all 5 clauses of `CoreSmoothLocalConvergesOn`)
to local chart higher-jet bounds `Analysis.HasLocalChartJetBoundsAt` on `Ω`.
The reductions used are:
1. `h_weitz_curv` ⇐ the Bochner inequality `h_bochner`
   (`Analysis.bochner_curvature_decomposition_of_lower_bound`);
2. `h_hit_exit_prop` ⇐ the radial differential inequality `h_hit_ode` plus north-pole continuity and
   small-ball exit (`Analysis.boundary_hit_energy_of_radial_diff_ineq` and
   `Analysis.smallBallExit_of_contDiff_stereo_and_exit`);
3. `h_osc_prop` ⇐ bounded-modulus (`R ≤ 18 * r`) radial/angular slice bounds `h_osc_slices`
   plus local cylinder energy decay `h_decay`
   (`Analysis.satisfiesCylinderCollarOscillation_of_radial_and_angular_bounds` and
   `Analysis.local_collar_oscillation_of_bounded_modulus_and_decay`);
4. `h_decay_prop` ⇐ local cylinder energy decay `h_decay`;
5. `h_punc_prop` ⇐ bounded-modulus (`R ≤ 18 * r`) slice bounds `h_osc_slices` + `h_decay`
   (via `Analysis.local_collar_oscillation_of_bounded_modulus_and_decay`,
   `Analysis.punctured_oscillation_of_local_collar_oscillation`, and
   `Analysis.exists_limit_point_of_puncture`) plus `C¹` regularity of the extension `h_punc_c1`
   (`Analysis.weakJHolomorphicOn_univ_of_c1_and_continuousAt_cr_at_puncture`);
6. `h_tower_prop` ⇐ the local one-step regularity gain `h_tower_step`
   (`Analysis.contMDiffOn_nat_of_weakJHolomorphicOn_aux`);
7. `h_aa_prop` ⇐ `local_lipschitz_of_bounded_energy_density` plus local chart higher-jet bounds `h_aa_jets`
   (`Analysis.exists_smoothLocalConvergesOn_subseq_of_equicontinuous_and_local_jet_bounds`). -/
theorem UniformNormalChartCertificates.of_first_principles
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (h_bochner : ∃ b : ℝ, 0 ≤ b ∧ ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
      ∀ (w : ℂ), -b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 ≤
        Analysis.laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w)
    (h_hit_ode : ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
      (∀ (u : CP1 → M) (x : M) (r : ℝ),
        0 < r → r ≤ r₀ → x ∈ Set.range u →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        (¬ ∃ c' : M, ∀ z, u z = c') →
        ∀ z_hit ∈ frontier (u ⁻¹' (Metric.ball x r)),
          dist (u z_hit) x = r →
          ∃ (F F' : ℝ → ℝ) (r_min : ℝ),
            0 < r_min ∧ r_min ≤ r ∧
            (∀ t ∈ Icc r_min r, HasDerivAt F (F' t) t) ∧
            (∀ t ∈ Icc r_min r, F t ≤ (1 / 2 : ℝ) * t * F' t) ∧
            c * r_min ^ 2 ≤ F r_min ∧
            F r ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r))) ∧
      (∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        (¬ ∃ c' : M, ∀ z, u z = c') →
        ContinuousAt (riemannianEnergyDensity I u) north_pole ∧
        ∀ x ∈ Set.range u, ∃ z : CP1, r₀ ≤ dist (u z) x))
    (h_osc_slices : ∃ (C ε : ℝ), 0 < C ∧ 0 < ε ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r R) →
        energyMeasure I u (annulus_at a r R) < ε →
        ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
          ∃ z_mid : CP1,
            dist (u z₁) (u z_mid) ≤ (C / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)) ∧
            dist (u z_mid) (u z₂) ≤ (C / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)))
    (h_decay : ∃ (C₀ a_decay ε_neck : ℝ), 0 < C₀ ∧ 0 < a_decay ∧ 0 < ε_neck ∧
      ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
        0 < r → 2 * r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at center r R) →
        energyMeasure I u (annulus_at center r R) < ε_neck →
        Analysis.SatisfiesCylinderEnergyDecayWith I C₀ a_decay u center r R)
    (h_punc_c1 : ∀ (u : CP1 → M) (p : CP1),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}) →
      energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤ →
      ∀ m_star : M, Filter.Tendsto u (𝓝[≠] p) (𝓝 m_star) →
        ContMDiffOn I_CP1 I 1 (Function.update u p m_star) Set.univ ∧
        ∀ v : TangentSpace I_CP1 p,
          ContinuousAt (fun z : CP1 =>
            mfderiv I_CP1 I (Function.update u p m_star) z (RiemannDomain.j z v) -
              (ClosedTameTarget.J (I := I) (Function.update u p m_star z))
                (mfderiv I_CP1 I (Function.update u p m_star) z v)) p)
    (h_tower_step : ∀ (u : CP1 → M) (Ω : Set CP1),
      IsOpen Ω → Analysis.WeakJHolomorphicOn I u Ω →
      ∀ k : ℕ, ContMDiffOn I_CP1 I (k : WithTop ℕ∞) u Ω →
        ∀ z ∈ Ω, ContMDiffWithinAt I_CP1 I ((k + 1 : ℕ) : WithTop ℕ∞) u Ω z)
    (h_aa_jets : ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1),
      IsOpen Ω →
      (∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω) →
      (∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) →
      ∀ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        ContinuousOn u_lim Ω →
        (∀ K ⊆ Ω, IsCompact K →
          TendstoUniformlyOn (fun n => u_seq (σ.1 n)) u_lim Filter.atTop K) →
        (∀ z ∈ Ω, Filter.Tendsto (fun n => u_seq (σ.1 n) z) Filter.atTop (𝓝 (u_lim z))) →
        ∀ z ∈ Ω, Analysis.HasLocalChartJetBoundsAt I (fun n => u_seq (σ.1 n)) u_lim z) :
    UniformNormalChartCertificates I fam where
  h_weitz_curv := by
    obtain ⟨b, hb, h⟩ := h_bochner
    exact ⟨b, hb, fun u hu => ⟨(h u hu).1, fun w =>
      Analysis.bochner_curvature_decomposition_of_lower_bound I u w hb ((h u hu).2 w)⟩⟩
  h_hit_exit_prop := by
    obtain ⟨b, _hb, h_boch⟩ := h_bochner
    obtain ⟨c, r₀, hc, hr₀, h_ode, h_exit⟩ := h_hit_ode
    refine ⟨c, r₀, hc, hr₀, ?_,
      Analysis.smallBallExit_of_contDiff_stereo_and_exit I (fun u hu => (h_boch u hu).1) h_exit⟩
    intro u x r hr hr0 hx hu h_nonconst z_hit hz_front hz_dist
    obtain ⟨F, F', r_min, hr_min, hle, h_deriv, h_ineq, h_init, h_sublevel⟩ :=
      h_ode u x r hr hr0 hx hu h_nonconst z_hit hz_front hz_dist
    exact Analysis.boundary_hit_energy_of_radial_diff_ineq
      I u x F F' hr_min hle h_deriv h_ineq h_init h_sublevel
  h_osc_prop := by
    obtain ⟨C_ring, ε_ring, hC_ring, hε_ring, h_slices⟩ := h_osc_slices
    have h_ring_osc : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
        ∀ (u' : CP1 → M) (a : ℂ) (r R : ℝ),
          0 < r → r < R → R ≤ 18 * r →
          JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at a r R) →
          energyMeasure I u' (annulus_at a r R) < ε_ring →
          Analysis.SatisfiesCylinderCollarOscillationWith I C_ring u' a r R :=
      ⟨C_ring, ε_ring, hC_ring, hε_ring, fun u' a r R hr hrR hr18 hu_ann hE =>
        Analysis.satisfiesCylinderCollarOscillation_of_radial_and_angular_bounds
          I C_ring u' a r R (h_slices u' a r R hr hrR hr18 hu_ann hE)⟩
    obtain ⟨C, ε_osc, hC, hε_osc, h_loc_osc⟩ :=
      Analysis.local_collar_oscillation_of_bounded_modulus_and_decay I h_ring_osc h_decay
    refine ⟨C, ε_osc, hC, hε_osc, fun u a r R hr hrR hu hE => ?_⟩
    have hu_loc : JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r R) :=
      ⟨hu.1.mono (Set.subset_univ _), fun z _ => hu.2 z (Set.mem_univ z)⟩
    exact h_loc_osc u a r R hr hrR hu_loc hE
  h_decay_prop := by
    obtain ⟨C₀, a_decay, ε_neck, hC₀, ha, hε_neck, h_dec⟩ := h_decay
    refine ⟨C₀, a_decay, ε_neck, hC₀, ha, hε_neck, fun u center r R hr h2r hu hE => ?_⟩
    have hu_loc : JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at center r R) :=
      ⟨hu.1.mono (Set.subset_univ _), fun z _ => hu.2 z (Set.mem_univ z)⟩
    exact h_dec u center r R hr h2r hu_loc hE
  h_punc_prop u p hu he := by
    obtain ⟨C_ring, ε_ring, hC_ring, hε_ring, h_slices⟩ := h_osc_slices
    have h_ring_osc : ∃ (C_ring ε_ring : ℝ), 0 < C_ring ∧ 0 < ε_ring ∧
        ∀ (u' : CP1 → M) (a : ℂ) (r R : ℝ),
          0 < r → r < R → R ≤ 18 * r →
          JHolomorphicOn (I := I) (I_dom := I_CP1) u' (annulus_at a r R) →
          energyMeasure I u' (annulus_at a r R) < ε_ring →
          Analysis.SatisfiesCylinderCollarOscillationWith I C_ring u' a r R :=
      ⟨C_ring, ε_ring, hC_ring, hε_ring, fun u' a r R hr hrR hr18 hu_ann hE =>
        Analysis.satisfiesCylinderCollarOscillation_of_radial_and_angular_bounds
          I C_ring u' a r R (h_slices u' a r R hr hrR hr18 hu_ann hE)⟩
    have h_loc_osc :=
      Analysis.local_collar_oscillation_of_bounded_modulus_and_decay I h_ring_osc h_decay
    have h_osc := Analysis.punctured_oscillation_of_local_collar_oscillation
      I h_loc_osc u p hu he
    obtain ⟨m_star, hm_star⟩ := Analysis.exists_limit_point_of_puncture u p h_osc
    obtain ⟨hc1, hcr⟩ := h_punc_c1 u p hu he m_star hm_star
    have h_weak := Analysis.weakJHolomorphicOn_univ_of_c1_and_continuousAt_cr_at_puncture
      I u (Function.update u p m_star) p hc1 (Analysis.eqOn_update_punctured_sphere u p m_star) hu hcr
    exact Analysis.satisfiesPunctureSobolevExtension_of_update_weakJHolomorphicOn I u p m_star h_weak
  h_tower_prop u Ω hΩ h_weak n :=
    Analysis.contMDiffOn_nat_of_weakJHolomorphicOn_aux I u Ω h_weak
      (fun k hk z hz => h_tower_step u Ω hΩ h_weak k hk z hz) n
  h_aa_prop u_seq Ω h_open h_jhol h_grad_bdd :=
    Analysis.exists_smoothLocalConvergesOn_subseq_of_equicontinuous_and_local_jet_bounds
      I u_seq Ω h_open (fun n => (h_jhol n).1)
      (Analysis.equicontinuous_of_local_lipschitz_on_domain u_seq Ω
        (local_lipschitz_of_bounded_energy_density I u_seq Ω h_open h_jhol h_grad_bdd))
      (h_aa_jets u_seq Ω h_open h_jhol h_grad_bdd)

theorem UniformNormalChartCertificates.of_collar_hole_filling
    [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (h_bochner : ∃ b : ℝ, 0 ≤ b ∧ ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
      ∀ (w : ℂ), -b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 ≤
        Analysis.laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w)
    (h_hit_ode : ∃ (c r₀ : ℝ), 0 < c ∧ 0 < r₀ ∧
      (∀ (u : CP1 → M) (x : M) (r : ℝ),
        0 < r → r ≤ r₀ → x ∈ Set.range u →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        (¬ ∃ c' : M, ∀ z, u z = c') →
        ∀ z_hit ∈ frontier (u ⁻¹' (Metric.ball x r)),
          dist (u z_hit) x = r →
          ∃ (F F' : ℝ → ℝ) (r_min : ℝ),
            0 < r_min ∧ r_min ≤ r ∧
            (∀ t ∈ Icc r_min r, HasDerivAt F (F' t) t) ∧
            (∀ t ∈ Icc r_min r, F t ≤ (1 / 2 : ℝ) * t * F' t) ∧
            c * r_min ^ 2 ≤ F r_min ∧
            F r ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r))) ∧
      (∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        (¬ ∃ c' : M, ∀ z, u z = c') →
        ContinuousAt (riemannianEnergyDensity I u) north_pole ∧
        ∀ x ∈ Set.range u, ∃ z : CP1, r₀ ≤ dist (u z) x))
    (h_osc_slices : ∃ (C ε : ℝ), 0 < C ∧ 0 < ε ∧
      ∀ (u : CP1 → M) (a : ℂ) (r R : ℝ),
        0 < r → r < R → R ≤ 18 * r →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at a r R) →
        energyMeasure I u (annulus_at a r R) < ε →
        ∀ z₁ ∈ annulus_at a (2 * r) (R / 2), ∀ z₂ ∈ annulus_at a (2 * r) (R / 2),
          ∃ z_mid : CP1,
            dist (u z₁) (u z_mid) ≤ (C / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)) ∧
            dist (u z_mid) (u z₂) ≤ (C / 2) * Real.sqrt (energyMeasure I u (annulus_at a r R)))
    (h_collar_decay : ∃ (K ε_neck : ℝ), 0 < K ∧ 0 < ε_neck ∧
      ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
        0 < r → 2 * r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u (annulus_at center r R) →
        energyMeasure I u (annulus_at center r R) < ε_neck →
        energyMeasureExtended I u (annulus_at center r R) ≠ ⊤ ∧
        (∀ r' R' : ℝ, r ≤ r' → R' ≤ R → 4 * r' < R' →
          energyMeasure I u (annulus_at center (2 * r') (R' / 2)) ≤
            K * (energyMeasure I u (annulus_at center r' (2 * r')) +
                 energyMeasure I u (annulus_at center (R' / 2) R'))))
    (h_punc_c1 : ∀ (u : CP1 → M) (p : CP1),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}) →
      energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤ →
      ∀ m_star : M, Filter.Tendsto u (𝓝[≠] p) (𝓝 m_star) →
        ContMDiffOn I_CP1 I 1 (Function.update u p m_star) Set.univ ∧
        ∀ v : TangentSpace I_CP1 p,
          ContinuousAt (fun z : CP1 =>
            mfderiv I_CP1 I (Function.update u p m_star) z (RiemannDomain.j z v) -
              (ClosedTameTarget.J (I := I) (Function.update u p m_star z))
                (mfderiv I_CP1 I (Function.update u p m_star) z v)) p)
    (h_tower_step : ∀ (u : CP1 → M) (Ω : Set CP1),
      IsOpen Ω → Analysis.WeakJHolomorphicOn I u Ω →
      ∀ k : ℕ, ContMDiffOn I_CP1 I (k : WithTop ℕ∞) u Ω →
        ∀ z ∈ Ω, ContMDiffWithinAt I_CP1 I ((k + 1 : ℕ) : WithTop ℕ∞) u Ω z)
    (h_aa_jets : ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1),
      IsOpen Ω →
      (∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω) →
      (∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) →
      ∀ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        ContinuousOn u_lim Ω →
        (∀ K ⊆ Ω, IsCompact K →
          TendstoUniformlyOn (fun n => u_seq (σ.1 n)) u_lim Filter.atTop K) →
        (∀ z ∈ Ω, Filter.Tendsto (fun n => u_seq (σ.1 n) z) Filter.atTop (𝓝 (u_lim z))) →
        ∀ z ∈ Ω, Analysis.HasLocalChartJetBoundsAt I (fun n => u_seq (σ.1 n)) u_lim z) :
    UniformNormalChartCertificates I fam :=
  UniformNormalChartCertificates.of_first_principles I fam h_bochner h_hit_ode h_osc_slices
    (by
      obtain ⟨K, ε_neck, hK, hε_neck, h_col⟩ := h_collar_decay
      let C₀ : ℝ := (1 + K) / K
      let a_decay : ℝ := Real.log C₀ / Real.log 2
      have hC₀_gt_one : 1 < C₀ := (one_lt_div hK).mpr (by linarith)
      have hC₀_pos : 0 < C₀ := lt_trans zero_lt_one hC₀_gt_one
      have ha_pos : 0 < a_decay :=
        div_pos (Real.log_pos hC₀_gt_one) (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      refine ⟨C₀, a_decay, ε_neck, hC₀_pos, ha_pos, hε_neck, ?_⟩
      intro u center r R hr h2rR hu hE
      obtain ⟨h_fin, h_step⟩ := h_col u center r R hr h2rR hu hE
      exact Analysis.satisfiesCylinderEnergyDecayWith_of_collar_hole_filling I u center hr hK h_fin h_step)
    h_punc_c1 h_tower_step h_aa_jets

--------------------------------------------------------------------------------
-- SECTION 6: `_unconditional` re-exports (Milestone M4 names)
--------------------------------------------------------------------------------

/-!
### `_unconditional` re-exports (Milestone M4 names)

Despite their names, these theorems are **not** unconditional: each takes
`certs : UniformNormalChartCertificates I fam` as a hypothesis and re-exports the corresponding
projection under the milestone M4 contract name.
-/

omit [I.Boundaryless] in
/-- Re-export of `discharge_h_weitz` (still conditional on `certs`). -/
theorem discharge_h_weitz_unconditional [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
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
  discharge_h_weitz_first_principles I fam certs

omit [I.Boundaryless] in
/-- Re-export of `discharge_h_hit_exit` (still conditional on `certs`). -/
theorem discharge_h_hit_exit_unconditional [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.HitExitProperty I M :=
  discharge_h_hit_exit_first_principles I fam certs

omit [I.Boundaryless] in
/-- Re-export of `discharge_h_osc` (still conditional on `certs`). -/
theorem discharge_h_osc_unconditional [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CollarOscillationProperty I M :=
  discharge_h_osc_first_principles I fam certs

omit [I.Boundaryless] in
/-- Re-export of `discharge_h_decay` (still conditional on `certs`). -/
theorem discharge_h_decay_unconditional [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    Analysis.CylinderEnergyDecayProperty I M :=
  discharge_h_decay_first_principles I fam certs

omit [I.Boundaryless] in
/-- Re-export of `discharge_h_punc` (still conditional on `certs`). -/
theorem discharge_h_punc_unconditional [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (p : CP1)
      (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
      (_h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤),
      ∃ (u_ext : CP1 → M),
        Continuous u_ext ∧
        Analysis.WeakJHolomorphicOn I u_ext Set.univ ∧
        EqOn u_ext u (punctured_sphere {p}) :=
  discharge_h_punc_first_principles I fam certs

omit [I.Boundaryless] in
/-- Re-export of `discharge_removal_of_singularities` (still conditional on `certs`). -/
theorem discharge_removal_of_singularities_unconditional [FiniteDimensional ℝ E]
    [T2Space M]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (p : CP1)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u (punctured_sphere {p}))
    (h_energy : energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤) :
    ∃! (u_smooth : CP1 → M),
      EqOn u_smooth u (punctured_sphere {p}) ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_smooth Set.univ :=
  discharge_removal_of_singularities I fam certs u p h_jhol h_energy

omit [I.Boundaryless] in
/-- Re-export of `discharge_h_tower` (still conditional on `certs`). -/
theorem discharge_h_tower_unconditional [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u : CP1 → M) (Ω : Set CP1) (_hΩ : IsOpen Ω)
      (_h_weak : Analysis.WeakJHolomorphicOn I u Ω) (n : ℕ),
      ContMDiffOn I_CP1 I (n : WithTop ℕ∞) u Ω :=
  discharge_h_tower_first_principles I fam certs

omit [I.Boundaryless] in
/-- Re-export of `discharge_nonlinear_elliptic_bootstrap` (still conditional on `certs`). -/
theorem discharge_nonlinear_elliptic_bootstrap_unconditional [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u : CP1 → M) (Ω : Set CP1) (hΩ : IsOpen Ω)
    (h_weak : Analysis.WeakJHolomorphicOn I u Ω) :
    ContMDiffOn I_CP1 I ∞ u Ω :=
  discharge_nonlinear_elliptic_bootstrap I fam certs u Ω hΩ h_weak

omit [I.Boundaryless] in
/-- Re-export of `discharge_h_aa` (still conditional on `certs`). -/
theorem discharge_h_aa_unconditional [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam) :
    ∀ (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (_h_open : IsOpen Ω)
      (_h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
      (_h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C),
      ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω :=
  discharge_h_aa_first_principles I fam certs

omit [I.Boundaryless] in
/-- Re-export of `discharge_local_smooth_compactness_of_arzela_ascoli` (still conditional on `certs`). -/
theorem discharge_local_smooth_compactness_of_arzela_ascoli_unconditional [FiniteDimensional ℝ E]
    (fam : UniformNormalChartFamily I (M := M))
    (certs : UniformNormalChartCertificates I fam)
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  discharge_local_smooth_compactness_of_arzela_ascoli I fam certs u_seq Ω h_open h_jhol h_grad_bdd

/-- First-principles proof of `Analysis.ArzelaAscoliProperty I M` (`cert_aa`) on any
`[BoundedChartedTarget I M] [FiniteDimensional ℝ E]` (`0 sorryAx`):
equicontinuity and $C^0_{\mathrm{loc}}(\Omega)$ extraction are discharged unconditionally via
`local_lipschitz_of_bounded_energy_density`, `Analysis.equicontinuous_of_local_lipschitz_on_domain`,
and `Analysis.exists_continuousOn_pointwise_convergent_subseq_on_domain`, and upgraded to full
frame-invariant `SmoothLocalConvergesOn` via `Analysis.smoothLocalConvergesOn_of_eventually_local_jet_bounds`. -/
theorem arzelaAscoliProperty_of_bounded_geometry_and_eventually_jet_bounds
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
  Analysis.arzelaAscoliProperty_of_equicontinuous_and_eventually_jet_bounds I M
    (fun u_seq Ω h_open h_jhol h_grad_bdd =>
      Analysis.equicontinuous_of_local_lipschitz_on_domain u_seq Ω
        (local_lipschitz_of_bounded_energy_density I u_seq Ω h_open h_jhol h_grad_bdd))
    h_jets

/-- First-principles proof of Contract A06 (`local_smooth_compactness`) on any
`[BoundedChartedTarget I M] [FiniteDimensional ℝ E]` via
`arzelaAscoliProperty_of_bounded_geometry_and_eventually_jet_bounds` (`0 sorryAx`). -/
theorem local_smooth_compactness_of_bounded_geometry_and_eventually_jet_bounds
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
        ∀ z ∈ Ω, Analysis.EventuallyHasLocalChartJetBoundsAt I (fun n => u_seq (σ.1 n)) u_lim z)
    (u_seq : ℕ → (CP1 → M)) (Ω : Set CP1) (h_open : IsOpen Ω)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Ω)
    (h_grad_bdd : ∀ K ⊆ Ω, IsCompact K → ∃ C > 0, ∀ n, ∀ z ∈ K, riemannianEnergyDensity I (u_seq n) z ≤ C) :
    ∃ (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M),
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Ω ∧
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Ω :=
  Analysis.local_smooth_compactness_of_arzelaAscoliProperty I
    (arzelaAscoliProperty_of_bounded_geometry_and_eventually_jet_bounds I h_jets)
    u_seq Ω h_open h_jhol h_grad_bdd

end GromovCompactness
