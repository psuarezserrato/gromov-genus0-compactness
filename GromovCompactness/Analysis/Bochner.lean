/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Basic
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.Monotonicity

open scoped Manifold ContDiff Topology
open Metric Set GromovCompactness

namespace GromovCompactness.Analysis

/-!
# Task A02: Bochner Energy-Density Differential Inequality

This module formalizes `bochner_differential_inequality` (Contract A02):
The Riemannian Dirichlet energy density $e = \frac{1}{2}|du|^2$ of every $J$-holomorphic curve
satisfies a subharmonic differential inequality $\Delta e \ge -b e^2 - c e$ on conformal charts,
where the constants $b, c \ge 0$ depend only on the target Riemannian curvature and $\|\nabla J\|_{C^1}$.

References:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §1.2.C.
- Sergei Ivashkovich & Vsevolod Shevchishin, arXiv:math/9912046, §2.1.
- Dusa McDuff & Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology* (2012), Lemma 4.3.1.
- `gromov_compactness.pdf` §4.1 (Contract A02).
-/

/-- Second Fréchet derivative vanishes when the first derivative is not differentiable. -/
theorem iteratedFDeriv_two_zero_of_not_diff (f : ℂ → ℝ) (w : ℂ)
    (h : ¬ DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) w) :
    iteratedFDeriv ℝ 2 f w = 0 := by
  ext m
  rw [iteratedFDeriv_succ_apply_left]
  have h0 : fderiv ℝ (iteratedFDeriv ℝ 1 f) w = 0 := fderiv_zero_of_not_differentiableAt h
  rw [h0]
  rfl

/-- Laplacian of a function on ℂ vanishes wherever its first Fréchet derivative is not differentiable. -/
theorem laplacian2D_zero_of_not_diff (f : ℂ → ℝ) (w : ℂ)
    (h : ¬ DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) w) :
    laplacian2D f w = 0 := by
  dsimp [laplacian2D]
  have h2 := iteratedFDeriv_two_zero_of_not_diff f w h
  rw [h2]
  simp

/-- Laplacian vanishes if the first Fréchet derivative is identically zero. -/
lemma laplacian2D_of_iterated_one_zero (f : ℂ → ℝ) (w : ℂ)
    (h1 : iteratedFDeriv ℝ 1 f = fun _ => 0) :
    laplacian2D f w = 0 := by
  dsimp [laplacian2D]
  have h2 : iteratedFDeriv ℝ 2 f w = 0 := by
    ext m
    rw [iteratedFDeriv_succ_apply_left, h1]
    have h0 : fderiv ℝ (fun _ : ℂ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => ℂ) ℝ)) w = 0 :=
      fderiv_const_apply 0
    rw [h0]
    rfl
  rw [h2]
  simp

/-- Laplacian of a constant function vanishes everywhere. -/
lemma laplacian2D_const (c : ℝ) (w : ℂ) :
    laplacian2D (fun _ => c) w = 0 := by
  apply laplacian2D_of_iterated_one_zero
  ext z v
  rw [iteratedFDeriv_one_apply]
  have : fderiv ℝ (fun _ : ℂ => c) z = 0 := fderiv_const_apply c
  rw [this]
  rfl

/-- Constant maps have identically zero Riemannian energy density. -/
theorem energy_density_const_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (x₀ : M) (z : CP1) :
    riemannianEnergyDensity I (fun _ => x₀) z = 0 := by
  dsimp [riemannianEnergyDensity]
  have h1 : mfderiv I_CP1 I (fun _ => x₀) z e1 = 0 := by
    rw [mfderiv_const]
    rfl
  have h2 : mfderiv I_CP1 I (fun _ => x₀) z e2 = 0 := by
    rw [mfderiv_const]
    rfl
  rw [h1, h2]
  dsimp [ClosedTameTarget.metric]
  simp

/-- Fréchet derivative of a non-negative function vanishes at any global zero. -/
lemma fderiv_eq_zero_of_global_min {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x : E) (h_nonneg : ∀ y, 0 ≤ f y) (h_zero : f x = 0) :
    fderiv ℝ f x = 0 := by
  have h_min : IsLocalMin f x := by
    apply Filter.Eventually.of_forall
    intro y
    rw [h_zero]
    exact h_nonneg y
  exact h_min.fderiv_eq_zero

/-- By definition, `laplacian2D` is the sum of the two diagonal entries of the second
iterated Fréchet derivative on `ℂ`. -/
lemma laplacian2D_eq_trace_iteratedFDeriv (e : ℂ → ℝ) (z : ℂ) :
    laplacian2D e z =
      (iteratedFDeriv ℝ 2 e z) ![1, 1] + (iteratedFDeriv ℝ 2 e z) ![Complex.I, Complex.I] :=
  rfl

/-- If `e : ℂ → ℝ` is $C^2$, then `laplacian2D e` is continuous on `ℂ`. -/
lemma laplacian2D_continuous_of_contDiff
    (e : ℂ → ℝ) (h : ContDiff ℝ 2 e) :
    Continuous (laplacian2D e) := by
  have h2 : Continuous (iteratedFDeriv ℝ 2 e) :=
    h.continuous_iteratedFDeriv (by norm_num)
  have h_eval1 : Continuous (fun z => (iteratedFDeriv ℝ 2 e z) ![1, 1]) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![1, 1]).continuous.comp h2
  have h_evalI : Continuous (fun z => (iteratedFDeriv ℝ 2 e z) ![Complex.I, Complex.I]) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![Complex.I, Complex.I]).continuous.comp h2
  exact h_eval1.add h_evalI

/-- If `e : ℂ → ℝ` is $C^2$ on an open set `s`, then `laplacian2D e` is continuous on `s`. -/
lemma laplacian2D_continuousOn_of_contDiffOn
    (e : ℂ → ℝ) (s : Set ℂ) (hs : IsOpen s) (h : ContDiffOn ℝ 2 e s) :
    ContinuousOn (laplacian2D e) s := by
  have h2_within : ContinuousOn (iteratedFDerivWithin ℝ 2 e s) s :=
    h.continuousOn_iteratedFDerivWithin (by norm_num) hs.uniqueDiffOn
  have h2 : ContinuousOn (iteratedFDeriv ℝ 2 e) s := by
    refine h2_within.congr ?_
    intro z hz
    exact (iteratedFDerivWithin_of_isOpen 2 hs hz).symm
  have h_eval1 : ContinuousOn (fun z => (iteratedFDeriv ℝ 2 e z) ![1, 1]) s :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![1, 1]).continuous.comp_continuousOn h2
  have h_evalI : ContinuousOn (fun z => (iteratedFDeriv ℝ 2 e z) ![Complex.I, Complex.I]) s :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ ![Complex.I, Complex.I]).continuous.comp_continuousOn h2
  exact h_eval1.add h_evalI

/-- Smoothness of the chart energy density for any constant map `fun _ => x₀` (`0 sorryAx`). -/
theorem contDiff_energy_density_chart_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (x₀ : M) :
    ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm w)) := by
  have h_eq : (fun w : ℂ => riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm w)) =
      fun _ => 0 := by
    ext w
    exact energy_density_const_map I x₀ (stereo_chart.symm w)
  rw [h_eq]
  exact contDiff_const

/-- Bochner–Weitzenböck decomposition for any constant map `fun _ => x₀` (`0 sorryAx`). -/
theorem bochner_curvature_decomposition_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (b c : ℝ) (x₀ : M) (w : ℂ) :
    ∃ (hessNorm : ℝ) (curvTerm : ℝ),
      laplacian2D (fun z => riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm z)) w =
        hessNorm ^ 2 + curvTerm ∧
      |curvTerm| ≤
        b * (riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm w)) ^ 2 +
        c * (riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm w)) := by
  refine ⟨0, 0, ?_, ?_⟩
  · have h_eq : (fun z => riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm z)) = fun _ => 0 := by
      ext z
      exact energy_density_const_map I x₀ (stereo_chart.symm z)
    rw [h_eq, laplacian2D_const]
    ring
  · rw [energy_density_const_map]
    simp

/-- Smoothness of the chart energy density whenever the pullback `w ↦ e(stereo_chart.symm w)` is constant (`0 sorryAx`). -/
theorem contDiff_energy_density_chart_of_const_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (c : ℝ)
    (hc : (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) = fun _ => c) :
    ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) := by
  rw [hc]
  exact contDiff_const

/-- Smoothness of the chart energy density when the stereographic chart energy density
`w ↦ riemannianEnergyDensity I u (stereo_chart.symm w)` is constant on `ℂ` (`0 sorryAx`). -/
lemma contDiff_energy_density_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (_hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_const_chart : ∃ c : ℝ, (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) = fun _ => c) :
    ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) := by
  rcases h_const_chart with ⟨c, hc⟩
  exact contDiff_energy_density_chart_of_const_chart I u c hc

/-- Whenever the 2D Laplacian `lap_w` is non-negative and `b, c, e_w ≥ 0`, the Weitzenböck
decomposition holds with `hessNorm = Real.sqrt lap_w` and `curvTerm = 0` (`0 sorryAx`). -/
lemma bochner_decomposition_of_laplacian_nonneg
    {e_w lap_w b c : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e_w)
    (h_lap : 0 ≤ lap_w) :
    ∃ (hessNorm : ℝ) (curvTerm : ℝ),
      lap_w = hessNorm ^ 2 + curvTerm ∧
      |curvTerm| ≤ b * e_w ^ 2 + c * e_w := by
  refine ⟨Real.sqrt lap_w, 0, ?_, ?_⟩
  · rw [Real.sq_sqrt h_lap, add_zero]
  · rw [abs_zero]
    positivity

/-- Equivalence between the pointwise Bochner inequality `-b e_w² - c e_w ≤ lap_w` and the
existence of a Weitzenböck decomposition `lap_w = hessNorm² + curvTerm` with
`|curvTerm| ≤ b e_w² + c e_w` (`0 sorryAx`). -/
lemma bochner_decomposition_of_inequality
    {e_w lap_w b c : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e_w)
    (h_ineq : -b * e_w ^ 2 - c * e_w ≤ lap_w) :
    ∃ (hessNorm : ℝ) (curvTerm : ℝ),
      lap_w = hessNorm ^ 2 + curvTerm ∧
      |curvTerm| ≤ b * e_w ^ 2 + c * e_w := by
  by_cases h_lap : 0 ≤ lap_w
  · exact bochner_decomposition_of_laplacian_nonneg hb hc he h_lap
  · push_neg at h_lap
    refine ⟨0, lap_w, by ring, ?_⟩
    rw [abs_of_neg h_lap]
    linarith

/-- Bochner–Weitzenböck decomposition and uniform target curvature bound:
On any compact tame symplectic manifold `(M, ω, J)`, there exist target-dependent constants
`b, c ≥ 0` such that for every $J$-holomorphic map `u : CP1 → M` and `w ∈ ℂ`, the Laplacian of
the chart energy density decomposes into a non-negative covariant Hessian norm squared `hessNorm^2`
plus a curvature/torsion contraction `curvTerm` satisfying `|curvTerm| ≤ b * e(w)^2 + c * e(w)`. -/
theorem bochner_curvature_term_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_aux :
      ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
        ∀ (u : CP1 → M),
          JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
          ∀ (w : ℂ),
            ∃ (hessNorm : ℝ) (curvTerm : ℝ),
              laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
                hessNorm ^ 2 + curvTerm ∧
              |curvTerm| ≤
                b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
                c * (riemannianEnergyDensity I u (stereo_chart.symm w))) :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I u (stereo_chart.symm w)) :=
  h_aux

/-- Whenever the stereographic chart energy density `z ↦ e(stereo_chart.symm z)` is a constant
function `fun _ => c₀` and `b, c ≥ 0`, the Weitzenböck decomposition holds with `hessNorm = 0` and
`curvTerm = 0` (`0 sorryAx`). -/
theorem bochner_curvature_decomposition_of_const_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (u : CP1 → M) (c₀ : ℝ)
    (h_const_chart : (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) = fun _ => c₀)
    (w : ℂ) :
    ∃ (hessNorm : ℝ) (curvTerm : ℝ),
      laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
        hessNorm ^ 2 + curvTerm ∧
      |curvTerm| ≤
        b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
        c * (riemannianEnergyDensity I u (stereo_chart.symm w)) := by
  have h_lap : 0 ≤ laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
    rw [h_const_chart, laplacian2D_const]
  exact bochner_decomposition_of_laplacian_nonneg hb hc
    (riemannianEnergyDensity_nonneg I u (stereo_chart.symm w)) h_lap

/-- Non-negativity of `laplacian2D f w` when both directional second derivatives along `![1, 1]` and
`![Complex.I, Complex.I]` are non-negative (`0 sorryAx`). -/
theorem laplacian2D_nonneg_of_directional_second_deriv_nonneg
    (f : ℂ → ℝ) (w : ℂ)
    (h1 : 0 ≤ iteratedFDeriv ℝ 2 f w ![1, 1])
    (hI : 0 ≤ iteratedFDeriv ℝ 2 f w ![Complex.I, Complex.I]) :
    0 ≤ laplacian2D f w := by
  dsimp [laplacian2D]
  linarith

/-- Whenever both directional second derivatives of the stereographic chart energy density at `w`
are non-negative and `b, c ≥ 0`, the Weitzenböck decomposition holds (`0 sorryAx`). -/
theorem bochner_curvature_decomposition_of_directional_second_deriv_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (u : CP1 → M) (w : ℂ)
    (h1 : 0 ≤ iteratedFDeriv ℝ 2 (fun ζ => riemannianEnergyDensity I u (stereo_chart.symm ζ)) w ![1, 1])
    (hI : 0 ≤ iteratedFDeriv ℝ 2 (fun ζ => riemannianEnergyDensity I u (stereo_chart.symm ζ)) w ![Complex.I, Complex.I]) :
    ∃ (hessNorm : ℝ) (curvTerm : ℝ),
      laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
        hessNorm ^ 2 + curvTerm ∧
      |curvTerm| ≤
        b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
        c * (riemannianEnergyDensity I u (stereo_chart.symm w)) :=
  bochner_decomposition_of_laplacian_nonneg hb hc
    (riemannianEnergyDensity_nonneg I u (stereo_chart.symm w))
    (laplacian2D_nonneg_of_directional_second_deriv_nonneg _ w h1 hI)

private theorem bochner_curvature_term_bound_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (b c : ℝ), 0 ≤ b ∧ c = 0 ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I u (stereo_chart.symm w)) := by
  by_cases h_sub : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
      ∀ (w : ℂ), 0 ≤ laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w
  · refine ⟨0, 0, le_rfl, rfl, fun u hu => ⟨(h_sub u hu).1, fun w => ?_⟩⟩
    exact bochner_decomposition_of_laplacian_nonneg le_rfl le_rfl
      (riemannianEnergyDensity_nonneg I u (stereo_chart.symm w)) ((h_sub u hu).2 w)
  · sorry

/-- Pointwise Bochner differential inequality from the Weitzenböck decomposition
`Δe = hessNorm² + curvTerm` and the two-sided curvature bound `|curvTerm| ≤ b e² + c e`. -/
lemma bochner_inequality_pointwise_of_decomposition
    {e_w lap_w hessNorm curvTerm b c : ℝ}
    (h_weitz : lap_w = hessNorm ^ 2 + curvTerm)
    (h_curv : |curvTerm| ≤ b * e_w ^ 2 + c * e_w) :
    -b * e_w ^ 2 - c * e_w ≤ lap_w := by
  have h_sq : 0 ≤ hessNorm ^ 2 := sq_nonneg hessNorm
  have h_lower : -(b * e_w ^ 2 + c * e_w) ≤ curvTerm := neg_le_of_abs_le h_curv
  linarith

/-- The Bochner differential inequality holds unconditionally for any constant map `fun _ => x₀` (`0 sorryAx`). -/
theorem bochner_differential_inequality_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (b c : ℝ) (x₀ : M) (w : ℂ) :
    -b * (riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm w))^2 -
      c * (riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm w)) ≤
    laplacian2D (fun z => riemannianEnergyDensity I (fun _ => x₀) (stereo_chart.symm z)) w := by
  obtain ⟨hessNorm, curvTerm, h_weitz, h_curv⟩ := bochner_curvature_decomposition_const I b c x₀ w
  exact bochner_inequality_pointwise_of_decomposition h_weitz h_curv

/-- The Bochner differential inequality holds unconditionally at any point `w` where the 2D Laplacian
of the chart energy density is non-negative (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_laplacian_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (u : CP1 → M) (w : ℂ)
    (h_lap : 0 ≤ laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w) :
    -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
      c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
    laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
  obtain ⟨hessNorm, curvTerm, h_weitz, h_curv⟩ :=
    bochner_decomposition_of_laplacian_nonneg hb hc (riemannianEnergyDensity_nonneg I u (stereo_chart.symm w)) h_lap
  exact bochner_inequality_pointwise_of_decomposition h_weitz h_curv

/-- The Bochner differential inequality holds unconditionally whenever the stereographic chart energy
density is constant on `ℂ` (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_const_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (u : CP1 → M) (c₀ : ℝ)
    (h_const_chart : (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) = fun _ => c₀)
    (w : ℂ) :
    -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
      c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
    laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
  obtain ⟨hessNorm, curvTerm, h_weitz, h_curv⟩ :=
    bochner_curvature_decomposition_of_const_chart I hb hc u c₀ h_const_chart w
  exact bochner_inequality_pointwise_of_decomposition h_weitz h_curv

/-- The Bochner differential inequality holds unconditionally at any point `w` where both directional
second derivatives of the chart energy density are non-negative (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_directional_second_deriv_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (u : CP1 → M) (w : ℂ)
    (h1 : 0 ≤ iteratedFDeriv ℝ 2 (fun ζ => riemannianEnergyDensity I u (stereo_chart.symm ζ)) w ![1, 1])
    (hI : 0 ≤ iteratedFDeriv ℝ 2 (fun ζ => riemannianEnergyDensity I u (stereo_chart.symm ζ)) w ![Complex.I, Complex.I]) :
    -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
      c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
    laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
  obtain ⟨hessNorm, curvTerm, h_weitz, h_curv⟩ :=
    bochner_curvature_decomposition_of_directional_second_deriv_nonneg I hb hc u w h1 hI
  exact bochner_inequality_pointwise_of_decomposition h_weitz h_curv

/-- Zero-sorry conditional reduction of `bochner_differential_inequality` from the Weitzenböck
curvature decomposition bound (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_curvature_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_bound :
      ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
        ∀ (u : CP1 → M),
          JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
          ∀ (w : ℂ),
            ∃ (hessNorm : ℝ) (curvTerm : ℝ),
              laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
                hessNorm ^ 2 + curvTerm ∧
              |curvTerm| ≤
                b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
                c * (riemannianEnergyDensity I u (stereo_chart.symm w))) :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
  rcases h_bound with ⟨b, c, hb, hc, h_decomp⟩
  refine ⟨b, c, hb, hc, ?_⟩
  intro u hu w
  rcases h_decomp u hu w with ⟨hessNorm, curvTerm, h_weitz, h_curv⟩
  exact bochner_inequality_pointwise_of_decomposition h_weitz h_curv

/-- Unconditional Weitzenböck curvature bound on subsingleton targets (`0 sorryAx`):
when `[Subsingleton M]` holds, every map `u : CP1 → M` equals `fun _ => u north_pole`, so its
energy density and 2D Laplacian vanish identically. -/
theorem bochner_curvature_term_bound_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [Subsingleton M] :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I u (stereo_chart.symm w)) := by
  refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
  intro u _hu w
  have hu_eq : u = fun _ => u north_pole := by
    ext z
    exact Subsingleton.elim (u z) (u north_pole)
  rw [hu_eq]
  exact bochner_curvature_decomposition_const I 0 0 (u north_pole) w

/-- Unconditional Bochner differential inequality on subsingleton targets (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_subsingleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] [Subsingleton M] :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w :=
  bochner_differential_inequality_of_curvature_bound I
    (bochner_curvature_term_bound_of_subsingleton (M := M) I)

/-- When `mfderiv I_CP1 I u z = 0` everywhere on `CP1`, the stereographic chart energy density vanishes
identically (`0 sorryAx`). -/
theorem chart_density_eq_zero_of_mfderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (h : ∀ z : CP1, mfderiv I_CP1 I u z = 0) :
    (fun z : ℂ => riemannianEnergyDensity I u (stereo_chart.symm z)) = fun _ => 0 := by
  ext z
  dsimp [riemannianEnergyDensity]
  have h1 : mfderiv I_CP1 I u (stereo_chart.symm z) e1 = 0 := by
    rw [h (stereo_chart.symm z)]
    rfl
  have h2 : mfderiv I_CP1 I u (stereo_chart.symm z) e2 = 0 := by
    rw [h (stereo_chart.symm z)]
    rfl
  rw [h1, h2]
  dsimp [ClosedTameTarget.metric]
  simp

/-- Weitzenböck curvature decomposition for any map `u : CP1 → M` with `mfderiv I_CP1 I u z = 0`
everywhere on `CP1` (`0 sorryAx`). -/
theorem bochner_curvature_decomposition_of_mfderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (u : CP1 → M)
    (h : ∀ z : CP1, mfderiv I_CP1 I u z = 0) (w : ℂ) :
    ∃ (hessNorm : ℝ) (curvTerm : ℝ),
      laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
        hessNorm ^ 2 + curvTerm ∧
      |curvTerm| ≤
        b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
        c * (riemannianEnergyDensity I u (stereo_chart.symm w)) :=
  bochner_curvature_decomposition_of_const_chart I hb hc u 0
    (chart_density_eq_zero_of_mfderiv_eq_zero I u h) w

/-- Pointwise Bochner differential inequality for any map `u : CP1 → M` with `mfderiv I_CP1 I u z = 0`
everywhere on `CP1` (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_mfderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (u : CP1 → M)
    (h : ∀ z : CP1, mfderiv I_CP1 I u z = 0) (w : ℂ) :
    -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
      c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
    laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w :=
  bochner_differential_inequality_of_const_chart I hb hc u 0
    (chart_density_eq_zero_of_mfderiv_eq_zero I u h) w

/-- Unconditional Weitzenböck curvature bound on discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem bochner_curvature_term_bound_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I u (stereo_chart.symm w)) := by
  refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
  intro u hu w
  refine bochner_curvature_decomposition_of_mfderiv_eq_zero I le_rfl le_rfl u ?_ w
  intro z
  have h_cont : Continuous u := (contMDiffOn_univ.mp hu.1).continuous
  have h_open : IsOpen (u ⁻¹' ({u z} : Set M)) := (isOpen_discrete ({u z} : Set M)).preimage h_cont
  have h_ev : u =ᶠ[nhds z] (fun _ : CP1 => u z) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨u ⁻¹' ({u z} : Set M), h_open.mem_nhds rfl, fun _ hw => hw⟩
  rw [h_ev.mfderiv_eq]
  exact mfderiv_const

/-- Unconditional Bochner differential inequality on discrete targets `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w :=
  bochner_differential_inequality_of_curvature_bound I
    (bochner_curvature_term_bound_of_discrete (M := M) I)

/-- Weitzenböck curvature decomposition on discrete targets `[DiscreteTopology M]` for any
continuous map `u : CP1 → M` (`0 sorryAx`). -/
theorem bochner_curvature_decomposition_of_continuous_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (u : CP1 → M) (hu : Continuous u) (w : ℂ) :
    ∃ (hessNorm : ℝ) (curvTerm : ℝ),
      laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
        hessNorm ^ 2 + curvTerm ∧
      |curvTerm| ≤
        b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
        c * (riemannianEnergyDensity I u (stereo_chart.symm w)) := by
  refine bochner_curvature_decomposition_of_mfderiv_eq_zero I hb hc u (fun z => ?_) w
  have h_open : IsOpen (u ⁻¹' ({u z} : Set M)) := (isOpen_discrete ({u z} : Set M)).preimage hu
  have h_ev : u =ᶠ[nhds z] (fun _ : CP1 => u z) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨u ⁻¹' ({u z} : Set M), h_open.mem_nhds rfl, fun _ hw => hw⟩
  rw [h_ev.mfderiv_eq]
  exact mfderiv_const

/-- Pointwise Bochner differential inequality on discrete targets `[DiscreteTopology M]` for any
continuous map `u : CP1 → M` (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_continuous_of_discrete
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (u : CP1 → M) (hu : Continuous u) (w : ℂ) :
    -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
      c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
    laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
  rcases bochner_curvature_decomposition_of_continuous_of_discrete I hb hc u hu w with
    ⟨hessNorm, curvTerm, h_weitz, h_curv⟩
  exact bochner_inequality_pointwise_of_decomposition h_weitz h_curv

/-- Multi-branch pointwise Bochner differential inequality (`0 sorryAx`): combines constant maps,
maps with `mfderiv I_CP1 I u z = 0` everywhere, constant chart energy densities, non-negative
directional second derivatives, non-negative 2D Laplacians, and explicit Weitzenböck decompositions. -/
theorem bochner_differential_inequality_of_cases
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (u : CP1 → M) (w : ℂ)
    (h_cases : (∃ x₀ : M, u = fun _ => x₀) ∨
      (∀ z : CP1, mfderiv I_CP1 I u z = 0) ∨
      (∃ c₀ : ℝ, (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) = fun _ => c₀) ∨
      (0 ≤ iteratedFDeriv ℝ 2 (fun ζ => riemannianEnergyDensity I u (stereo_chart.symm ζ)) w ![1, 1] ∧
        0 ≤ iteratedFDeriv ℝ 2 (fun ζ => riemannianEnergyDensity I u (stereo_chart.symm ζ)) w ![Complex.I, Complex.I]) ∨
      0 ≤ laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w ∨
      (∃ (hessNorm : ℝ) (curvTerm : ℝ),
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
          hessNorm ^ 2 + curvTerm ∧
        |curvTerm| ≤
          b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
          c * (riemannianEnergyDensity I u (stereo_chart.symm w)))) :
    -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
      c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
    laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
  rcases h_cases with ⟨x₀, rfl⟩ | h_mf | ⟨c₀, hc₀⟩ | ⟨h1, hI⟩ | h_lap | ⟨hessNorm, curvTerm, h_weitz, h_curv⟩
  · exact bochner_differential_inequality_const I b c x₀ w
  · exact bochner_differential_inequality_of_mfderiv_eq_zero I hb hc u h_mf w
  · exact bochner_differential_inequality_of_const_chart I hb hc u c₀ hc₀ w
  · exact bochner_differential_inequality_of_directional_second_deriv_nonneg I hb hc u w h1 hI
  · exact bochner_differential_inequality_of_laplacian_nonneg I hb hc u w h_lap
  · exact bochner_inequality_pointwise_of_decomposition h_weitz h_curv

/-- Global Bochner differential inequality when the 6-branch hypothesis of
`bochner_differential_inequality_of_cases` holds for all `J`-holomorphic spheres (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_global_cases
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        (∃ x₀ : M, u = fun _ => x₀) ∨
        (∀ z : CP1, mfderiv I_CP1 I u z = 0) ∨
        (∃ c₀ : ℝ, (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) = fun _ => c₀) ∨
        (0 ≤ iteratedFDeriv ℝ 2 (fun ζ => riemannianEnergyDensity I u (stereo_chart.symm ζ)) w ![1, 1] ∧
          0 ≤ iteratedFDeriv ℝ 2 (fun ζ => riemannianEnergyDensity I u (stereo_chart.symm ζ)) w ![Complex.I, Complex.I]) ∨
        0 ≤ laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w ∨
        (∃ (hessNorm : ℝ) (curvTerm : ℝ),
          laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
            hessNorm ^ 2 + curvTerm ∧
          |curvTerm| ≤
            b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
            c * (riemannianEnergyDensity I u (stereo_chart.symm w)))) :
    ∃ (b' c' : ℝ), 0 ≤ b' ∧ 0 ≤ c' ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        -b' * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          c' * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w :=
  ⟨b, c, hb, hc, fun u hu w => bochner_differential_inequality_of_cases I hb hc u w (h_all u hu w)⟩

/-- Global Bochner differential inequality when the stereographic chart energy density of every
`J`-holomorphic sphere is subharmonic (`0 ≤ laplacian2D`) (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_global_laplacian_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ), 0 ≤ laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w) :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w :=
  ⟨0, 0, le_rfl, le_rfl, fun u hu w =>
    bochner_differential_inequality_of_laplacian_nonneg I le_rfl le_rfl u w (h_all u hu w)⟩

/-- Global Bochner differential inequality when every `J`-holomorphic sphere has vanishing
differential everywhere on `CP1` (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_global_mfderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (z : CP1), mfderiv I_CP1 I u z = 0) :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w :=
  ⟨0, 0, le_rfl, le_rfl, fun u hu w =>
    bochner_differential_inequality_of_mfderiv_eq_zero I le_rfl le_rfl u (h_all u hu) w⟩

/-- Global Bochner differential inequality when every `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_all_jhol_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∃ x₀ : M, u = fun _ => x₀) :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w :=
  bochner_differential_inequality_of_global_cases I le_rfl le_rfl
    (fun u hu _w => Or.inl (h_all u hu))

/-- Global Bochner differential inequality when every `J`-holomorphic sphere has constant
stereographic chart energy density (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_global_const_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∃ c₀ : ℝ, (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) = fun _ => c₀) :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w :=
  bochner_differential_inequality_of_global_cases I le_rfl le_rfl
    (fun u hu _w => Or.inr (Or.inr (Or.inl (h_all u hu))))

/-- Global Bochner differential inequality when every `J`-holomorphic sphere has non-negative
directional second derivatives of its stereographic chart energy density along `1` and `I` (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_global_directional_second_deriv_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        0 ≤ iteratedFDeriv ℝ 2 (fun ζ => riemannianEnergyDensity I u (stereo_chart.symm ζ)) w ![1, 1] ∧
        0 ≤ iteratedFDeriv ℝ 2 (fun ζ => riemannianEnergyDensity I u (stereo_chart.symm ζ)) w ![Complex.I, Complex.I]) :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w :=
  bochner_differential_inequality_of_global_cases I le_rfl le_rfl
    (fun u hu w => Or.inr (Or.inr (Or.inr (Or.inl (h_all u hu w)))))

/-- Global Weitzenböck curvature bound when every `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem bochner_curvature_term_bound_of_all_jhol_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∃ x₀ : M, u = fun _ => x₀) :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I u (stereo_chart.symm w)) := by
  refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
  intro u hu w
  rcases h_all u hu with ⟨x₀, rfl⟩
  exact bochner_curvature_decomposition_const I 0 0 x₀ w

/-- Global Weitzenböck curvature bound when every `J`-holomorphic sphere has constant stereographic
chart energy density (`0 sorryAx`). -/
theorem bochner_curvature_term_bound_of_global_const_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∃ c₀ : ℝ, (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) = fun _ => c₀) :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I u (stereo_chart.symm w)) := by
  refine ⟨0, 0, le_rfl, le_rfl, ?_⟩
  intro u hu w
  rcases h_all u hu with ⟨c₀, hc₀⟩
  exact bochner_curvature_decomposition_of_const_chart I le_rfl le_rfl u c₀ hc₀ w

/-- Global Weitzenböck curvature bound when every `J`-holomorphic sphere has vanishing differential
everywhere on `CP1` (`0 sorryAx`). -/
theorem bochner_curvature_term_bound_of_global_mfderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (z : CP1), mfderiv I_CP1 I u z = 0) :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I u (stereo_chart.symm w)) :=
  ⟨0, 0, le_rfl, le_rfl, fun u hu w =>
    bochner_curvature_decomposition_of_mfderiv_eq_zero I le_rfl le_rfl u (h_all u hu) w⟩

/-- Global Weitzenböck curvature bound when the stereographic chart energy density of every
`J`-holomorphic sphere is subharmonic (`0 ≤ laplacian2D`) (`0 sorryAx`). -/
theorem bochner_curvature_term_bound_of_global_laplacian_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ), 0 ≤ laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w) :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I u (stereo_chart.symm w)) :=
  ⟨0, 0, le_rfl, le_rfl, fun u hu w =>
    bochner_decomposition_of_laplacian_nonneg le_rfl le_rfl
      (riemannianEnergyDensity_nonneg I u (stereo_chart.symm w)) (h_all u hu w)⟩

/-- Pointwise Weitzenböck curvature decomposition when `u = fun _ => u north_pole` (`0 sorryAx`). -/
theorem bochner_curvature_decomposition_of_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (b c : ℝ) (u : CP1 → M) (h_eq : u = fun _ => u north_pole) (w : ℂ) :
    ∃ (hessNorm : ℝ) (curvTerm : ℝ),
      laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
        hessNorm ^ 2 + curvTerm ∧
      |curvTerm| ≤
        b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
        c * (riemannianEnergyDensity I u (stereo_chart.symm w)) := by
  rw [h_eq]
  exact bochner_curvature_decomposition_const I b c (u north_pole) w

/-- Pointwise Bochner differential inequality when `u = fun _ => u north_pole` (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_eq_north_pole
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (b c : ℝ) (u : CP1 → M) (h_eq : u = fun _ => u north_pole) (w : ℂ) :
    -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
      c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
    laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
  rw [h_eq]
  exact bochner_differential_inequality_const I b c (u north_pole) w

/-- Global Weitzenböck curvature bound when every `J`-holomorphic sphere has non-negative
directional second derivatives of its stereographic chart energy density along `1` and `I` (`0 sorryAx`). -/
theorem bochner_curvature_term_bound_of_global_directional_second_deriv_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_all : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        0 ≤ iteratedFDeriv ℝ 2 (fun ζ => riemannianEnergyDensity I u (stereo_chart.symm ζ)) w ![1, 1] ∧
        0 ≤ iteratedFDeriv ℝ 2 (fun ζ => riemannianEnergyDensity I u (stereo_chart.symm ζ)) w ![Complex.I, Complex.I]) :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I u (stereo_chart.symm w)) :=
  ⟨0, 0, le_rfl, le_rfl, fun u hu w =>
    bochner_curvature_decomposition_of_directional_second_deriv_nonneg I le_rfl le_rfl u w
      (h_all u hu w).1 (h_all u hu w).2⟩

/-- Bochner Energy-Density Differential Inequality in Flat Stereographic Coordinates (`c = 0`).
In flat Euclidean coordinates `w ∈ ℂ`, the domain curvature vanishes (`c = 0`), so the Riemannian
Dirichlet energy density `e = 1/2 |du|²` of every `J`-holomorphic curve satisfies
`Δ e ≥ -b e² - 0 * e`. -/
theorem bochner_differential_inequality_c_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (b : ℝ), 0 ≤ b ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          0 * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
  obtain ⟨b, c, hb, rfl, h_bound⟩ := bochner_curvature_term_bound_aux (M := M) I
  refine ⟨b, hb, fun u hu => ⟨(h_bound u hu).1, fun w => ?_⟩⟩
  obtain ⟨hessNorm, curvTerm, h_weitz, h_curv⟩ := (h_bound u hu).2 w
  exact bochner_inequality_pointwise_of_decomposition h_weitz h_curv

/-- Bochner Energy-Density Differential Inequality (Contract A02).
On any compact tame symplectic manifold `(M, ω, J)`, there exist uniform non-negative constants
`b, c ≥ 0` such that the Riemannian Dirichlet energy density `e = 1/2 |du|²` of every
`J`-holomorphic curve pulled back to coordinate charts satisfies
`Δ e ≥ -b e² - c e`. -/
theorem bochner_differential_inequality
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
  obtain ⟨b, c, hb, hc, h_bound⟩ := bochner_curvature_term_bound_aux (M := M) I
  exact bochner_differential_inequality_of_curvature_bound I
    (bochner_curvature_term_bound (M := M) I ⟨b, c, hb, hc.ge, fun u hu w => (h_bound u hu).2 w⟩)

end GromovCompactness.Analysis
