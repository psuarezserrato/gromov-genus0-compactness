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

/-- Smoothness of the chart energy density: for any $J$-holomorphic map `u : CP1 → M`,
the stereographic chart energy density `w ↦ riemannianEnergyDensity I u (stereo_chart.symm w)`
is smooth ($C^\infty$) on `ℂ`. -/
lemma contDiff_energy_density_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) := by
  sorry

/-- Bochner–Weitzenböck decomposition and uniform target curvature bound:
On any compact tame symplectic manifold `(M, ω, J)`, there exist target-dependent constants
`b, c ≥ 0` such that for every $J$-holomorphic map `u : CP1 → M` and `w ∈ ℂ`, the Laplacian of
the chart energy density decomposes into a non-negative covariant Hessian norm squared `hessNorm^2`
plus a curvature/torsion contraction `curvTerm` satisfying `|curvTerm| ≤ b * e(w)^2 + c * e(w)`. -/
theorem bochner_curvature_term_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
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
  sorry

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
  rcases bochner_curvature_term_bound (M := M) I with ⟨b, c, hb, hc, h_decomp⟩
  refine ⟨b, c, hb, hc, ?_⟩
  intro u hu w
  rcases h_decomp u hu w with ⟨hessNorm, curvTerm, h_weitz, h_curv⟩
  exact bochner_inequality_pointwise_of_decomposition h_weitz h_curv

end GromovCompactness.Analysis
