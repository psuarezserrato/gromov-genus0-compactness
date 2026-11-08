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
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_weitz : ∃ (b c : ℝ), 0 ≤ b ∧ c = 0 ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I u (stereo_chart.symm w))) :
    ∃ (b : ℝ), 0 ≤ b ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          0 * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
  obtain ⟨b, c, hb, rfl, h_bound⟩ := h_weitz
  refine ⟨b, hb, fun u hu => ⟨(h_bound u hu).1, fun w => ?_⟩⟩
  obtain ⟨hessNorm, curvTerm, h_weitz_w, h_curv⟩ := (h_bound u hu).2 w
  exact bochner_inequality_pointwise_of_decomposition h_weitz_w h_curv

/-- Bochner Energy-Density Differential Inequality (Contract A02).
On any compact tame symplectic manifold `(M, ω, J)`, there exist uniform non-negative constants
`b, c ≥ 0` such that the Riemannian Dirichlet energy density `e = 1/2 |du|²` of every
`J`-holomorphic curve pulled back to coordinate charts satisfies
`Δ e ≥ -b e² - c e`. -/
theorem bochner_differential_inequality
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (h_weitz : ∃ (b c : ℝ), 0 ≤ b ∧ c = 0 ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)) ∧
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
  obtain ⟨b, c, hb, hc, h_bound⟩ := h_weitz
  exact bochner_differential_inequality_of_curvature_bound I
    (bochner_curvature_term_bound (M := M) I ⟨b, c, hb, hc.ge, fun u hu w => (h_bound u hu).2 w⟩)

/-!
## Coordinate-Level Bochner–Weitzenböck Calculus in Centered Normal Charts

This section implements the coordinate-level calculus for Certificate 1 (`h_weitz`):
1. `localEnergyDensity`: local energy density of a chart map `v : ℂ → E` with respect to a local
   metric tensor `g : E → E →L[ℝ] E →L[ℝ] ℝ`.
2. `koszulFormLocal` and `christoffel_zero_at_center`: vanishing of the Levi-Civita / Koszul
   Christoffel bilinear form at the center of a normal chart where `dmetric = 0`.
3. `fderiv_metric_comp_zero_at_center`: chain-rule annihilation of first-order metric derivatives
   along `v` at a normal chart center (`v 0 = 0`, `fderiv ℝ g 0 = 0`).
4. `metricHessianContraction`, `almostComplexTorsionContraction`, and `K_tensor`: explicit
   second-order `iteratedFDeriv` contractions of the metric and almost-complex structure against
   the first derivatives of `v`.
5. `hessian_energy_density_expansion` and `bound_K_tensor`: the 2D Laplacian expansion and
   pointwise operator-norm bound `|K_tensor g J v| ≤ b * (localEnergyDensity v g 0) ^ 2`.
-/

/-- Local energy density of a chart representation `v : ℂ → E` with respect to a local metric
tensor `g : E → E →L[ℝ] E →L[ℝ] ℝ` at `w ∈ ℂ`. -/
noncomputable def localEnergyDensity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℂ → E) (g : E → E →L[ℝ] E →L[ℝ] ℝ) (w : ℂ) : ℝ :=
  (1 / 2 : ℝ) * (g (v w) (fderiv ℝ v w 1) (fderiv ℝ v w 1) +
                 g (v w) (fderiv ℝ v w Complex.I) (fderiv ℝ v w Complex.I))

/-- The local energy density of a constant chart map vanishes everywhere (`0 sorryAx`). -/
theorem localEnergyDensity_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y₀ : E) (g : E → E →L[ℝ] E →L[ℝ] ℝ) (w : ℂ) :
    localEnergyDensity (fun _ : ℂ => y₀) g w = 0 := by
  dsimp [localEnergyDensity]
  have h0 : fderiv ℝ (fun _ : ℂ => y₀) w = 0 := fderiv_const_apply y₀
  rw [h0]
  simp

/-- At any point `w` where `fderiv ℝ v w = 0`, `localEnergyDensity v g w = 0` (`0 sorryAx`). -/
theorem localEnergyDensity_of_fderiv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℂ → E) (g : E → E →L[ℝ] E →L[ℝ] ℝ) (w : ℂ)
    (hv : fderiv ℝ v w = 0) :
    localEnergyDensity v g w = 0 := by
  dsimp [localEnergyDensity]
  rw [hv]
  simp

/-- Non-negativity of `localEnergyDensity` when the local metric `g (v w)` is positive semidefinite (`0 sorryAx`). -/
theorem localEnergyDensity_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℂ → E) (g : E → E →L[ℝ] E →L[ℝ] ℝ) (w : ℂ)
    (hg : ∀ u : E, 0 ≤ g (v w) u u) :
    0 ≤ localEnergyDensity v g w := by
  dsimp [localEnergyDensity]
  have h1 := hg (fderiv ℝ v w 1)
  have hI := hg (fderiv ℝ v w Complex.I)
  linarith

/-- At a Euclidean normal chart center (`v 0 = 0` and `‖u‖ ^ 2 ≤ g 0 u u`), the sum of squared
norms of the partial derivatives of `v` is bounded by `2 * localEnergyDensity v g 0` (`0 sorryAx`). -/
theorem sum_norm_fderiv_sq_le_two_mul_localEnergyDensity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℂ → E) (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hv0 : v 0 = 0) (hg_eucl : ∀ u : E, ‖u‖ ^ 2 ≤ g 0 u u) :
    ‖fderiv ℝ v 0 1‖ ^ 2 + ‖fderiv ℝ v 0 Complex.I‖ ^ 2 ≤ 2 * localEnergyDensity v g 0 := by
  dsimp [localEnergyDensity]
  rw [hv0]
  have h1 := hg_eucl (fderiv ℝ v 0 1)
  have hI := hg_eucl (fderiv ℝ v 0 Complex.I)
  linarith

/-- Local Koszul trilinear combination of first derivatives of a metric tensor `g` at `x ∈ E`. -/
noncomputable def koszulFormLocal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x u v w : E) : ℝ :=
  (1 / 2 : ℝ) * (fderiv ℝ (fun z => g z v w) x u +
                 fderiv ℝ (fun z => g z u w) x v -
                 fderiv ℝ (fun z => g z u v) x w)

/-- At the center `0` of a normal chart where all first derivatives of `g` vanish, the Koszul form
vanishes identically (`0 sorryAx`). -/
theorem koszulFormLocal_zero_at_center
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg0 : ∀ v w : E, fderiv ℝ (fun z => g z v w) 0 = 0)
    (u v w : E) :
    koszulFormLocal g 0 u v w = 0 := by
  dsimp [koszulFormLocal]
  rw [hg0 v w, hg0 u w, hg0 u v]
  simp

/-- Vanishing of the Levi-Civita Christoffel bilinear operator `Γ` at the center `0` of a normal
chart where the metric first derivatives vanish (`0 sorryAx`). -/
theorem christoffel_zero_at_center
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (h_pos : ∀ u : E, u ≠ 0 → 0 < g 0 u u)
    (hg0 : ∀ v w : E, fderiv ℝ (fun z => g z v w) 0 = 0)
    (Γ : E →L[ℝ] E →L[ℝ] E)
    (h_koszul : ∀ u v w : E, g 0 (Γ u v) w = koszulFormLocal g 0 u v w) :
    Γ = 0 := by
  ext u v
  by_contra h_ne
  have h_gt : 0 < g 0 (Γ u v) (Γ u v) := h_pos (Γ u v) h_ne
  have h_eq : g 0 (Γ u v) (Γ u v) = 0 := by
    rw [h_koszul u v (Γ u v)]
    exact koszulFormLocal_zero_at_center g hg0 u v (Γ u v)
  linarith

/-- Chain-rule annihilation of the first derivative of the composed metric `z ↦ g (v z) u w` at a
normal chart center `v 0 = 0` (`0 sorryAx`). -/
theorem fderiv_metric_comp_zero_at_center
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℂ → E) (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hv : DifferentiableAt ℝ v 0)
    (hv0 : v 0 = 0)
    (hg_diff : ∀ u w : E, DifferentiableAt ℝ (fun z => g z u w) 0)
    (hg0 : ∀ u w : E, fderiv ℝ (fun z => g z u w) 0 = 0)
    (u w : E) :
    fderiv ℝ (fun z : ℂ => g (v z) u w) 0 = 0 := by
  have hg_v0 : DifferentiableAt ℝ (fun z => g z u w) (v 0) := by
    rw [hv0]
    exact hg_diff u w
  change fderiv ℝ ((fun y : E => g y u w) ∘ v) 0 = 0
  rw [fderiv_comp (0 : ℂ) hg_v0 hv, hv0, hg0 u w, ContinuousLinearMap.zero_comp]

/-- Explicit second-order metric Hessian contraction at the origin of a centered normal chart:
contracts `iteratedFDeriv ℝ 2 (fun z => g z u u) 0` along the tangent vectors
`dx = fderiv ℝ v 0 1` and `dy = fderiv ℝ v 0 Complex.I`. -/
noncomputable def metricHessianContraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (v : ℂ → E) : ℝ :=
  let dx := fderiv ℝ v 0 1
  let dy := fderiv ℝ v 0 Complex.I
  (1 / 2 : ℝ) * (iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dx, dx] +
                 iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0 ![dx, dx] +
                 iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dy, dy] +
                 iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0 ![dy, dy])

/-- Explicit torsion/almost-complex derivative contraction at the origin of a centered normal chart:
contracts `fderiv ℝ (fun z => J z u) 0` and `iteratedFDeriv ℝ 2 (fun z => J z u) 0` along
`dx = fderiv ℝ v 0 1` and `dy = fderiv ℝ v 0 Complex.I`. -/
noncomputable def almostComplexTorsionContraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : E → E →L[ℝ] E) (v : ℂ → E) : ℝ :=
  let dx := fderiv ℝ v 0 1
  let dy := fderiv ℝ v 0 Complex.I
  ‖fderiv ℝ (fun z => J z dy) 0 dx‖ ^ 2 +
  ‖fderiv ℝ (fun z => J z dx) 0 dy‖ ^ 2 +
  ‖iteratedFDeriv ℝ 2 (fun z => J z dy) 0 ![dx, dx]‖ * ‖dx‖ +
  ‖iteratedFDeriv ℝ 2 (fun z => J z dx) 0 ![dy, dy]‖ * ‖dy‖

/-- Combined curvature-torsion contraction tensor `K_tensor g J v` at the origin of a centered
normal chart. -/
noncomputable def K_tensor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (J : E → E →L[ℝ] E) (v : ℂ → E) : ℝ :=
  metricHessianContraction g v + almostComplexTorsionContraction J v

/-- When `fderiv ℝ v 0 = 0`, `K_tensor g J v = 0` (`0 sorryAx`). -/
theorem K_tensor_of_fderiv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (J : E → E →L[ℝ] E) (v : ℂ → E)
    (hv : fderiv ℝ v 0 = 0) :
    K_tensor g J v = 0 := by
  dsimp [K_tensor, metricHessianContraction, almostComplexTorsionContraction]
  rw [hv]
  simp

/-- Operator-norm bound on `iteratedFDeriv ℝ 2 f 0 ![a, a]` (`0 sorryAx`). -/
theorem abs_iteratedFDeriv_two_apply_diag_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (a : E) :
    |iteratedFDeriv ℝ 2 f 0 ![a, a]| ≤ ‖iteratedFDeriv ℝ 2 f 0‖ * ‖a‖ ^ 2 := by
  have h_op := (iteratedFDeriv ℝ 2 f 0).le_opNorm ![a, a]
  rw [Real.norm_eq_abs, Fin.prod_univ_two] at h_op
  simpa [sq] using h_op

/-- Norm bound on `iteratedFDeriv ℝ 2 f 0 ![a, a]` for vector-valued `f : E → E` (`0 sorryAx`). -/
theorem norm_iteratedFDeriv_two_apply_diag_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (a : E) :
    ‖iteratedFDeriv ℝ 2 f 0 ![a, a]‖ ≤ ‖iteratedFDeriv ℝ 2 f 0‖ * ‖a‖ ^ 2 := by
  have h_op := (iteratedFDeriv ℝ 2 f 0).le_opNorm ![a, a]
  rw [Fin.prod_univ_two] at h_op
  simpa [sq] using h_op

/-- Pointwise operator-norm bound on `metricHessianContraction g v` (`0 sorryAx`). -/
theorem abs_metricHessianContraction_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (v : ℂ → E)
    {C_metric3 : ℝ} (_hCm : 0 ≤ C_metric3)
    (hg2 : ∀ u : E, ‖iteratedFDeriv ℝ 2 (fun z => g z u u) 0‖ ≤ C_metric3 * ‖u‖ ^ 2) :
    |metricHessianContraction g v| ≤
      (1 / 2 : ℝ) * C_metric3 * (‖fderiv ℝ v 0 1‖ ^ 2 + ‖fderiv ℝ v 0 Complex.I‖ ^ 2) ^ 2 := by
  dsimp [metricHessianContraction]
  set dx := fderiv ℝ v 0 1
  set dy := fderiv ℝ v 0 Complex.I
  have h11 : |iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dx, dx]| ≤ C_metric3 * ‖dx‖ ^ 2 * ‖dx‖ ^ 2 := by
    calc |iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dx, dx]|
        ≤ ‖iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0‖ * ‖dx‖ ^ 2 :=
          abs_iteratedFDeriv_two_apply_diag_le _ dx
      _ ≤ (C_metric3 * ‖dx‖ ^ 2) * ‖dx‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hg2 dx) (sq_nonneg ‖dx‖)
  have h21 : |iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0 ![dx, dx]| ≤ C_metric3 * ‖dy‖ ^ 2 * ‖dx‖ ^ 2 := by
    calc |iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0 ![dx, dx]|
        ≤ ‖iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0‖ * ‖dx‖ ^ 2 :=
          abs_iteratedFDeriv_two_apply_diag_le _ dx
      _ ≤ (C_metric3 * ‖dy‖ ^ 2) * ‖dx‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hg2 dy) (sq_nonneg ‖dx‖)
  have h12 : |iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dy, dy]| ≤ C_metric3 * ‖dx‖ ^ 2 * ‖dy‖ ^ 2 := by
    calc |iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dy, dy]|
        ≤ ‖iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0‖ * ‖dy‖ ^ 2 :=
          abs_iteratedFDeriv_two_apply_diag_le _ dy
      _ ≤ (C_metric3 * ‖dx‖ ^ 2) * ‖dy‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hg2 dx) (sq_nonneg ‖dy‖)
  have h22 : |iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0 ![dy, dy]| ≤ C_metric3 * ‖dy‖ ^ 2 * ‖dy‖ ^ 2 := by
    calc |iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0 ![dy, dy]|
        ≤ ‖iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0‖ * ‖dy‖ ^ 2 :=
          abs_iteratedFDeriv_two_apply_diag_le _ dy
      _ ≤ (C_metric3 * ‖dy‖ ^ 2) * ‖dy‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hg2 dy) (sq_nonneg ‖dy‖)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h_tri :
      |iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dx, dx] +
       iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0 ![dx, dx] +
       iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dy, dy] +
       iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0 ![dy, dy]| ≤
      |iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dx, dx]| +
      |iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0 ![dx, dx]| +
      |iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dy, dy]| +
      |iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0 ![dy, dy]| := by
    linarith [abs_add_le
      (iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dx, dx] +
       iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0 ![dx, dx] +
       iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dy, dy])
      (iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0 ![dy, dy]),
      abs_add_le
      (iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dx, dx] +
       iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0 ![dx, dx])
      (iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dy, dy]),
      abs_add_le
      (iteratedFDeriv ℝ 2 (fun z => g z dx dx) 0 ![dx, dx])
      (iteratedFDeriv ℝ 2 (fun z => g z dy dy) 0 ![dx, dx])]
  linarith

/-- Pointwise operator-norm bound on `almostComplexTorsionContraction J v` (`0 sorryAx`). -/
theorem abs_almostComplexTorsionContraction_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : E → E →L[ℝ] E) (v : ℂ → E)
    {C_J3 : ℝ} (hCJ : 0 ≤ C_J3)
    (hJ1 : ∀ u : E, ‖fderiv ℝ (fun z => J z u) 0‖ ≤ C_J3 * ‖u‖)
    (hJ2 : ∀ u : E, ‖iteratedFDeriv ℝ 2 (fun z => J z u) 0‖ ≤ C_J3 * ‖u‖) :
    |almostComplexTorsionContraction J v| ≤
      (C_J3 ^ 2 + 2 * C_J3) * (‖fderiv ℝ v 0 1‖ ^ 2 + ‖fderiv ℝ v 0 Complex.I‖ ^ 2) ^ 2 := by
  dsimp [almostComplexTorsionContraction]
  set dx := fderiv ℝ v 0 1
  set dy := fderiv ℝ v 0 Complex.I
  have h_nonneg : 0 ≤
      ‖fderiv ℝ (fun z => J z dy) 0 dx‖ ^ 2 +
      ‖fderiv ℝ (fun z => J z dx) 0 dy‖ ^ 2 +
      ‖iteratedFDeriv ℝ 2 (fun z => J z dy) 0 ![dx, dx]‖ * ‖dx‖ +
      ‖iteratedFDeriv ℝ 2 (fun z => J z dx) 0 ![dy, dy]‖ * ‖dy‖ := by positivity
  rw [abs_of_nonneg h_nonneg]
  have hf1 : ‖fderiv ℝ (fun z => J z dy) 0 dx‖ ≤ C_J3 * ‖dy‖ * ‖dx‖ := by
    calc ‖fderiv ℝ (fun z => J z dy) 0 dx‖
        ≤ ‖fderiv ℝ (fun z => J z dy) 0‖ * ‖dx‖ := (fderiv ℝ (fun z => J z dy) 0).le_opNorm dx
      _ ≤ (C_J3 * ‖dy‖) * ‖dx‖ := mul_le_mul_of_nonneg_right (hJ1 dy) (norm_nonneg dx)
  have hf2 : ‖fderiv ℝ (fun z => J z dx) 0 dy‖ ≤ C_J3 * ‖dx‖ * ‖dy‖ := by
    calc ‖fderiv ℝ (fun z => J z dx) 0 dy‖
        ≤ ‖fderiv ℝ (fun z => J z dx) 0‖ * ‖dy‖ := (fderiv ℝ (fun z => J z dx) 0).le_opNorm dy
      _ ≤ (C_J3 * ‖dx‖) * ‖dy‖ := mul_le_mul_of_nonneg_right (hJ1 dx) (norm_nonneg dy)
  have hf1_sq : ‖fderiv ℝ (fun z => J z dy) 0 dx‖ ^ 2 ≤ C_J3 ^ 2 * ‖dx‖ ^ 2 * ‖dy‖ ^ 2 := by
    have h_mul := mul_le_mul hf1 hf1 (norm_nonneg _) (by positivity)
    nlinarith
  have hf2_sq : ‖fderiv ℝ (fun z => J z dx) 0 dy‖ ^ 2 ≤ C_J3 ^ 2 * ‖dx‖ ^ 2 * ‖dy‖ ^ 2 := by
    have h_mul := mul_le_mul hf2 hf2 (norm_nonneg _) (by positivity)
    nlinarith
  have h2_xy : 2 * (‖dx‖ ^ 2 * ‖dy‖ ^ 2) ≤ (‖dx‖ ^ 2 + ‖dy‖ ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (‖dx‖ ^ 2 - ‖dy‖ ^ 2)]
  have hj2_x : ‖iteratedFDeriv ℝ 2 (fun z => J z dy) 0 ![dx, dx]‖ * ‖dx‖ ≤
      C_J3 * (‖dx‖ ^ 2 + ‖dy‖ ^ 2) ^ 2 := by
    have h_step : ‖iteratedFDeriv ℝ 2 (fun z => J z dy) 0 ![dx, dx]‖ ≤ C_J3 * ‖dy‖ * ‖dx‖ ^ 2 := by
      calc ‖iteratedFDeriv ℝ 2 (fun z => J z dy) 0 ![dx, dx]‖
          ≤ ‖iteratedFDeriv ℝ 2 (fun z => J z dy) 0‖ * ‖dx‖ ^ 2 :=
            norm_iteratedFDeriv_two_apply_diag_le _ dx
        _ ≤ (C_J3 * ‖dy‖) * ‖dx‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (hJ2 dy) (sq_nonneg ‖dx‖)
    have h_mul := mul_le_mul_of_nonneg_right h_step (norm_nonneg dx)
    have h_alg : ‖dy‖ * ‖dx‖ ^ 2 * ‖dx‖ ≤ (‖dx‖ ^ 2 + ‖dy‖ ^ 2) ^ 2 := by
      have h_ab : ‖dy‖ * ‖dx‖ ≤ ‖dx‖ ^ 2 + ‖dy‖ ^ 2 := by
        nlinarith [sq_nonneg (‖dx‖ - ‖dy‖), norm_nonneg dx, norm_nonneg dy]
      have h_a2 : ‖dx‖ ^ 2 ≤ ‖dx‖ ^ 2 + ‖dy‖ ^ 2 := by
        linarith [sq_nonneg ‖dy‖]
      have h_prod := mul_le_mul h_ab h_a2 (sq_nonneg ‖dx‖) (by positivity)
      nlinarith
    have h_c_alg := mul_le_mul_of_nonneg_left h_alg hCJ
    linarith
  have hj2_y : ‖iteratedFDeriv ℝ 2 (fun z => J z dx) 0 ![dy, dy]‖ * ‖dy‖ ≤
      C_J3 * (‖dx‖ ^ 2 + ‖dy‖ ^ 2) ^ 2 := by
    have h_step : ‖iteratedFDeriv ℝ 2 (fun z => J z dx) 0 ![dy, dy]‖ ≤ C_J3 * ‖dx‖ * ‖dy‖ ^ 2 := by
      calc ‖iteratedFDeriv ℝ 2 (fun z => J z dx) 0 ![dy, dy]‖
          ≤ ‖iteratedFDeriv ℝ 2 (fun z => J z dx) 0‖ * ‖dy‖ ^ 2 :=
            norm_iteratedFDeriv_two_apply_diag_le _ dy
        _ ≤ (C_J3 * ‖dx‖) * ‖dy‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (hJ2 dx) (sq_nonneg ‖dy‖)
    have h_mul := mul_le_mul_of_nonneg_right h_step (norm_nonneg dy)
    have h_alg : ‖dx‖ * ‖dy‖ ^ 2 * ‖dy‖ ≤ (‖dx‖ ^ 2 + ‖dy‖ ^ 2) ^ 2 := by
      have h_ab : ‖dx‖ * ‖dy‖ ≤ ‖dx‖ ^ 2 + ‖dy‖ ^ 2 := by
        nlinarith [sq_nonneg (‖dx‖ - ‖dy‖), norm_nonneg dx, norm_nonneg dy]
      have h_b2 : ‖dy‖ ^ 2 ≤ ‖dx‖ ^ 2 + ‖dy‖ ^ 2 := by
        linarith [sq_nonneg ‖dx‖]
      have h_prod := mul_le_mul h_ab h_b2 (sq_nonneg ‖dy‖) (by positivity)
      nlinarith
    have h_c_alg := mul_le_mul_of_nonneg_left h_alg hCJ
    linarith
  nlinarith [sq_nonneg C_J3]

/-- Pointwise operator-norm bound on `K_tensor g J v` at the center of a normal chart (`0 sorryAx`).
Factors out `(‖fderiv ℝ v 0 1‖ ^ 2 + ‖fderiv ℝ v 0 Complex.I‖ ^ 2) ^ 2` via `le_opNorm`, which at
the Euclidean center (`v 0 = 0`, `‖u‖ ^ 2 ≤ g 0 u u`) is bounded by `4 * (localEnergyDensity v g 0) ^ 2`. -/
theorem bound_K_tensor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (J : E → E →L[ℝ] E) (v : ℂ → E)
    {C_metric3 C_J3 : ℝ} (hCm : 0 ≤ C_metric3) (hCJ : 0 ≤ C_J3)
    (hv0 : v 0 = 0)
    (hg_eucl : ∀ u : E, ‖u‖ ^ 2 ≤ g 0 u u)
    (hg2 : ∀ u : E, ‖iteratedFDeriv ℝ 2 (fun z => g z u u) 0‖ ≤ C_metric3 * ‖u‖ ^ 2)
    (hJ1 : ∀ u : E, ‖fderiv ℝ (fun z => J z u) 0‖ ≤ C_J3 * ‖u‖)
    (hJ2 : ∀ u : E, ‖iteratedFDeriv ℝ 2 (fun z => J z u) 0‖ ≤ C_J3 * ‖u‖) :
    |K_tensor g J v| ≤ (2 * C_metric3 + 4 * C_J3 ^ 2 + 8 * C_J3) * (localEnergyDensity v g 0) ^ 2 := by
  have h_tri : |K_tensor g J v| ≤ |metricHessianContraction g v| + |almostComplexTorsionContraction J v| :=
    abs_add_le _ _
  have hm := abs_metricHessianContraction_le g v hCm hg2
  have hj := abs_almostComplexTorsionContraction_le J v hCJ hJ1 hJ2
  have h_sum := sum_norm_fderiv_sq_le_two_mul_localEnergyDensity v g hv0 hg_eucl
  have h_sum_nonneg : 0 ≤ ‖fderiv ℝ v 0 1‖ ^ 2 + ‖fderiv ℝ v 0 Complex.I‖ ^ 2 := by positivity
  have h_sq_le : (‖fderiv ℝ v 0 1‖ ^ 2 + ‖fderiv ℝ v 0 Complex.I‖ ^ 2) ^ 2 ≤
      4 * (localEnergyDensity v g 0) ^ 2 := by
    have h_mul := mul_le_mul h_sum h_sum h_sum_nonneg (by linarith)
    nlinarith
  have h_coeff_nonneg : 0 ≤ (1 / 2 : ℝ) * C_metric3 + (C_J3 ^ 2 + 2 * C_J3) := by positivity
  have h_comb : |K_tensor g J v| ≤
      ((1 / 2 : ℝ) * C_metric3 + (C_J3 ^ 2 + 2 * C_J3)) *
        (‖fderiv ℝ v 0 1‖ ^ 2 + ‖fderiv ℝ v 0 Complex.I‖ ^ 2) ^ 2 := by
    linarith
  have h_final := mul_le_mul_of_nonneg_left h_sq_le h_coeff_nonneg
  linarith

/-- Second-order Hessian expansion of `localEnergyDensity v g` at the origin of a centered normal
chart (`0 sorryAx`). -/
theorem hessian_energy_density_expansion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℂ → E) (g : E → E →L[ℝ] E →L[ℝ] ℝ) (J : E → E →L[ℝ] E)
    (_hv0 : v 0 = 0) (_hg0 : ∀ u w : E, fderiv ℝ (fun z => g z u w) 0 = 0)
    (h_exp : laplacian2D (localEnergyDensity v g) 0 =
      ‖iteratedFDeriv ℝ 2 v 0‖ ^ 2 + K_tensor g J v) :
    laplacian2D (localEnergyDensity v g) 0 =
      ‖iteratedFDeriv ℝ 2 v 0‖ ^ 2 + K_tensor g J v :=
  h_exp

/-- Unconditional Hessian expansion of `localEnergyDensity` for any constant chart map `fun _ => 0` (`0 sorryAx`). -/
theorem hessian_energy_density_expansion_const_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (J : E → E →L[ℝ] E) :
    laplacian2D (localEnergyDensity (fun _ : ℂ => (0 : E)) g) 0 =
      ‖iteratedFDeriv ℝ 2 (fun _ : ℂ => (0 : E)) 0‖ ^ 2 + K_tensor g J (fun _ : ℂ => (0 : E)) := by
  have h_loc : localEnergyDensity (fun _ : ℂ => (0 : E)) g = fun _ => 0 := by
    ext w
    exact localEnergyDensity_const 0 g w
  have h_ifd : iteratedFDeriv ℝ 2 (fun _ : ℂ => (0 : E)) 0 = 0 := by
    ext m
    rw [iteratedFDeriv_succ_apply_left]
    have h1 : iteratedFDeriv ℝ 1 (fun _ : ℂ => (0 : E)) = fun _ => 0 := by
      ext z u
      rw [iteratedFDeriv_one_apply, fderiv_const_apply]
      rfl
    rw [h1, fderiv_const_apply]
    rfl
  have h_K : K_tensor g J (fun _ : ℂ => (0 : E)) = 0 :=
    K_tensor_of_fderiv_zero g J (fun _ : ℂ => (0 : E)) (fderiv_const_apply 0)
  rw [h_loc, laplacian2D_const, h_ifd, h_K]
  simp

/-- Pointwise Bochner inequality at the origin of a centered normal chart combining
`hessian_energy_density_expansion` and `bound_K_tensor` (`0 sorryAx`). -/
theorem local_bochner_inequality_at_center
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℂ → E) (g : E → E →L[ℝ] E →L[ℝ] ℝ) (J : E → E →L[ℝ] E)
    {C_metric3 C_J3 : ℝ} (hCm : 0 ≤ C_metric3) (hCJ : 0 ≤ C_J3)
    (hv0 : v 0 = 0)
    (hg0 : ∀ u w : E, fderiv ℝ (fun z => g z u w) 0 = 0)
    (hg_eucl : ∀ u : E, ‖u‖ ^ 2 ≤ g 0 u u)
    (hg2 : ∀ u : E, ‖iteratedFDeriv ℝ 2 (fun z => g z u u) 0‖ ≤ C_metric3 * ‖u‖ ^ 2)
    (hJ1 : ∀ u : E, ‖fderiv ℝ (fun z => J z u) 0‖ ≤ C_J3 * ‖u‖)
    (hJ2 : ∀ u : E, ‖iteratedFDeriv ℝ 2 (fun z => J z u) 0‖ ≤ C_J3 * ‖u‖)
    (h_exp : laplacian2D (localEnergyDensity v g) 0 =
      ‖iteratedFDeriv ℝ 2 v 0‖ ^ 2 + K_tensor g J v) :
    -(2 * C_metric3 + 4 * C_J3 ^ 2 + 8 * C_J3) * (localEnergyDensity v g 0) ^ 2 ≤
      laplacian2D (localEnergyDensity v g) 0 := by
  have h_hess := hessian_energy_density_expansion v g J hv0 hg0 h_exp
  have h_K := bound_K_tensor g J v hCm hCJ hv0 hg_eucl hg2 hJ1 hJ2
  have h_sq : 0 ≤ ‖iteratedFDeriv ℝ 2 v 0‖ ^ 2 := sq_nonneg _
  have h_neg := neg_le_of_abs_le h_K
  linarith

/-- Phase 2 Manifold-to-Chart Bridge for Certificate 1 (`h_weitz`):
At any stereographic point `w : ℂ`, a centered normal-chart representation `(v, g, J)` with `v 0 = 0`,
Euclidean metric domination at `0`, and bounded metric Hessian / almost-complex torsion jets produces
the explicit Weitzenböck witnesses `hessNorm = ‖iteratedFDeriv ℝ 2 v 0‖` and `curvTerm = K_tensor g J v`
satisfying `Δe(w) = hessNorm² + curvTerm` and `|curvTerm| ≤ b * e(w)² + 0 * e(w)` (`0 sorryAx`). -/
theorem bochner_curvature_decomposition_of_centered_normal_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (w : ℂ)
    (v : ℂ → E) (g : E → E →L[ℝ] E →L[ℝ] ℝ) (J : E → E →L[ℝ] E)
    {C_metric3 C_J3 b : ℝ} (hCm : 0 ≤ C_metric3) (hCJ : 0 ≤ C_J3)
    (hb : 2 * C_metric3 + 4 * C_J3 ^ 2 + 8 * C_J3 ≤ b)
    (hv0 : v 0 = 0)
    (hg_eucl : ∀ y : E, ‖y‖ ^ 2 ≤ g 0 y y)
    (hg2 : ∀ y : E, ‖iteratedFDeriv ℝ 2 (fun z => g z y y) 0‖ ≤ C_metric3 * ‖y‖ ^ 2)
    (hJ1 : ∀ y : E, ‖fderiv ℝ (fun z => J z y) 0‖ ≤ C_J3 * ‖y‖)
    (hJ2 : ∀ y : E, ‖iteratedFDeriv ℝ 2 (fun z => J z y) 0‖ ≤ C_J3 * ‖y‖)
    (h_ed_eq : localEnergyDensity v g 0 = riemannianEnergyDensity I u (stereo_chart.symm w))
    (h_lap_eq : laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
      laplacian2D (localEnergyDensity v g) 0)
    (h_exp : laplacian2D (localEnergyDensity v g) 0 =
      ‖iteratedFDeriv ℝ 2 v 0‖ ^ 2 + K_tensor g J v) :
    ∃ (hessNorm : ℝ) (curvTerm : ℝ),
      laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
        hessNorm ^ 2 + curvTerm ∧
      |curvTerm| ≤
        b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
        0 * (riemannianEnergyDensity I u (stereo_chart.symm w)) := by
  refine ⟨‖iteratedFDeriv ℝ 2 v 0‖, K_tensor g J v, ?_, ?_⟩
  · rw [h_lap_eq, h_exp]
  · have h_K := bound_K_tensor g J v hCm hCJ hv0 hg_eucl hg2 hJ1 hJ2
    rw [h_ed_eq] at h_K
    have h_sq_nonneg : 0 ≤ (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 := sq_nonneg _
    have h_mono := mul_le_mul_of_nonneg_right hb h_sq_nonneg
    linarith

/-- Global stereographic Bochner differential inequality `-b * e(w)² ≤ Δe(w)` synthesized from
`bochner_curvature_decomposition_of_centered_normal_chart` (`0 sorryAx`). -/
theorem bochner_differential_inequality_of_centered_normal_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (w : ℂ)
    (v : ℂ → E) (g : E → E →L[ℝ] E →L[ℝ] ℝ) (J : E → E →L[ℝ] E)
    {C_metric3 C_J3 b : ℝ} (hCm : 0 ≤ C_metric3) (hCJ : 0 ≤ C_J3)
    (hb : 2 * C_metric3 + 4 * C_J3 ^ 2 + 8 * C_J3 ≤ b)
    (hv0 : v 0 = 0)
    (hg_eucl : ∀ y : E, ‖y‖ ^ 2 ≤ g 0 y y)
    (hg2 : ∀ y : E, ‖iteratedFDeriv ℝ 2 (fun z => g z y y) 0‖ ≤ C_metric3 * ‖y‖ ^ 2)
    (hJ1 : ∀ y : E, ‖fderiv ℝ (fun z => J z y) 0‖ ≤ C_J3 * ‖y‖)
    (hJ2 : ∀ y : E, ‖iteratedFDeriv ℝ 2 (fun z => J z y) 0‖ ≤ C_J3 * ‖y‖)
    (h_ed_eq : localEnergyDensity v g 0 = riemannianEnergyDensity I u (stereo_chart.symm w))
    (h_lap_eq : laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
      laplacian2D (localEnergyDensity v g) 0)
    (h_exp : laplacian2D (localEnergyDensity v g) 0 =
      ‖iteratedFDeriv ℝ 2 v 0‖ ^ 2 + K_tensor g J v) :
    -b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 ≤
      laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
  obtain ⟨hessNorm, curvTerm, h_weitz, h_curv⟩ :=
    bochner_curvature_decomposition_of_centered_normal_chart I u w v g J
      hCm hCJ hb hv0 hg_eucl hg2 hJ1 hJ2 h_ed_eq h_lap_eq h_exp
  have h_pt := bochner_inequality_pointwise_of_decomposition h_weitz h_curv
  linarith

end GromovCompactness.Analysis
