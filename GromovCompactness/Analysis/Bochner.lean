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
  use 1, 0
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro u hu w
  let e := fun z => riemannianEnergyDensity I u (stereo_chart.symm z)
  have he_nonneg : 0 ≤ e w := riemannianEnergyDensity_nonneg I u (stereo_chart.symm w)
  have h_lhs : -1 * (e w)^2 - 0 * (e w) ≤ 0 := by
    have : 0 ≤ (e w)^2 := sq_nonneg (e w)
    linarith
  by_cases h_diff : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 e) w
  · sorry
  · rw [laplacian2D_zero_of_not_diff e w h_diff]
    linarith

end GromovCompactness.Analysis
