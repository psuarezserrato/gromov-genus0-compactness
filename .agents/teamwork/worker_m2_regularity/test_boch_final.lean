import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Basic
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.Monotonicity

open scoped Manifold ContDiff Topology
open Metric Set GromovCompactness GromovCompactness.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

theorem iteratedFDeriv_two_zero_of_not_diff (f : ℂ → ℝ) (w : ℂ)
    (h : ¬ DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) w) :
    iteratedFDeriv ℝ 2 f w = 0 := by
  ext m
  rw [iteratedFDeriv_succ_apply_left]
  have h0 : fderiv ℝ (iteratedFDeriv ℝ 1 f) w = 0 := fderiv_zero_of_not_differentiableAt h
  rw [h0]
  rfl

theorem laplacian2D_zero_of_not_diff (f : ℂ → ℝ) (w : ℂ)
    (h : ¬ DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) w) :
    laplacian2D f w = 0 := by
  dsimp [laplacian2D]
  have h2 := iteratedFDeriv_two_zero_of_not_diff f w h
  rw [h2]
  simp

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

lemma laplacian2D_const (c : ℝ) (w : ℂ) :
    laplacian2D (fun _ => c) w = 0 := by
  apply laplacian2D_of_iterated_one_zero
  ext z v
  rw [iteratedFDeriv_one_apply]
  have : fderiv ℝ (fun _ : ℂ => c) z = 0 := fderiv_const_apply c
  rw [this]
  rfl
