import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Basic
import GromovCompactness.Analysis.Monotonicity

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness GromovCompactness.Analysis

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

#print axioms laplacian2D_of_iterated_one_zero
