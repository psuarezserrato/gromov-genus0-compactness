import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Basic
import GromovCompactness.Analysis.Monotonicity

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness GromovCompactness.Analysis

theorem laplacian2D_const (c : ℝ) (w : ℂ) : laplacian2D (fun _ : ℂ => c) w = 0 := by
  dsimp [laplacian2D]
  have h2 : iteratedFDeriv ℝ 2 (fun _ : ℂ => c) w = 0 := by
    have h := iteratedFDeriv_succ_const (𝕜 := ℝ) (E := ℂ) 1 c
    exact congr_fun h w
  rw [h2]
  simp

#print axioms laplacian2D_const
