/-!
# Example: Hofer Gradient Rescaling for Pseudo-Holomorphic Curves
-/

import Mathlib.Analysis.Hofer
import Mathlib.Topology.MetricSpace.Basic

open Metric

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

/-- Rescaling helper synthesizing Patrick Massot's Hofer lemma. -/
theorem hofer_gradient_rescaling (f : X → ℝ) (hf : Continuous f) (x : X) (ε : ℝ)
    (hε : 0 < ε) (hfx : 0 ≤ f x) :
    ∃ x' : X, ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ f x ≤ f x' ∧ ∀ y ∈ closedBall x' ε', f y ≤ 2 * f x' := by
  obtain ⟨x', ε', hε'_pos, hε'_le, hf_le, h_bound⟩ := Mathlib.Analysis.Hofer.hofer f x ε hε hf hfx
  exact ⟨x', ε', hε'_pos, hε'_le, hf_le, fun y hy => h_bound y hy⟩
