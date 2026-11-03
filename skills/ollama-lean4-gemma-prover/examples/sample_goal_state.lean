/-!
# Sample Open Proof Goal State in Symplectic Bubbling Analysis
-/

import Mathlib.Analysis.Hofer
import Mathlib.Topology.MetricSpace.Basic

open Metric

variable {M : Type*} [MetricSpace M] [CompleteSpace M]

theorem rescale_around_blowup_point (u : ℕ → ℂ → M) (f : ℂ → ℝ) (hf_cont : Continuous f)
    (x0 : ℂ) (ε0 : ℝ) (hε0 : 0 < ε0) (hfx : 0 ≤ f x0) :
    ∃ x' ε', 0 < ε' ∧ ε' ≤ ε0 ∧ f x0 ≤ f x' ∧ ∀ y ∈ closedBall x' ε', f y ≤ 2 * f x' := by
  -- Target Goal State:
  -- ⊢ ∃ x' ε', 0 < ε' ∧ ε' ≤ ε0 ∧ f x0 ≤ f x' ∧ ∀ y ∈ closedBall x' ε', f y ≤ 2 * f x'
  exact Mathlib.Analysis.Hofer.hofer f x0 ε0 hε0 hf_cont hfx
