import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.SingularityRemoval

open scoped Manifold ContDiff Topology
open Metric Set GromovCompactness GromovCompactness.Analysis

-- Stress-test 1: Cauchy-Schwarz quadratic on a perfect square
example : (2 : ℝ)^2 ≤ (1 : ℝ) * 4 := by
  have h_quad : ∀ t : ℝ, 0 ≤ (1 : ℝ) * t^2 + 2 * 2 * t + 4 := by
    intro t
    have : (1 : ℝ) * t^2 + 2 * 2 * t + 4 = (t + 2)^2 := by ring
    rw [this]
    exact sq_nonneg (t + 2)
  exact cauchy_schwarz_quadratic 1 2 4 (by norm_num) h_quad

-- Stress-test 2: Annulus emptiness when outer radius is strictly smaller than inner radius
example (a : ℂ) : annulus_at a (2 * 1) (4 / 2) = ∅ := by
  have h_le : (4 : ℝ) / 2 ≤ 2 * 1 := by norm_num
  exact annulus_at_empty_of_le a (r := 1) (R := 4) h_le

-- Stress-test 3: Nonconstant equivalence on CP1
example (u : CP1 → ℝ) (z w : CP1) (h : u z ≠ u w) : ¬ ∃ c : ℝ, ∀ x, u x = c := by
  intro ⟨c, hc⟩
  have hz : u z = c := hc z
  have hw : u w = c := hc w
  apply h
  rw [hz, hw]

-- Stress-test 4: Exponential decay factor strictly decreasing
example (α : ℝ) (hα : 0 < α) : Real.exp (-α * 2) < Real.exp (-α * 1) := by
  rw [Real.exp_lt_exp]
  linarith
