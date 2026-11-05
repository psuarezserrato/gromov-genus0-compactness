import GromovCompactness.Analysis.Monotonicity

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness
open GromovCompactness.Analysis

lemma integral_zero_implies_zero (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ)
    (he_nonneg : ∀ z, 0 ≤ e z)
    (he_cont : ContinuousOn e (Metric.closedBall 0 r))
    (h_int : (∫ w in Metric.ball (0 : ℂ) r, e w) = 0)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) (r / 2)) :
    e z = 0 := by
  sorry
