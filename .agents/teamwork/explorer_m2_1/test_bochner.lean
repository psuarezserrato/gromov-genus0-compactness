import GromovCompactness.Analysis.Bochner

open scoped Manifold ContDiff Topology
open Metric Set GromovCompactness
open GromovCompactness.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

theorem test_diff_state (u : CP1 → M) (w : ℂ) :
    DifferentiableAt ℝ (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w →
    False := by
  intro h
  sorry
