import Mathlib
import GromovCompactness.Analysis.Bochner

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness GromovCompactness.Analysis

lemma weitzenboeck_decomposition_of_lower_bound (L B : ℝ) (hB : 0 ≤ B) (hL : -B ≤ L) :
    ∃ (H K : ℝ), L = H^2 + K ∧ |K| ≤ B := by
  refine ⟨Real.sqrt (L + B), -B, ?_, ?_⟩
  · rw [Real.sq_sqrt (by linarith)]
    ring
  · rw [abs_neg, abs_of_nonneg hB]

theorem bochner_curvature_term_bound_closed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
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
  -- We prove existence of uniform constants b, c ≥ 0
  sorry
