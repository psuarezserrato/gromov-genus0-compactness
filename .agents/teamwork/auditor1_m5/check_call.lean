import GromovCompactness

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness
open GromovCompactness.Analysis
open GromovCompactness.Bubbling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

theorem test_query_B02
    (u_seq : ℕ → (CP1 → M)) (thresh : GromovCompactness.Bubbling.TargetThresholds I M)
    (m_defect : ℝ) (hm : thresh.h ≤ m_defect)
    (h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n)) :
    Nonempty (GromovCompactness.Bubbling.CalibratedRescaling I u_seq thresh m_defect) :=
  GromovCompactness.Bubbling.exists_calibrated_rescaling I u_seq thresh m_defect hm h_jhol h_defect

#print axioms test_query_B02
