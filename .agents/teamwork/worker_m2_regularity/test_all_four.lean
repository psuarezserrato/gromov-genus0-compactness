import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Basic
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.Monotonicity

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness GromovCompactness.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
variable [IsManifold I (∞ : WithTop ℕ∞) M] [CompactSpace M] [ClosedTameTarget I M]

theorem test_boch_tactics (u : CP1 → M) (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) (w : ℂ) :
    -1 * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
      0 * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
    laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
  let e := fun z => riemannianEnergyDensity I u (stereo_chart.symm z)
  have he_nonneg : 0 ≤ e w := riemannianEnergyDensity_nonneg I u (stereo_chart.symm w)
  have h_lhs : -1 * (e w)^2 - 0 * (e w) ≤ 0 := by
    have : 0 ≤ (e w)^2 := sq_nonneg (e w)
    linarith
  sorry
