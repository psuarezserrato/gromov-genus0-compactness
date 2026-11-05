import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Complex.Basic
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.Monotonicity

open scoped Manifold ContDiff Topology
open Metric Set GromovCompactness GromovCompactness.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

theorem test_linarith (u : CP1 → M) (w : ℂ)
    (h_lap : 0 ≤ laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w) :
    -1 * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
      0 * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
    laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w := by
  have he_nonneg : 0 ≤ riemannianEnergyDensity I u (stereo_chart.symm w) :=
    riemannianEnergyDensity_nonneg I u (stereo_chart.symm w)
  have : 0 ≤ (riemannianEnergyDensity I u (stereo_chart.symm w))^2 := sq_nonneg _
  linarith
