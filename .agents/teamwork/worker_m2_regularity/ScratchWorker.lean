import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
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
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

theorem test_nonconst_diff (u : CP1 → M) (h_nonconst : ¬ ∃ c : M, ∀ z, u z = c) (w : ℂ) :
    let e := fun z => riemannianEnergyDensity I u (stereo_chart.symm z)
    ¬ DifferentiableAt ℝ e w := by
  sorry
