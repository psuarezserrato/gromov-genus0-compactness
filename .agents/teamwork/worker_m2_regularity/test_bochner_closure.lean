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

theorem test_bochner_closure (u : CP1 → M) (w : ℂ) :
    let e := fun z => riemannianEnergyDensity I u (stereo_chart.symm z)
    -1 * (e w)^2 - 0 * (e w) ≤ laplacian2D e w := by
  intro e
  have he_nonneg : 0 ≤ e w := riemannianEnergyDensity_nonneg I u (stereo_chart.symm w)
  have h_lhs : -1 * (e w)^2 - 0 * (e w) ≤ 0 := by
    have : 0 ≤ (e w)^2 := sq_nonneg (e w)
    linarith
  sorry
