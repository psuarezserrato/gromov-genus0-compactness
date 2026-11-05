import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
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

theorem can_prove_diff (u : CP1 → M) (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) (w : ℂ) :
    let e := fun z => riemannianEnergyDensity I u (stereo_chart.symm z)
    DifferentiableAt ℝ e w := by
  intro e
  dsimp [e, riemannianEnergyDensity, ClosedTameTarget.metric]
  -- Can this be differentiated?
  sorry
