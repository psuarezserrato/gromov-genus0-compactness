/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Analysis.HoferRescaling
import Mathlib.Topology.MetricSpace.Bounded

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory Filter GromovCompactness GromovCompactness.Analysis

namespace GromovCompactness.Bubbling

/-!
# Task B03: Vanishing Neck Energy and Diameter

This module formalizes the vanishing of symplectic energy and target metric diameter on the
annular neck connecting the base curve to the rescaled bubble, following Gromov (1985, §2.2),
Ivashkovich-Shevchishin (1999, §2.3), and `gromov_compactness.pdf` §4.6 (Task `B03`).

## Key Theorem
- `neck_vanishing_quantified`: Quantified $\forall \eta > 0, \exists R_0, \dots$ vanishing of neck energy and diameter.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- Vanishing Neck Energy and Target Diameter (Contract B03).
For every target margin `η > 0`, there exist a scaling ratio threshold `R₀ > 1` and an outer radius `δ₀ > 0`
such that for any `R ≥ R₀` and `δ ∈ (0, δ₀)`, the annular neck `A(Rλ_n, δ; a_n)` asymptotically has
symplectic energy `< η` and image diameter `< η`. -/
theorem neck_vanishing_quantified
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (_hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          energyMeasure I (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ) < η ∧
          Metric.diam (Set.image (u_seq n) (annulus_at (res.a n) (R * res.«λ» n) δ)) < η := by
  sorry

/-- Companion Pointwise Distance Oscillation Bound on Neck Annuli (Contract B03). -/
theorem neck_pointwise_oscillation_bound
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (η : ℝ) (_hη : 0 < η) :
    ∃ R₀ > (1 : ℝ), ∀ R ≥ R₀,
      ∃ δ₀ > (0 : ℝ), ∀ δ ∈ Set.Ioo 0 δ₀,
        ∃ N : ℕ, ∀ n ≥ N,
          R * res.«λ» n < δ ∧
          ∀ z w, z ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 w ∈ annulus_at (res.a n) (R * res.«λ» n) δ →
                 dist (u_seq n z) (u_seq n w) < η := by
  sorry

end GromovCompactness.Bubbling
