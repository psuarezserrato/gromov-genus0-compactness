/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.MeasureTheory.Measure.Portmanteau
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Topology.Subsequence

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory Filter GromovCompactness GromovCompactness.Bookkeeping

namespace GromovCompactness.Compactness

/-!
# Task C01: Weak Compactness of Energy Measures

This module formalizes the weak compactness of finite nonnegative Radon measures on the
Riemann sphere $\mathbb{CP}^1 \cong S^2$, following Gromov (1985, §1.2), Ivashkovich-Shevchishin (1999, §2),
and `gromov_compactness.pdf` §4.5 (Task `C01`).

## Key Definitions & Theorems
- `WeakMeasureConvergence`: Characterization of weak convergence $\mu_n \rightharpoonup \mu$ on $\mathbb{CP}^1$
  combining continuous function pairing, closed set upper bounds, and continuity set convergence.
- `weak_measure_compactness`: Master extraction theorem for uniformly bounded measures.
- `weak_energy_measure_compactness`: Specialization to energy measures of $J$-holomorphic curve sequences.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- Weak convergence of a sequence of finite Borel measures on the Riemann sphere CP1. -/
def WeakMeasureConvergence (μ_seq : ℕ → Measure CP1) (μ_lim : Measure CP1) : Prop :=
  (∀ (f : CP1 → ℝ), Continuous f →
    Tendsto (fun n => ∫ z, f z ∂(μ_seq n)) atTop (nhds (∫ z, f z ∂μ_lim))) ∧
  (∀ (K : Set CP1), IsClosed K →
    Filter.limsup (fun n => μ_seq n K) atTop ≤ μ_lim K) ∧
  (∀ (A : Set CP1), μ_lim (frontier A) = 0 →
    Tendsto (fun n => μ_seq n A) atTop (nhds (μ_lim A))) ∧
  Tendsto (fun n => μ_seq n Set.univ) atTop (nhds (μ_lim Set.univ))

/-- Weak Compactness of Energy Measures on CP1 (Contract C01).
Any sequence of finite nonnegative Borel measures on CP1 with uniformly bounded total mass
has a weakly convergent subsequence. -/
theorem weak_measure_compactness (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)]
    (h_bdd : ∃ B > 0, ∀ n, μ_seq n Set.univ ≤ ENNReal.ofReal B) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim := by
  sorry

/-- Weak Compactness of Energy Measures for sequences of J-holomorphic curves (Contract C01). -/
theorem weak_energy_measure_compactness
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (_hB : 0 < B)
    (_h_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  sorry

end GromovCompactness.Compactness
