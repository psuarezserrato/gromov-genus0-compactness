/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Compactness.Measures
import GromovCompactness.Analysis.HoferRescaling
import GromovCompactness.Topology.SmoothLocal

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory Filter GromovCompactness GromovCompactness.Bookkeeping GromovCompactness.Analysis Classical

namespace GromovCompactness.Compactness

/-!
# Task C02: Finite Concentration Set and Smooth Convergence

This module formalizes the extraction of the finite concentration set $S \subset \mathbb{CP}^1$ and
the smooth limit curve $u_0 : \mathbb{CP}^1 \to M$ from a bounded-energy sequence of pseudo-holomorphic curves,
following Gromov (1985, §1.3), Ivashkovich-Shevchishin (1999, §2.2), and `gromov_compactness.pdf` §4.5 (Task `C02`).

## Key Definitions & Theorems
- `ConcentrationData`: Bundled structure packaging subsequence, weak limit measure, singular set $S$,
  cardinality bound $|S| \le B / \varepsilon_{\mathrm{reg}}$, smooth limit $u_0$, and $C^\infty_{\mathrm{loc}}$ convergence on $\mathbb{CP}^1 \setminus S$.
- `exists_concentration_data`: Top-level extraction theorem.
- `smooth_convergence_upgrade_of_zero_mass`: No-atom regularity upgrade theorem.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- Concentration Compactness Data (Contract C02).
Bundles the subsequence, weak limit measure, finite singular set S, cardinality bound,
smooth limit curve, and smooth local convergence outside S. -/
structure ConcentrationData
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M) where
  σ : SubseqMap
  μ : Measure CP1
  [μ_fin : IsFiniteMeasure μ]
  μ_total_le : μ Set.univ ≤ ENNReal.ofReal B
  weak_lim : WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ
  S : Finset CP1
  S_def : ∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p}
  card_S_mul_le : (S.card : ℝ) * thresh.ε_reg ≤ B
  card_S_le : (S.card : ℝ) ≤ B / thresh.ε_reg
  u₀ : CP1 → M
  u₀_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ
  smooth_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S)

/-- Extraction of Concentration Data from bounded-energy J-spheres (Contract C02). -/
theorem exists_concentration_data
    (u_seq : ℕ → (CP1 → M))
    (_h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (_hB : 0 ≤ B)
    (_h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  sorry

/-- No-Atom Regularity Upgrade: if the defect measure has no atom at p, convergence is smooth at p. -/
theorem smooth_convergence_upgrade_of_zero_mass
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (p : CP1) (_hp : cdata.μ {p} = 0) :
    SmoothLocalConvergesOn I (fun n => u_seq (cdata.σ.1 n)) cdata.u₀ (Set.univ \ (cdata.S.erase p)) := by
  sorry

end GromovCompactness.Compactness
