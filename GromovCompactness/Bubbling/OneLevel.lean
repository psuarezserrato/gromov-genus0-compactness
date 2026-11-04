/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Analysis.HoferRescaling
import GromovCompactness.Bubbling.Neck

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory Filter GromovCompactness GromovCompactness.Analysis Finset

namespace GromovCompactness.Bubbling

/-!
# Task B04: One-Level Mass Decomposition and Node Matching

This module formalizes the extraction of a single-level bubble curve $v : \mathbb{CP}^1 \to M$
and child defect points $q \subset \mathbb{C}$ from a calibrated rescaling, following Gromov (1985, §2.2),
Ivashkovich-Shevchishin (1999, §2.3), and `gromov_compactness.pdf` §4.6 (Task `B04`).

## Key Definitions & Theorems
- `OneLevelDecomposition`: Bundled record containing limit bubble $v$, child defect set $q$,
  mass conservation $m = E(v) + \sum m_i$, node matching $v(\infty) = u_0(p)$, and calibrated unit disk mass.
- `exists_one_level_decomposition`: Extraction theorem from calibrated rescalings.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- One-Level Mass Decomposition Data (Contract B04).
Bundles the extracted bubble curve `v`, child concentration points `q ⊂ ℂ`, mass conservation,
node matching at ∞, and calibrated unit disk mass. -/
structure OneLevelDecomposition
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M) where
  v : CP1 → M
  v_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ
  q : Finset ℂ
  m_child : ℂ → ℝ
  m_child_pos : ∀ z ∈ q, thresh.h ≤ m_child z
  m_child_zero : ∀ z ∉ q, m_child z = 0
  mass_sum : m_defect = totalEnergy I v + ∑ z ∈ q, m_child z
  node_match : v north_pole = base_val
  calibrated_unit_mass :
    energyMeasure I v (disk_at 0 1) + ∑ z ∈ q.filter (fun w => ‖w‖ < 1), m_child z =
      m_defect - thresh.h / 2

/-- Existence of One-Level Mass Decomposition (Contract B04). -/
theorem exists_one_level_decomposition
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (_hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (_h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val)) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) := by
  sorry

end GromovCompactness.Bubbling
