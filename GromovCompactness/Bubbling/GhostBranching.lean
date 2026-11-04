/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Bubbling.OneLevel

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory Filter GromovCompactness GromovCompactness.Analysis Finset

namespace GromovCompactness.Bubbling

/-!
# Task B05: Ghost Branching Condition

This module formalizes the ghost branching condition: if an extracted bubble component
is constant ($E(v) = 0$), the calibration condition guarantees that it carries at least
two child defect points in $\mathbb{C}$, ensuring stability ($\ge 3$ special points including $\infty$),
following Gromov (1985, §2.2), Ivashkovich-Shevchishin (1999, §2.3), and `gromov_compactness.pdf` §4.6 & §6 (Task `B05`, Stress Case 3).

## Key Theorem
- `ghost_component_branches`: Proof that $2 \le |q|$ for constant bubbles.
- `ghost_bubble_degree_ge_three`: Total nodal degree $\operatorname{deg}(v) \ge 3$.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- Ghost Component Branching Condition (Contract B05).
If the limit bubble v is constant, the calibrated unit energy forces at least one defect
inside the unit disk and at least one defect outside, guaranteeing at least 2 child bubbles. -/
theorem ghost_component_branches
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (hm : thresh.h ≤ m_defect)
    (_h_const : ∃ c : M, ∀ z, decomp.v z = c)
    (h_const_en : totalEnergy I decomp.v = 0)
    (h_const_disk : energyMeasure I decomp.v (disk_at 0 1) = 0) :
    2 ≤ decomp.q.card :=
  decomp.ghost_branching I thresh m_defect base_val hm h_const_en h_const_disk

/-- Ghost Component Branching Condition from constancy alone (Contract B05). -/
theorem ghost_component_branches_of_const
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (hm : thresh.h ≤ m_defect)
    (h_const : ∃ c : M, ∀ z, decomp.v z = c) :
    2 ≤ decomp.q.card := by
  rcases h_const with ⟨c, hc⟩
  have hu : decomp.v = fun _ => c := funext hc
  have h_en0 : totalEnergy I decomp.v = 0 := by
    rw [hu]
    exact totalEnergy_const I c
  have h_meas0 : energyMeasure I decomp.v (disk_at 0 1) = 0 := by
    rw [hu]
    exact energyMeasure_const I c (disk_at 0 1)
  exact decomp.ghost_branching I thresh m_defect base_val hm h_en0 h_meas0

/-- Total Nodal Degree of Ghost Bubbles is at least 3 (Contract B05). -/
theorem ghost_bubble_degree_ge_three
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (hm : thresh.h ≤ m_defect)
    (h_const : ∃ c : M, ∀ z, decomp.v z = c)
    (h_const_en : totalEnergy I decomp.v = 0)
    (h_const_disk : energyMeasure I decomp.v (disk_at 0 1) = 0) :
    3 ≤ decomp.q.card + 1 := by
  have h2 := ghost_component_branches I thresh m_defect base_val decomp hm h_const h_const_en h_const_disk
  omega

/-- Total Nodal Degree of Ghost Bubbles from constancy alone (Contract B05). -/
theorem ghost_bubble_degree_ge_three_of_const
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (hm : thresh.h ≤ m_defect)
    (h_const : ∃ c : M, ∀ z, decomp.v z = c) :
    3 ≤ decomp.q.card + 1 := by
  have h2 := ghost_component_branches_of_const I thresh m_defect base_val decomp hm h_const
  omega

#print axioms ghost_component_branches
#print axioms ghost_component_branches_of_const
#print axioms ghost_bubble_degree_ge_three
#print axioms ghost_bubble_degree_ge_three_of_const

end GromovCompactness.Bubbling
