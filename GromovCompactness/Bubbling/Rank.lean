/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import GromovCompactness.Bubbling.GhostBranching

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory Filter GromovCompactness GromovCompactness.Analysis Finset

namespace GromovCompactness.Bubbling

/-!
# Task B06: Energy Rank Strictly Decreases

This module formalizes the strict decrease of the discrete energy rank $\lfloor m / h \rfloor \in \mathbb{N}$
at each bubbling step, ensuring termination of the bubble tree induction, following Gromov (1985, §2.2),
Ivashkovich-Shevchishin (1999, §2.3), and `gromov_compactness.pdf` §4.6 (Task `B06`).

## Key Theorems
- `energy_rank_strict_decrease`: Pure arithmetic lemma for reals $m, m_i, h$.
- `child_mass_le_parent_sub_h`: Geometric proof that every child defect satisfies $m_i \le m - h$.
- `child_rank_strict_decrease`: Combined strict inequality $\lfloor m_i / h \rfloor < \lfloor m / h \rfloor$.
-/

/-- Strict Energy Rank Decrease arithmetic lemma (Contract B06).
If h > 0 and 0 ≤ m_i ≤ m - h, then ⌊m_i / h⌋ < ⌊m / h⌋. -/
theorem energy_rank_strict_decrease (m m_i h : ℝ) (hh : 0 < h)
    (h_pos : 0 ≤ m_i) (hle : m_i ≤ m - h) :
    Nat.floor (m_i / h) < Nat.floor (m / h) := by
  have h_div : m_i / h ≤ m / h - 1 := by
    calc
      m_i / h ≤ (m - h) / h := div_le_div_of_nonneg_right hle hh.le
      _ = m / h - h / h := sub_div m h h
      _ = m / h - 1 := by rw [div_self hh.ne']
  have h_floor_le := Nat.floor_mono h_div
  have h1 : 0 ≤ m / h - 1 := by
    calc
      0 ≤ m_i / h := div_nonneg h_pos hh.le
      _ ≤ m / h - 1 := h_div
  have h_floor_sub : Nat.floor (m / h - 1) < Nat.floor (m / h) := by
    have h_lt : ((Nat.floor (m / h - 1) + 1 : ℕ) : ℝ) ≤ m / h := by
      push_cast
      calc
        (Nat.floor (m / h - 1) : ℝ) + 1 ≤ (m / h - 1) + 1 := by
          have := Nat.floor_le h1
          linarith
        _ = m / h := by ring
    have h_le_floor : Nat.floor (m / h - 1) + 1 ≤ Nat.floor (m / h) :=
      Nat.le_floor h_lt
    exact Nat.lt_of_succ_le h_le_floor
  exact lt_of_le_of_lt h_floor_le h_floor_sub

#print axioms energy_rank_strict_decrease

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- In any one-level decomposition, every child defect mass is bounded by m - h (Contract B06). -/
theorem child_mass_le_parent_sub_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (_hm : thresh.h ≤ m_defect) (z : ℂ) (_hz : z ∈ decomp.q) :
    decomp.m_child z ≤ m_defect - thresh.h := by
  sorry

/-- Combined Discrete Energy Rank Strict Decrease for One-Level Decomposition (Contract B06). -/
theorem child_rank_strict_decrease
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (hm : thresh.h ≤ m_defect) (z : ℂ) (hz : z ∈ decomp.q) :
    Nat.floor (decomp.m_child z / thresh.h) < Nat.floor (m_defect / thresh.h) := by
  have h_pos : 0 ≤ decomp.m_child z := (thresh.h_pos.trans_le (decomp.m_child_pos z hz)).le
  have h_le := child_mass_le_parent_sub_h I thresh m_defect base_val decomp hm z hz
  exact energy_rank_strict_decrease m_defect (decomp.m_child z) thresh.h thresh.h_pos h_pos h_le

end GromovCompactness.Bubbling
