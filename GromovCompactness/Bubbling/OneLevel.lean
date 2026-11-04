/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Analysis.HoferRescaling
import GromovCompactness.Bubbling.Neck

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory Filter GromovCompactness GromovCompactness.Analysis Finset Classical

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

lemma OneLevelDecomposition.child_mass_nonneg
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) (z : ℂ) :
    0 ≤ decomp.m_child z := by
  by_cases hz : z ∈ decomp.q
  · exact (thresh.h_pos.trans_le (decomp.m_child_pos z hz)).le
  · rw [decomp.m_child_zero z hz]

lemma OneLevelDecomposition.energy_bubble_le
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    totalEnergy I decomp.v ≤ m_defect := by
  have h_ms := decomp.mass_sum
  have h_sum_nonneg : 0 ≤ ∑ z ∈ decomp.q, decomp.m_child z := by
    apply Finset.sum_nonneg
    intro z hz
    exact (thresh.h_pos.trans_le (decomp.m_child_pos z hz)).le
  linarith

lemma OneLevelDecomposition.child_mass_sum_le
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    (∑ z ∈ decomp.q, decomp.m_child z) ≤ m_defect := by
  have h_ms := decomp.mass_sum
  have h_en : 0 ≤ totalEnergy I decomp.v := energy_nonneg I decomp.v Set.univ
  linarith

lemma OneLevelDecomposition.card_q_mul_h_le
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    (decomp.q.card : ℝ) * thresh.h ≤ m_defect := by
  have h_sum := OneLevelDecomposition.child_mass_sum_le I thresh m_defect base_val decomp
  have h_le_sum : (decomp.q.card : ℝ) * thresh.h ≤ ∑ z ∈ decomp.q, decomp.m_child z := by
    have h_const : (decomp.q.card : ℝ) * thresh.h = ∑ _x ∈ decomp.q, thresh.h := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h_const]
    apply Finset.sum_le_sum
    intro z hz
    exact decomp.m_child_pos z hz
  exact h_le_sum.trans h_sum

lemma OneLevelDecomposition.card_q_le
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    (decomp.q.card : ℝ) ≤ m_defect / thresh.h := by
  exact (le_div_iff₀ thresh.h_pos).mpr (OneLevelDecomposition.card_q_mul_h_le I thresh m_defect base_val decomp)

lemma OneLevelDecomposition.card_q_floor_le
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) (hm : 0 ≤ m_defect) :
    decomp.q.card ≤ Nat.floor (m_defect / thresh.h) := by
  have _h_div_nonneg : 0 ≤ m_defect / thresh.h := div_nonneg hm thresh.h_pos.le
  exact Nat.le_floor (OneLevelDecomposition.card_q_le I thresh m_defect base_val decomp)

lemma OneLevelDecomposition.ghost_outside_unit_disk_mass
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_const_en : totalEnergy I decomp.v = 0)
    (h_const_disk : energyMeasure I decomp.v (disk_at 0 1) = 0) :
    (∑ z ∈ decomp.q.filter (fun w => ¬ (‖w‖ < 1)), decomp.m_child z) = thresh.h / 2 := by
  let q_in := decomp.q.filter (fun w => ‖w‖ < 1)
  let q_out := decomp.q.filter (fun w => ¬ (‖w‖ < 1))
  have h_split : decomp.q = q_in ∪ q_out := by
    ext z
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro hz
      by_cases h : ‖z‖ < 1
      · left; exact ⟨hz, h⟩
      · right; exact ⟨hz, h⟩
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩)
      · exact hz
      · exact hz
  have h_disj : Disjoint q_in q_out := by
    rw [Finset.disjoint_filter]
    intro x _ hx_in hx_out
    exact hx_out hx_in
  have h_sum_split : (∑ z ∈ decomp.q, decomp.m_child z) =
      (∑ z ∈ q_in, decomp.m_child z) + (∑ z ∈ q_out, decomp.m_child z) := by
    rw [h_split, Finset.sum_union h_disj]
  have h_in_sum : (∑ z ∈ q_in, decomp.m_child z) = m_defect - thresh.h / 2 := by
    have h_calib := decomp.calibrated_unit_mass
    rw [h_const_disk, zero_add] at h_calib
    exact h_calib
  have h_tot_sum : (∑ z ∈ decomp.q, decomp.m_child z) = m_defect := by
    have h_ms := decomp.mass_sum
    rw [h_const_en, zero_add] at h_ms
    exact h_ms.symm
  linarith [h_sum_split, h_in_sum, h_tot_sum]

lemma OneLevelDecomposition.ghost_branching
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (hm : thresh.h ≤ m_defect)
    (h_const_en : totalEnergy I decomp.v = 0)
    (h_const_disk : energyMeasure I decomp.v (disk_at 0 1) = 0) :
    2 ≤ decomp.q.card := by
  let q_in := decomp.q.filter (fun w => ‖w‖ < 1)
  let q_out := decomp.q.filter (fun w => ¬ (‖w‖ < 1))
  have h_split : decomp.q = q_in ∪ q_out := by
    ext z
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro hz
      by_cases h : ‖z‖ < 1
      · left; exact ⟨hz, h⟩
      · right; exact ⟨hz, h⟩
    · rintro (⟨hz, _⟩ | ⟨hz, _⟩)
      · exact hz
      · exact hz
  have h_disj : Disjoint q_in q_out := by
    rw [Finset.disjoint_filter]
    intro x _ hx_in hx_out
    exact hx_out hx_in
  have h_card_split : decomp.q.card = q_in.card + q_out.card := by
    rw [h_split, Finset.card_union_of_disjoint h_disj]
  have h_out_mass := OneLevelDecomposition.ghost_outside_unit_disk_mass I thresh m_defect base_val decomp h_const_en h_const_disk
  have h_out_pos : 0 < thresh.h / 2 := half_pos thresh.h_pos
  have h_q_out_nonempty : q_out.Nonempty := by
    by_contra h_empty
    rw [Finset.nonempty_iff_ne_empty, not_not] at h_empty
    have h_zero : (∑ z ∈ q_out, decomp.m_child z) = 0 := by
      rw [h_empty, Finset.sum_empty]
    linarith [h_out_mass, h_out_pos, h_zero]
  have h_q_out_card : 0 < q_out.card := h_q_out_nonempty.card_pos
  have h_in_mass : (∑ z ∈ q_in, decomp.m_child z) = m_defect - thresh.h / 2 := by
    have h_calib := decomp.calibrated_unit_mass
    rw [h_const_disk, zero_add] at h_calib
    exact h_calib
  have h_in_pos : 0 < m_defect - thresh.h / 2 := by
    linarith [thresh.h_pos, hm]
  have h_q_in_nonempty : q_in.Nonempty := by
    by_contra h_empty
    rw [Finset.nonempty_iff_ne_empty, not_not] at h_empty
    have h_zero : (∑ z ∈ q_in, decomp.m_child z) = 0 := by
      rw [h_empty, Finset.sum_empty]
    linarith [h_in_mass, h_in_pos, h_zero]
  have h_q_in_card : 0 < q_in.card := h_q_in_nonempty.card_pos
  linarith [h_card_split, h_q_in_card, h_q_out_card]

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
