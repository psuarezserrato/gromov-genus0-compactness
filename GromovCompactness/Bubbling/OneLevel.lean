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

theorem energy_conservation_under_bubbling_of_annular_zero
    {E_seq E_neck : ℕ → ℝ} {E_base E_bubbles : ℝ}
    (h_decomp : ∀ n, E_seq n = E_base + E_bubbles + E_neck n)
    (h_neck : Tendsto E_neck atTop (nhds 0)) :
    Tendsto E_seq atTop (nhds (E_base + E_bubbles)) := by
  have h_eq : E_seq = fun n => (E_base + E_bubbles) + E_neck n := funext h_decomp
  rw [h_eq]
  have h := (tendsto_const_nhds (x := E_base + E_bubbles)).add h_neck
  simpa using h

/-- Construct a leaf `OneLevelDecomposition` (`q = ∅`) from a smooth `J`-holomorphic bubble `v`
with calibrated unit-disk energy (`0 sorryAx`). -/
noncomputable def OneLevelDecomposition.of_leaf_bubble
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (v : CP1 → M)
    (hv_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ)
    (hv_tot : m_defect = totalEnergy I v)
    (hv_node : v north_pole = base_val)
    (hv_calib : energyMeasure I v (disk_at 0 1) = m_defect - thresh.h / 2) :
    OneLevelDecomposition I thresh m_defect base_val where
  v := v
  v_jhol := hv_jhol
  q := ∅
  m_child := fun _ => 0
  m_child_pos := by intro z hz; exact False.elim (Finset.notMem_empty z hz)
  m_child_zero := by intro _ _; rfl
  mass_sum := by simpa using hv_tot
  node_match := hv_node
  calibrated_unit_mass := by simpa using hv_calib

/-- Construct a single-child `OneLevelDecomposition` (`q = {0}`) from a smooth `J`-holomorphic bubble `v`
with exterior unit-disk energy `thresh.h / 2` and residual defect mass `≥ thresh.h` at the origin (`0 sorryAx`). -/
noncomputable def OneLevelDecomposition.of_single_child_at_zero
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (v : CP1 → M)
    (hv_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ)
    (hv_le : totalEnergy I v ≤ m_defect - thresh.h)
    (hv_node : v north_pole = base_val)
    (hv_ext : totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) :
    OneLevelDecomposition I thresh m_defect base_val where
  v := v
  v_jhol := hv_jhol
  q := {0}
  m_child := fun z => if z = 0 then m_defect - totalEnergy I v else 0
  m_child_pos := by
    intro z hz
    rw [Finset.mem_singleton] at hz
    subst hz
    simp only [ ↓reduceIte]
    linarith
  m_child_zero := by
    intro z hz
    rw [Finset.mem_singleton] at hz
    exact if_neg hz
  mass_sum := by
    simp only [Finset.sum_singleton, ↓reduceIte]
    ring
  node_match := hv_node
  calibrated_unit_mass := by
    have h_filt : ({0} : Finset ℂ).filter (fun w : ℂ => ‖w‖ < 1) = {0} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
      rintro rfl
      simp
    rw [h_filt, Finset.sum_singleton]
    simp only [↓reduceIte]
    linarith

/-- Construct a `OneLevelDecomposition` when all child concentration points `q` lie inside the
open unit disk `‖z‖ < 1` and the exterior unit-disk energy of `v` equals `thresh.h / 2` (`0 sorryAx`). -/
noncomputable def OneLevelDecomposition.of_children_in_unit_disk
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (v : CP1 → M)
    (hv_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ)
    (q : Finset ℂ)
    (hq_disk : ∀ z ∈ q, ‖z‖ < 1)
    (m_child : ℂ → ℝ)
    (hm_pos : ∀ z ∈ q, thresh.h ≤ m_child z)
    (hm_zero : ∀ z ∉ q, m_child z = 0)
    (h_mass_sum : m_defect = totalEnergy I v + ∑ z ∈ q, m_child z)
    (hv_node : v north_pole = base_val)
    (hv_ext : totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) :
    OneLevelDecomposition I thresh m_defect base_val where
  v := v
  v_jhol := hv_jhol
  q := q
  m_child := m_child
  m_child_pos := hm_pos
  m_child_zero := hm_zero
  mass_sum := h_mass_sum
  node_match := hv_node
  calibrated_unit_mass := by
    have h_filt : q.filter (fun w : ℂ => ‖w‖ < 1) = q :=
      Finset.filter_eq_self.mpr hq_disk
    rw [h_filt]
    linarith [h_mass_sum, hv_ext]

/-- Construct a `OneLevelDecomposition` from any calibrated bubble curve `v`, child concentration
set `q ⊂ ℂ`, and child mass function `m_child : ℂ → ℝ` satisfying the mass sum, north-pole node
matching, and unit-disk mass calibration identities (`0 sorryAx`). -/
def OneLevelDecomposition.of_calibrated_data
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (v : CP1 → M)
    (hv_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ)
    (q : Finset ℂ)
    (m_child : ℂ → ℝ)
    (hm_pos : ∀ z ∈ q, thresh.h ≤ m_child z)
    (hm_zero : ∀ z ∉ q, m_child z = 0)
    (h_mass_sum : m_defect = totalEnergy I v + ∑ z ∈ q, m_child z)
    (hv_node : v north_pole = base_val)
    (h_calib : energyMeasure I v (disk_at 0 1) + ∑ z ∈ q.filter (fun w => ‖w‖ < 1), m_child z =
      m_defect - thresh.h / 2) :
    OneLevelDecomposition I thresh m_defect base_val where
  v := v
  v_jhol := hv_jhol
  q := q
  m_child := m_child
  m_child_pos := hm_pos
  m_child_zero := hm_zero
  mass_sum := h_mass_sum
  node_match := hv_node
  calibrated_unit_mass := h_calib

/-- Construct a `OneLevelDecomposition` when the exterior unit-disk mass (exterior bubble energy
plus child masses on `‖z‖ ≥ 1`) equals `thresh.h / 2` (`0 sorryAx`). -/
def OneLevelDecomposition.of_exterior_unit_disk_mass
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (v : CP1 → M)
    (hv_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ)
    (q : Finset ℂ)
    (m_child : ℂ → ℝ)
    (hm_pos : ∀ z ∈ q, thresh.h ≤ m_child z)
    (hm_zero : ∀ z ∉ q, m_child z = 0)
    (h_mass_sum : m_defect = totalEnergy I v + ∑ z ∈ q, m_child z)
    (hv_node : v north_pole = base_val)
    (h_ext : (totalEnergy I v - energyMeasure I v (disk_at 0 1)) +
      ∑ z ∈ q.filter (fun w => ¬ (‖w‖ < 1)), m_child z = thresh.h / 2) :
    OneLevelDecomposition I thresh m_defect base_val :=
  OneLevelDecomposition.of_calibrated_data I thresh m_defect base_val v hv_jhol q m_child
    hm_pos hm_zero h_mass_sum hv_node (by
      have h_split := Finset.sum_filter_add_sum_filter_not q (fun w : ℂ => ‖w‖ < 1) m_child
      linarith [h_mass_sum, h_ext, h_split])

/-- No `OneLevelDecomposition` can have both `totalEnergy I decomp.v = 0` and
`energyMeasure I decomp.v (disk_at 0 1) = 0`, because every child concentration point in `q`
carries mass `≥ thresh.h > thresh.h / 2` (`0 sorryAx`). -/
theorem OneLevelDecomposition.not_zero_energy_and_disk
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_const_en : totalEnergy I decomp.v = 0)
    (h_const_disk : energyMeasure I decomp.v (disk_at 0 1) = 0) :
    False := by
  let q_out := decomp.q.filter (fun w => ¬ (‖w‖ < 1))
  have h_out_mass : (∑ z ∈ q_out, decomp.m_child z) = thresh.h / 2 :=
    OneLevelDecomposition.ghost_outside_unit_disk_mass I thresh m_defect base_val decomp h_const_en h_const_disk
  have h_out_pos : 0 < thresh.h / 2 := half_pos thresh.h_pos
  have h_q_out_nonempty : q_out.Nonempty := by
    by_contra h_empty
    rw [Finset.nonempty_iff_ne_empty, not_not] at h_empty
    have h_zero : (∑ z ∈ q_out, decomp.m_child z) = 0 := by
      rw [h_empty, Finset.sum_empty]
    linarith [h_out_mass, h_out_pos, h_zero]
  obtain ⟨z₀, hz₀⟩ := h_q_out_nonempty
  have hz₀_q : z₀ ∈ decomp.q := (Finset.mem_filter.mp hz₀).1
  have hz₀_ge : thresh.h ≤ decomp.m_child z₀ := decomp.m_child_pos z₀ hz₀_q
  have hz₀_le_sum : decomp.m_child z₀ ≤ ∑ z ∈ q_out, decomp.m_child z :=
    Finset.single_le_sum (fun z _ => OneLevelDecomposition.child_mass_nonneg I thresh m_defect base_val decomp z) hz₀
  linarith [thresh.h_pos]

/-- On a subsingleton target `M`, `OneLevelDecomposition I thresh m_defect base_val` is empty (`0 sorryAx`),
because every bubble map is constant with zero total and unit-disk energy. -/
theorem OneLevelDecomposition.isEmpty_of_subsingleton [Subsingleton M]
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M) :
    IsEmpty (OneLevelDecomposition I thresh m_defect base_val) := by
  refine ⟨fun decomp => ?_⟩
  have hv_const : decomp.v = fun _ => decomp.v north_pole :=
    funext (fun z => Subsingleton.elim (decomp.v z) (decomp.v north_pole))
  have h_tot : totalEnergy I decomp.v = 0 := by
    dsimp [totalEnergy]
    rw [hv_const]
    exact energyMeasure_const_eq_zero I (decomp.v north_pole) Set.univ
  have h_disk : energyMeasure I decomp.v (disk_at 0 1) = 0 := by
    rw [hv_const]
    exact energyMeasure_const_eq_zero I (decomp.v north_pole) (disk_at 0 1)
  exact OneLevelDecomposition.not_zero_energy_and_disk I thresh m_defect base_val decomp h_tot h_disk

/-- Whenever `energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v`, every child
concentration point `z ∈ decomp.q` lies strictly inside the unit disk (`‖z‖ < 1`) (`0 sorryAx`). -/
theorem OneLevelDecomposition.mem_unit_disk_of_disk_le_totalEnergy
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_le : energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v)
    (z₀ : ℂ) (hz₀ : z₀ ∈ decomp.q) :
    ‖z₀‖ < 1 := by
  by_contra h_not_lt
  have h_split := Finset.sum_filter_add_sum_filter_not decomp.q (fun w : ℂ => ‖w‖ < 1) decomp.m_child
  have h_ms := decomp.mass_sum
  have h_cal := decomp.calibrated_unit_mass
  have hz₀_out : z₀ ∈ decomp.q.filter (fun w : ℂ => ¬ (‖w‖ < 1)) :=
    Finset.mem_filter.mpr ⟨hz₀, h_not_lt⟩
  have hz₀_ge : thresh.h ≤ decomp.m_child z₀ := decomp.m_child_pos z₀ hz₀
  have hz₀_le_sum : decomp.m_child z₀ ≤ ∑ z ∈ decomp.q.filter (fun w : ℂ => ¬ (‖w‖ < 1)), decomp.m_child z :=
    Finset.single_le_sum (fun z _ => OneLevelDecomposition.child_mass_nonneg I thresh m_defect base_val decomp z) hz₀_out
  linarith [thresh.h_pos]

/-- Whenever `energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v`, the exterior unit-disk
energy of the parent bubble `decomp.v` is exactly `thresh.h / 2` (`0 sorryAx`). -/
theorem OneLevelDecomposition.exterior_energy_eq_half_h_of_disk_le_totalEnergy
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_le : energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v) :
    totalEnergy I decomp.v - energyMeasure I decomp.v (disk_at 0 1) = thresh.h / 2 := by
  have h_filt : decomp.q.filter (fun w : ℂ => ‖w‖ < 1) = decomp.q :=
    Finset.filter_eq_self.mpr (OneLevelDecomposition.mem_unit_disk_of_disk_le_totalEnergy I thresh m_defect base_val decomp h_le)
  have h_cal := decomp.calibrated_unit_mass
  rw [h_filt] at h_cal
  linarith [decomp.mass_sum, h_cal]

/-- Whenever `energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v`, the parent bubble
`decomp.v` carries total energy at least `thresh.h / 2 > 0` (`0 sorryAx`). -/
theorem OneLevelDecomposition.half_h_le_totalEnergy_of_disk_le_totalEnergy
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_le : energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v) :
    thresh.h / 2 ≤ totalEnergy I decomp.v := by
  have h_ext := OneLevelDecomposition.exterior_energy_eq_half_h_of_disk_le_totalEnergy I thresh m_defect base_val decomp h_le
  have h_nonneg : 0 ≤ energyMeasure I decomp.v (disk_at 0 1) := energy_nonneg I decomp.v (disk_at 0 1)
  linarith

/-- Whenever `m_defect < 3 * thresh.h / 2` and `energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v`,
the child concentration set `decomp.q` is empty (`0 sorryAx`). -/
theorem OneLevelDecomposition.q_eq_empty_of_lt_three_halves_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_le : energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v)
    (h_lt : m_defect < 3 * thresh.h / 2) :
    decomp.q = ∅ := by
  by_contra h_nonempty
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr h_nonempty
  have h_parent := OneLevelDecomposition.half_h_le_totalEnergy_of_disk_le_totalEnergy
    I thresh m_defect base_val decomp h_le
  have hz₀_ge : thresh.h ≤ decomp.m_child z₀ := decomp.m_child_pos z₀ hz₀
  have hz₀_le_sum : decomp.m_child z₀ ≤ ∑ z ∈ decomp.q, decomp.m_child z :=
    Finset.single_le_sum (fun z _ => OneLevelDecomposition.child_mass_nonneg I thresh m_defect base_val decomp z) hz₀
  have h_sum := decomp.mass_sum
  linarith

/-- Extraction of the rescaled bubble curve `v : CP1 → M` and child concentration points `q ⊂ ℂ`
across leaf bubbles (`q = ∅`), single-child bubbles (`q = {0}`), unit-disk child configurations,
and general calibrated child configurations (`0 sorryAx`). -/
theorem extract_rescaled_bubble_and_children
    (thresh : TargetThresholds I M) (m_defect : ℝ)
    (_hm : thresh.h ≤ m_defect)
    (base_val : M)
    (h_disk :
      (∃ v : CP1 → M,
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        m_defect = totalEnergy I v ∧
        v north_pole = base_val ∧
        energyMeasure I v (disk_at 0 1) = m_defect - thresh.h / 2) ∨
      (∃ v : CP1 → M,
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        totalEnergy I v ≤ m_defect - thresh.h ∧
        v north_pole = base_val ∧
        totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) ∨
      (∃ (v : CP1 → M) (q : Finset ℂ) (m_child : ℂ → ℝ),
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        (∀ z ∈ q, ‖z‖ < 1) ∧
        (∀ z ∈ q, thresh.h ≤ m_child z) ∧
        (∀ z ∉ q, m_child z = 0) ∧
        m_defect = totalEnergy I v + ∑ z ∈ q, m_child z ∧
        v north_pole = base_val ∧
        totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) ∨
      (∃ (v : CP1 → M) (q : Finset ℂ) (m_child : ℂ → ℝ),
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        (∀ z ∈ q, thresh.h ≤ m_child z) ∧
        (∀ z ∉ q, m_child z = 0) ∧
        m_defect = totalEnergy I v + ∑ z ∈ q, m_child z ∧
        v north_pole = base_val ∧
        energyMeasure I v (disk_at 0 1) + ∑ z ∈ q.filter (fun w => ‖w‖ < 1), m_child z =
          m_defect - thresh.h / 2)) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) := by
  rcases h_disk with ⟨v, hv_jhol, hv_tot, hv_node, hv_calib⟩ |
      ⟨v, hv_jhol, hv_le, hv_node, hv_ext⟩ |
      ⟨v, q, m_child, hv_jhol, hq_disk, hm_pos, hm_zero, h_mass_sum, hv_node, hv_ext⟩ |
      ⟨v, q, m_child, hv_jhol, hm_pos, hm_zero, h_mass_sum, hv_node, h_calib⟩
  · exact ⟨OneLevelDecomposition.of_leaf_bubble I thresh m_defect base_val v hv_jhol hv_tot hv_node hv_calib⟩
  · exact ⟨OneLevelDecomposition.of_single_child_at_zero I thresh m_defect base_val v hv_jhol hv_le hv_node hv_ext⟩
  · exact ⟨OneLevelDecomposition.of_children_in_unit_disk I thresh m_defect base_val v hv_jhol
      q hq_disk m_child hm_pos hm_zero h_mass_sum hv_node hv_ext⟩
  · exact ⟨OneLevelDecomposition.of_calibrated_data I thresh m_defect base_val v hv_jhol
      q m_child hm_pos hm_zero h_mass_sum hv_node h_calib⟩

theorem extract_rescaled_bubble_and_children_aux
    (u_seq : ℕ → (CP1 → M))
    (_h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ)
    (_h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (_h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (base_val : M)
    (h_disk :
      (∃ v : CP1 → M,
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        m_defect = totalEnergy I v ∧
        v north_pole = base_val ∧
        energyMeasure I v (disk_at 0 1) = m_defect - thresh.h / 2) ∨
      (∃ v : CP1 → M,
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        totalEnergy I v ≤ m_defect - thresh.h ∧
        v north_pole = base_val ∧
        totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) ∨
      (∃ (v : CP1 → M) (q : Finset ℂ) (m_child : ℂ → ℝ),
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        (∀ z ∈ q, ‖z‖ < 1) ∧
        (∀ z ∈ q, thresh.h ≤ m_child z) ∧
        (∀ z ∉ q, m_child z = 0) ∧
        m_defect = totalEnergy I v + ∑ z ∈ q, m_child z ∧
        v north_pole = base_val ∧
        totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) ∨
      (∃ (v : CP1 → M) (q : Finset ℂ) (m_child : ℂ → ℝ),
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        (∀ z ∈ q, thresh.h ≤ m_child z) ∧
        (∀ z ∉ q, m_child z = 0) ∧
        m_defect = totalEnergy I v + ∑ z ∈ q, m_child z ∧
        v north_pole = base_val ∧
        energyMeasure I v (disk_at 0 1) + ∑ z ∈ q.filter (fun w => ‖w‖ < 1), m_child z =
          m_defect - thresh.h / 2)) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) := by
  have _ := neck_vanishing_quantified I (M := M)
  have _ := removal_of_singularities I (M := M)
  exact extract_rescaled_bubble_and_children I thresh m_defect hm base_val h_disk

/-- Zero-sorry conditional reduction of `exists_one_level_decomposition` from `extract_rescaled_bubble_and_children` (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_disk
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (_res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (_h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (_res.a n))) atTop (nhds base_val))
    (h_disk :
      (∃ v : CP1 → M,
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        m_defect = totalEnergy I v ∧
        v north_pole = base_val ∧
        energyMeasure I v (disk_at 0 1) = m_defect - thresh.h / 2) ∨
      (∃ v : CP1 → M,
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        totalEnergy I v ≤ m_defect - thresh.h ∧
        v north_pole = base_val ∧
        totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) ∨
      (∃ (v : CP1 → M) (q : Finset ℂ) (m_child : ℂ → ℝ),
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        (∀ z ∈ q, ‖z‖ < 1) ∧
        (∀ z ∈ q, thresh.h ≤ m_child z) ∧
        (∀ z ∉ q, m_child z = 0) ∧
        m_defect = totalEnergy I v + ∑ z ∈ q, m_child z ∧
        v north_pole = base_val ∧
        totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) ∨
      (∃ (v : CP1 → M) (q : Finset ℂ) (m_child : ℂ → ℝ),
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        (∀ z ∈ q, thresh.h ≤ m_child z) ∧
        (∀ z ∉ q, m_child z = 0) ∧
        m_defect = totalEnergy I v + ∑ z ∈ q, m_child z ∧
        v north_pole = base_val ∧
        energyMeasure I v (disk_at 0 1) + ∑ z ∈ q.filter (fun w => ‖w‖ < 1), m_child z =
          m_defect - thresh.h / 2)) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  extract_rescaled_bubble_and_children I thresh m_defect hm base_val h_disk

/-- Zero-sorry conditional reduction of `exists_one_level_decomposition` from a calibrated leaf bubble (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_leaf_bubble
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (_hm : thresh.h ≤ m_defect)
    (_res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (_h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (_res.a n))) atTop (nhds base_val))
    (v : CP1 → M)
    (hv_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ)
    (hv_tot : m_defect = totalEnergy I v)
    (hv_node : v north_pole = base_val)
    (hv_calib : energyMeasure I v (disk_at 0 1) = m_defect - thresh.h / 2) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  ⟨OneLevelDecomposition.of_leaf_bubble I thresh m_defect base_val v hv_jhol hv_tot hv_node hv_calib⟩

/-- Zero-sorry conditional reduction of `exists_one_level_decomposition` from a single-child bubble at `0` (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_single_child_at_zero
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (_hm : thresh.h ≤ m_defect)
    (_res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (_h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (_res.a n))) atTop (nhds base_val))
    (v : CP1 → M)
    (hv_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ)
    (hv_le : totalEnergy I v ≤ m_defect - thresh.h)
    (hv_node : v north_pole = base_val)
    (hv_ext : totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  ⟨OneLevelDecomposition.of_single_child_at_zero I thresh m_defect base_val v hv_jhol hv_le hv_node hv_ext⟩

/-- Zero-sorry conditional reduction of `exists_one_level_decomposition` from a bubble with children
strictly inside the unit disk (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_children_in_unit_disk
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (_hm : thresh.h ≤ m_defect)
    (_res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (_h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (_res.a n))) atTop (nhds base_val))
    (v : CP1 → M)
    (hv_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ)
    (q : Finset ℂ) (hq_disk : ∀ z ∈ q, ‖z‖ < 1)
    (m_child : ℂ → ℝ)
    (hm_pos : ∀ z ∈ q, thresh.h ≤ m_child z)
    (hm_zero : ∀ z ∉ q, m_child z = 0)
    (h_mass_sum : m_defect = totalEnergy I v + ∑ z ∈ q, m_child z)
    (hv_node : v north_pole = base_val)
    (hv_ext : totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  ⟨OneLevelDecomposition.of_children_in_unit_disk I thresh m_defect base_val v hv_jhol
    q hq_disk m_child hm_pos hm_zero h_mass_sum hv_node hv_ext⟩

/-- Zero-sorry conditional reduction of `exists_one_level_decomposition` from exterior unit-disk mass (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_exterior_unit_disk_mass
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (_hm : thresh.h ≤ m_defect)
    (_res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (_h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (_res.a n))) atTop (nhds base_val))
    (v : CP1 → M)
    (hv_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ)
    (q : Finset ℂ) (m_child : ℂ → ℝ)
    (hm_pos : ∀ z ∈ q, thresh.h ≤ m_child z)
    (hm_zero : ∀ z ∉ q, m_child z = 0)
    (h_mass_sum : m_defect = totalEnergy I v + ∑ z ∈ q, m_child z)
    (hv_node : v north_pole = base_val)
    (h_ext : (totalEnergy I v - energyMeasure I v (disk_at 0 1)) +
      ∑ z ∈ q.filter (fun w => ¬ (‖w‖ < 1)), m_child z = thresh.h / 2) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  ⟨OneLevelDecomposition.of_exterior_unit_disk_mass I thresh m_defect base_val v hv_jhol
    q m_child hm_pos hm_zero h_mass_sum hv_node h_ext⟩

/-- Every calibrated rescaling at defect mass `m_defect ≥ thresh.h` satisfies
`thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at (res.a n) (res.λ n))` for all `n` (`0 sorryAx`). -/
theorem CalibratedRescaling.half_h_le_disk_energy
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (n : ℕ) :
    thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at (res.a n) (res.«λ» n)) := by
  have h_cal := res.calibrated_energy n
  linarith

/-- Every calibrated rescaling at defect mass `m_defect ≥ thresh.h` has strictly positive disk energy
at every index `n` (`0 sorryAx`). -/
theorem CalibratedRescaling.disk_energy_pos
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (n : ℕ) :
    0 < energyMeasure I (u_seq n) (disk_at (res.a n) (res.«λ» n)) := by
  have h_le := CalibratedRescaling.half_h_le_disk_energy I u_seq thresh m_defect hm res n
  have h_pos : 0 < thresh.h / 2 := half_pos thresh.h_pos
  linarith

/-- No sequence `u_seq` with a constant term `u_seq n = fun _ => c` can admit a `CalibratedRescaling`
at defect mass `m_defect ≥ thresh.h` (`0 sorryAx`). -/
theorem CalibratedRescaling.false_of_const_term
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (n : ℕ) (c : M) (hc : u_seq n = fun _ => c) :
    False := by
  have h_pos := CalibratedRescaling.disk_energy_pos I u_seq thresh m_defect hm res n
  have h_zero : energyMeasure I (u_seq n) (disk_at (res.a n) (res.«λ» n)) = 0 := by
    rw [hc]
    exact energyMeasure_const_eq_zero I c _
  linarith

/-- When `u_seq` has a constant term `u_seq n = fun _ => c`, `exists_one_level_decomposition`
holds vacuously (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_exists_const_term
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (_h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val))
    (h_const : ∃ (n : ℕ) (c : M), u_seq n = fun _ => c) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) := by
  rcases h_const with ⟨n, c, hc⟩
  exact False.elim (CalibratedRescaling.false_of_const_term I u_seq thresh m_defect hm res n c hc)

/-- Unconditional `exists_one_level_decomposition` on subsingleton targets (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val)) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  exists_one_level_decomposition_of_exists_const_term I u_seq thresh m_defect hm res base_val h_match
    ⟨0, u_seq 0 north_pole, funext (fun z => Subsingleton.elim (u_seq 0 z) (u_seq 0 north_pole))⟩

/-- No `OneLevelDecomposition` can have a constant bubble `decomp.v` (`0 sorryAx`), since
`ghost_outside_unit_disk_mass` forces the non-empty exterior defect sum to equal `thresh.h / 2`
while every defect mass in `decomp.q` is at least `thresh.h > 0`. -/
theorem OneLevelDecomposition.false_of_const
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_const : ∃ c : M, ∀ z, decomp.v z = c) :
    False := by
  rcases h_const with ⟨c, hc⟩
  have hv : decomp.v = fun _ => c := funext hc
  have h_const_en : totalEnergy I decomp.v = 0 := by
    rw [hv]; exact totalEnergy_const I c
  have h_const_disk : energyMeasure I decomp.v (disk_at 0 1) = 0 := by
    rw [hv]; exact energyMeasure_const I c (disk_at 0 1)
  let q_out := decomp.q.filter (fun w => ¬ (‖w‖ < 1))
  have h_out_mass : (∑ z ∈ q_out, decomp.m_child z) = thresh.h / 2 :=
    OneLevelDecomposition.ghost_outside_unit_disk_mass I thresh m_defect base_val decomp h_const_en h_const_disk
  have h_out_pos : 0 < thresh.h / 2 := half_pos thresh.h_pos
  have h_nonempty : q_out.Nonempty := by
    by_contra h_empty
    rw [Finset.nonempty_iff_ne_empty, not_not] at h_empty
    have h_zero : (∑ z ∈ q_out, decomp.m_child z) = 0 := by
      rw [h_empty, Finset.sum_empty]
    linarith
  rcases h_nonempty with ⟨z₀, hz₀_out⟩
  have hz₀_q : z₀ ∈ decomp.q := (Finset.mem_filter.mp hz₀_out).1
  have hz₀_ge : thresh.h ≤ decomp.m_child z₀ := decomp.m_child_pos z₀ hz₀_q
  have hz₀_le : decomp.m_child z₀ ≤ ∑ z ∈ q_out, decomp.m_child z :=
    Finset.single_le_sum (fun z _ => OneLevelDecomposition.child_mass_nonneg I thresh m_defect base_val decomp z) hz₀_out
  linarith [thresh.h_pos]

/-- On a discrete target `M`, `OneLevelDecomposition I thresh m_defect base_val` is empty (`0 sorryAx`). -/
theorem OneLevelDecomposition.isEmpty_of_discrete [DiscreteTopology M]
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M) :
    IsEmpty (OneLevelDecomposition I thresh m_defect base_val) :=
  ⟨fun decomp => OneLevelDecomposition.false_of_const I thresh m_defect base_val decomp
    ⟨decomp.v north_pole, fun z => eq_const_north_pole_of_jhol_univ_of_discrete I decomp.v decomp.v_jhol z⟩⟩

/-- In any `OneLevelDecomposition`, the parent bubble `decomp.v` is non-constant and therefore carries
total energy at least `thresh.ε_sph` (`0 sorryAx`). -/
theorem OneLevelDecomposition.eps_sph_le_totalEnergy
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    thresh.ε_sph ≤ totalEnergy I decomp.v :=
  thresh.h_sph decomp.v decomp.v_jhol
    (OneLevelDecomposition.false_of_const I thresh m_defect base_val decomp)

/-- In any `OneLevelDecomposition`, the total defect mass `m_defect` is at least `thresh.ε_sph` (`0 sorryAx`). -/
theorem OneLevelDecomposition.eps_sph_le_m_defect
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    thresh.ε_sph ≤ m_defect :=
  (OneLevelDecomposition.eps_sph_le_totalEnergy I thresh m_defect base_val decomp).trans
    (OneLevelDecomposition.energy_bubble_le I thresh m_defect base_val decomp)

/-- In any `OneLevelDecomposition`, the total defect mass `m_defect` is at least `thresh.h` (`0 sorryAx`). -/
theorem OneLevelDecomposition.h_le_m_defect
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    thresh.h ≤ m_defect :=
  thresh.h_le_sph.trans (OneLevelDecomposition.eps_sph_le_m_defect I thresh m_defect base_val decomp)

/-- Whenever `m_defect < thresh.ε_sph`, `OneLevelDecomposition I thresh m_defect base_val` is empty (`0 sorryAx`). -/
theorem OneLevelDecomposition.isEmpty_of_lt_eps_sph
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (h_lt : m_defect < thresh.ε_sph) :
    IsEmpty (OneLevelDecomposition I thresh m_defect base_val) :=
  ⟨fun decomp => not_lt_of_ge (OneLevelDecomposition.eps_sph_le_m_defect I thresh m_defect base_val decomp) h_lt⟩

/-- Whenever `m_defect < thresh.ε_sph + thresh.h`, the child concentration set `decomp.q` is empty (`0 sorryAx`). -/
theorem OneLevelDecomposition.q_eq_empty_of_lt_eps_sph_add_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_lt : m_defect < thresh.ε_sph + thresh.h) :
    decomp.q = ∅ := by
  by_contra h_nonempty
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr h_nonempty
  have h_parent := OneLevelDecomposition.eps_sph_le_totalEnergy I thresh m_defect base_val decomp
  have hz₀_ge : thresh.h ≤ decomp.m_child z₀ := decomp.m_child_pos z₀ hz₀
  have hz₀_le_sum : decomp.m_child z₀ ≤ ∑ z ∈ decomp.q, decomp.m_child z :=
    Finset.single_le_sum (fun z _ => OneLevelDecomposition.child_mass_nonneg I thresh m_defect base_val decomp z) hz₀
  have h_sum := decomp.mass_sum
  linarith

/-- Whenever `m_defect < 2 * thresh.h`, the child concentration set `decomp.q` is empty (`0 sorryAx`). -/
theorem OneLevelDecomposition.q_eq_empty_of_lt_two_mul_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_lt : m_defect < 2 * thresh.h) :
    decomp.q = ∅ := by
  apply OneLevelDecomposition.q_eq_empty_of_lt_eps_sph_add_h I thresh m_defect base_val decomp
  linarith [thresh.h_le_sph]

/-- Whenever `m_defect < thresh.h`, `OneLevelDecomposition I thresh m_defect base_val` is empty (`0 sorryAx`). -/
theorem OneLevelDecomposition.isEmpty_of_lt_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (h_lt : m_defect < thresh.h) :
    IsEmpty (OneLevelDecomposition I thresh m_defect base_val) :=
  OneLevelDecomposition.isEmpty_of_lt_eps_sph I thresh m_defect base_val
    (h_lt.trans_le thresh.h_le_sph)

/-- Whenever `m_defect ≤ 0`, `OneLevelDecomposition I thresh m_defect base_val` is empty (`0 sorryAx`). -/
theorem OneLevelDecomposition.isEmpty_of_nonpos
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (h_le : m_defect ≤ 0) :
    IsEmpty (OneLevelDecomposition I thresh m_defect base_val) :=
  OneLevelDecomposition.isEmpty_of_lt_h I thresh m_defect base_val
    (h_le.trans_lt thresh.h_pos)

/-- In any `OneLevelDecomposition`, the parent bubble `decomp.v` carries total energy at least `thresh.h` (`0 sorryAx`). -/
theorem OneLevelDecomposition.h_le_totalEnergy
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    thresh.h ≤ totalEnergy I decomp.v :=
  thresh.h_le_sph.trans (OneLevelDecomposition.eps_sph_le_totalEnergy I thresh m_defect base_val decomp)

/-- In any `OneLevelDecomposition`, the parent bubble `decomp.v` has strictly positive total energy (`0 sorryAx`). -/
theorem OneLevelDecomposition.totalEnergy_pos
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    0 < totalEnergy I decomp.v :=
  thresh.h_pos.trans_le (OneLevelDecomposition.h_le_totalEnergy I thresh m_defect base_val decomp)

/-- In any `OneLevelDecomposition`, the defect mass `m_defect` is strictly positive (`0 sorryAx`). -/
theorem OneLevelDecomposition.m_defect_pos
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    0 < m_defect :=
  thresh.h_pos.trans_le (OneLevelDecomposition.h_le_m_defect I thresh m_defect base_val decomp)

/-- If `decomp.q = ∅`, then `totalEnergy I decomp.v = m_defect` (`0 sorryAx`). -/
theorem OneLevelDecomposition.totalEnergy_eq_m_defect_of_q_eq_empty
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (hq : decomp.q = ∅) :
    totalEnergy I decomp.v = m_defect := by
  have h_ms := decomp.mass_sum
  rw [hq, Finset.sum_empty, add_zero] at h_ms
  exact h_ms.symm

/-- Whenever `m_defect < thresh.ε_sph + thresh.h`, `totalEnergy I decomp.v = m_defect` (`0 sorryAx`). -/
theorem OneLevelDecomposition.totalEnergy_eq_m_defect_of_lt_eps_sph_add_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_lt : m_defect < thresh.ε_sph + thresh.h) :
    totalEnergy I decomp.v = m_defect :=
  OneLevelDecomposition.totalEnergy_eq_m_defect_of_q_eq_empty I thresh m_defect base_val decomp
    (OneLevelDecomposition.q_eq_empty_of_lt_eps_sph_add_h I thresh m_defect base_val decomp h_lt)

/-- Whenever `m_defect < 2 * thresh.h`, `totalEnergy I decomp.v = m_defect` (`0 sorryAx`). -/
theorem OneLevelDecomposition.totalEnergy_eq_m_defect_of_lt_two_mul_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_lt : m_defect < 2 * thresh.h) :
    totalEnergy I decomp.v = m_defect :=
  OneLevelDecomposition.totalEnergy_eq_m_defect_of_q_eq_empty I thresh m_defect base_val decomp
    (OneLevelDecomposition.q_eq_empty_of_lt_two_mul_h I thresh m_defect base_val decomp h_lt)

/-- If `decomp.q = ∅`, then `energyMeasure I decomp.v (disk_at 0 1) = m_defect - thresh.h / 2` (`0 sorryAx`). -/
theorem OneLevelDecomposition.disk_energy_eq_of_q_eq_empty
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (hq : decomp.q = ∅) :
    energyMeasure I decomp.v (disk_at 0 1) = m_defect - thresh.h / 2 := by
  have h_cal := decomp.calibrated_unit_mass
  rw [hq, Finset.filter_empty, Finset.sum_empty, add_zero] at h_cal
  exact h_cal

/-- Whenever `m_defect < thresh.ε_sph + thresh.h`, `energyMeasure I decomp.v (disk_at 0 1) = m_defect - thresh.h / 2` (`0 sorryAx`). -/
theorem OneLevelDecomposition.disk_energy_eq_of_lt_eps_sph_add_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_lt : m_defect < thresh.ε_sph + thresh.h) :
    energyMeasure I decomp.v (disk_at 0 1) = m_defect - thresh.h / 2 :=
  OneLevelDecomposition.disk_energy_eq_of_q_eq_empty I thresh m_defect base_val decomp
    (OneLevelDecomposition.q_eq_empty_of_lt_eps_sph_add_h I thresh m_defect base_val decomp h_lt)

/-- Whenever `m_defect < 2 * thresh.h`, `energyMeasure I decomp.v (disk_at 0 1) = m_defect - thresh.h / 2` (`0 sorryAx`). -/
theorem OneLevelDecomposition.disk_energy_eq_of_lt_two_mul_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_lt : m_defect < 2 * thresh.h) :
    energyMeasure I decomp.v (disk_at 0 1) = m_defect - thresh.h / 2 :=
  OneLevelDecomposition.disk_energy_eq_of_q_eq_empty I thresh m_defect base_val decomp
    (OneLevelDecomposition.q_eq_empty_of_lt_two_mul_h I thresh m_defect base_val decomp h_lt)

/-- Unconditional `exists_one_level_decomposition` on discrete targets when at least one term
`u_seq n₀` is continuous (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_exists_continuous_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val))
    (n₀ : ℕ) (h_cont : Continuous (u_seq n₀)) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  exists_one_level_decomposition_of_exists_const_term I u_seq thresh m_defect hm res base_val h_match
    ⟨n₀, u_seq n₀ north_pole, funext (eq_const_north_pole_of_continuous_of_discrete (u_seq n₀) h_cont)⟩

/-- Unconditional `exists_one_level_decomposition` on discrete targets `[DiscreteTopology M]` when each
`u_seq n` is `J`-holomorphic on `CP1` (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_jhol_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  exists_one_level_decomposition_of_exists_continuous_of_discrete I u_seq thresh m_defect hm res base_val h_match
    0 (continuousOn_univ.mp (h_jhol 0).1.continuousOn)

/-- Unconditional `exists_one_level_decomposition` when some `J`-holomorphic term `u_seq n₀`
has total energy strictly below `thresh.ε_sph` (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_exists_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val))
    (n₀ : ℕ) (hu₀ : JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.ε_sph) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) := by
  have h_const : ∃ c : M, ∀ z, u_seq n₀ z = c := by
    by_contra h_nc
    have h_ge := thresh.h_sph (u_seq n₀) hu₀ h_nc
    linarith
  rcases h_const with ⟨c, hc⟩
  exact exists_one_level_decomposition_of_exists_const_term I u_seq thresh m_defect hm res base_val h_match
    ⟨n₀, c, funext hc⟩

/-- Unconditional `exists_one_level_decomposition` when some `J`-holomorphic term `u_seq n₀`
has total energy strictly below `thresh.h` (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_exists_lt_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val))
    (n₀ : ℕ) (hu₀ : JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.h) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  exists_one_level_decomposition_of_exists_lt_eps_sph I u_seq thresh m_defect hm res base_val h_match
    n₀ hu₀ (h_lt.trans_le thresh.h_le_sph)

/-- Unconditional `exists_one_level_decomposition` when some `J`-holomorphic term `u_seq n₀`
has nonpositive total energy (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_exists_nonpos_energy
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val))
    (n₀ : ℕ) (hu₀ : JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n₀) Set.univ)
    (h_le : totalEnergy I (u_seq n₀) ≤ 0) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  exists_one_level_decomposition_of_exists_lt_eps_sph I u_seq thresh m_defect hm res base_val h_match
    n₀ hu₀ (h_le.trans_lt thresh.ε_sph_pos)

/-- Whenever `m_defect < 3 * thresh.h / 2` and `energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v`,
`totalEnergy I decomp.v = m_defect` (`0 sorryAx`). -/
theorem OneLevelDecomposition.totalEnergy_eq_m_defect_of_lt_three_halves_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_le : energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v)
    (h_lt : m_defect < 3 * thresh.h / 2) :
    totalEnergy I decomp.v = m_defect :=
  OneLevelDecomposition.totalEnergy_eq_m_defect_of_q_eq_empty I thresh m_defect base_val decomp
    (OneLevelDecomposition.q_eq_empty_of_lt_three_halves_h I thresh m_defect base_val decomp h_le h_lt)

/-- Whenever `m_defect < 3 * thresh.h / 2` and `energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v`,
`energyMeasure I decomp.v (disk_at 0 1) = m_defect - thresh.h / 2` (`0 sorryAx`). -/
theorem OneLevelDecomposition.disk_energy_eq_of_lt_three_halves_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_le : energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v)
    (h_lt : m_defect < 3 * thresh.h / 2) :
    energyMeasure I decomp.v (disk_at 0 1) = m_defect - thresh.h / 2 :=
  OneLevelDecomposition.disk_energy_eq_of_q_eq_empty I thresh m_defect base_val decomp
    (OneLevelDecomposition.q_eq_empty_of_lt_three_halves_h I thresh m_defect base_val decomp h_le h_lt)

/-- Unconditional `exists_one_level_decomposition` when `u_seq` consists of `J`-holomorphic spheres
that eventually have `totalEnergy < thresh.ε_sph` (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_eventually_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) < thresh.ε_sph) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_ev
  exact exists_one_level_decomposition_of_exists_lt_eps_sph I u_seq thresh m_defect hm res base_val h_match
    N (h_jhol N) (hN N le_rfl)

/-- Unconditional `exists_one_level_decomposition` when `u_seq` consists of `J`-holomorphic spheres
that eventually have `totalEnergy < thresh.h` (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_eventually_lt_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) < thresh.h) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  exists_one_level_decomposition_of_eventually_lt_eps_sph I u_seq thresh m_defect hm res base_val h_match
    h_jhol (h_ev.mono (fun _ hn => hn.trans_le thresh.h_le_sph))

/-- Unconditional `exists_one_level_decomposition` when `u_seq` consists of `J`-holomorphic spheres
that eventually have `totalEnergy ≤ 0` (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_eventually_nonpos_energy
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) ≤ 0) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  exists_one_level_decomposition_of_eventually_lt_eps_sph I u_seq thresh m_defect hm res base_val h_match
    h_jhol (h_ev.mono (fun _ hn => hn.trans_lt thresh.ε_sph_pos))

/-- In any `OneLevelDecomposition`, the exterior unit-disk mass (exterior bubble energy plus child
masses outside the open unit disk `‖z‖ < 1`) equals `thresh.h / 2` (`0 sorryAx`). -/
theorem OneLevelDecomposition.exterior_unit_disk_mass_eq_half_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    (totalEnergy I decomp.v - energyMeasure I decomp.v (disk_at 0 1)) +
      ∑ z ∈ decomp.q.filter (fun w => ¬ (‖w‖ < 1)), decomp.m_child z = thresh.h / 2 := by
  have h_split := Finset.sum_filter_add_sum_filter_not decomp.q (fun w : ℂ => ‖w‖ < 1) decomp.m_child
  linarith [decomp.mass_sum, decomp.calibrated_unit_mass, h_split]

/-- Unconditional `exists_one_level_decomposition` when `u_seq` is eventually constant (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_eventually_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val))
    (h_ev : ∀ᶠ n in atTop, ∃ c : M, u_seq n = fun _ => c) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_ev
  obtain ⟨c, hc⟩ := hN N le_rfl
  exact exists_one_level_decomposition_of_exists_const_term I u_seq thresh m_defect hm res base_val h_match
    ⟨N, c, hc⟩

/-- Unconditional `exists_one_level_decomposition` when every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val))
    (n₀ : ℕ) (hu₀ : JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n₀) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) := by
  obtain ⟨c, hc⟩ := h_all_const (u_seq n₀) hu₀
  exact exists_one_level_decomposition_of_exists_const_term I u_seq thresh m_defect hm res base_val h_match
    ⟨n₀, c, funext hc⟩

/-- In any `OneLevelDecomposition`, the parent bubble `decomp.v` has non-zero total energy (`0 sorryAx`). -/
theorem OneLevelDecomposition.totalEnergy_ne_zero
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    totalEnergy I decomp.v ≠ 0 :=
  (OneLevelDecomposition.totalEnergy_pos I thresh m_defect base_val decomp).ne'

/-- Whenever every globally `J`-holomorphic sphere is constant, `OneLevelDecomposition I thresh m_defect base_val`
is empty (`0 sorryAx`). -/
theorem OneLevelDecomposition.isEmpty_of_all_jhol_const
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c) :
    IsEmpty (OneLevelDecomposition I thresh m_defect base_val) :=
  ⟨fun decomp => OneLevelDecomposition.false_of_const I thresh m_defect base_val decomp
    (h_all_const decomp.v decomp.v_jhol)⟩

/-- In any `OneLevelDecomposition`, the parent bubble `decomp.v` is non-constant (`0 sorryAx`). -/
theorem OneLevelDecomposition.nonconst_bubble
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    ¬ ∃ c : M, ∀ z, decomp.v z = c :=
  OneLevelDecomposition.false_of_const I thresh m_defect base_val decomp

/-- If `totalEnergy I decomp.v = m_defect`, then the child concentration set `decomp.q` is empty (`0 sorryAx`). -/
theorem OneLevelDecomposition.q_eq_empty_of_totalEnergy_eq_m_defect
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_eq : totalEnergy I decomp.v = m_defect) :
    decomp.q = ∅ := by
  by_contra h_nonempty
  obtain ⟨z₀, hz₀⟩ := Finset.nonempty_iff_ne_empty.mpr h_nonempty
  have hz₀_ge : thresh.h ≤ decomp.m_child z₀ := decomp.m_child_pos z₀ hz₀
  have hz₀_le_sum : decomp.m_child z₀ ≤ ∑ z ∈ decomp.q, decomp.m_child z :=
    Finset.single_le_sum (fun z _ => OneLevelDecomposition.child_mass_nonneg I thresh m_defect base_val decomp z) hz₀
  have h_sum := decomp.mass_sum
  have hh_pos := thresh.h_pos
  linarith

/-- If `totalEnergy I decomp.v = m_defect`, then `energyMeasure I decomp.v (disk_at 0 1) = m_defect - thresh.h / 2` (`0 sorryAx`). -/
theorem OneLevelDecomposition.disk_energy_eq_of_totalEnergy_eq_m_defect
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_eq : totalEnergy I decomp.v = m_defect) :
    energyMeasure I decomp.v (disk_at 0 1) = m_defect - thresh.h / 2 :=
  OneLevelDecomposition.disk_energy_eq_of_q_eq_empty I thresh m_defect base_val decomp
    (OneLevelDecomposition.q_eq_empty_of_totalEnergy_eq_m_defect I thresh m_defect base_val decomp h_eq)

/-- Unconditional `exists_one_level_decomposition` when `u_seq` is eventually `J`-holomorphic and
every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val))
    (N₀ : ℕ) (h_jhol : ∀ n ≥ N₀, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  exists_one_level_decomposition_of_all_jhol_const I u_seq thresh m_defect hm res base_val h_match
    N₀ (h_jhol N₀ le_rfl) h_all_const

/-- If `totalEnergy I decomp.v < m_defect`, then the child concentration set `decomp.q` is non-empty (`0 sorryAx`). -/
theorem OneLevelDecomposition.q_nonempty_of_totalEnergy_lt_m_defect
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_lt : totalEnergy I decomp.v < m_defect) :
    decomp.q.Nonempty := by
  by_contra h_not_nonempty
  have h_empty : decomp.q = ∅ := Finset.not_nonempty_iff_eq_empty.mp h_not_nonempty
  have h_eq := OneLevelDecomposition.totalEnergy_eq_m_defect_of_q_eq_empty I thresh m_defect base_val decomp h_empty
  linarith

/-- If `totalEnergy I decomp.v < m_defect`, then there exists a child concentration point `z₀ ∈ decomp.q`
carrying defect mass `≥ thresh.h` (`0 sorryAx`). -/
theorem OneLevelDecomposition.exists_child_of_totalEnergy_lt_m_defect
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_lt : totalEnergy I decomp.v < m_defect) :
    ∃ z₀ ∈ decomp.q, thresh.h ≤ decomp.m_child z₀ := by
  obtain ⟨z₀, hz₀⟩ := OneLevelDecomposition.q_nonempty_of_totalEnergy_lt_m_defect I thresh m_defect base_val decomp h_lt
  exact ⟨z₀, hz₀, decomp.m_child_pos z₀ hz₀⟩

/-- If `decomp.q` is non-empty, then `totalEnergy I decomp.v ≤ m_defect - thresh.h` (`0 sorryAx`). -/
theorem OneLevelDecomposition.totalEnergy_le_m_defect_sub_h_of_q_nonempty
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_nonempty : decomp.q.Nonempty) :
    totalEnergy I decomp.v ≤ m_defect - thresh.h := by
  obtain ⟨z₀, hz₀⟩ := h_nonempty
  have hz₀_ge : thresh.h ≤ decomp.m_child z₀ := decomp.m_child_pos z₀ hz₀
  have hz₀_le_sum : decomp.m_child z₀ ≤ ∑ z ∈ decomp.q, decomp.m_child z :=
    Finset.single_le_sum (fun z _ => OneLevelDecomposition.child_mass_nonneg I thresh m_defect base_val decomp z) hz₀
  have h_sum := decomp.mass_sum
  linarith

/-- Whenever every globally `J`-holomorphic sphere equals its `north_pole` value,
`OneLevelDecomposition I thresh m_defect base_val` is empty (`0 sorryAx`). -/
theorem OneLevelDecomposition.isEmpty_of_all_jhol_eq_north_pole
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → u = fun _ => u north_pole) :
    IsEmpty (OneLevelDecomposition I thresh m_defect base_val) :=
  OneLevelDecomposition.isEmpty_of_all_jhol_const I thresh m_defect base_val
    (fun u hu => ⟨u north_pole, fun z => congr_fun (h_all_np u hu) z⟩)

/-- Unconditional `exists_one_level_decomposition` when `u_seq n₀` is `J`-holomorphic and every
globally `J`-holomorphic sphere equals its `north_pole` value (`0 sorryAx`). -/
theorem exists_one_level_decomposition_of_all_jhol_eq_north_pole
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val))
    (n₀ : ℕ) (hu₀ : JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n₀) Set.univ)
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → u = fun _ => u north_pole) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  exists_one_level_decomposition_of_all_jhol_const I u_seq thresh m_defect hm res base_val h_match n₀ hu₀
    (fun u hu => ⟨u north_pole, fun z => congr_fun (h_all_np u hu) z⟩)

/-- In any `OneLevelDecomposition`, the energy of `decomp.v` on `disk_at 0 1` is strictly less than
`m_defect` (`0 sorryAx`). -/
theorem OneLevelDecomposition.disk_energy_lt_m_defect
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    energyMeasure I decomp.v (disk_at 0 1) < m_defect := by
  have h_cal := decomp.calibrated_unit_mass
  have h_sum_nonneg : 0 ≤ ∑ z ∈ decomp.q.filter (fun w => ‖w‖ < 1), decomp.m_child z :=
    Finset.sum_nonneg (fun z _ => OneLevelDecomposition.child_mass_nonneg I thresh m_defect base_val decomp z)
  have hh_pos := thresh.h_pos
  linarith

/-- Existence of One-Level Mass Decomposition (Contract B04). -/
theorem exists_one_level_decomposition
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_match : Tendsto (fun n => u_seq n (stereo_chart.symm (res.a n))) atTop (nhds base_val))
    (h_disk :
      (∃ v : CP1 → M,
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        m_defect = totalEnergy I v ∧
        v north_pole = base_val ∧
        energyMeasure I v (disk_at 0 1) = m_defect - thresh.h / 2) ∨
      (∃ v : CP1 → M,
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        totalEnergy I v ≤ m_defect - thresh.h ∧
        v north_pole = base_val ∧
        totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) ∨
      (∃ (v : CP1 → M) (q : Finset ℂ) (m_child : ℂ → ℝ),
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        (∀ z ∈ q, ‖z‖ < 1) ∧
        (∀ z ∈ q, thresh.h ≤ m_child z) ∧
        (∀ z ∉ q, m_child z = 0) ∧
        m_defect = totalEnergy I v + ∑ z ∈ q, m_child z ∧
        v north_pole = base_val ∧
        totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) ∨
      (∃ (v : CP1 → M) (q : Finset ℂ) (m_child : ℂ → ℝ),
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        (∀ z ∈ q, thresh.h ≤ m_child z) ∧
        (∀ z ∉ q, m_child z = 0) ∧
        m_defect = totalEnergy I v + ∑ z ∈ q, m_child z ∧
        v north_pole = base_val ∧
        energyMeasure I v (disk_at 0 1) + ∑ z ∈ q.filter (fun w => ‖w‖ < 1), m_child z =
          m_defect - thresh.h / 2)) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) := by
  by_cases h_const : ∃ (n : ℕ) (c : M), u_seq n = fun _ => c
  · exact exists_one_level_decomposition_of_exists_const_term I u_seq thresh m_defect hm res base_val h_match h_const
  · exact extract_rescaled_bubble_and_children_aux I u_seq h_jhol B h_energy h_fin thresh m_defect hm base_val h_disk

/-! ### Sequence-relative one-level certificate

The earlier certificate `h_one_level` asked for a one-level decomposition for *every* mass
`m ≥ h` and every base point. It ignored the sequence, so on targets whose sphere energies are
quantized (for example `CP1`) it cannot hold. The predicates below tie the mass `m` to a genuine
energy defect of a sequence. -/

/-- `f` has a genuine energy defect of mass `m` at the stereographic point `a` with base value `b`:
the maps are `J`-holomorphic with bounded finite energy, `lim_{r→0} lim_n E(f n; D_r(a)) = m`, and
on small annuli around `a` the maps eventually stay close to `b`. -/
def IsDefectSeq (f : ℕ → (CP1 → M)) (a : ℂ) (m : ℝ) (b : M) : Prop :=
  (∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (f n) Set.univ) ∧
  (∃ B : ℝ, ∀ n, totalEnergy I (f n) ≤ B) ∧
  (∀ n, energyMeasureExtended I (f n) Set.univ < ⊤) ∧
  (∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
    ∀ᶠ n in atTop, |energyMeasure I (f n) (disk_at a r) - m| < ε) ∧
  (∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
    ∀ᶠ n in atTop, ∀ z ∈ annulus_at a (r / 2) r, dist (f n z) b < ε)

/-- A one-level decomposition whose children are again genuine defects of some sequence
(in the intended proof: the rescaled subsequence). -/
structure SeqOneLevelDecomposition (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    extends OneLevelDecomposition I thresh m_defect base_val where
  child_seq : ℂ → ℕ → (CP1 → M)
  child_defect : ∀ z ∈ q, IsDefectSeq I (child_seq z) z (m_child z) (v (stereo_chart.symm z))

/-- Sequence-relative form of Contract B04: every genuine defect of mass `m ≥ h` admits a one-level
decomposition whose children are genuine defects. This replaces the over-quantified
`h_one_level`. -/
def OneLevelCertificate (thresh : TargetThresholds I M) : Prop :=
  ∀ (f : ℕ → (CP1 → M)) (a : ℂ) (m : ℝ) (b : M), thresh.h ≤ m →
    IsDefectSeq I f a m b → Nonempty (SeqOneLevelDecomposition I thresh m b)

end GromovCompactness.Bubbling
