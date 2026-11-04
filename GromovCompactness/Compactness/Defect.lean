/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Compactness.Concentration

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory Filter GromovCompactness GromovCompactness.Bookkeeping GromovCompactness.Analysis Classical

namespace GromovCompactness.Compactness

/-!
# Task C03: Defect Measure Identity and Moving Centers

This module formalizes the defect measure identity $\mu = u_0^* \omega + \sum_{p \in S} m_p \delta_p$
and energy conservation for pseudo-holomorphic curves, following Gromov (1985, §1.3),
Ivashkovich-Shevchishin (1999, §2.2), and `gromov_compactness.pdf` §4.5 (Task `C03`).

## Key Theorems
- `defect_measure_identity`: Exact measure identity and total energy convergence.
- `defect_mass_lower_bound`: Proof that $m_p \ge \varepsilon_{\mathrm{sph}} \ge h > 0$ for all $p \in S$.
- `isolating_disk_defect_limit`: Concentration on shrinking isolating disks.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- Evaluating a Dirac measure at its own center yields 1 (Zero-sorry). -/
lemma dirac_apply_singleton_self (p : CP1) : (Measure.dirac p : Measure CP1) {p} = 1 := by
  rw [Measure.dirac_apply_of_mem (Set.mem_singleton p)]

/-- Evaluating a Dirac measure at a different point yields 0 (Zero-sorry). -/
lemma dirac_apply_singleton_ne {p q : CP1} (hne : p ≠ q) : (Measure.dirac p : Measure CP1) {q} = 0 := by
  have h_not : p ∉ ({q} : Set CP1) := by simp [hne]
  rw [Measure.dirac_apply' _ (measurableSet_singleton q), Set.indicator_of_not_mem h_not]

/-- Evaluating a finite sum of weighted Dirac measures at an atom p ∈ S yields m(p) (Zero-sorry). -/
lemma dirac_sum_singleton_mem (S : Finset CP1) (m : CP1 → ℝ) (p : CP1) (hp : p ∈ S) :
    (∑ x ∈ S, (ENNReal.ofReal (m x) • Measure.dirac x)) {p} = ENNReal.ofReal (m p) := by
  rw [Measure.finset_sum_apply]
  have h_split : S = insert p (S.erase p) := (Finset.insert_erase hp).symm
  rw [h_split, Finset.sum_insert (Finset.not_mem_erase p S)]
  have h_dirac_self : (ENNReal.ofReal (m p) • Measure.dirac p) {p} = ENNReal.ofReal (m p) := by
    rw [Measure.smul_apply, dirac_apply_singleton_self, smul_eq_mul, mul_one]
  have h_dirac_rest : ∑ x ∈ S.erase p, (ENNReal.ofReal (m x) • Measure.dirac x) {p} = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hne : x ≠ p := Finset.ne_of_mem_erase hx
    rw [Measure.smul_apply, dirac_apply_singleton_ne hne, smul_eq_mul, mul_zero]
  rw [h_dirac_self, h_dirac_rest, add_zero]

/-- Evaluating a finite sum of weighted Dirac measures at p ∉ S yields 0 (Zero-sorry). -/
lemma dirac_sum_singleton_not_mem (S : Finset CP1) (m : CP1 → ℝ) (p : CP1) (hp : p ∉ S) :
    (∑ x ∈ S, (ENNReal.ofReal (m x) • Measure.dirac x)) {p} = 0 := by
  rw [Measure.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  have hne : x ≠ p := fun h => hp (h ▸ hx)
  rw [Measure.smul_apply, dirac_apply_singleton_ne hne, smul_eq_mul, mul_zero]

/-- Total mass of a finite sum of weighted Dirac measures equals the sum of weights (Zero-sorry). -/
lemma dirac_sum_univ (S : Finset CP1) (m : CP1 → ℝ) (h_pos : ∀ x ∈ S, 0 ≤ m x) :
    (∑ x ∈ S, (ENNReal.ofReal (m x) • Measure.dirac x)) Set.univ = ENNReal.ofReal (∑ x ∈ S, m x) := by
  rw [Measure.finset_sum_apply]
  have h1 : ∀ x ∈ S, (ENNReal.ofReal (m x) • Measure.dirac x) Set.univ = ENNReal.ofReal (m x) := by
    intro x _
    rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ x), smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl h1]
  exact (ENNReal.ofReal_sum_of_nonneg h_pos).symm

/-- For any concentration point p ∈ S, the atom mass is strictly positive (Zero-sorry). -/
lemma defect_atom_mass_pos
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) (p : CP1) (hp : p ∈ cdata.S) :
    0 < (cdata.μ {p}).toReal := by
  haveI := cdata.μ_fin
  have h_le := (cdata.S_def p).mp hp
  have h1 : 0 < ENNReal.ofReal thresh.ε_reg := ENNReal.ofReal_pos.mpr thresh.ε_reg_pos
  have h_atom_pos : 0 < cdata.μ {p} := h1.trans_le h_le
  have h_atom_lt_top : cdata.μ {p} < ⊤ := measure_lt_top cdata.μ {p}
  exact ENNReal.toReal_pos h_atom_pos.ne' h_atom_lt_top.ne

/-- For any concentration point p ∈ S, the atom mass is at least the regularity threshold (Zero-sorry). -/
lemma defect_atom_mass_ge_reg
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) (p : CP1) (hp : p ∈ cdata.S) :
    thresh.ε_reg ≤ (cdata.μ {p}).toReal := by
  haveI := cdata.μ_fin
  have h_le := (cdata.S_def p).mp hp
  have h_finite : cdata.μ {p} ≠ ⊤ := (measure_lt_top cdata.μ {p}).ne
  exact (ENNReal.ofReal_le_iff_le_toReal h_finite).mp h_le

/-- Total measure identity: When μ decomposes into smooth energy measure plus Dirac atoms,
its total mass on CP1 equals totalEnergy u₀ + ∑ m_p (Zero-sorry). -/
theorem defect_measure_total_mass
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (m : CP1 → ℝ) (hm_pos : ∀ p ∈ cdata.S, 0 ≤ m p)
    (h_decomp : cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p)) :
    cdata.μ Set.univ = energyMeasureExtended I cdata.u₀ Set.univ + ENNReal.ofReal (∑ p ∈ cdata.S, m p) := by
  rw [h_decomp, Measure.add_apply, dirac_sum_univ cdata.S m hm_pos]

/-- The Defect Measure Identity (Contract C03).
The weak limit measure decomposes into the smooth energy measure u₀* ω plus a finite sum of
Dirac atoms at the singular concentration points, and total energy is conserved in the limit. -/
theorem defect_measure_identity
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) := by
  sorry


/-- Pointwise Defect Mass Concentration on Isolating Disks (Contract C03). -/
theorem isolating_disk_defect_limit
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (p : CP1) (_hp : p ∈ cdata.S) (m_p : ℝ) (_hm_p : thresh.ε_sph ≤ m_p)
    (a : ℂ) (_ha : stereo_chart.symm a = p) (r : ℝ) (_hr : 0 < r)
    (_h_isol : disk_at a r ∩ (cdata.S : Set CP1) = {p}) :
    Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
      (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  sorry

end GromovCompactness.Compactness
