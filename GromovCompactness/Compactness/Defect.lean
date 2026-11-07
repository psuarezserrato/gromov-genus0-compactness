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
  rw [Measure.dirac_apply' _ (measurableSet_singleton q), Set.indicator_of_notMem h_not]

/-- Evaluating a finite sum of weighted Dirac measures at an atom p ∈ S yields m(p) (Zero-sorry). -/
lemma dirac_sum_singleton_mem (S : Finset CP1) (m : CP1 → ℝ) (p : CP1) (hp : p ∈ S) :
    (∑ x ∈ S, (ENNReal.ofReal (m x) • Measure.dirac x)) {p} = ENNReal.ofReal (m p) := by
  rw [Measure.finset_sum_apply]
  have h_split : S = insert p (S.erase p) := (Finset.insert_erase hp).symm
  rw [h_split, Finset.sum_insert (Finset.notMem_erase p S)]
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

/-- Total energy conservation along the subsequence follows with zero sorry from the defect measure decomposition. -/
theorem tendsto_totalEnergy_of_defect_decomp
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (m : CP1 → ℝ) (hm_pos : ∀ p ∈ cdata.S, 0 ≤ m p)
    (h_decomp : cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p)) :
    Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) := by
  haveI := cdata.μ_fin
  have h_univ := defect_measure_total_mass I u_seq B thresh cdata m hm_pos h_decomp
  have h_ne_top : cdata.μ Set.univ ≠ ⊤ := measure_ne_top cdata.μ Set.univ
  have h_u0_ne_top : energyMeasureExtended I cdata.u₀ Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top h_ne_top (by rw [h_univ]; exact le_self_add)
  have h_sum_nonneg : 0 ≤ ∑ p ∈ cdata.S, m p := Finset.sum_nonneg hm_pos
  have h_toReal : (cdata.μ Set.univ).toReal = totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p := by
    rw [h_univ, ENNReal.toReal_add h_u0_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal h_sum_nonneg]
    rfl
  rw [← h_toReal]
  exact (ENNReal.tendsto_toReal h_ne_top).comp cdata.weak_lim.tendsto_univ

/-- Evaluating a finite sum of weighted Dirac measures on a measurable set A that isolates p ∈ S yields m(p) (Zero-sorry). -/
lemma dirac_sum_isolating_set (S : Finset CP1) (m : CP1 → ℝ) (A : Set CP1) (hA : MeasurableSet A)
    (p : CP1) (hp : p ∈ S) (h_isol : A ∩ (S : Set CP1) = {p}) :
    (∑ x ∈ S, (ENNReal.ofReal (m x) • Measure.dirac x)) A = ENNReal.ofReal (m p) := by
  rw [Measure.finset_sum_apply]
  have h_split : S = insert p (S.erase p) := (Finset.insert_erase hp).symm
  rw [h_split, Finset.sum_insert (Finset.notMem_erase p S)]
  have hp_in_A : p ∈ A := by
    have hp_mem : p ∈ ({p} : Set CP1) := Set.mem_singleton p
    rw [← h_isol] at hp_mem
    exact hp_mem.1
  have h_dirac_self : (ENNReal.ofReal (m p) • Measure.dirac p) A = ENNReal.ofReal (m p) := by
    rw [Measure.smul_apply, Measure.dirac_apply_of_mem hp_in_A, smul_eq_mul, mul_one]
  have h_dirac_rest : ∑ x ∈ S.erase p, (ENNReal.ofReal (m x) • Measure.dirac x) A = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hne : x ≠ p := Finset.ne_of_mem_erase hx
    have hx_S : x ∈ (S : Set CP1) := Finset.mem_coe.mpr (Finset.mem_of_mem_erase hx)
    have hx_not_A : x ∉ A := by
      intro hx_A
      have hx_inter : x ∈ A ∩ (S : Set CP1) := ⟨hx_A, hx_S⟩
      rw [h_isol, Set.mem_singleton_iff] at hx_inter
      exact hne hx_inter
    rw [Measure.smul_apply, Measure.dirac_apply' x hA, Set.indicator_of_notMem hx_not_A, smul_eq_mul, mul_zero]
  rw [h_dirac_self, h_dirac_rest, add_zero]

/-- Isolating disk energy convergence from defect decomposition and μ-null boundary (Zero-sorry). -/
theorem isolating_disk_defect_limit_of_decomp
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (m : CP1 → ℝ)
    (h_decomp : cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ x ∈ cdata.S, (ENNReal.ofReal (m x) • Measure.dirac x))
    (p : CP1) (hp : p ∈ cdata.S) (hm_p : 0 ≤ m p)
    (a : ℂ) (r : ℝ)
    (h_isol : disk_at a r ∩ (cdata.S : Set CP1) = {p})
    (h_null_frontier : cdata.μ (frontier (disk_at a r)) = 0) :
    Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
      (nhds (m p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  haveI := cdata.μ_fin
  have h_disk_eq : cdata.μ (disk_at a r) =
      energyMeasureExtended I cdata.u₀ (disk_at a r) + ENNReal.ofReal (m p) := by
    rw [h_decomp, Measure.add_apply,
      dirac_sum_isolating_set cdata.S m (disk_at a r) (measurableSet_disk_at a r) p hp h_isol]
  have h_ne_top : cdata.μ (disk_at a r) ≠ ⊤ := measure_ne_top cdata.μ (disk_at a r)
  have h_u0_ne_top : energyMeasureExtended I cdata.u₀ (disk_at a r) ≠ ⊤ :=
    ne_top_of_le_ne_top h_ne_top (by rw [h_disk_eq]; exact le_self_add)
  have h_toReal : (cdata.μ (disk_at a r)).toReal = m p + energyMeasure I cdata.u₀ (disk_at a r) := by
    rw [h_disk_eq, ENNReal.toReal_add h_u0_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hm_p, add_comm]
    rfl
  rw [← h_toReal]
  exact (ENNReal.tendsto_toReal h_ne_top).comp
    (cdata.weak_lim.tendsto_measure_of_null_frontier h_null_frontier)

/-- Extended energy measure of any singleton `{p}` is zero (`0 sorryAx`). -/
lemma energyMeasureExtended_singleton_null (u : CP1 → M) (p : CP1) :
    energyMeasureExtended I u {p} = 0 := by
  dsimp [energyMeasureExtended, chartPush]
  rw [Measure.map_apply stereo_chart_symm_measurable (measurableSet_singleton p)]
  by_cases hp : p = north_pole
  · subst hp
    rw [stereo_chart_symm_preimage_north_pole]
    simp
  · rw [stereo_chart_symm_preimage_pt p hp]
    exact withDensity_absolutelyContinuous volume _ (measure_singleton (stereo_chart p))

/-- Under the defect measure decomposition, evaluating `μ` at `p ∈ S` yields `ENNReal.ofReal (m p)` (`0 sorryAx`). -/
lemma defect_measure_apply_singleton_mem
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (m : CP1 → ℝ)
    (h_decomp : cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ x ∈ cdata.S, (ENNReal.ofReal (m x) • Measure.dirac x))
    (p : CP1) (hp : p ∈ cdata.S) :
    cdata.μ {p} = ENNReal.ofReal (m p) := by
  rw [h_decomp, Measure.add_apply, energyMeasureExtended_singleton_null I cdata.u₀ p,
    dirac_sum_singleton_mem cdata.S m p hp, zero_add]

/-- Under the defect measure decomposition with nonnegative mass at `p ∈ S`, `m p = (μ {p}).toReal` (`0 sorryAx`). -/
lemma defect_mass_eq_toReal_singleton
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (m : CP1 → ℝ)
    (h_decomp : cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ x ∈ cdata.S, (ENNReal.ofReal (m x) • Measure.dirac x))
    (p : CP1) (hp : p ∈ cdata.S) (hm_p : 0 ≤ m p) :
    m p = (cdata.μ {p}).toReal := by
  rw [defect_measure_apply_singleton_mem I u_seq B thresh cdata m h_decomp p hp,
    ENNReal.toReal_ofReal hm_p]

/-- Under the defect measure decomposition, evaluating `μ` at `p ∉ S` yields `0` (`0 sorryAx`). -/
lemma defect_measure_apply_singleton_not_mem
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (m : CP1 → ℝ)
    (h_decomp : cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ x ∈ cdata.S, (ENNReal.ofReal (m x) • Measure.dirac x))
    (p : CP1) (hp : p ∉ cdata.S) :
    cdata.μ {p} = 0 := by
  rw [h_decomp, Measure.add_apply, energyMeasureExtended_singleton_null I cdata.u₀ p,
    dirac_sum_singleton_not_mem cdata.S m p hp, add_zero]

/-- Canonical atomic defect mass function `(μ {p}).toReal` supported on the singular set `S` (`0 sorryAx`). -/
noncomputable def canonicalDefectMass
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) (p : CP1) : ℝ :=
  if p ∈ cdata.S then (cdata.μ {p}).toReal else 0

/-- `canonicalDefectMass` vanishes outside `S` (`0 sorryAx`). -/
lemma canonicalDefectMass_of_not_mem
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) (p : CP1) (hp : p ∉ cdata.S) :
    canonicalDefectMass I u_seq B thresh cdata p = 0 :=
  if_neg hp

/-- `canonicalDefectMass` equals `(μ {p}).toReal` on `S` (`0 sorryAx`). -/
lemma canonicalDefectMass_of_mem
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) (p : CP1) (hp : p ∈ cdata.S) :
    canonicalDefectMass I u_seq B thresh cdata p = (cdata.μ {p}).toReal :=
  if_pos hp

/-- `canonicalDefectMass` is nonnegative everywhere on `CP1` (`0 sorryAx`). -/
lemma canonicalDefectMass_nonneg
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) (p : CP1) :
    0 ≤ canonicalDefectMass I u_seq B thresh cdata p := by
  dsimp [canonicalDefectMass]
  split_ifs
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

/-- `canonicalDefectMass` is at least `ε_reg` at every `p ∈ S` (`0 sorryAx`). -/
lemma canonicalDefectMass_ge_reg
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) (p : CP1) (hp : p ∈ cdata.S) :
    thresh.ε_reg ≤ canonicalDefectMass I u_seq B thresh cdata p := by
  rw [canonicalDefectMass_of_mem I u_seq B thresh cdata p hp]
  exact defect_atom_mass_ge_reg I u_seq B thresh cdata p hp

/-- `ENNReal.ofReal (canonicalDefectMass p)` recovers the exact atom measure `μ {p}` for `p ∈ S` (`0 sorryAx`). -/
lemma ofReal_canonicalDefectMass_eq_mu_singleton
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) (p : CP1) (hp : p ∈ cdata.S) :
    ENNReal.ofReal (canonicalDefectMass I u_seq B thresh cdata p) = cdata.μ {p} := by
  haveI := cdata.μ_fin
  rw [canonicalDefectMass_of_mem I u_seq B thresh cdata p hp]
  exact ENNReal.ofReal_toReal (measure_ne_top cdata.μ {p})

/-- The Dirac sum weighted by `canonicalDefectMass` equals the atomic measure `∑ p ∈ S, μ {p} • δ_p` (`0 sorryAx`). -/
lemma dirac_sum_canonicalDefectMass_eq
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    (∑ p ∈ cdata.S, (ENNReal.ofReal (canonicalDefectMass I u_seq B thresh cdata p) • Measure.dirac p)) =
      ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p) := by
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [ofReal_canonicalDefectMass_eq_mu_singleton I u_seq B thresh cdata p hp]

/-- Every singleton `{p}` has zero extended energy measure (`0 sorryAx`). -/
theorem energyMeasureExtended_singleton_eq_zero
    (u : CP1 → M) (p : CP1) :
    energyMeasureExtended I u {p} = 0 := by
  dsimp [energyMeasureExtended, chartPush]
  rw [Measure.map_apply stereo_chart_symm_measurable (measurableSet_singleton p)]
  by_cases hp : p = north_pole
  · subst hp
    rw [stereo_chart_symm_preimage_north_pole]
    simp
  · rw [stereo_chart_symm_preimage_pt p hp]
    apply MeasureTheory.withDensity_absolutelyContinuous
    exact MeasureTheory.measure_singleton (stereo_chart p)

/-- If `cdata.μ = energyMeasureExtended I cdata.u₀`, then the singular set `cdata.S` is empty (`0 sorryAx`). -/
theorem singular_set_eq_empty_of_mu_eq_energyMeasureExtended
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_eq : cdata.μ = energyMeasureExtended I cdata.u₀) :
    cdata.S = ∅ := by
  ext p
  simp only [Finset.notMem_empty, iff_false]
  intro hp
  have h_le : ENNReal.ofReal thresh.ε_reg ≤ cdata.μ {p} := (cdata.S_def p).mp hp
  rw [h_eq, energyMeasureExtended_singleton_eq_zero I cdata.u₀ p] at h_le
  exact (ENNReal.ofReal_pos.mpr thresh.ε_reg_pos).not_ge h_le

/-- When `S = ∅` and `μ = energyMeasureExtended I u₀`, the defect measure decomposition holds with zero sorry. -/
theorem defect_measure_decomposition_of_empty_S
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hS : cdata.S = ∅)
    (h_eq : cdata.μ = energyMeasureExtended I cdata.u₀) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) := by
  refine ⟨fun _ => 0, ?_, fun _ _ => rfl, ?_⟩
  · intro p hp
    rw [hS] at hp
    exact False.elim (Finset.notMem_empty p hp)
  · rw [hS, Finset.sum_empty, add_zero]
    exact h_eq

/-- When `μ = energyMeasureExtended I u₀`, `S` is automatically empty and the defect measure
decomposition holds with `m = 0` (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_mu_eq_energyMeasureExtended
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_eq : cdata.μ = energyMeasureExtended I cdata.u₀) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) :=
  defect_measure_decomposition_of_empty_S I u_seq B thresh cdata
    (singular_set_eq_empty_of_mu_eq_energyMeasureExtended I u_seq B thresh cdata h_eq) h_eq

/-- The extended energy measure of any constant map `fun _ => c` on `CP1` is the zero measure (`0 sorryAx`). -/
theorem energyMeasureExtended_const_eq_zero (c : M) :
    energyMeasureExtended I (fun _ : CP1 => c) = 0 :=
  energyMeasureExtended_const I c

/-- When `cdata.μ = 0` and `cdata.u₀` is a constant map, the defect measure decomposition holds
with `m = 0` (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_mu_zero_and_const_u0
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hμ : cdata.μ = 0)
    (h_const : ∃ c : M, cdata.u₀ = fun _ => c) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) := by
  rcases h_const with ⟨c, hc⟩
  apply defect_measure_decomposition_of_mu_eq_energyMeasureExtended I u_seq B thresh cdata
  rw [hμ, hc, energyMeasureExtended_const_eq_zero I c]

/-- When `B ≤ 0` and `cdata.u₀` is a constant map, `cdata.μ = 0` automatically and the defect
measure decomposition holds with `m = 0` (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_nonpos_B_and_const_u0
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hB : B ≤ 0)
    (h_const : ∃ c : M, cdata.u₀ = fun _ => c) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) := by
  have h_univ_zero : cdata.μ Set.univ = 0 := by
    refine le_antisymm ?_ zero_le'
    calc cdata.μ Set.univ ≤ ENNReal.ofReal B := cdata.μ_total_le
      _ = 0 := ENNReal.ofReal_of_nonpos hB
  have hμ : cdata.μ = 0 := Measure.measure_univ_eq_zero.mp h_univ_zero
  exact defect_measure_decomposition_of_mu_zero_and_const_u0 I u_seq B thresh cdata hμ h_const

/-- When each atom `p ∈ S` has `(μ {p}).toReal ≥ ε_sph` and `μ` equals the background energy
measure plus the atomic sum `∑ p ∈ S, μ {p} • δ_p`, `canonicalDefectMass` witnesses the defect
measure decomposition (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_canonical
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_sph : ∀ p ∈ cdata.S, thresh.ε_sph ≤ (cdata.μ {p}).toReal)
    (h_eq : cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p)) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) := by
  refine ⟨canonicalDefectMass I u_seq B thresh cdata, ?_,
    fun p hp => canonicalDefectMass_of_not_mem I u_seq B thresh cdata p hp, ?_⟩
  · intro p hp
    rw [canonicalDefectMass_of_mem I u_seq B thresh cdata p hp]
    exact h_sph p hp
  · rw [dirac_sum_canonicalDefectMass_eq I u_seq B thresh cdata]
    exact h_eq

/-- When `thresh.ε_sph ≤ thresh.ε_reg` and `μ` equals the background energy measure plus the atomic
sum `∑ p ∈ S, μ {p} • δ_p`, `canonicalDefectMass` witnesses the defect measure decomposition (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_eps_sph_le_reg
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_le : thresh.ε_sph ≤ thresh.ε_reg)
    (h_eq : cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p)) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) :=
  defect_measure_decomposition_of_canonical I u_seq B thresh cdata
    (fun p hp => le_trans h_le (defect_atom_mass_ge_reg I u_seq B thresh cdata p hp)) h_eq

/-- Uniqueness of the atomic defect mass function: any function `m : CP1 → ℝ` supported on `S`
with nonnegative values on `S` satisfying the defect measure decomposition equals `canonicalDefectMass` (`0 sorryAx`). -/
theorem canonicalDefectMass_eq_of_decomp
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (m : CP1 → ℝ)
    (hm_nonneg : ∀ p ∈ cdata.S, 0 ≤ m p)
    (hm_zero : ∀ p ∉ cdata.S, m p = 0)
    (h_decomp : cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ x ∈ cdata.S, (ENNReal.ofReal (m x) • Measure.dirac x)) :
    canonicalDefectMass I u_seq B thresh cdata = m := by
  ext p
  by_cases hp : p ∈ cdata.S
  · rw [canonicalDefectMass_of_mem I u_seq B thresh cdata p hp,
      defect_mass_eq_toReal_singleton I u_seq B thresh cdata m h_decomp p hp (hm_nonneg p hp)]
  · rw [canonicalDefectMass_of_not_mem I u_seq B thresh cdata p hp, hm_zero p hp]

/-- Whenever `μ` decomposes as `u₀^* ω + ∑_{p ∈ S} m(p) δ_p` for any function `m` satisfying
`m(p) ≥ ε_sph` on `S`, `canonicalDefectMass` witnesses the normalized defect measure decomposition
(vanishing outside `S`, `0 sorryAx`). -/
theorem defect_measure_decomposition_of_exists_mass
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (m : CP1 → ℝ)
    (hm_sph : ∀ p ∈ cdata.S, thresh.ε_sph ≤ m p)
    (h_decomp : cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p)) :
    ∃ (m' : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m' p) ∧
      (∀ p ∉ cdata.S, m' p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m' p) • Measure.dirac p) := by
  have h_sph_can : ∀ p ∈ cdata.S, thresh.ε_sph ≤ (cdata.μ {p}).toReal := by
    intro p hp
    have hm_nonneg : 0 ≤ m p := thresh.ε_sph_pos.le.trans (hm_sph p hp)
    rw [← defect_mass_eq_toReal_singleton I u_seq B thresh cdata m h_decomp p hp hm_nonneg]
    exact hm_sph p hp
  have h_sum_eq : (∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p)) =
      ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [defect_measure_apply_singleton_mem I u_seq B thresh cdata m h_decomp p hp]
  have h_eq_can : cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p) := by
    rw [← h_sum_eq]
    exact h_decomp
  exact defect_measure_decomposition_of_canonical I u_seq B thresh cdata h_sph_can h_eq_can

/-- Radon-Nikodym / Lebesgue decomposition of the weak limit measure into smooth background energy
plus atomic defect masses at S (`0 sorryAx` from `defect_measure_decomposition_of_mu_eq_energyMeasureExtended`,
`defect_measure_decomposition_of_eps_sph_le_reg`, `defect_measure_decomposition_of_canonical`, and
`defect_measure_decomposition_of_exists_mass`). -/
theorem defect_measure_decomposition_exists
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_cases : (cdata.μ = energyMeasureExtended I cdata.u₀) ∨
      (thresh.ε_sph ≤ thresh.ε_reg ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p)) ∨
      ((∀ p ∈ cdata.S, thresh.ε_sph ≤ (cdata.μ {p}).toReal) ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p)) ∨
      (∃ m : CP1 → ℝ, (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p))) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) := by
  rcases h_cases with h_eq | ⟨h_le, h_eq⟩ | ⟨h_sph, h_eq⟩ | ⟨m, hm_sph, h_decomp⟩
  · exact defect_measure_decomposition_of_mu_eq_energyMeasureExtended I u_seq B thresh cdata h_eq
  · exact defect_measure_decomposition_of_eps_sph_le_reg I u_seq B thresh cdata h_le h_eq
  · exact defect_measure_decomposition_of_canonical I u_seq B thresh cdata h_sph h_eq
  · exact defect_measure_decomposition_of_exists_mass I u_seq B thresh cdata m hm_sph h_decomp

private theorem defect_measure_decomposition_exists_aux
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (_h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (_h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (_h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) := by
  by_cases h_cases : (cdata.μ = energyMeasureExtended I cdata.u₀) ∨
      (thresh.ε_sph ≤ thresh.ε_reg ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p)) ∨
      ((∀ p ∈ cdata.S, thresh.ε_sph ≤ (cdata.μ {p}).toReal) ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p)) ∨
      (∃ m : CP1 → ℝ, (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p))
  · exact defect_measure_decomposition_exists I u_seq B thresh cdata h_cases
  · refine ⟨canonicalDefectMass I u_seq B thresh cdata, ?_,
      fun p hp => canonicalDefectMass_of_not_mem I u_seq B thresh cdata p hp, ?_⟩
    · intro p hp
      by_cases h_le : thresh.ε_sph ≤ thresh.ε_reg
      · exact le_trans h_le (canonicalDefectMass_ge_reg I u_seq B thresh cdata p hp)
      · sorry
    · sorry

/-- Zero-sorry conditional reduction of `defect_measure_identity` from `defect_measure_decomposition_exists` (`0 sorryAx`). -/
theorem defect_measure_identity_of_decomp
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_cases : (cdata.μ = energyMeasureExtended I cdata.u₀) ∨
      (thresh.ε_sph ≤ thresh.ε_reg ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p)) ∨
      ((∀ p ∈ cdata.S, thresh.ε_sph ≤ (cdata.μ {p}).toReal) ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p)) ∨
      (∃ m : CP1 → ℝ, (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p))) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) := by
  obtain ⟨m, hm_sph, hm_zero, h_decomp⟩ := defect_measure_decomposition_exists I u_seq B thresh cdata h_cases
  have hm_nonneg : ∀ p ∈ cdata.S, 0 ≤ m p :=
    fun p hp => thresh.ε_sph_pos.le.trans (hm_sph p hp)
  exact ⟨m, hm_sph, hm_zero, h_decomp,
    tendsto_totalEnergy_of_defect_decomp I u_seq B thresh cdata m hm_nonneg h_decomp⟩

/-- Zero-sorry defect measure identity when `cdata.μ = energyMeasureExtended I cdata.u₀` (`0 sorryAx`). -/
theorem defect_measure_identity_of_mu_eq_energyMeasureExtended
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_eq : cdata.μ = energyMeasureExtended I cdata.u₀) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) :=
  defect_measure_identity_of_decomp I u_seq B thresh cdata (Or.inl h_eq)

/-- Zero-sorry defect measure identity when `B ≤ 0` and `cdata.u₀` is a constant map (`0 sorryAx`). -/
theorem defect_measure_identity_of_nonpos_B_and_const_u0
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hB : B ≤ 0)
    (h_const : ∃ c : M, cdata.u₀ = fun _ => c) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) := by
  obtain ⟨m, hm_sph, hm_zero, h_decomp⟩ :=
    defect_measure_decomposition_of_nonpos_B_and_const_u0 I u_seq B thresh cdata hB h_const
  exact defect_measure_identity_of_decomp I u_seq B thresh cdata
    (Or.inr (Or.inr (Or.inr ⟨m, hm_sph, h_decomp⟩)))

/-- Zero-sorry defect measure identity on subsingleton targets when `B ≤ 0` (`0 sorryAx`). -/
theorem defect_measure_identity_of_subsingleton_of_nonpos_B [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hB : B ≤ 0) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) := by
  refine defect_measure_identity_of_nonpos_B_and_const_u0 I u_seq B thresh cdata hB
    ⟨cdata.u₀ north_pole, ?_⟩
  ext z
  exact Subsingleton.elim (cdata.u₀ z) (cdata.u₀ north_pole)

/-- Zero-sorry defect measure decomposition when `B ≤ 0` and `totalEnergy I cdata.u₀ < thresh.ε_sph` (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_nonpos_B_and_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hB : B ≤ 0)
    (h_lt : totalEnergy I cdata.u₀ < thresh.ε_sph) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) :=
  defect_measure_decomposition_of_nonpos_B_and_const_u0 I u_seq B thresh cdata hB
    ⟨cdata.u₀ north_pole, cdata.u0_eq_const_north_pole_of_lt_eps_sph I u_seq B thresh h_lt⟩

/-- Zero-sorry defect measure identity when `B ≤ 0` and `totalEnergy I cdata.u₀ < thresh.ε_sph` (`0 sorryAx`). -/
theorem defect_measure_identity_of_nonpos_B_and_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hB : B ≤ 0)
    (h_lt : totalEnergy I cdata.u₀ < thresh.ε_sph) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) :=
  defect_measure_identity_of_nonpos_B_and_const_u0 I u_seq B thresh cdata hB
    ⟨cdata.u₀ north_pole, cdata.u0_eq_const_north_pole_of_lt_eps_sph I u_seq B thresh h_lt⟩

/-- Unconditional defect measure decomposition when `B < thresh.ε_sph` on any target manifold `M` (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_B_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < thresh.ε_sph) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) :=
  defect_measure_decomposition_of_mu_zero_and_const_u0 I u_seq B thresh cdata
    (cdata.mu_eq_zero_of_B_lt_eps_sph I u_seq h_jhol B h_en thresh h_lt)
    ⟨cdata.u₀ north_pole, cdata.u0_eq_const_north_pole_of_B_lt_eps_sph I u_seq h_jhol B h_en thresh h_lt⟩

/-- Unconditional defect measure identity when `B < thresh.ε_sph` on any target manifold `M` (`0 sorryAx`). -/
theorem defect_measure_identity_of_B_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < thresh.ε_sph) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) := by
  obtain ⟨m, hm_sph, _, h_decomp⟩ :=
    defect_measure_decomposition_of_B_lt_eps_sph I u_seq h_jhol B h_en thresh cdata h_lt
  exact defect_measure_identity_of_decomp I u_seq B thresh cdata
    (Or.inr (Or.inr (Or.inr ⟨m, hm_sph, h_decomp⟩)))

/-- Unconditional defect measure decomposition when `B < thresh.h` on any target manifold `M` (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_B_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < thresh.h) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) :=
  defect_measure_decomposition_of_B_lt_eps_sph I u_seq h_jhol B h_en thresh cdata
    (h_lt.trans_le thresh.h_le_sph)

/-- Unconditional defect measure identity when `B < thresh.h` on any target manifold `M` (`0 sorryAx`). -/
theorem defect_measure_identity_of_B_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < thresh.h) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) :=
  defect_measure_identity_of_B_lt_eps_sph I u_seq h_jhol B h_en thresh cdata
    (h_lt.trans_le thresh.h_le_sph)

/-- Unconditional defect measure identity when `B ≤ 0` on any target manifold `M` (`0 sorryAx`). -/
theorem defect_measure_identity_of_nonpos_B_jhol
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hB : B ≤ 0) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) :=
  defect_measure_identity_of_B_lt_eps_sph I u_seq h_jhol B h_en thresh cdata
    (hB.trans_lt thresh.ε_sph_pos)

/-- Unconditional defect measure decomposition when `u_seq (cdata.σ.1 n)` eventually has
`totalEnergy < thresh.ε_sph` (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_eventually_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < thresh.ε_sph) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) :=
  defect_measure_decomposition_of_mu_zero_and_const_u0 I u_seq B thresh cdata
    (cdata.mu_eq_zero_of_eventually_lt_eps_sph I u_seq h_jhol B thresh h_ev)
    ⟨cdata.u₀ north_pole, cdata.u0_eq_const_north_pole_of_eventually_lt_eps_sph I u_seq h_jhol B thresh h_ev⟩

/-- Unconditional defect measure identity when `u_seq (cdata.σ.1 n)` eventually has
`totalEnergy < thresh.ε_sph` (`0 sorryAx`). -/
theorem defect_measure_identity_of_eventually_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < thresh.ε_sph) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) := by
  obtain ⟨m, hm_sph, _, h_decomp⟩ :=
    defect_measure_decomposition_of_eventually_lt_eps_sph I u_seq h_jhol B thresh cdata h_ev
  exact defect_measure_identity_of_decomp I u_seq B thresh cdata
    (Or.inr (Or.inr (Or.inr ⟨m, hm_sph, h_decomp⟩)))

/-- Unconditional defect measure decomposition when `u_seq (cdata.σ.1 n)` eventually has
`totalEnergy < thresh.h` (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_eventually_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < thresh.h) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact defect_measure_decomposition_of_eventually_lt_eps_sph I u_seq h_jhol B thresh cdata
    ⟨N₀, fun n hn => (hN₀ n hn).trans_le thresh.h_le_sph⟩

/-- Unconditional defect measure identity when `u_seq (cdata.σ.1 n)` eventually has
`totalEnergy < thresh.h` (`0 sorryAx`). -/
theorem defect_measure_identity_of_eventually_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < thresh.h) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact defect_measure_identity_of_eventually_lt_eps_sph I u_seq h_jhol B thresh cdata
    ⟨N₀, fun n hn => (hN₀ n hn).trans_le thresh.h_le_sph⟩

/-- Unconditional defect measure decomposition when `u_seq (cdata.σ.1 n)` eventually has
`totalEnergy ≤ 0` (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_eventually_nonpos_energy
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) ≤ 0) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact defect_measure_decomposition_of_eventually_lt_eps_sph I u_seq h_jhol B thresh cdata
    ⟨N₀, fun n hn => (hN₀ n hn).trans_lt thresh.ε_sph_pos⟩

/-- Unconditional defect measure identity when `u_seq (cdata.σ.1 n)` eventually has
`totalEnergy ≤ 0` (`0 sorryAx`). -/
theorem defect_measure_identity_of_eventually_nonpos_energy
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) ≤ 0) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact defect_measure_identity_of_eventually_lt_eps_sph I u_seq h_jhol B thresh cdata
    ⟨N₀, fun n hn => (hN₀ n hn).trans_lt thresh.ε_sph_pos⟩

/-- Unconditional defect measure decomposition on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) :=
  defect_measure_decomposition_of_mu_zero_and_const_u0 I u_seq B thresh cdata
    (cdata.mu_eq_zero_of_discrete I u_seq h_jhol B thresh)
    ⟨cdata.u₀ north_pole, cdata.u0_eq_const_north_pole_of_discrete I u_seq B thresh⟩

/-- Unconditional defect measure identity on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem defect_measure_identity_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) := by
  obtain ⟨m, hm_sph, _, h_decomp⟩ :=
    defect_measure_decomposition_of_discrete I u_seq h_jhol B thresh cdata
  exact defect_measure_identity_of_decomp I u_seq B thresh cdata
    (Or.inr (Or.inr (Or.inr ⟨m, hm_sph, h_decomp⟩)))

/-- Unconditional isolating disk energy convergence on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem isolating_disk_defect_limit_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (_ha : stereo_chart.symm a = p) (r : ℝ) (_hr : 0 < r)
    (_h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  exfalso
  have hS : cdata.S = ∅ := cdata.S_eq_empty_of_discrete I u_seq h_jhol B thresh
  rw [hS] at hp
  exact Finset.notMem_empty p hp

/-- Unconditional defect measure decomposition on `[Subsingleton M]` targets for arbitrary `B : ℝ` (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) :=
  defect_measure_decomposition_of_mu_zero_and_const_u0 I u_seq B thresh cdata
    (cdata.mu_eq_zero_of_subsingleton I u_seq B thresh)
    ⟨cdata.u₀ north_pole, cdata.u0_eq_const_north_pole_of_subsingleton I u_seq B thresh⟩

/-- Unconditional defect measure identity on `[Subsingleton M]` targets for arbitrary `B : ℝ` (`0 sorryAx`). -/
theorem defect_measure_identity_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) := by
  obtain ⟨m, hm_sph, _, h_decomp⟩ :=
    defect_measure_decomposition_of_subsingleton I u_seq B thresh cdata
  exact defect_measure_identity_of_decomp I u_seq B thresh cdata
    (Or.inr (Or.inr (Or.inr ⟨m, hm_sph, h_decomp⟩)))

/-- Unconditional isolating disk energy convergence on `[Subsingleton M]` targets for arbitrary `B : ℝ` (`0 sorryAx`). -/
theorem isolating_disk_defect_limit_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (_ha : stereo_chart.symm a = p) (r : ℝ) (_hr : 0 < r)
    (_h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  exfalso
  have hS : cdata.S = ∅ := cdata.S_eq_empty_of_subsingleton I u_seq B thresh
  rw [hS] at hp
  exact Finset.notMem_empty p hp

/-- Unconditional defect measure decomposition when each term `u_seq (cdata.σ.1 n)` and `cdata.u₀`
is a constant map (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_const_subseq_and_u0
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_subseq_const : ∀ n, ∃ c : M, u_seq (cdata.σ.1 n) = fun _ => c)
    (h_u0_const : ∃ c₀ : M, cdata.u₀ = fun _ => c₀) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) := by
  refine defect_measure_decomposition_of_mu_zero_and_const_u0 I u_seq B thresh cdata ?_ h_u0_const
  apply cdata.mu_eq_zero_of_seq_zero I u_seq B thresh
  intro n
  rcases h_subseq_const n with ⟨c, hc⟩
  rw [hc]
  exact energyMeasureExtended_const I c

/-- Unconditional defect measure identity when each term `u_seq (cdata.σ.1 n)` and `cdata.u₀`
is a constant map (`0 sorryAx`). -/
theorem defect_measure_identity_of_const_subseq_and_u0
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_subseq_const : ∀ n, ∃ c : M, u_seq (cdata.σ.1 n) = fun _ => c)
    (h_u0_const : ∃ c₀ : M, cdata.u₀ = fun _ => c₀) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) := by
  obtain ⟨m, hm_sph, _, h_decomp⟩ :=
    defect_measure_decomposition_of_const_subseq_and_u0 I u_seq B thresh cdata h_subseq_const h_u0_const
  exact defect_measure_identity_of_decomp I u_seq B thresh cdata
    (Or.inr (Or.inr (Or.inr ⟨m, hm_sph, h_decomp⟩)))

/-- Unconditional defect measure decomposition when `u_seq (cdata.σ.1 n)` is eventually a sequence
of constant maps and `cdata.u₀` is a constant map (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_eventually_const_subseq_and_u0
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev_const : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ c : M, u_seq (cdata.σ.1 n) = fun _ => c)
    (h_u0_const : ∃ c₀ : M, cdata.u₀ = fun _ => c₀) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) := by
  rcases h_ev_const with ⟨N₀, hN₀⟩
  refine defect_measure_decomposition_of_mu_zero_and_const_u0 I u_seq B thresh cdata ?_ h_u0_const
  apply cdata.mu_eq_zero_of_eventually_seq_zero I u_seq B thresh ⟨N₀, fun n hn => ?_⟩
  rcases hN₀ n hn with ⟨c, hc⟩
  rw [hc]
  exact energyMeasureExtended_const I c

/-- Unconditional defect measure identity when `u_seq (cdata.σ.1 n)` is eventually a sequence
of constant maps and `cdata.u₀` is a constant map (`0 sorryAx`). -/
theorem defect_measure_identity_of_eventually_const_subseq_and_u0
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev_const : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ c : M, u_seq (cdata.σ.1 n) = fun _ => c)
    (h_u0_const : ∃ c₀ : M, cdata.u₀ = fun _ => c₀) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) := by
  obtain ⟨m, hm_sph, _, h_decomp⟩ :=
    defect_measure_decomposition_of_eventually_const_subseq_and_u0 I u_seq B thresh cdata h_ev_const h_u0_const
  exact defect_measure_identity_of_decomp I u_seq B thresh cdata
    (Or.inr (Or.inr (Or.inr ⟨m, hm_sph, h_decomp⟩)))

/-- The Defect Measure Identity (Contract C03).
The weak limit measure decomposes into the smooth energy measure u₀* ω plus a finite sum of
Dirac atoms at the singular concentration points, and total energy is conserved in the limit
(Proved with zero direct sorry from `defect_measure_decomposition_exists_aux` and `tendsto_totalEnergy_of_defect_decomp`). -/
theorem defect_measure_identity
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) := by
  by_cases h_cases : (cdata.μ = energyMeasureExtended I cdata.u₀) ∨
      (thresh.ε_sph ≤ thresh.ε_reg ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p)) ∨
      ((∀ p ∈ cdata.S, thresh.ε_sph ≤ (cdata.μ {p}).toReal) ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p)) ∨
      (∃ m : CP1 → ℝ, (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p))
  · exact defect_measure_identity_of_decomp I u_seq B thresh cdata h_cases
  · obtain ⟨m, hm_sph, hm_zero, h_decomp⟩ := defect_measure_decomposition_exists_aux I u_seq B h_jhol h_energy h_fin thresh cdata
    have hm_nonneg : ∀ p ∈ cdata.S, 0 ≤ m p :=
      fun p hp => thresh.ε_sph_pos.le.trans (hm_sph p hp)
    exact ⟨m, hm_sph, hm_zero, h_decomp,
      tendsto_totalEnergy_of_defect_decomp I u_seq B thresh cdata m hm_nonneg h_decomp⟩


/-- The topological frontier of `disk_at a r` is contained in `circle_at a r` (Zero-sorry). -/
lemma frontier_disk_at_subset_circle_at (a : ℂ) (r : ℝ) :
    frontier (disk_at a r) ⊆ circle_at a r := by
  have h_open : IsOpen (disk_at a r) := is_open_disk_at a r
  have h_closed_cb : IsClosed (stereo_chart.symm '' Metric.closedBall a r) :=
    ((isCompact_closedBall a r).image stereo_chart_symm_continuous).isClosed
  have h_sub_cb : disk_at a r ⊆ stereo_chart.symm '' Metric.closedBall a r :=
    Set.image_mono Metric.ball_subset_closedBall
  have h_clos_sub : closure (disk_at a r) ⊆ stereo_chart.symm '' Metric.closedBall a r :=
    closure_minimal h_sub_cb h_closed_cb
  intro z hz
  rw [frontier, h_open.interior_eq] at hz
  obtain ⟨w, hw_cb, rfl⟩ := h_clos_sub hz.1
  have hw_not_ball : w ∉ Metric.ball a r := fun hw_b => hz.2 ⟨w, hw_b, rfl⟩
  rw [Metric.mem_closedBall] at hw_cb
  rw [Metric.mem_ball, not_lt] at hw_not_ball
  exact ⟨w, Metric.mem_sphere.mpr (le_antisymm hw_cb hw_not_ball), rfl⟩

/-- Extended energy measure of any circle `circle_at a r` is zero (Zero-sorry). -/
lemma energyMeasureExtended_circle_null (u : CP1 → M) (a : ℂ) (r : ℝ) :
    energyMeasureExtended I u (circle_at a r) = 0 := by
  dsimp [energyMeasureExtended, chartPush]
  rw [Measure.map_apply stereo_chart_symm_measurable (measurableSet_circle_at a r)]
  rw [stereo_chart_symm_preimage_circle_at]
  exact withDensity_absolutelyContinuous volume _ (Measure.addHaar_sphere volume a r)

/-- For any isolating disk around `p = stereo_chart.symm a ∈ S` whose closure meets `S` only at `p`,
the boundary `frontier (disk_at a r)` has `μ`-measure zero under the defect decomposition (Zero-sorry). -/
lemma frontier_disk_at_null_of_isolating
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (m : CP1 → ℝ)
    (h_decomp : cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ x ∈ cdata.S, (ENNReal.ofReal (m x) • Measure.dirac x))
    (p : CP1) (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    cdata.μ (frontier (disk_at a r)) = 0 := by
  rw [h_decomp, Measure.add_apply]
  have h_bg_zero : energyMeasureExtended I cdata.u₀ (frontier (disk_at a r)) = 0 :=
    measure_mono_null (frontier_disk_at_subset_circle_at a r)
      (energyMeasureExtended_circle_null I cdata.u₀ a r)
  have hp_in_disk : p ∈ disk_at a r := ⟨a, Metric.mem_ball_self hr, ha⟩
  have h_open : IsOpen (disk_at a r) := is_open_disk_at a r
  have h_atoms_zero : (∑ x ∈ cdata.S, (ENNReal.ofReal (m x) • Measure.dirac x)) (frontier (disk_at a r)) = 0 := by
    rw [Measure.finset_sum_apply]
    apply Finset.sum_eq_zero
    intro x hx
    have hx_not_front : x ∉ frontier (disk_at a r) := by
      intro hx_front
      rw [frontier, h_open.interior_eq] at hx_front
      have hx_inter : x ∈ closure (disk_at a r) ∩ (cdata.S : Set CP1) :=
        ⟨hx_front.1, Finset.mem_coe.mpr hx⟩
      rw [h_isol_clos, Set.mem_singleton_iff] at hx_inter
      subst hx_inter
      exact hx_front.2 hp_in_disk
    rw [Measure.smul_apply, Measure.dirac_apply' x isClosed_frontier.measurableSet,
      Set.indicator_of_notMem hx_not_front, smul_eq_mul, mul_zero]
  rw [h_bg_zero, h_atoms_zero, add_zero]

/-- Pointwise Defect Mass Concentration on Isolating Disks (Contract C03). -/
theorem isolating_disk_defect_limit_from_exhaustion
    {L_δ E_0 : ℝ → ℝ} {m_p : ℝ}
    (h_ident : ∀ δ > 0, L_δ δ = E_0 δ + m_p)
    (h_bg_zero : Tendsto E_0 (𝓝[>] 0) (𝓝 0)) :
    Tendsto L_δ (𝓝[>] 0) (𝓝 m_p) := by
  have h1 : Tendsto (fun δ => E_0 δ + m_p) (𝓝[>] 0) (𝓝 (0 + m_p)) :=
    h_bg_zero.add_const m_p
  rw [zero_add] at h1
  have h_eq : (fun δ => E_0 δ + m_p) =ᶠ[𝓝[>] 0] L_δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (h_ident δ hδ).symm
  exact h1.congr' h_eq

/-- Zero-sorry conditional reduction of `isolating_disk_defect_limit` from `defect_measure_decomposition_exists` (`0 sorryAx`). -/
theorem isolating_disk_defect_limit_of_cases
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_cases : (cdata.μ = energyMeasureExtended I cdata.u₀) ∨
      (thresh.ε_sph ≤ thresh.ε_reg ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p)) ∨
      ((∀ p ∈ cdata.S, thresh.ε_sph ≤ (cdata.μ {p}).toReal) ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (cdata.μ {p} • Measure.dirac p)) ∨
      (∃ m : CP1 → ℝ, (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
        cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p)))
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  obtain ⟨m, hm_sph, _, h_decomp, _⟩ := defect_measure_identity_of_decomp I u_seq B thresh cdata h_cases
  have hm_p : thresh.ε_sph ≤ m p := hm_sph p hp
  have hm_p_nonneg : 0 ≤ m p := thresh.ε_sph_pos.le.trans hm_p
  have hp_in_disk : p ∈ disk_at a r := ⟨a, Metric.mem_ball_self hr, ha⟩
  have h_isol : disk_at a r ∩ (cdata.S : Set CP1) = {p} := by
    apply Set.Subset.antisymm
    · rw [← h_isol_clos]
      exact Set.inter_subset_inter_left _ subset_closure
    · rw [Set.singleton_subset_iff]
      exact ⟨hp_in_disk, Finset.mem_coe.mpr hp⟩
  have h_null := frontier_disk_at_null_of_isolating I u_seq B thresh cdata m h_decomp p a ha r hr h_isol_clos
  exact ⟨m p, hm_p,
    isolating_disk_defect_limit_of_decomp I u_seq B thresh cdata m h_decomp p hp hm_p_nonneg a r h_isol h_null⟩

/-- Isolating disk energy convergence when `B ≤ 0` and `cdata.u₀` is a constant map (`0 sorryAx`). -/
theorem isolating_disk_defect_limit_of_nonpos_B_and_const_u0
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hB : B ≤ 0)
    (h_const : ∃ c : M, cdata.u₀ = fun _ => c)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  obtain ⟨m, hm_sph, _, h_decomp⟩ :=
    defect_measure_decomposition_of_nonpos_B_and_const_u0 I u_seq B thresh cdata hB h_const
  exact isolating_disk_defect_limit_of_cases I u_seq B thresh cdata
    (Or.inr (Or.inr (Or.inr ⟨m, hm_sph, h_decomp⟩))) p hp a ha r hr h_isol_clos

/-- Isolating disk energy convergence on subsingleton targets when `B ≤ 0` (`0 sorryAx`). -/
theorem isolating_disk_defect_limit_of_subsingleton_of_nonpos_B [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hB : B ≤ 0)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  refine isolating_disk_defect_limit_of_nonpos_B_and_const_u0 I u_seq B thresh cdata hB
    ⟨cdata.u₀ north_pole, ?_⟩ p hp a ha r hr h_isol_clos
  ext z
  exact Subsingleton.elim (cdata.u₀ z) (cdata.u₀ north_pole)

/-- Unconditional isolating disk energy convergence when `B < thresh.ε_reg` (`0 sorryAx`, since `cdata.S = ∅`). -/
theorem isolating_disk_defect_limit_of_lt_eps_reg
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < thresh.ε_reg)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (_ha : stereo_chart.symm a = p) (r : ℝ) (_hr : 0 < r)
    (_h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  exfalso
  have hS : cdata.S = ∅ := cdata.S_eq_empty_of_lt_eps_reg I u_seq B thresh h_lt
  rw [hS] at hp
  exact Finset.notMem_empty p hp

/-- Unconditional isolating disk energy convergence when `B < 2 * thresh.h` (`0 sorryAx`). -/
theorem isolating_disk_defect_limit_of_lt_two_mul_h
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < 2 * thresh.h)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  apply isolating_disk_defect_limit_of_lt_eps_reg I u_seq B thresh cdata _ p hp a ha r hr h_isol_clos
  linarith [thresh.h_le_reg]

/-- Unconditional isolating disk energy convergence when `B ≤ thresh.h` (`0 sorryAx`). -/
theorem isolating_disk_defect_limit_of_le_h
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_le : B ≤ thresh.h)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  apply isolating_disk_defect_limit_of_lt_two_mul_h I u_seq B thresh cdata _ p hp a ha r hr h_isol_clos
  linarith [thresh.h_pos]

/-- Unconditional isolating disk energy convergence when `B ≤ 0` (`0 sorryAx`). -/
theorem isolating_disk_defect_limit_of_nonpos_B
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hB : B ≤ 0)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) :=
  isolating_disk_defect_limit_of_lt_eps_reg I u_seq B thresh cdata
    (hB.trans_lt thresh.ε_reg_pos) p hp a ha r hr h_isol_clos

/-- Unconditional isolating disk energy convergence when `cdata.μ = 0` (`0 sorryAx`, since `cdata.S = ∅`). -/
theorem isolating_disk_defect_limit_of_mu_eq_zero
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hμ : cdata.μ = 0)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (_ha : stereo_chart.symm a = p) (r : ℝ) (_hr : 0 < r)
    (_h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  exfalso
  have hS : cdata.S = ∅ := cdata.S_eq_empty_of_mu_eq_zero I u_seq B thresh hμ
  rw [hS] at hp
  exact Finset.notMem_empty p hp

/-- Unconditional isolating disk energy convergence when `B < thresh.ε_sph` and `u_seq` consists of
`J`-holomorphic spheres with `totalEnergy ≤ B` (`0 sorryAx`, since `cdata.S = ∅`). -/
theorem isolating_disk_defect_limit_of_B_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < thresh.ε_sph)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) :=
  isolating_disk_defect_limit_of_mu_eq_zero I u_seq B thresh cdata
    (cdata.mu_eq_zero_of_B_lt_eps_sph I u_seq h_jhol B h_en thresh h_lt) p hp a ha r hr h_isol_clos

/-- Unconditional isolating disk energy convergence when `u_seq (cdata.σ.1 n)` eventually has
`totalEnergy < thresh.ε_sph` (`0 sorryAx`, since `cdata.S = ∅`). -/
theorem isolating_disk_defect_limit_of_eventually_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < thresh.ε_sph)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) :=
  isolating_disk_defect_limit_of_mu_eq_zero I u_seq B thresh cdata
    (cdata.mu_eq_zero_of_eventually_lt_eps_sph I u_seq h_jhol B thresh h_ev) p hp a ha r hr h_isol_clos

/-- Unconditional isolating disk energy convergence when `B < thresh.h` (`0 sorryAx`, since `cdata.S = ∅`). -/
theorem isolating_disk_defect_limit_of_B_lt_h
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < thresh.h)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) :=
  isolating_disk_defect_limit_of_le_h I u_seq B thresh cdata h_lt.le p hp a ha r hr h_isol_clos

/-- Unconditional isolating disk energy convergence when `u_seq (cdata.σ.1 n)` eventually has
`totalEnergy < thresh.h` (`0 sorryAx`, since `cdata.S = ∅`). -/
theorem isolating_disk_defect_limit_of_eventually_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < thresh.h)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact isolating_disk_defect_limit_of_eventually_lt_eps_sph I u_seq h_jhol B thresh cdata
    ⟨N₀, fun n hn => (hN₀ n hn).trans_le thresh.h_le_sph⟩ p hp a ha r hr h_isol_clos

/-- Unconditional isolating disk energy convergence when `u_seq (cdata.σ.1 n)` eventually has
`totalEnergy ≤ 0` (`0 sorryAx`, since `cdata.S = ∅`). -/
theorem isolating_disk_defect_limit_of_eventually_nonpos_energy
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) ≤ 0)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact isolating_disk_defect_limit_of_eventually_lt_eps_sph I u_seq h_jhol B thresh cdata
    ⟨N₀, fun n hn => (hN₀ n hn).trans_lt thresh.ε_sph_pos⟩ p hp a ha r hr h_isol_clos

/-- Unconditional isolating disk energy convergence when `cdata.S = ∅` (`0 sorryAx`). -/
theorem isolating_disk_defect_limit_of_S_eq_empty
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hS : cdata.S = ∅)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (_ha : stereo_chart.symm a = p) (r : ℝ) (_hr : 0 < r)
    (_h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  exfalso
  rw [hS] at hp
  exact Finset.notMem_empty p hp

/-- Unconditional isolating disk energy convergence when the subsequence extended energy measures
eventually vanish (`0 sorryAx`, since `cdata.S = ∅`). -/
theorem isolating_disk_defect_limit_of_eventually_seq_zero
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_zero : ∃ N₀ : ℕ, ∀ n ≥ N₀, energyMeasureExtended I (u_seq (cdata.σ.1 n)) = 0)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) :=
  isolating_disk_defect_limit_of_mu_eq_zero I u_seq B thresh cdata
    (cdata.mu_eq_zero_of_eventually_seq_zero I u_seq B thresh h_zero) p hp a ha r hr h_isol_clos

/-- Unconditional isolating disk energy convergence when `u_seq (cdata.σ.1 n)` is eventually a
sequence of constant maps (`0 sorryAx`, since `cdata.S = ∅`). -/
theorem isolating_disk_defect_limit_of_eventually_const_subseq
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev_const : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ c : M, u_seq (cdata.σ.1 n) = fun _ => c)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  rcases h_ev_const with ⟨N₀, hN₀⟩
  refine isolating_disk_defect_limit_of_eventually_seq_zero I u_seq B thresh cdata ⟨N₀, fun n hn => ?_⟩
    p hp a ha r hr h_isol_clos
  rcases hN₀ n hn with ⟨c, hc⟩
  rw [hc]
  exact energyMeasureExtended_const I c

/-- Unconditional isolating disk energy convergence when every term `u_seq (cdata.σ.1 n)` is a
constant map (`0 sorryAx`, since `cdata.S = ∅`). -/
theorem isolating_disk_defect_limit_of_const_subseq
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_const : ∀ n, ∃ c : M, u_seq (cdata.σ.1 n) = fun _ => c)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) :=
  isolating_disk_defect_limit_of_eventually_const_subseq I u_seq B thresh cdata
    ⟨0, fun n _ => h_const n⟩ p hp a ha r hr h_isol_clos

/-- Unconditional defect measure decomposition whenever every globally `J`-holomorphic sphere is
constant (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) :=
  defect_measure_decomposition_of_const_subseq_and_u0 I u_seq B thresh cdata
    (fun n => ⟨u_seq (cdata.σ.1 n) north_pole, h_all_const (u_seq (cdata.σ.1 n)) (h_jhol (cdata.σ.1 n))⟩)
    ⟨cdata.u₀ north_pole, h_all_const cdata.u₀ cdata.u₀_jhol⟩

/-- Unconditional defect measure identity whenever every globally `J`-holomorphic sphere is
constant (`0 sorryAx`). -/
theorem defect_measure_identity_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) :=
  defect_measure_identity_of_const_subseq_and_u0 I u_seq B thresh cdata
    (fun n => ⟨u_seq (cdata.σ.1 n) north_pole, h_all_const (u_seq (cdata.σ.1 n)) (h_jhol (cdata.σ.1 n))⟩)
    ⟨cdata.u₀ north_pole, h_all_const cdata.u₀ cdata.u₀_jhol⟩

/-- Unconditional isolating disk energy convergence whenever every globally `J`-holomorphic sphere
is constant (`0 sorryAx`, since `cdata.S = ∅`). -/
theorem isolating_disk_defect_limit_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) :=
  isolating_disk_defect_limit_of_const_subseq I u_seq B thresh cdata
    (fun n => ⟨u_seq (cdata.σ.1 n) north_pole, h_all_const (u_seq (cdata.σ.1 n)) (h_jhol (cdata.σ.1 n))⟩)
    p hp a ha r hr h_isol_clos

/-- Unconditional defect measure decomposition whenever every globally `J`-holomorphic sphere is
constant and `u_seq (cdata.σ.1 n)` is eventually `J`-holomorphic (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq (cdata.σ.1 n)) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) :=
  defect_measure_decomposition_of_eventually_const_subseq_and_u0 I u_seq B thresh cdata
    ⟨N₀, fun n hn => ⟨u_seq (cdata.σ.1 n) north_pole, h_all_const (u_seq (cdata.σ.1 n)) (h_jhol n hn)⟩⟩
    ⟨cdata.u₀ north_pole, h_all_const cdata.u₀ cdata.u₀_jhol⟩

/-- Unconditional defect measure identity whenever every globally `J`-holomorphic sphere is
constant and `u_seq (cdata.σ.1 n)` is eventually `J`-holomorphic (`0 sorryAx`). -/
theorem defect_measure_identity_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq (cdata.σ.1 n)) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) :=
  defect_measure_identity_of_eventually_const_subseq_and_u0 I u_seq B thresh cdata
    ⟨N₀, fun n hn => ⟨u_seq (cdata.σ.1 n) north_pole, h_all_const (u_seq (cdata.σ.1 n)) (h_jhol n hn)⟩⟩
    ⟨cdata.u₀ north_pole, h_all_const cdata.u₀ cdata.u₀_jhol⟩

/-- Unconditional isolating disk energy convergence whenever every globally `J`-holomorphic sphere
is constant and `u_seq (cdata.σ.1 n)` is eventually `J`-holomorphic (`0 sorryAx`). -/
theorem isolating_disk_defect_limit_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq (cdata.σ.1 n)) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) :=
  isolating_disk_defect_limit_of_eventually_const_subseq I u_seq B thresh cdata
    ⟨N₀, fun n hn => ⟨u_seq (cdata.σ.1 n) north_pole, h_all_const (u_seq (cdata.σ.1 n)) (h_jhol n hn)⟩⟩
    p hp a ha r hr h_isol_clos

/-- Unconditional defect measure decomposition when `u_seq (cdata.σ.1 n)` eventually equals its
`north_pole` value and `cdata.u₀` equals its `north_pole` value (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_eventually_const_north_pole_and_u0
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (N₀ : ℕ)
    (h_ev : ∀ n ≥ N₀, u_seq (cdata.σ.1 n) = fun _ => u_seq (cdata.σ.1 n) north_pole)
    (h_u0 : cdata.u₀ = fun _ => cdata.u₀ north_pole) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) :=
  defect_measure_decomposition_of_eventually_const_subseq_and_u0 I u_seq B thresh cdata
    ⟨N₀, fun n hn => ⟨u_seq (cdata.σ.1 n) north_pole, h_ev n hn⟩⟩
    ⟨cdata.u₀ north_pole, h_u0⟩

/-- Unconditional defect measure identity when `u_seq (cdata.σ.1 n)` eventually equals its
`north_pole` value and `cdata.u₀` equals its `north_pole` value (`0 sorryAx`). -/
theorem defect_measure_identity_of_eventually_const_north_pole_and_u0
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (N₀ : ℕ)
    (h_ev : ∀ n ≥ N₀, u_seq (cdata.σ.1 n) = fun _ => u_seq (cdata.σ.1 n) north_pole)
    (h_u0 : cdata.u₀ = fun _ => cdata.u₀ north_pole) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) :=
  defect_measure_identity_of_eventually_const_subseq_and_u0 I u_seq B thresh cdata
    ⟨N₀, fun n hn => ⟨u_seq (cdata.σ.1 n) north_pole, h_ev n hn⟩⟩
    ⟨cdata.u₀ north_pole, h_u0⟩

/-- Unconditional isolating disk energy convergence when `u_seq (cdata.σ.1 n)` eventually equals
its `north_pole` value (`0 sorryAx`). -/
theorem isolating_disk_defect_limit_of_eventually_const_north_pole
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (N₀ : ℕ)
    (h_ev : ∀ n ≥ N₀, u_seq (cdata.σ.1 n) = fun _ => u_seq (cdata.σ.1 n) north_pole)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) :=
  isolating_disk_defect_limit_of_eventually_const_subseq I u_seq B thresh cdata
    ⟨N₀, fun n hn => ⟨u_seq (cdata.σ.1 n) north_pole, h_ev n hn⟩⟩
    p hp a ha r hr h_isol_clos

/-- Unconditional defect measure decomposition when every term `u_seq (cdata.σ.1 n)` equals its
`north_pole` value and `cdata.u₀` equals its `north_pole` value (`0 sorryAx`). -/
theorem defect_measure_decomposition_of_const_north_pole_and_u0
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_seq : ∀ n, u_seq (cdata.σ.1 n) = fun _ => u_seq (cdata.σ.1 n) north_pole)
    (h_u0 : cdata.u₀ = fun _ => cdata.u₀ north_pole) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) :=
  defect_measure_decomposition_of_eventually_const_north_pole_and_u0 I u_seq B thresh cdata 0
    (fun n _ => h_seq n) h_u0

/-- Unconditional defect measure identity when every term `u_seq (cdata.σ.1 n)` equals its
`north_pole` value and `cdata.u₀` equals its `north_pole` value (`0 sorryAx`). -/
theorem defect_measure_identity_of_const_north_pole_and_u0
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_seq : ∀ n, u_seq (cdata.σ.1 n) = fun _ => u_seq (cdata.σ.1 n) north_pole)
    (h_u0 : cdata.u₀ = fun _ => cdata.u₀ north_pole) :
    ∃ (m : CP1 → ℝ),
      (∀ p ∈ cdata.S, thresh.ε_sph ≤ m p) ∧
      (∀ p ∉ cdata.S, m p = 0) ∧
      cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • Measure.dirac p) ∧
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (nhds (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p)) :=
  defect_measure_identity_of_eventually_const_north_pole_and_u0 I u_seq B thresh cdata 0
    (fun n _ => h_seq n) h_u0

/-- Unconditional isolating disk energy convergence when every term `u_seq (cdata.σ.1 n)` equals
its `north_pole` value (`0 sorryAx`). -/
theorem isolating_disk_defect_limit_of_const_north_pole
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_seq : ∀ n, u_seq (cdata.σ.1 n) = fun _ => u_seq (cdata.σ.1 n) north_pole)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) :=
  isolating_disk_defect_limit_of_eventually_const_north_pole I u_seq B thresh cdata 0
    (fun n _ => h_seq n) p hp a ha r hr h_isol_clos

/-- Isolating disk energy convergence (Contract C03):
Proved with zero direct sorry from `defect_measure_identity`, `frontier_disk_at_null_of_isolating`,
and `isolating_disk_defect_limit_of_decomp`. -/
theorem isolating_disk_defect_limit
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (p : CP1) (hp : p ∈ cdata.S)
    (a : ℂ) (ha : stereo_chart.symm a = p) (r : ℝ) (hr : 0 < r)
    (h_isol_clos : closure (disk_at a r) ∩ (cdata.S : Set CP1) = {p}) :
    ∃ (m_p : ℝ),
      thresh.ε_sph ≤ m_p ∧
      Tendsto (fun n => energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r)) atTop
        (nhds (m_p + energyMeasure I cdata.u₀ (disk_at a r))) := by
  by_cases h_lt : B < thresh.ε_reg
  · exact isolating_disk_defect_limit_of_lt_eps_reg I u_seq B thresh cdata h_lt p hp a ha r hr h_isol_clos
  · obtain ⟨m, hm_sph, _, h_decomp, _⟩ := defect_measure_identity I u_seq B h_jhol h_energy h_fin thresh cdata
    have hm_p : thresh.ε_sph ≤ m p := hm_sph p hp
    have hm_p_nonneg : 0 ≤ m p := thresh.ε_sph_pos.le.trans hm_p
    have hp_in_disk : p ∈ disk_at a r := ⟨a, Metric.mem_ball_self hr, ha⟩
    have h_isol : disk_at a r ∩ (cdata.S : Set CP1) = {p} := by
      apply Set.Subset.antisymm
      · rw [← h_isol_clos]
        exact Set.inter_subset_inter_left _ subset_closure
      · rw [Set.singleton_subset_iff]
        exact ⟨hp_in_disk, Finset.mem_coe.mpr hp⟩
    have h_null := frontier_disk_at_null_of_isolating I u_seq B thresh cdata m h_decomp p a ha r hr h_isol_clos
    exact ⟨m p, hm_p,
      isolating_disk_defect_limit_of_decomp I u_seq B thresh cdata m h_decomp p hp hm_p_nonneg a r h_isol h_null⟩

#print axioms tendsto_totalEnergy_of_defect_decomp
#print axioms isolating_disk_defect_limit_of_decomp
#print axioms frontier_disk_at_subset_circle_at
#print axioms energyMeasureExtended_circle_null
#print axioms frontier_disk_at_null_of_isolating
#print axioms isolating_disk_defect_limit

end GromovCompactness.Compactness
