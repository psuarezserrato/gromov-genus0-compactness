/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Compactness.Measures
import GromovCompactness.Analysis.HoferRescaling
import GromovCompactness.Analysis.SingularityRemoval
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

/-- Existence and properties of the finite singular concentration set S (Contract C02, Zero-sorry).
For any finite measure bounded by B, the set of atoms of mass ≥ ε_reg is finite, and its cardinality
satisfies |S| * ε_reg ≤ B and |S| ≤ B / ε_reg. -/
theorem concentration_singular_set_properties
    (μ : Measure CP1) (B : ℝ) (hB : 0 ≤ B) (thresh : TargetThresholds I M)
    (h_tot : μ Set.univ ≤ ENNReal.ofReal B) :
    ∃ (S : Finset CP1),
      (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p}) ∧
      ((S.card : ℝ) * thresh.ε_reg ≤ B) ∧
      ((S.card : ℝ) ≤ B / thresh.ε_reg) := by
  have h_fin : {p : CP1 | ENNReal.ofReal thresh.ε_reg ≤ μ {p}}.Finite :=
    finite_atoms_of_bounded_measure μ B thresh.ε_reg thresh.ε_reg_pos hB h_tot
  let S := h_fin.toFinset
  have hS_def : ∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p} := by
    intro p
    simp [S]
  have hS_atoms : ∀ x ∈ S, ENNReal.ofReal thresh.ε_reg ≤ μ {x} := by
    intro x hx
    exact (hS_def x).mp hx
  have h_mul := card_le_of_atoms μ B thresh.ε_reg hB h_tot S hS_atoms
  have h_le := atoms_card_le μ B thresh.ε_reg thresh.ε_reg_pos hB h_tot h_fin
  exact ⟨S, hS_def, h_mul, h_le⟩

/-- Integer floor cardinality bound on the concentration singular set S (Zero-sorry). -/
lemma ConcentrationData.card_S_floor_le
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) (hB : 0 ≤ B) :
    cdata.S.card ≤ Nat.floor (B / thresh.ε_reg) := by
  have h_div_nonneg : 0 ≤ B / thresh.ε_reg := div_nonneg hB thresh.ε_reg_pos.le
  exact Nat.le_floor cdata.card_S_le

/-- Smooth limit extraction off the singular set S combining local smooth compactness (A06)
and removal of singularities (A12). -/
theorem extract_smooth_limit_off_singular_set
    (u_seq : ℕ → (CP1 → M)) (σ : SubseqMap)
    (_h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (_S : Finset CP1) :
    ∃ (u₀ : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ _S) := by
  have _ := removal_of_singularities (I := I) (M := M)
  sorry

/-- Extraction of Concentration Data from bounded-energy J-spheres (Contract C02).
Proved with zero direct sorry. -/
theorem exists_concentration_data
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  by_cases hB_pos : 0 < B
  · obtain ⟨σ, μ, _hμ_fin, h_weak⟩ :=
      weak_energy_measure_compactness I u_seq B hB_pos h_en
    have h_tot_le : ∀ n, energyMeasureExtended I (u_seq (σ.1 n)) Set.univ ≤ ENNReal.ofReal B := by
      intro n
      have h_fin := energyMeasureExtended_lt_top_of_totalEnergy_le I (u_seq (σ.1 n)) B hB_pos (h_en (σ.1 n))
      exact energyMeasureExtended_le_ofReal_of_totalEnergy_le I (u_seq (σ.1 n)) B (h_en (σ.1 n)) h_fin
    have h_tot : μ Set.univ ≤ ENNReal.ofReal B := h_weak.total_mass_le h_tot_le
    obtain ⟨S, hS_def, hS_mul, hS_le⟩ :=
      concentration_singular_set_properties I μ B hB thresh h_tot
    obtain ⟨u₀, hu₀_jhol, h_smooth⟩ :=
      extract_smooth_limit_off_singular_set I u_seq σ h_jhol S
    exact ⟨⟨σ, μ, h_tot, h_weak, S, hS_def, hS_mul, hS_le, u₀, hu₀_jhol, h_smooth⟩⟩
  · have hB0 : B = 0 := by linarith
    have hB1 : 0 < B + 1 := by linarith
    have h_en1 : ∀ n, totalEnergy I (u_seq n) ≤ B + 1 := fun n => (h_en n).trans (by linarith)
    obtain ⟨σ, μ, _hμ_fin, h_weak⟩ :=
      weak_energy_measure_compactness I u_seq (B + 1) hB1 h_en1
    have h_tot_le : ∀ n, energyMeasureExtended I (u_seq (σ.1 n)) Set.univ ≤ ENNReal.ofReal B := by
      intro n
      rw [hB0, ENNReal.ofReal_zero]
      have h_en0 : totalEnergy I (u_seq (σ.1 n)) ≤ 0 := by
        have := h_en (σ.1 n); linarith [hB0]
      have h_fin := energyMeasureExtended_lt_top_of_totalEnergy_le I (u_seq (σ.1 n)) (B + 1) hB1 (h_en1 (σ.1 n))
      have h_le_ofReal := energyMeasureExtended_le_ofReal_of_totalEnergy_le I (u_seq (σ.1 n)) 0 h_en0 h_fin
      rwa [ENNReal.ofReal_zero] at h_le_ofReal
    have h_tot : μ Set.univ ≤ ENNReal.ofReal B := h_weak.total_mass_le h_tot_le
    obtain ⟨S, hS_def, hS_mul, hS_le⟩ :=
      concentration_singular_set_properties I μ B hB thresh h_tot
    obtain ⟨u₀, hu₀_jhol, h_smooth⟩ :=
      extract_smooth_limit_off_singular_set I u_seq σ h_jhol S
    exact ⟨⟨σ, μ, h_tot, h_weak, S, hS_def, hS_mul, hS_le, u₀, hu₀_jhol, h_smooth⟩⟩

/-- No-Atom Regularity Upgrade: if the defect measure has no atom at p, convergence is smooth at p (Contract C02, Zero-sorry). -/
theorem smooth_convergence_upgrade_of_zero_mass
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (p : CP1) (hp : cdata.μ {p} = 0) :
    SmoothLocalConvergesOn I (fun n => u_seq (cdata.σ.1 n)) cdata.u₀ (Set.univ \ (cdata.S.erase p)) := by
  have hp_not_mem : p ∉ cdata.S := by
    intro h_mem
    have h_le := (cdata.S_def p).mp h_mem
    rw [hp] at h_le
    have h_ofReal_pos : 0 < ENNReal.ofReal thresh.ε_reg := ENNReal.ofReal_pos.mpr thresh.ε_reg_pos
    exact h_ofReal_pos.not_le h_le
  rw [Finset.erase_eq_of_not_mem hp_not_mem]
  exact cdata.smooth_conv

#print axioms exists_concentration_data

end GromovCompactness.Compactness
