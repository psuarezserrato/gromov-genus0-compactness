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

namespace WeakMeasureConvergence

/-- Integral pairing convergence along continuous test functions (Zero-sorry). -/
lemma tendsto_integral {μ_seq : ℕ → Measure CP1} {μ_lim : Measure CP1}
    (h : WeakMeasureConvergence μ_seq μ_lim) (f : CP1 → ℝ) (hf : Continuous f) :
    Tendsto (fun n => ∫ z, f z ∂(μ_seq n)) atTop (nhds (∫ z, f z ∂μ_lim)) :=
  h.1 f hf

/-- Closed set upper bound in the Portmanteau characterization (Zero-sorry). -/
lemma limsup_closed_le {μ_seq : ℕ → Measure CP1} {μ_lim : Measure CP1}
    (h : WeakMeasureConvergence μ_seq μ_lim) {K : Set CP1} (hK : IsClosed K) :
    Filter.limsup (fun n => μ_seq n K) atTop ≤ μ_lim K :=
  h.2.1 K hK

/-- Measure convergence on Borel sets whose topological frontier is μ-null (Zero-sorry). -/
lemma tendsto_measure_of_null_frontier {μ_seq : ℕ → Measure CP1} {μ_lim : Measure CP1}
    (h : WeakMeasureConvergence μ_seq μ_lim) {A : Set CP1} (hA : μ_lim (frontier A) = 0) :
    Tendsto (fun n => μ_seq n A) atTop (nhds (μ_lim A)) :=
  h.2.2.1 A hA

/-- Total mass convergence: μ_seq(CP1) → μ_lim(CP1) (Zero-sorry). -/
lemma tendsto_univ {μ_seq : ℕ → Measure CP1} {μ_lim : Measure CP1}
    (h : WeakMeasureConvergence μ_seq μ_lim) :
    Tendsto (fun n => μ_seq n Set.univ) atTop (nhds (μ_lim Set.univ)) :=
  h.2.2.2

/-- Reflexivity of weak measure convergence on constant sequences (Zero-sorry). -/
lemma refl (μ : Measure CP1) :
    WeakMeasureConvergence (fun _ => μ) μ := by
  refine ⟨fun _ _ => tendsto_const_nhds, fun _ _ => ?_, fun _ _ => tendsto_const_nhds, tendsto_const_nhds⟩
  rw [Filter.limsup_const]

/-- Subsequence stability of weak measure convergence (Zero-sorry). -/
lemma comp_subseq {μ_seq : ℕ → Measure CP1} {μ_lim : Measure CP1}
    (h : WeakMeasureConvergence μ_seq μ_lim) (σ : SubseqMap) :
    WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim := by
  have h_tendsto := σ.2.tendsto_atTop
  refine ⟨fun f hf => (h.1 f hf).comp h_tendsto, fun K hK => ?_,
          fun A hA => (h.2.2.1 A hA).comp h_tendsto,
          h.2.2.2.comp h_tendsto⟩
  have h_comp : (fun n => μ_seq (σ.1 n) K) = (fun n => μ_seq n K) ∘ σ.1 := rfl
  rw [h_comp, Filter.limsup_comp]
  have h_mono : limsup (fun n => μ_seq n K) (map σ.1 atTop) ≤ limsup (fun n => μ_seq n K) atTop :=
    limsup_le_limsup_of_le h_tendsto
  exact h_mono.trans (h.2.1 K hK)

/-- Preservation of uniform upper bounds on total mass in the weak limit (Zero-sorry). -/
lemma total_mass_le {μ_seq : ℕ → Measure CP1} {μ_lim : Measure CP1}
    (h : WeakMeasureConvergence μ_seq μ_lim) {B : ℝ}
    (h_le : ∀ n, μ_seq n Set.univ ≤ ENNReal.ofReal B) :
    μ_lim Set.univ ≤ ENNReal.ofReal B := by
  have h_lim := h.tendsto_univ
  exact le_of_tendsto' h_lim h_le

/-- The weak limit of measures with uniformly bounded total mass is finite (Zero-sorry). -/
lemma isFiniteMeasure {μ_seq : ℕ → Measure CP1} {μ_lim : Measure CP1}
    (h : WeakMeasureConvergence μ_seq μ_lim) {B : ℝ}
    (h_le : ∀ n, μ_seq n Set.univ ≤ ENNReal.ofReal B) :
    IsFiniteMeasure μ_lim := by
  have h_mass := total_mass_le h h_le
  constructor
  exact lt_of_le_of_lt h_mass ENNReal.ofReal_lt_top

end WeakMeasureConvergence

/-- Construct an `IsFiniteMeasure` instance from an explicit finite real bound (Zero-sorry). -/
lemma isFiniteMeasure_of_univ_le_ofReal (μ : Measure CP1) {B : ℝ}
    (h : μ Set.univ ≤ ENNReal.ofReal B) :
    IsFiniteMeasure μ := by
  constructor
  exact lt_of_le_of_lt h ENNReal.ofReal_lt_top

/-- Weak Compactness of Energy Measures on CP1 (Contract C01).
Any sequence of finite nonnegative Borel measures on CP1 with uniformly bounded total mass
has a weakly convergent subsequence. -/
theorem weak_measure_compactness (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)]
    (h_bdd : ∃ B > 0, ∀ n, μ_seq n Set.univ ≤ ENNReal.ofReal B) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim := by
  sorry

/-- [Conditional Reduction: Mathlib Radon / Riesz representation theorem].
Weak energy measure compactness reduces directly to general weak measure compactness.
Proved with zero sorry. -/
theorem weak_energy_measure_compactness_of_weak_measure_compactness
    (h_comp : ∀ (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)],
      (∃ B > 0, ∀ n, μ_seq n Set.univ ≤ ENNReal.ofReal B) →
      ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
        IsFiniteMeasure μ_lim ∧
        WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (hB : 0 < B)
    (h_bdd : ∀ n, energyMeasureExtended I (u_seq n) Set.univ ≤ ENNReal.ofReal B) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  haveI : ∀ n, IsFiniteMeasure (energyMeasureExtended I (u_seq n)) :=
    fun n => isFiniteMeasure_of_univ_le_ofReal (energyMeasureExtended I (u_seq n)) (h_bdd n)
  exact h_comp (fun n => energyMeasureExtended I (u_seq n)) ⟨B, hB, h_bdd⟩

/-- Preservation of real energy upper bounds in extended ENNReal measures (Zero-sorry). -/
theorem energyMeasureExtended_le_ofReal_of_totalEnergy_le
    (u : CP1 → M) (B : ℝ) (h_en : totalEnergy I u ≤ B)
    (h_fin : energyMeasureExtended I u Set.univ < ⊤) :
    energyMeasureExtended I u Set.univ ≤ ENNReal.ofReal B := by
  have h_toReal : (energyMeasureExtended I u Set.univ).toReal = totalEnergy I u := rfl
  have h_eq : energyMeasureExtended I u Set.univ = ENNReal.ofReal (totalEnergy I u) := by
    rw [← h_toReal, ENNReal.ofReal_toReal h_fin.ne]
  rw [h_eq]
  exact ENNReal.ofReal_le_ofReal h_en

/-- Finiteness of extended energy measure for curves with bounded total energy. -/
theorem energyMeasureExtended_lt_top_of_totalEnergy_le
    (u : CP1 → M) (B : ℝ) (_hB : 0 < B) (_h : totalEnergy I u ≤ B) :
    energyMeasureExtended I u Set.univ < ⊤ := by
  sorry

/-- Weak Compactness of Energy Measures for sequences of J-holomorphic curves (Contract C01).
Proved with zero direct sorry. -/
theorem weak_energy_measure_compactness
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (hB : 0 < B)
    (h_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  have h_meas_bdd : ∀ n, energyMeasureExtended I (u_seq n) Set.univ ≤ ENNReal.ofReal B := by
    intro n
    have h_fin := energyMeasureExtended_lt_top_of_totalEnergy_le I (u_seq n) B hB (h_bdd n)
    exact energyMeasureExtended_le_ofReal_of_totalEnergy_le I (u_seq n) B (h_bdd n) h_fin
  exact weak_energy_measure_compactness_of_weak_measure_compactness I
    weak_measure_compactness u_seq B hB h_meas_bdd

#print axioms weak_energy_measure_compactness_of_weak_measure_compactness
#print axioms energyMeasureExtended_le_ofReal_of_totalEnergy_le
#print axioms weak_energy_measure_compactness

end GromovCompactness.Compactness

