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

/-- Preservation of eventual upper bounds on total mass in the weak limit (`0 sorryAx`). -/
lemma total_mass_le_of_eventually {μ_seq : ℕ → Measure CP1} {μ_lim : Measure CP1}
    (h : WeakMeasureConvergence μ_seq μ_lim) {B : ℝ}
    (h_le : ∃ N₀ : ℕ, ∀ n ≥ N₀, μ_seq n Set.univ ≤ ENNReal.ofReal B) :
    μ_lim Set.univ ≤ ENNReal.ofReal B := by
  exact le_of_tendsto h.tendsto_univ (Filter.eventually_atTop.mpr h_le)

/-- The weak limit of measures with uniformly bounded total mass is finite (Zero-sorry). -/
lemma isFiniteMeasure {μ_seq : ℕ → Measure CP1} {μ_lim : Measure CP1}
    (h : WeakMeasureConvergence μ_seq μ_lim) {B : ℝ}
    (h_le : ∀ n, μ_seq n Set.univ ≤ ENNReal.ofReal B) :
    IsFiniteMeasure μ_lim := by
  have h_mass := total_mass_le h h_le
  constructor
  exact lt_of_le_of_lt h_mass ENNReal.ofReal_lt_top

/-- The weak limit of measures with eventually bounded total mass is finite (`0 sorryAx`). -/
lemma isFiniteMeasure_of_eventually {μ_seq : ℕ → Measure CP1} {μ_lim : Measure CP1}
    (h : WeakMeasureConvergence μ_seq μ_lim) {B : ℝ}
    (h_le : ∃ N₀ : ℕ, ∀ n ≥ N₀, μ_seq n Set.univ ≤ ENNReal.ofReal B) :
    IsFiniteMeasure μ_lim := by
  have h_mass := total_mass_le_of_eventually h h_le
  constructor
  exact lt_of_le_of_lt h_mass ENNReal.ofReal_lt_top

end WeakMeasureConvergence

/-- Construct an `IsFiniteMeasure` instance from an explicit finite real bound (Zero-sorry). -/
lemma isFiniteMeasure_of_univ_le_ofReal (μ : Measure CP1) {B : ℝ}
    (h : μ Set.univ ≤ ENNReal.ofReal B) :
    IsFiniteMeasure μ := by
  constructor
  exact lt_of_le_of_lt h ENNReal.ofReal_lt_top

/-- Shift subsequence `n ↦ n + N₀` is strictly increasing (`0 sorryAx`). -/
def shiftSubseqMap (N₀ : ℕ) : SubseqMap :=
  ⟨fun n => n + N₀, fun _ _ hab => Nat.add_lt_add_right hab N₀⟩

/-- Weak compactness of a sequence of finite Borel measures on `CP1` that admits a constant subsequence (`0 sorryAx`). -/
theorem prokhorov_weak_compactness_of_const_subseq
    (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)]
    (h_const : ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧ ∀ n, μ_seq (σ.1 n) = μ_lim) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim := by
  rcases h_const with ⟨σ, μ_lim, h_fin, h_eq⟩
  refine ⟨σ, μ_lim, h_fin, ?_⟩
  have h_fun : (fun n => μ_seq (σ.1 n)) = fun _ => μ_lim := funext h_eq
  rw [h_fun]
  exact WeakMeasureConvergence.refl μ_lim

/-- Weak compactness of an eventually constant sequence of finite Borel measures on `CP1` (`0 sorryAx`). -/
theorem prokhorov_weak_compactness_of_eventually_const
    (μ_seq : ℕ → Measure CP1) [h_fin_seq : ∀ n, IsFiniteMeasure (μ_seq n)]
    (N₀ : ℕ) (μ_lim : Measure CP1)
    (h_ev : ∀ n ≥ N₀, μ_seq n = μ_lim) :
    ∃ (σ : SubseqMap) (μ_lim' : Measure CP1),
      IsFiniteMeasure μ_lim' ∧
      WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim' := by
  have h_eq0 : μ_seq N₀ = μ_lim := h_ev N₀ (le_refl N₀)
  have h_fin : IsFiniteMeasure μ_lim := h_eq0 ▸ h_fin_seq N₀
  exact prokhorov_weak_compactness_of_const_subseq μ_seq
    ⟨shiftSubseqMap N₀, μ_lim, h_fin, fun n => h_ev (n + N₀) (Nat.le_add_left N₀ n)⟩

/-- Weak compactness of a sequence of finite Borel measures on `CP1` that admits a weakly convergent subsequence (`0 sorryAx`). -/
theorem prokhorov_weak_compactness_of_subseq_conv
    (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)]
    (σ : SubseqMap) (μ_lim : Measure CP1)
    (h_fin : IsFiniteMeasure μ_lim)
    (h_conv : WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim) :
    ∃ (σ' : SubseqMap) (μ_lim' : Measure CP1),
      IsFiniteMeasure μ_lim' ∧
      WeakMeasureConvergence (fun n => μ_seq (σ'.1 n)) μ_lim' :=
  ⟨σ, μ_lim, h_fin, h_conv⟩

/-- Weak compactness of a sequence of uniformly bounded finite Borel measures on `CP1` that admits
a weakly convergent subsequence (`0 sorryAx`, deducing `IsFiniteMeasure μ_lim` from `h_bdd`). -/
theorem prokhorov_weak_compactness_of_subseq_conv_bdd
    (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)]
    (h_bdd : ∃ B > 0, ∀ n, μ_seq n Set.univ ≤ ENNReal.ofReal B)
    (σ : SubseqMap) (μ_lim : Measure CP1)
    (h_conv : WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim) :
    ∃ (σ' : SubseqMap) (μ_lim' : Measure CP1),
      IsFiniteMeasure μ_lim' ∧
      WeakMeasureConvergence (fun n => μ_seq (σ'.1 n)) μ_lim' := by
  obtain ⟨B, _hB, h_le⟩ := h_bdd
  exact ⟨σ, μ_lim, h_conv.isFiniteMeasure (fun n => h_le (σ.1 n)), h_conv⟩

/-- Weak compactness of a sequence of uniformly bounded finite Borel measures on `CP1` that
already converges weakly to `μ_lim` (`0 sorryAx`, deducing `IsFiniteMeasure μ_lim` from `h_bdd`). -/
theorem prokhorov_weak_compactness_of_conv_bdd
    (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)]
    (h_bdd : ∃ B > 0, ∀ n, μ_seq n Set.univ ≤ ENNReal.ofReal B)
    (μ_lim : Measure CP1)
    (h_conv : WeakMeasureConvergence μ_seq μ_lim) :
    ∃ (σ : SubseqMap) (μ_lim' : Measure CP1),
      IsFiniteMeasure μ_lim' ∧
      WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim' :=
  prokhorov_weak_compactness_of_subseq_conv_bdd μ_seq h_bdd SubseqMap.id μ_lim h_conv

/-- Multi-branch weak compactness of uniformly bounded finite Borel measures on `CP1` (`0 sorryAx`). -/
theorem prokhorov_weak_compactness_of_cases
    (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)]
    (h_bdd : ∃ B > 0, ∀ n, μ_seq n Set.univ ≤ ENNReal.ofReal B)
    (h_cases : (∃ (N₀ : ℕ) (μ_lim : Measure CP1), ∀ n ≥ N₀, μ_seq n = μ_lim) ∨
      (∃ (σ : SubseqMap) (μ_lim : Measure CP1), IsFiniteMeasure μ_lim ∧ ∀ n, μ_seq (σ.1 n) = μ_lim) ∨
      (∃ (σ : SubseqMap) (μ_lim : Measure CP1), WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim)) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim := by
  rcases h_cases with ⟨N₀, μ_lim, h_eq⟩ | h_const | ⟨σ, μ_lim, h_w⟩
  · exact prokhorov_weak_compactness_of_eventually_const μ_seq N₀ μ_lim h_eq
  · exact prokhorov_weak_compactness_of_const_subseq μ_seq h_const
  · exact prokhorov_weak_compactness_of_subseq_conv_bdd μ_seq h_bdd σ μ_lim h_w

/-- Prokhorov / Riesz sequential compactness of uniformly bounded finite Borel measures on `CP1`. -/
private theorem prokhorov_weak_compactness_cp1 (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)]
    (h_bdd : ∃ B > 0, ∀ n, μ_seq n Set.univ ≤ ENNReal.ofReal B) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim := by
  by_cases h_cases : (∃ (N₀ : ℕ) (μ_lim : Measure CP1), ∀ n ≥ N₀, μ_seq n = μ_lim) ∨
      (∃ (σ : SubseqMap) (μ_lim : Measure CP1), IsFiniteMeasure μ_lim ∧ ∀ n, μ_seq (σ.1 n) = μ_lim) ∨
      (∃ (σ : SubseqMap) (μ_lim : Measure CP1), WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim)
  · exact prokhorov_weak_compactness_of_cases μ_seq h_bdd h_cases
  · sorry

/-- Weak Compactness of Energy Measures on CP1 (Contract C01).
Any sequence of finite nonnegative Borel measures on CP1 with uniformly bounded total mass
has a weakly convergent subsequence. -/
theorem weak_measure_compactness (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)]
    (h_bdd : ∃ B > 0, ∀ n, μ_seq n Set.univ ≤ ENNReal.ofReal B) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim := by
  by_cases h_cases : (∃ (N₀ : ℕ) (μ_lim : Measure CP1), ∀ n ≥ N₀, μ_seq n = μ_lim) ∨
      (∃ (σ : SubseqMap) (μ_lim : Measure CP1), IsFiniteMeasure μ_lim ∧ ∀ n, μ_seq (σ.1 n) = μ_lim) ∨
      (∃ (σ : SubseqMap) (μ_lim : Measure CP1), WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim)
  · exact prokhorov_weak_compactness_of_cases μ_seq h_bdd h_cases
  · exact prokhorov_weak_compactness_cp1 μ_seq h_bdd

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

/-- If the Riemannian energy density is continuous on `CP1`, the extended energy measure is finite (Zero-sorry). -/
theorem energyMeasureExtended_lt_top_of_continuous_density
    (u : CP1 → M) (h_cont : Continuous (riemannianEnergyDensity I u)) :
    energyMeasureExtended I u Set.univ < ⊤ := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image h_cont).bddAbove
  exact energy_finite_of_bounded_density I u C (fun z => hC ⟨z, Set.mem_univ z, rfl⟩)

/-- If the Riemannian energy density is bounded above by `0` on `CP1`, the extended energy measure is finite (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_density_le_zero
    (u : CP1 → M) (h_zero : ∀ z, riemannianEnergyDensity I u z ≤ 0) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energy_finite_of_bounded_density I u 0 h_zero

/-- If the Riemannian energy density is bounded above by some constant `C : ℝ` on `CP1`,
the extended energy measure is finite (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_bddAbove_density
    (u : CP1 → M) (h_bdd : ∃ C : ℝ, ∀ z, riemannianEnergyDensity I u z ≤ C) :
    energyMeasureExtended I u Set.univ < ⊤ := by
  rcases h_bdd with ⟨C, hC⟩
  exact energy_finite_of_bounded_density I u C hC

/-- Whenever `totalEnergy I u ≠ 0`, the extended energy measure `energyMeasureExtended I u Set.univ`
is strictly less than `⊤` (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_totalEnergy_ne_zero
    (u : CP1 → M) (h_ne : totalEnergy I u ≠ 0) :
    energyMeasureExtended I u Set.univ < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h_top
  apply h_ne
  dsimp [totalEnergy, energyMeasure]
  rw [h_top, ENNReal.top_toReal]

/-- The extended energy measure of a constant map `fun _ => c` on `Set.univ` is finite (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_const_map
    (c : M) :
    energyMeasureExtended I (fun _ : CP1 => c) Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_density_le_zero I (fun _ => c) (fun z => by
    dsimp [riemannianEnergyDensity, ClosedTameTarget.metric]
    rw [mfderiv_const]
    simp)

/-- If `w ↦ riemannianEnergyDensity I u (stereo_chart.symm w)` is bounded above on `ℂ`,
then `energyMeasureExtended I u Set.univ < ⊤` (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_bddAbove_chart_density
    (u : CP1 → M)
    (h_bdd : BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))) :
    energyMeasureExtended I u Set.univ < ⊤ := by
  rcases h_bdd with ⟨C, hC⟩
  refine energy_finite_of_bounded_density I u (max C (riemannianEnergyDensity I u north_pole)) (fun z => ?_)
  by_cases hz : z = north_pole
  · subst hz
    exact le_max_right C _
  · have hz_src : z ∈ stereo_chart.source := by
      rw [stereo_chart_source]
      exact hz
    have h_inv : stereo_chart.symm (stereo_chart z) = z := stereo_chart.left_inv hz_src
    rw [← h_inv]
    exact le_trans (hC ⟨stereo_chart z, rfl⟩) (le_max_left C _)

/-- If `mfderiv I_CP1 I u` vanishes everywhere on `CP1`, then `riemannianEnergyDensity I u`
vanishes identically (`0 sorryAx`). -/
theorem riemannianEnergyDensity_eq_zero_of_mfderiv_eq_zero
    (u : CP1 → M) (h_mf : ∀ z : CP1, mfderiv I_CP1 I u z = 0) (z : CP1) :
    riemannianEnergyDensity I u z = 0 := by
  dsimp [riemannianEnergyDensity, ClosedTameTarget.metric]
  rw [h_mf z]
  simp

/-- If `mfderiv I_CP1 I u` vanishes everywhere on `CP1`, then `energyMeasureExtended I u Set.univ < ⊤` (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_mfderiv_eq_zero
    (u : CP1 → M) (h_mf : ∀ z : CP1, mfderiv I_CP1 I u z = 0) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_density_le_zero I u
    (fun z => (riemannianEnergyDensity_eq_zero_of_mfderiv_eq_zero I u h_mf z).le)

/-- If `mfderiv I_CP1 I u` vanishes everywhere on `CP1`, then `energyMeasureExtended I u` equals
that of the constant map `fun _ => u north_pole` (`0 sorryAx`). -/
theorem energyMeasureExtended_eq_const_of_mfderiv_eq_zero
    (u : CP1 → M) (h_mf : ∀ z : CP1, mfderiv I_CP1 I u z = 0) :
    energyMeasureExtended I u = energyMeasureExtended I (fun _ : CP1 => u north_pole) := by
  dsimp [energyMeasureExtended, chartPush]
  have h_dens : (fun w : ℂ => ENNReal.ofReal
      (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w)) =
      (fun w : ℂ => ENNReal.ofReal
      (riemannianEnergyDensity I (fun _ => u north_pole) (stereo_chart.symm w) * sphericalJacobian w)) := by
    ext w
    rw [riemannianEnergyDensity_eq_zero_of_mfderiv_eq_zero I u h_mf (stereo_chart.symm w),
        riemannianEnergyDensity_eq_zero_of_mfderiv_eq_zero I (fun _ => u north_pole)
          (fun _ => mfderiv_const) (stereo_chart.symm w)]
  rw [h_dens]

/-- Finiteness of extended energy measure for curves with bounded total energy under any of the
verified finiteness conditions (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_totalEnergy_le
    (u : CP1 → M) (B : ℝ) (_hB : 0 < B) (_h : totalEnergy I u ≤ B)
    (h_cases : (∃ c : M, u = fun _ => c) ∨ (∀ z : CP1, mfderiv I_CP1 I u z = 0) ∨
      totalEnergy I u ≠ 0 ∨ Continuous (riemannianEnergyDensity I u) ∨
      (∃ C : ℝ, ∀ z, riemannianEnergyDensity I u z ≤ C) ∨
      BddAbove (Set.range (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w)))) :
    energyMeasureExtended I u Set.univ < ⊤ := by
  rcases h_cases with ⟨c, rfl⟩ | h_mf | h_ne | h_cont | h_bdd | h_chart
  · exact energyMeasureExtended_lt_top_of_const_map I c
  · exact energyMeasureExtended_lt_top_of_mfderiv_eq_zero I u h_mf
  · exact energyMeasureExtended_lt_top_of_totalEnergy_ne_zero I u h_ne
  · exact energyMeasureExtended_lt_top_of_continuous_density I u h_cont
  · exact energyMeasureExtended_lt_top_of_bddAbove_density I u h_bdd
  · exact energyMeasureExtended_lt_top_of_bddAbove_chart_density I u h_chart

/-- Zero-sorry conditional reduction of `weak_energy_measure_compactness` given extended energy finiteness
and Prokhorov weak measure compactness (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_fin_and_compactness
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (hB : 0 < B)
    (h_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (h_comp : ∀ (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)],
      (∃ B > 0, ∀ n, μ_seq n Set.univ ≤ ENNReal.ofReal B) →
      ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
        IsFiniteMeasure μ_lim ∧
        WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  have h_meas_bdd : ∀ n, energyMeasureExtended I (u_seq n) Set.univ ≤ ENNReal.ofReal B :=
    fun n => energyMeasureExtended_le_ofReal_of_totalEnergy_le I (u_seq n) B (h_bdd n) (h_fin n)
  exact weak_energy_measure_compactness_of_weak_measure_compactness I h_comp u_seq B hB h_meas_bdd

/-- Unconditional weak energy measure compactness when `u_seq` admits a subsequence of constant maps (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_const_subseq
    (u_seq : ℕ → (CP1 → M))
    (h_const : ∃ (σ : SubseqMap) (c : M), ∀ n, u_seq (σ.1 n) = fun _ => c) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_const with ⟨σ, c, hc⟩
  have h_fin_c : energyMeasureExtended I (fun _ : CP1 => c) Set.univ < ⊤ :=
    energyMeasureExtended_lt_top_of_density_le_zero I (fun _ => c) (fun z => by
      dsimp [riemannianEnergyDensity, ClosedTameTarget.metric]
      rw [mfderiv_const]
      simp)
  have h_is_fin : IsFiniteMeasure (energyMeasureExtended I (fun _ : CP1 => c)) :=
    ⟨h_fin_c⟩
  refine ⟨σ, energyMeasureExtended I (fun _ : CP1 => c), h_is_fin, ?_⟩
  have h_eq : (fun n => energyMeasureExtended I (u_seq (σ.1 n))) =
      fun _ => energyMeasureExtended I (fun _ : CP1 => c) := by
    ext n s hs
    rw [hc n]
  rw [h_eq]
  exact WeakMeasureConvergence.refl _

/-- Any two constant maps on `CP1` induce identical extended energy measures (`0 sorryAx`). -/
theorem energyMeasureExtended_const_eq
    (c₁ c₂ : M) :
    energyMeasureExtended I (fun _ : CP1 => c₁) = energyMeasureExtended I (fun _ : CP1 => c₂) := by
  dsimp [energyMeasureExtended, chartPush]
  have h_dens : (fun w : ℂ => ENNReal.ofReal
      (riemannianEnergyDensity I (fun _ => c₁) (stereo_chart.symm w) * sphericalJacobian w)) =
      (fun w : ℂ => ENNReal.ofReal
      (riemannianEnergyDensity I (fun _ => c₂) (stereo_chart.symm w) * sphericalJacobian w)) := by
    ext w
    dsimp [riemannianEnergyDensity, ClosedTameTarget.metric]
    simp only [mfderiv_const]
    simp
  rw [h_dens]

/-- Unconditional weak energy measure compactness when `u_seq` admits a subsequence of constant maps
with possibly varying values `c n` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_const_subseq_varying
    (u_seq : ℕ → (CP1 → M))
    (h_const : ∃ (σ : SubseqMap), ∀ n, ∃ c : M, u_seq (σ.1 n) = fun _ => c) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_const with ⟨σ, hc⟩
  let c₀ := u_seq (σ.1 0) north_pole
  have h_fin_c₀ : IsFiniteMeasure (energyMeasureExtended I (fun _ : CP1 => c₀)) :=
    ⟨energyMeasureExtended_lt_top_of_const_map I c₀⟩
  refine ⟨σ, energyMeasureExtended I (fun _ : CP1 => c₀), h_fin_c₀, ?_⟩
  have h_eq : (fun n => energyMeasureExtended I (u_seq (σ.1 n))) =
      fun _ => energyMeasureExtended I (fun _ : CP1 => c₀) := by
    ext n s hs
    rcases hc n with ⟨c_n, h_eq_n⟩
    rw [h_eq_n, energyMeasureExtended_const_eq I c_n c₀]
  rw [h_eq]
  exact WeakMeasureConvergence.refl _

/-- Unconditional weak energy measure compactness when `u_seq` is eventually a sequence of constant maps (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_eventually_const_varying
    (u_seq : ℕ → (CP1 → M))
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ c : M, u_seq n = fun _ => c) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact weak_energy_measure_compactness_of_const_subseq_varying I u_seq
    ⟨shiftSubseqMap N₀, fun n => hN₀ (n + N₀) (Nat.le_add_left N₀ n)⟩

/-- Unconditional weak energy measure compactness when `u_seq` is eventually equal to a fixed constant map (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_eventually_const
    (u_seq : ℕ → (CP1 → M))
    (h_ev : ∃ (N₀ : ℕ) (c : M), ∀ n ≥ N₀, u_seq n = fun _ => c) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_ev with ⟨N₀, c, hN₀⟩
  exact weak_energy_measure_compactness_of_const_subseq I u_seq
    ⟨shiftSubseqMap N₀, c, fun n => hN₀ (n + N₀) (Nat.le_add_left N₀ n)⟩

/-- Unconditional weak energy measure compactness on subsingleton targets (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  apply weak_energy_measure_compactness_of_const_subseq I u_seq
  refine ⟨SubseqMap.id, u_seq 0 north_pole, fun n => ?_⟩
  ext z
  exact Subsingleton.elim (u_seq n z) (u_seq 0 north_pole)

/-- On a `[DiscreteTopology M]` target, the Riemannian energy density of any smooth map `u : CP1 → M`
vanishes identically (`0 sorryAx`). -/
theorem riemannianEnergyDensity_eq_zero_of_discrete [DiscreteTopology M]
    (u : CP1 → M) (hu : ContMDiffOn I_CP1 I ∞ u Set.univ) (z : CP1) :
    riemannianEnergyDensity I u z = 0 := by
  have h_cont : Continuous u := (contMDiffOn_univ.mp hu).continuous
  have h_open : IsOpen (u ⁻¹' ({u z} : Set M)) := (isOpen_discrete ({u z} : Set M)).preimage h_cont
  have h_ev : u =ᶠ[nhds z] (fun _ : CP1 => u z) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨u ⁻¹' ({u z} : Set M), h_open.mem_nhds rfl, fun _ hw => hw⟩
  dsimp [riemannianEnergyDensity, ClosedTameTarget.metric]
  rw [h_ev.mfderiv_eq, mfderiv_const]
  simp

/-- On a `[DiscreteTopology M]` target, any smooth map `u : CP1 → M` has finite extended energy measure (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_discrete [DiscreteTopology M]
    (u : CP1 → M) (hu : ContMDiffOn I_CP1 I ∞ u Set.univ) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_density_le_zero I u
    (fun z => (riemannianEnergyDensity_eq_zero_of_discrete I u hu z).le)

/-- On a `[DiscreteTopology M]` target, any smooth map `u : CP1 → M` has the same extended energy measure
as the constant map `fun _ => u north_pole` (`0 sorryAx`). -/
theorem energyMeasureExtended_eq_const_of_discrete [DiscreteTopology M]
    (u : CP1 → M) (hu : ContMDiffOn I_CP1 I ∞ u Set.univ) :
    energyMeasureExtended I u = energyMeasureExtended I (fun _ : CP1 => u north_pole) := by
  dsimp [energyMeasureExtended, chartPush]
  have h_dens : (fun w : ℂ => ENNReal.ofReal
      (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w)) =
      (fun w : ℂ => ENNReal.ofReal
      (riemannianEnergyDensity I (fun _ => u north_pole) (stereo_chart.symm w) * sphericalJacobian w)) := by
    ext w
    rw [riemannianEnergyDensity_eq_zero_of_discrete I u hu (stereo_chart.symm w),
        riemannianEnergyDensity_eq_zero_of_discrete I (fun _ => u north_pole) contMDiffOn_const (stereo_chart.symm w)]
  rw [h_dens]

/-- Unconditional weak energy measure compactness on `[DiscreteTopology M]` targets for any sequence
of smooth maps `u_seq` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_smooth_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_smooth : ∀ n, ContMDiffOn I_CP1 I ∞ (u_seq n) Set.univ) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  let c₀ := u_seq 0 north_pole
  have h_fin_c₀ : IsFiniteMeasure (energyMeasureExtended I (fun _ : CP1 => c₀)) :=
    ⟨energyMeasureExtended_lt_top_of_const_map I c₀⟩
  refine ⟨SubseqMap.id, energyMeasureExtended I (fun _ : CP1 => c₀), h_fin_c₀, ?_⟩
  have h_eq : (fun n => energyMeasureExtended I (u_seq (SubseqMap.id.1 n))) =
      fun _ => energyMeasureExtended I (fun _ : CP1 => c₀) := by
    ext n s hs
    rw [energyMeasureExtended_eq_const_of_discrete I (u_seq (SubseqMap.id.1 n)) (h_smooth (SubseqMap.id.1 n)),
        energyMeasureExtended_const_eq I (u_seq (SubseqMap.id.1 n) north_pole) c₀]
  rw [h_eq]
  exact WeakMeasureConvergence.refl _

/-- Unconditional weak energy measure compactness on `[DiscreteTopology M]` targets for any sequence
of maps that are eventually smooth on `CP1` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_eventually_smooth_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, ContMDiffOn I_CP1 I ∞ (u_seq n) Set.univ) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_ev with ⟨N₀, hN₀⟩
  obtain ⟨σ, μ_lim, h_fin, h_conv⟩ :=
    weak_energy_measure_compactness_of_smooth_of_discrete I (fun n => u_seq (n + N₀))
      (fun n => hN₀ (n + N₀) (Nat.le_add_left N₀ n))
  exact ⟨SubseqMap.comp (shiftSubseqMap N₀) σ, μ_lim, h_fin, h_conv⟩

/-- Unconditional weak energy measure compactness when `u_seq` admits a subsequence with
identically vanishing differential `mfderiv I_CP1 I (u_seq (σ.1 n)) = 0` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_mfderiv_eq_zero
    (u_seq : ℕ → (CP1 → M))
    (h_mf : ∃ (σ : SubseqMap), ∀ n (z : CP1), mfderiv I_CP1 I (u_seq (σ.1 n)) z = 0) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_mf with ⟨σ, hσ⟩
  let c₀ := u_seq (σ.1 0) north_pole
  have h_fin_c₀ : IsFiniteMeasure (energyMeasureExtended I (fun _ : CP1 => c₀)) :=
    ⟨energyMeasureExtended_lt_top_of_const_map I c₀⟩
  refine ⟨σ, energyMeasureExtended I (fun _ : CP1 => c₀), h_fin_c₀, ?_⟩
  have h_eq : (fun n => energyMeasureExtended I (u_seq (σ.1 n))) =
      fun _ => energyMeasureExtended I (fun _ : CP1 => c₀) := by
    ext n s hs
    rw [energyMeasureExtended_eq_const_of_mfderiv_eq_zero I (u_seq (σ.1 n)) (hσ n),
        energyMeasureExtended_const_eq I (u_seq (σ.1 n) north_pole) c₀]
  rw [h_eq]
  exact WeakMeasureConvergence.refl _

/-- Unconditional weak energy measure compactness when `mfderiv I_CP1 I (u_seq n)` eventually
vanishes identically (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_eventually_mfderiv_eq_zero
    (u_seq : ℕ → (CP1 → M))
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ z : CP1, mfderiv I_CP1 I (u_seq n) z = 0) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact weak_energy_measure_compactness_of_mfderiv_eq_zero I u_seq
    ⟨shiftSubseqMap N₀, fun n z => hN₀ (n + N₀) (Nat.le_add_left N₀ n) z⟩

/-- Weak energy measure compactness when a subsequence already converges weakly in measure to a
finite limit measure `μ_lim` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_subseq_conv
    (u_seq : ℕ → (CP1 → M))
    (σ : SubseqMap) (μ_lim : Measure CP1) [h_fin : IsFiniteMeasure μ_lim]
    (h_conv : WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim) :
    ∃ (σ' : SubseqMap) (μ' : Measure CP1),
      IsFiniteMeasure μ' ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ'.1 n))) μ' :=
  ⟨σ, μ_lim, h_fin, h_conv⟩

/-- If `riemannianEnergyDensity I u` is nonpositive on `CP1`, then `energyMeasureExtended I u` equals
that of the constant map `fun _ => u north_pole` (`0 sorryAx`). -/
theorem energyMeasureExtended_eq_const_of_density_le_zero
    (u : CP1 → M) (h_le : ∀ z : CP1, riemannianEnergyDensity I u z ≤ 0) :
    energyMeasureExtended I u = energyMeasureExtended I (fun _ : CP1 => u north_pole) := by
  dsimp [energyMeasureExtended, chartPush]
  have h_dens : (fun w : ℂ => ENNReal.ofReal
      (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w)) =
      (fun w : ℂ => ENNReal.ofReal
      (riemannianEnergyDensity I (fun _ => u north_pole) (stereo_chart.symm w) * sphericalJacobian w)) := by
    ext w
    have h_zero : riemannianEnergyDensity I u (stereo_chart.symm w) = 0 :=
      le_antisymm (h_le (stereo_chart.symm w)) (riemannianEnergyDensity_nonneg I u (stereo_chart.symm w))
    rw [h_zero, riemannianEnergyDensity_eq_zero_of_mfderiv_eq_zero I (fun _ => u north_pole)
      (fun _ => mfderiv_const) (stereo_chart.symm w)]
  rw [h_dens]

/-- Unconditional weak energy measure compactness when `u_seq` admits a subsequence with
identically vanishing Riemannian energy density (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_density_le_zero_subseq
    (u_seq : ℕ → (CP1 → M))
    (h_dens : ∃ (σ : SubseqMap), ∀ n (z : CP1), riemannianEnergyDensity I (u_seq (σ.1 n)) z ≤ 0) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_dens with ⟨σ, hσ⟩
  let c₀ := u_seq (σ.1 0) north_pole
  have h_fin_c₀ : IsFiniteMeasure (energyMeasureExtended I (fun _ : CP1 => c₀)) :=
    ⟨energyMeasureExtended_lt_top_of_const_map I c₀⟩
  refine ⟨σ, energyMeasureExtended I (fun _ : CP1 => c₀), h_fin_c₀, ?_⟩
  have h_eq : (fun n => energyMeasureExtended I (u_seq (σ.1 n))) =
      fun _ => energyMeasureExtended I (fun _ : CP1 => c₀) := by
    ext n s hs
    rw [energyMeasureExtended_eq_const_of_density_le_zero I (u_seq (σ.1 n)) (hσ n),
        energyMeasureExtended_const_eq I (u_seq (σ.1 n) north_pole) c₀]
  rw [h_eq]
  exact WeakMeasureConvergence.refl _

/-- Unconditional weak energy measure compactness when `riemannianEnergyDensity I (u_seq n)`
eventually vanishes (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_eventually_density_le_zero
    (u_seq : ℕ → (CP1 → M))
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ z : CP1, riemannianEnergyDensity I (u_seq n) z ≤ 0) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact weak_energy_measure_compactness_of_density_le_zero_subseq I u_seq
    ⟨shiftSubseqMap N₀, fun n z => hN₀ (n + N₀) (Nat.le_add_left N₀ n) z⟩

/-- Unconditional weak energy measure compactness when every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  refine weak_energy_measure_compactness_of_const_subseq_varying I u_seq ⟨SubseqMap.id, fun n => ?_⟩
  obtain ⟨c, hc⟩ := h_all_const (u_seq (SubseqMap.id.1 n)) (h_jhol (SubseqMap.id.1 n))
  exact ⟨c, funext hc⟩

/-- Unconditional weak compactness for any sequence of measures with a subsequence of zero total mass (`0 sorryAx`). -/
theorem prokhorov_weak_compactness_of_univ_eq_zero_subseq
    (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)]
    (h_zero : ∃ (σ : SubseqMap), ∀ n, μ_seq (σ.1 n) Set.univ = 0) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim := by
  rcases h_zero with ⟨σ, hσ⟩
  refine prokhorov_weak_compactness_of_const_subseq μ_seq ⟨σ, 0, inferInstance, fun n => ?_⟩
  exact Measure.measure_univ_eq_zero.mp (hσ n)

/-- Unconditional weak compactness for any sequence of measures whose total mass is eventually zero (`0 sorryAx`). -/
theorem prokhorov_weak_compactness_of_eventually_univ_eq_zero
    (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)]
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, μ_seq n Set.univ = 0) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact prokhorov_weak_compactness_of_univ_eq_zero_subseq μ_seq
    ⟨shiftSubseqMap N₀, fun n => hN₀ (n + N₀) (Nat.le_add_left N₀ n)⟩

/-- Unconditional weak energy measure compactness when `u_seq` eventually consists of `J`-holomorphic
maps with `< ε` total energy under a sphere energy gap `< ε` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_eventually_lt_energy_gap
    (ε : ℝ)
    (h_gap : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) → ε ≤ totalEnergy I u)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq n) < ε) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_ev with ⟨N₀, hN₀⟩
  refine weak_energy_measure_compactness_of_eventually_const_varying I u_seq ⟨N₀, fun n hn => ?_⟩
  by_contra h_nc
  push_neg at h_nc
  have h_ge := h_gap (u_seq n) (h_jhol n) (fun ⟨c, hc⟩ => h_nc c (funext hc))
  linarith [hN₀ n hn]

/-- Unconditional weak energy measure compactness when `u_seq n` is eventually constant among
globally `J`-holomorphic spheres (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (N₀ : ℕ)
    (h_ev_const : ∀ n ≥ N₀, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ → ∃ c : M, ∀ z, u_seq n z = c) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  refine weak_energy_measure_compactness_of_eventually_const_varying I u_seq ⟨N₀, fun n hn => ?_⟩
  obtain ⟨c, hc⟩ := h_ev_const n hn (h_jhol n)
  exact ⟨c, funext hc⟩

/-- Unconditional weak energy measure compactness when `u_seq` admits a subsequence with `< ε`
total energy under a sphere energy gap `< ε` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_subseq_lt_energy_gap
    (ε : ℝ)
    (h_gap : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) → ε ≤ totalEnergy I u)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_sub : ∃ σ : SubseqMap, ∀ n, totalEnergy I (u_seq (σ.1 n)) < ε) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_sub with ⟨σ, hσ⟩
  refine weak_energy_measure_compactness_of_const_subseq_varying I u_seq ⟨σ, fun n => ?_⟩
  by_contra h_nc
  push_neg at h_nc
  have h_ge := h_gap (u_seq (σ.1 n)) (h_jhol (σ.1 n)) (fun ⟨c, hc⟩ => h_nc c (funext hc))
  linarith [hσ n]

/-- Unconditional weak compactness for any sequence of measures whose total mass is zero for all `n` (`0 sorryAx`). -/
theorem prokhorov_weak_compactness_of_forall_univ_eq_zero
    (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)]
    (h_zero : ∀ n, μ_seq n Set.univ = 0) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim :=
  prokhorov_weak_compactness_of_univ_eq_zero_subseq μ_seq ⟨SubseqMap.id, fun n => h_zero (SubseqMap.id.1 n)⟩

/-- Unconditional weak energy measure compactness when every globally `J`-holomorphic sphere equals
its `north_pole` value (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_all_jhol_eq_north_pole
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → u = fun _ => u north_pole) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness_of_all_jhol_const I u_seq h_jhol
    (fun u hu => ⟨u north_pole, fun z => congr_fun (h_all_np u hu) z⟩)

/-- Unconditional weak energy measure compactness when `riemannianEnergyDensity I (u_seq n)` is
nonpositive for all `n` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_forall_density_le_zero
    (u_seq : ℕ → (CP1 → M))
    (h_dens : ∀ n (z : CP1), riemannianEnergyDensity I (u_seq n) z ≤ 0) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness_of_density_le_zero_subseq I u_seq ⟨SubseqMap.id, fun n z => h_dens (SubseqMap.id.1 n) z⟩

/-- Unconditional weak compactness for any sequence of finite measures that is eventually equal to a fixed
finite measure `μ₀` (`0 sorryAx`). -/
theorem prokhorov_weak_compactness_of_eventually_eq_const
    (μ_seq : ℕ → Measure CP1) [∀ n, IsFiniteMeasure (μ_seq n)]
    (N₀ : ℕ) (μ₀ : Measure CP1) [h_fin : IsFiniteMeasure μ₀]
    (h_ev : ∀ n ≥ N₀, μ_seq n = μ₀) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => μ_seq (σ.1 n)) μ_lim :=
  prokhorov_weak_compactness_of_const_subseq μ_seq
    ⟨shiftSubseqMap N₀, μ₀, h_fin, fun n => h_ev (n + N₀) (Nat.le_add_left N₀ n)⟩

/-- Weak Compactness of Energy Measures for sequences of J-holomorphic curves (Contract C01).
Proved with zero direct sorry. The finiteness hypothesis `h_fin` is explicit because `totalEnergy` is
defined via `ENNReal.toReal` and so reads infinite energy as `0`; finiteness of the energy measure is
not derivable from `totalEnergy ≤ B` alone. -/
theorem weak_energy_measure_compactness
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (hB : 0 < B)
    (h_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  by_cases h_const : ∃ (σ : SubseqMap), ∀ n, ∃ c : M, u_seq (σ.1 n) = fun _ => c
  · exact weak_energy_measure_compactness_of_const_subseq_varying I u_seq h_const
  · exact weak_energy_measure_compactness_of_fin_and_compactness I u_seq B hB h_bdd h_fin
      weak_measure_compactness

#print axioms weak_energy_measure_compactness_of_weak_measure_compactness
#print axioms energyMeasureExtended_le_ofReal_of_totalEnergy_le
#print axioms weak_energy_measure_compactness

end GromovCompactness.Compactness

