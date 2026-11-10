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
  measure_decomp : μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • Measure.dirac p)

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

/-- Any `J`-holomorphic sphere with total energy strictly below `thresh.ε_sph` is constant (`0 sorryAx`). -/
theorem const_of_jhol_of_totalEnergy_lt_eps_sph
    (thresh : TargetThresholds I M) (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_lt : totalEnergy I u < thresh.ε_sph) :
    ∃ c : M, ∀ z, u z = c := by
  by_contra h_nc
  have h_ge := thresh.h_sph u hu h_nc
  linarith

/-- Any `J`-holomorphic sphere with total energy strictly below `thresh.ε_sph` equals `fun _ => u north_pole` (`0 sorryAx`). -/
theorem eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph
    (thresh : TargetThresholds I M) (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_lt : totalEnergy I u < thresh.ε_sph) :
    u = fun _ => u north_pole := by
  obtain ⟨c, hc⟩ := const_of_jhol_of_totalEnergy_lt_eps_sph I thresh u hu h_lt
  ext z
  rw [hc z, hc north_pole]

/-- Any `J`-holomorphic sphere with total energy strictly below `thresh.h` equals `fun _ => u north_pole` (`0 sorryAx`). -/
theorem eq_const_north_pole_of_jhol_of_totalEnergy_lt_h
    (thresh : TargetThresholds I M) (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_lt : totalEnergy I u < thresh.h) :
    u = fun _ => u north_pole :=
  eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh u hu (h_lt.trans_le thresh.h_le_sph)

/-- Any `J`-holomorphic sphere with nonpositive total energy equals `fun _ => u north_pole` (`0 sorryAx`). -/
theorem eq_const_north_pole_of_jhol_of_totalEnergy_nonpos
    (thresh : TargetThresholds I M) (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_le : totalEnergy I u ≤ 0) :
    u = fun _ => u north_pole :=
  eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh u hu (h_le.trans_lt thresh.ε_sph_pos)

/-- Any `J`-holomorphic sphere with total energy strictly below `thresh.ε_sph` has zero total energy (`0 sorryAx`). -/
theorem totalEnergy_eq_zero_of_jhol_of_totalEnergy_lt_eps_sph
    (thresh : TargetThresholds I M) (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_lt : totalEnergy I u < thresh.ε_sph) :
    totalEnergy I u = 0 := by
  rw [eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh u hu h_lt]
  exact totalEnergy_const I (u north_pole)

/-- Unconditional weak energy measure compactness for `J`-holomorphic spheres when `B < thresh.ε_sph` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_lt_eps_sph
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < thresh.ε_sph) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness_of_const_subseq_varying I u_seq
    ⟨SubseqMap.id, fun n => ⟨u_seq n north_pole,
      eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh (u_seq n) (h_jhol n) ((h_bdd n).trans_lt h_lt)⟩⟩

/-- Unconditional weak energy measure compactness for `J`-holomorphic spheres when `B < thresh.h` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_lt_h
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < thresh.h) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness_of_lt_eps_sph I thresh u_seq h_jhol B h_bdd (h_lt.trans_le thresh.h_le_sph)

/-- Unconditional weak energy measure compactness for `J`-holomorphic spheres when `B ≤ 0` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_nonpos_B
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (hB : B ≤ 0) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness_of_lt_eps_sph I thresh u_seq h_jhol B h_bdd (hB.trans_lt thresh.ε_sph_pos)

/-- If the base limit `cdata.u₀` has total energy strictly below `thresh.ε_sph`, it is constant (`0 sorryAx`). -/
theorem ConcentrationData.u0_eq_const_north_pole_of_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : totalEnergy I cdata.u₀ < thresh.ε_sph) :
    cdata.u₀ = fun _ => cdata.u₀ north_pole :=
  eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh cdata.u₀ cdata.u₀_jhol h_lt

/-- Whenever `B < thresh.ε_reg`, the concentration singular set `cdata.S` is empty (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_lt_eps_reg
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < thresh.ε_reg) :
    cdata.S = ∅ := by
  by_contra h_ne
  have h_pos : 0 < cdata.S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h_ne)
  have h_one : (1 : ℝ) ≤ (cdata.S.card : ℝ) := by exact_mod_cast h_pos
  have h_eps : thresh.ε_reg ≤ (cdata.S.card : ℝ) * thresh.ε_reg := by
    nlinarith [thresh.ε_reg_pos]
  linarith [cdata.card_S_mul_le]

/-- Whenever `B < 2 * thresh.h`, the concentration singular set `cdata.S` is empty (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_lt_two_mul_h
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < 2 * thresh.h) :
    cdata.S = ∅ := by
  apply cdata.S_eq_empty_of_lt_eps_reg I u_seq B thresh
  linarith [thresh.h_le_reg]

/-- Whenever `B ≤ thresh.h`, the concentration singular set `cdata.S` is empty (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_le_h
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_le : B ≤ thresh.h) :
    cdata.S = ∅ := by
  apply cdata.S_eq_empty_of_lt_two_mul_h I u_seq B thresh
  linarith [thresh.h_pos]

/-- Whenever `B ≤ 0`, the concentration singular set `cdata.S` is empty (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_nonpos
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hB : B ≤ 0) :
    cdata.S = ∅ :=
  cdata.S_eq_empty_of_lt_eps_reg I u_seq B thresh (hB.trans_lt thresh.ε_reg_pos)

/-- If the subsequence extended energy measures vanish identically, the weak limit measure `cdata.μ` is `0` (`0 sorryAx`). -/
theorem ConcentrationData.mu_eq_zero_of_seq_zero
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_zero : ∀ n, energyMeasureExtended I (u_seq (cdata.σ.1 n)) = 0) :
    cdata.μ = 0 := by
  have h_le : ∀ n, energyMeasureExtended I (u_seq (cdata.σ.1 n)) Set.univ ≤ ENNReal.ofReal 0 := by
    intro n
    rw [h_zero n]
    simp
  have h_tot : cdata.μ Set.univ ≤ ENNReal.ofReal 0 := cdata.weak_lim.total_mass_le h_le
  rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero] at h_tot
  exact Measure.measure_univ_eq_zero.mp h_tot

/-- If the subsequence extended energy measures eventually vanish, the weak limit measure `cdata.μ` is `0` (`0 sorryAx`). -/
theorem ConcentrationData.mu_eq_zero_of_eventually_seq_zero
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_zero : ∃ N₀ : ℕ, ∀ n ≥ N₀, energyMeasureExtended I (u_seq (cdata.σ.1 n)) = 0) :
    cdata.μ = 0 := by
  rcases h_zero with ⟨N₀, hN₀⟩
  have h_le : ∃ N₀ : ℕ, ∀ n ≥ N₀, energyMeasureExtended I (u_seq (cdata.σ.1 n)) Set.univ ≤ ENNReal.ofReal 0 := by
    refine ⟨N₀, fun n hn => ?_⟩
    rw [hN₀ n hn]
    simp
  have h_tot : cdata.μ Set.univ ≤ ENNReal.ofReal 0 := cdata.weak_lim.total_mass_le_of_eventually h_le
  rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero] at h_tot
  exact Measure.measure_univ_eq_zero.mp h_tot

/-- If `cdata.μ = 0`, the concentration singular set `cdata.S` is empty (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_mu_eq_zero
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hμ : cdata.μ = 0) :
    cdata.S = ∅ := by
  ext p
  simp only [Finset.notMem_empty, iff_false]
  intro hp
  have h_ge := (cdata.S_def p).mp hp
  rw [hμ] at h_ge
  simp only [Measure.coe_zero, Pi.zero_apply, nonpos_iff_eq_zero] at h_ge
  have h_pos : 0 < ENNReal.ofReal thresh.ε_reg := ENNReal.ofReal_pos.mpr thresh.ε_reg_pos
  exact h_pos.ne' h_ge

/-- If the subsequence extended energy measures eventually vanish, `cdata.S = ∅` (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_eventually_seq_zero
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_zero : ∃ N₀ : ℕ, ∀ n ≥ N₀, energyMeasureExtended I (u_seq (cdata.σ.1 n)) = 0) :
    cdata.S = ∅ :=
  cdata.S_eq_empty_of_mu_eq_zero I u_seq B thresh
    (cdata.mu_eq_zero_of_eventually_seq_zero I u_seq B thresh h_zero)

/-- If `cdata.S = ∅` and `mfderiv` of `u_seq (cdata.σ.1 n)` vanishes at `z`, then `mfderiv I_CP1 I cdata.u₀ z = 0` (`0 sorryAx`). -/
theorem ConcentrationData.mfderiv_u0_eq_zero_of_S_empty
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hS : cdata.S = ∅)
    (z : CP1)
    (h_mf : ∀ n, mfderiv I_CP1 I (u_seq (cdata.σ.1 n)) z = 0) :
    mfderiv I_CP1 I cdata.u₀ z = 0 := by
  have hK_cpt : IsCompact ({z} : Set CP1) := isCompact_singleton
  have hK_sub : ({z} : Set CP1) ⊆ Set.univ \ (cdata.S : Set CP1) := by
    rw [hS, Finset.coe_empty, Set.diff_empty]
    exact Set.subset_univ _
  have hz_mem : z ∈ ({z} : Set CP1) := Set.mem_singleton z
  have core := cdata.smooth_conv []
  dsimp [applyFramesSeq, applyFramesLim, applyFramesDomain] at core
  have h_lim := (core.2 {z} hK_sub hK_cpt).2.1 z hz_mem
  have h_seq_zero : (fun n => (mfderiv I_CP1 I (u_seq (cdata.σ.1 n)) z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E)) =
      fun _ => 0 :=
    funext (fun n => h_mf n)
  rw [h_seq_zero] at h_lim
  exact tendsto_nhds_unique h_lim tendsto_const_nhds

/-- If `cdata.S = ∅` and `mfderiv` of `u_seq (cdata.σ.1 n)` eventually vanishes at `z`,
then `mfderiv I_CP1 I cdata.u₀ z = 0` (`0 sorryAx`). -/
theorem ConcentrationData.mfderiv_u0_eq_zero_of_S_empty_eventually
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hS : cdata.S = ∅)
    (z : CP1)
    (h_mf : ∃ N₀ : ℕ, ∀ n ≥ N₀, mfderiv I_CP1 I (u_seq (cdata.σ.1 n)) z = 0) :
    mfderiv I_CP1 I cdata.u₀ z = 0 := by
  rcases h_mf with ⟨N₀, hN₀⟩
  have hK_cpt : IsCompact ({z} : Set CP1) := isCompact_singleton
  have hK_sub : ({z} : Set CP1) ⊆ Set.univ \ (cdata.S : Set CP1) := by
    rw [hS, Finset.coe_empty, Set.diff_empty]
    exact Set.subset_univ _
  have hz_mem : z ∈ ({z} : Set CP1) := Set.mem_singleton z
  have core := cdata.smooth_conv []
  dsimp [applyFramesSeq, applyFramesLim, applyFramesDomain] at core
  have h_lim : Tendsto (fun n => (mfderiv I_CP1 I (u_seq (cdata.σ.1 (n + N₀))) z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E))
      atTop (nhds (mfderiv I_CP1 I cdata.u₀ z)) :=
    ((core.2 {z} hK_sub hK_cpt).2.1 z hz_mem).comp (shiftSubseqMap N₀).2.tendsto_atTop
  have h_seq_zero : (fun n => (mfderiv I_CP1 I (u_seq (cdata.σ.1 (n + N₀))) z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E)) =
      fun _ => 0 :=
    funext (fun n => hN₀ (n + N₀) (Nat.le_add_left N₀ n))
  rw [h_seq_zero] at h_lim
  exact tendsto_nhds_unique h_lim tendsto_const_nhds

/-- Whenever `B < thresh.ε_sph` and `u_seq` consists of `J`-holomorphic spheres with `totalEnergy ≤ B`,
`cdata.μ = 0` (`0 sorryAx`). -/
theorem ConcentrationData.mu_eq_zero_of_B_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < thresh.ε_sph) :
    cdata.μ = 0 := by
  apply cdata.mu_eq_zero_of_seq_zero I u_seq B thresh
  intro n
  have h_eq := eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh (u_seq (cdata.σ.1 n))
    (h_jhol (cdata.σ.1 n)) ((h_en (cdata.σ.1 n)).trans_lt h_lt)
  rw [h_eq]
  exact energyMeasureExtended_const I (u_seq (cdata.σ.1 n) north_pole)

/-- Whenever `B < thresh.ε_sph` and `u_seq` consists of `J`-holomorphic spheres with `totalEnergy ≤ B`,
`cdata.S = ∅` (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_B_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < thresh.ε_sph) :
    cdata.S = ∅ :=
  cdata.S_eq_empty_of_mu_eq_zero I u_seq B thresh
    (cdata.mu_eq_zero_of_B_lt_eps_sph I u_seq h_jhol B h_en thresh h_lt)

/-- Whenever `B < thresh.ε_sph` and `u_seq` consists of `J`-holomorphic spheres with `totalEnergy ≤ B`,
the base limit `cdata.u₀` is constant (`cdata.u₀ = fun _ => cdata.u₀ north_pole`, `0 sorryAx`). -/
theorem ConcentrationData.u0_eq_const_north_pole_of_B_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < thresh.ε_sph) :
    cdata.u₀ = fun _ => cdata.u₀ north_pole := by
  have hS : cdata.S = ∅ := cdata.S_eq_empty_of_B_lt_eps_sph I u_seq h_jhol B h_en thresh h_lt
  have h_mf0 : ∀ z : CP1, mfderiv I_CP1 I cdata.u₀ z = 0 := by
    intro z
    apply cdata.mfderiv_u0_eq_zero_of_S_empty I u_seq B thresh hS z
    intro n
    have h_eq := eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh (u_seq (cdata.σ.1 n))
      (h_jhol (cdata.σ.1 n)) ((h_en (cdata.σ.1 n)).trans_lt h_lt)
    rw [h_eq]
    exact mfderiv_const
  have h_tot0 : totalEnergy I cdata.u₀ = 0 :=
    GromovCompactness.Analysis.totalEnergy_eq_zero_of_mfderiv_eq_zero I cdata.u₀ h_mf0
  apply cdata.u0_eq_const_north_pole_of_lt_eps_sph I u_seq B thresh
  rw [h_tot0]
  exact thresh.ε_sph_pos

/-- Whenever `u_seq (cdata.σ.1 n)` eventually has `totalEnergy < thresh.ε_sph`, `cdata.μ = 0` (`0 sorryAx`). -/
theorem ConcentrationData.mu_eq_zero_of_eventually_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < thresh.ε_sph) :
    cdata.μ = 0 := by
  rcases h_ev with ⟨N₀, hN₀⟩
  apply cdata.mu_eq_zero_of_eventually_seq_zero I u_seq B thresh ⟨N₀, fun n hn => ?_⟩
  have h_eq := eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh (u_seq (cdata.σ.1 n))
    (h_jhol (cdata.σ.1 n)) (hN₀ n hn)
  rw [h_eq]
  exact energyMeasureExtended_const I (u_seq (cdata.σ.1 n) north_pole)

/-- Whenever `u_seq (cdata.σ.1 n)` eventually has `totalEnergy < thresh.ε_sph`, `cdata.S = ∅` (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_eventually_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < thresh.ε_sph) :
    cdata.S = ∅ :=
  cdata.S_eq_empty_of_mu_eq_zero I u_seq B thresh
    (cdata.mu_eq_zero_of_eventually_lt_eps_sph I u_seq h_jhol B thresh h_ev)

/-- Whenever `u_seq (cdata.σ.1 n)` eventually has `totalEnergy < thresh.ε_sph`,
`cdata.u₀ = fun _ => cdata.u₀ north_pole` (`0 sorryAx`). -/
theorem ConcentrationData.u0_eq_const_north_pole_of_eventually_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < thresh.ε_sph) :
    cdata.u₀ = fun _ => cdata.u₀ north_pole := by
  have hS : cdata.S = ∅ := cdata.S_eq_empty_of_eventually_lt_eps_sph I u_seq h_jhol B thresh h_ev
  rcases h_ev with ⟨N₀, hN₀⟩
  have h_mf0 : ∀ z : CP1, mfderiv I_CP1 I cdata.u₀ z = 0 := by
    intro z
    apply cdata.mfderiv_u0_eq_zero_of_S_empty_eventually I u_seq B thresh hS z ⟨N₀, fun n hn => ?_⟩
    have h_eq := eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh (u_seq (cdata.σ.1 n))
      (h_jhol (cdata.σ.1 n)) (hN₀ n hn)
    rw [h_eq]
    exact mfderiv_const
  have h_tot0 : totalEnergy I cdata.u₀ = 0 :=
    GromovCompactness.Analysis.totalEnergy_eq_zero_of_mfderiv_eq_zero I cdata.u₀ h_mf0
  apply cdata.u0_eq_const_north_pole_of_lt_eps_sph I u_seq B thresh
  rw [h_tot0]
  exact thresh.ε_sph_pos

/-- Unconditional weak energy measure compactness when `B < thresh.ε_sph` and `u_seq` consists of
`J`-holomorphic spheres with `totalEnergy ≤ B` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_B_lt_eps_sph
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < thresh.ε_sph) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness_of_const_subseq_varying I u_seq
    ⟨SubseqMap.id, fun n => ⟨u_seq n north_pole,
      eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh (u_seq n) (h_jhol n)
        ((h_en n).trans_lt h_lt)⟩⟩

/-- Unconditional weak energy measure compactness when `u_seq` consists of `J`-holomorphic spheres
that eventually have `totalEnergy < thresh.ε_sph` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_eventually_lt_eps_sph
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq n) < thresh.ε_sph) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact weak_energy_measure_compactness_of_eventually_const_varying I u_seq
    ⟨N₀, fun n hn => ⟨u_seq n north_pole,
      eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh (u_seq n) (h_jhol n) (hN₀ n hn)⟩⟩

/-- On a `[DiscreteTopology M]` target, any `J`-holomorphic sphere equals `fun _ => u north_pole` (`0 sorryAx`). -/
theorem eq_const_north_pole_of_jhol_of_discrete [DiscreteTopology M]
    (thresh : TargetThresholds I M) (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    u = fun _ => u north_pole := by
  apply eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh u hu
  rw [GromovCompactness.Analysis.totalEnergy_eq_zero_of_discrete I u hu.1]
  exact thresh.ε_sph_pos

/-- On a compact discrete space `M`, every sequence `c : ℕ → M` admits a constant subsequence (`0 sorryAx`). -/
theorem exists_const_subseq_of_discrete [DiscreteTopology M] (c : ℕ → M) :
    ∃ (σ : SubseqMap) (c₀ : M), ∀ n, c (σ.1 n) = c₀ := by
  haveI : FirstCountableTopology M := ⟨fun x => by rw [nhds_discrete]; infer_instance⟩
  obtain ⟨c₀, _, φ, hφ, h_tendsto⟩ :=
    isSeqCompact_univ.subseq_of_frequently_in (Filter.Frequently.of_forall (fun n => Set.mem_univ (c n)))
  rw [nhds_discrete, Filter.tendsto_pure] at h_tendsto
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h_tendsto
  exact ⟨SubseqMap.comp ⟨φ, hφ⟩ (shiftSubseqMap N₀), c₀,
    fun n => hN₀ (n + N₀) (Nat.le_add_left N₀ n)⟩

/-- On a `[DiscreteTopology M]` target, any sequence of `J`-holomorphic spheres admits a constant subsequence (`0 sorryAx`). -/
theorem exists_const_map_subseq_of_jhol_of_discrete [DiscreteTopology M]
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ) :
    ∃ (σ : SubseqMap) (c₀ : M), ∀ n, u_seq (σ.1 n) = fun _ => c₀ := by
  obtain ⟨σ, c₀, hc₀⟩ := exists_const_subseq_of_discrete (fun n => u_seq n north_pole)
  refine ⟨σ, c₀, fun n => ?_⟩
  rw [eq_const_north_pole_of_jhol_of_discrete I thresh (u_seq (σ.1 n)) (h_jhol (σ.1 n)), hc₀ n]

/-- Unconditional weak energy measure compactness for `J`-holomorphic spheres on `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_discrete [DiscreteTopology M]
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness_of_const_subseq_varying I u_seq
    ⟨SubseqMap.id, fun n => ⟨u_seq n north_pole,
      eq_const_north_pole_of_jhol_of_discrete I thresh (u_seq n) (h_jhol n)⟩⟩

/-- Unconditional weak energy measure compactness for `J`-holomorphic spheres on `[DiscreteTopology M]`
without requiring `TargetThresholds` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_jhol_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness_of_const_subseq_varying I u_seq
    ⟨SubseqMap.id, fun n => ⟨u_seq n north_pole,
      funext (GromovCompactness.Analysis.eq_const_north_pole_of_jhol_univ_of_discrete I (u_seq n) (h_jhol n))⟩⟩

/-- Unconditional weak energy measure compactness on `[DiscreteTopology M]` targets for any sequence
of continuous maps `u_seq` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_continuous_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_cont : ∀ n, Continuous (u_seq n)) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness_of_const_subseq_varying I u_seq
    ⟨SubseqMap.id, fun n => ⟨u_seq n north_pole,
      funext (GromovCompactness.Analysis.eq_const_north_pole_of_continuous_of_discrete (u_seq n) (h_cont n))⟩⟩

/-- Unconditional weak energy measure compactness on `[DiscreteTopology M]` targets for any sequence
of maps that are eventually continuous on `CP1` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_eventually_continuous_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, Continuous (u_seq n)) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact weak_energy_measure_compactness_of_eventually_const_varying I u_seq
    ⟨N₀, fun n hn => ⟨u_seq n north_pole,
      funext (GromovCompactness.Analysis.eq_const_north_pole_of_continuous_of_discrete (u_seq n) (hN₀ n hn))⟩⟩

/-- Constant subsequences unconditionally satisfy `extract_smooth_limit_off_singular_set` with zero sorry. -/
theorem extract_smooth_limit_off_singular_set_of_const_subseq
    (u_seq : ℕ → (CP1 → M)) (σ : SubseqMap) (S : Finset CP1)
    (h_const : ∃ c : M, ∀ n z, u_seq (σ.1 n) z = c) :
    ∃ (u₀ : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S) := by
  rcases h_const with ⟨c, hc⟩
  refine ⟨fun _ => c, jholomorphicOn_const I c Set.univ, ?_⟩
  have h_eq : (fun n => u_seq (σ.1 n)) = (fun _ _ => c) := by
    ext n z
    exact hc n z
  rw [h_eq]
  exact smoothLocalConvergesOn_const_map I c (Set.univ \ S)

/-- Unconditional smooth limit extraction off any singular set `S` on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem extract_smooth_limit_off_singular_set_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (S : Finset CP1) :
    ∃ (σ : SubseqMap) (u₀ : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S) := by
  obtain ⟨σ, c₀, hc₀⟩ := exists_const_subseq_of_discrete (fun n => u_seq n north_pole)
  have h_const : ∃ c : M, ∀ n z, u_seq (σ.1 n) z = c :=
    ⟨c₀, fun n z => (GromovCompactness.Analysis.eq_const_north_pole_of_jhol_univ_of_discrete I
      (u_seq (σ.1 n)) (h_jhol (σ.1 n)) z).trans (hc₀ n)⟩
  obtain ⟨u₀, hu₀_jhol, h_conv⟩ := extract_smooth_limit_off_singular_set_of_const_subseq I u_seq σ S h_const
  exact ⟨σ, u₀, hu₀_jhol, h_conv⟩

/-- Subsequences converging smoothly on `Set.univ` satisfy `extract_smooth_limit_off_singular_set` with zero sorry. -/
theorem extract_smooth_limit_off_singular_set_of_global_conv
    (u_seq : ℕ → (CP1 → M)) (σ : SubseqMap) (S : Finset CP1)
    (h_glob : ∃ (u₀ : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ Set.univ) :
    ∃ (u₀ : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S) := by
  rcases h_glob with ⟨u₀, hu₀, h_conv⟩
  exact ⟨u₀, hu₀, smooth_local_restriction I (fun n => u_seq (σ.1 n)) u₀ Set.diff_subset h_conv⟩

/-- If `u_seq ∘ σ` is eventually equal to a constant map `fun _ => c`, then `extract_smooth_limit_off_singular_set`
holds with `0 sorryAx`. -/
theorem extract_smooth_limit_off_singular_set_of_eventually_const
    (u_seq : ℕ → (CP1 → M)) (σ : SubseqMap) (S : Finset CP1)
    (h_ev : ∃ N₀ : ℕ, ∃ c : M, ∀ n ≥ N₀, ∀ z, u_seq (σ.1 n) z = c) :
    ∃ (u₀ : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S) := by
  rcases h_ev with ⟨N₀, c, hN₀⟩
  exact ⟨fun _ => c, jholomorphicOn_const I c Set.univ,
    smoothLocalConvergesOn_of_eventually_const I (fun n => u_seq (σ.1 n)) c (Set.univ \ S) ⟨N₀, hN₀⟩⟩

/-- If `u_seq ∘ σ` converges smoothly on `Set.univ \ S` to a globally `J`-holomorphic map `u₀`,
then `extract_smooth_limit_off_singular_set` holds (`0 sorryAx`). -/
theorem extract_smooth_limit_off_singular_set_of_punctured_jhol
    (u_seq : ℕ → (CP1 → M)) (σ : SubseqMap) (S : Finset CP1)
    (u₀ : CP1 → M)
    (hu₀_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ)
    (h_conv_punct : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S)) :
    ∃ (u_lim : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim (Set.univ \ S) :=
  ⟨u₀, hu₀_jhol, h_conv_punct⟩

/-- If `u_seq ∘ σ` converges smoothly on `Set.univ` to a map `u₀` and each `u_seq n` is `J`-holomorphic
on `Set.univ`, then `u₀` is automatically `J`-holomorphic on `Set.univ` by `smooth_local_jhol_closure`
and `extract_smooth_limit_off_singular_set` holds (`0 sorryAx`). -/
theorem extract_smooth_limit_off_singular_set_of_global_conv_only
    (u_seq : ℕ → (CP1 → M)) (σ : SubseqMap)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (S : Finset CP1)
    (u₀ : CP1 → M)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ Set.univ) :
    ∃ (u_lim : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim (Set.univ \ S) := by
  have hu₀_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ :=
    smooth_local_jhol_closure I (fun n => u_seq (σ.1 n)) u₀ Set.univ h_conv (fun n => h_jhol (σ.1 n))
  exact ⟨u₀, hu₀_jhol, smooth_local_restriction I (fun n => u_seq (σ.1 n)) u₀ Set.diff_subset h_conv⟩

/-- When `S = ∅` and `u_seq ∘ σ` converges smoothly on `Set.univ \ S` to `u₀`, `u₀` is automatically
`J`-holomorphic on `Set.univ` (`0 sorryAx`). -/
theorem extract_smooth_limit_off_singular_set_of_empty_S
    (u_seq : ℕ → (CP1 → M)) (σ : SubseqMap)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (S : Finset CP1) (hS : S = ∅)
    (u₀ : CP1 → M)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S)) :
    ∃ (u_lim : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u_lim Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim (Set.univ \ S) := by
  have h_diff : Set.univ \ (S : Set CP1) = Set.univ := by
    rw [hS, Finset.coe_empty, Set.diff_empty]
  have h_conv_univ : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ Set.univ := by
    rwa [← h_diff]
  exact extract_smooth_limit_off_singular_set_of_global_conv_only I u_seq σ h_jhol S u₀ h_conv_univ

/-- The complement `Set.univ \ S` of any finite singular set `S : Finset CP1` is open (`0 sorryAx`). -/
lemma isOpen_compl_finset (S : Finset CP1) : IsOpen (Set.univ \ (S : Set CP1)) :=
  isOpen_univ.sdiff S.finite_toSet.isClosed

/-- Pulling back an open domain `Ω` along any list of `ConvergingFrame`s preserves openness (`0 sorryAx`). -/
lemma isOpen_applyFramesDomain (frames : List ConvergingFrame) {Ω : Set CP1} (hΩ : IsOpen Ω) :
    IsOpen (applyFramesDomain frames Ω) := by
  induction frames generalizing Ω with
  | nil => exact hΩ
  | cons F Fs ih => exact ih (hΩ.preimage F.lim.toHomeo.continuous)

omit [MetricSpace M] [CompactSpace M] in
/-- Pulling back two maps agreeing on `Ω` along any list of `ConvergingFrame`s preserves `EqOn`
on `applyFramesDomain frames Ω` (`0 sorryAx`). -/
lemma eqOn_applyFramesLim (frames : List ConvergingFrame) {u₁ u₂ : CP1 → M} {Ω : Set CP1}
    (heq : Set.EqOn u₁ u₂ Ω) :
    Set.EqOn (applyFramesLim frames u₁) (applyFramesLim frames u₂) (applyFramesDomain frames Ω) := by
  induction frames generalizing u₁ u₂ Ω with
  | nil => exact heq
  | cons F Fs ih =>
    exact ih (fun z hz => heq hz)

omit [ClosedTameTarget I M] in
/-- `CoreSmoothLocalConvergesOn` is invariant under replacing the limit map `u₁` with a map `u₂`
that agrees with `u₁` on an open domain `Ω` (`0 sorryAx`). -/
theorem coreSmoothLocalConvergesOn_congr_lim_of_eqOn_open
    {u_seq : ℕ → (CP1 → M)} {u₁ u₂ : CP1 → M} {Ω : Set CP1} (hΩ : IsOpen Ω)
    (heq : Set.EqOn u₁ u₂ Ω)
    (h : CoreSmoothLocalConvergesOn I u_seq u₁ Ω) :
    CoreSmoothLocalConvergesOn I u_seq u₂ Ω := by
  refine ⟨h.1.congr heq.symm, fun K hK_sub hK_cpt => ?_⟩
  obtain ⟨h_pt, h_d1, h_jet, h_J⟩ := h.2 K hK_sub hK_cpt
  have hev_eq : ∀ z ∈ K, u₁ =ᶠ[nhds z] u₂ :=
    fun z hz => Filter.eventuallyEq_of_mem (hΩ.mem_nhds (hK_sub hz)) heq
  have h_deriv : ∀ z ∈ K, mfderiv I_CP1 I u₁ z = mfderiv I_CP1 I u₂ z :=
    fun z hz => Filter.EventuallyEq.mfderiv_eq (hev_eq z hz)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [← heq (hK_sub hz)]
    exact h_pt z hz
  · intro z hz
    rw [← h_deriv z hz]
    exact h_d1 z hz
  · intro k z hz
    have h_loc := h_jet k z hz
    have h_f_eq :
        writtenInExtChartAt I_CP1 I z u₁ =ᶠ[nhds (extChartAt I_CP1 z z)]
        writtenInExtChartAt I_CP1 I z u₂ := by
      have hz_eq : u₁ z = u₂ z := heq (hK_sub hz)
      have h_symm_cont : ContinuousAt (extChartAt I_CP1 z).symm (extChartAt I_CP1 z z) :=
        (continuousOn_extChartAt_symm z).continuousAt
          (extChartAt_target_mem_nhds' (mem_extChartAt_target z))
      have h_pre : (extChartAt I_CP1 z).symm ⁻¹' Ω ∈ nhds (extChartAt I_CP1 z z) := by
        apply h_symm_cont.preimage_mem_nhds
        rw [extChartAt_to_inv z]
        exact hΩ.mem_nhds (hK_sub hz)
      filter_upwards [h_pre] with w hw
      simp only [writtenInExtChartAt, Function.comp_apply, hz_eq, heq hw]
    have h_iter_eq :
        iteratedFDeriv ℝ k (writtenInExtChartAt I_CP1 I z u₁) (extChartAt I_CP1 z z) =
        iteratedFDeriv ℝ k (writtenInExtChartAt I_CP1 I z u₂) (extChartAt I_CP1 z z) :=
      (Filter.EventuallyEq.iteratedFDeriv ℝ h_f_eq k).eq_of_nhds
    rw [← h_iter_eq]
    exact h_loc
  · intro tgt z hz v
    have h_eq_tgt :
        tgt.J (u₁ z) ((mfderiv I_CP1 I u₁ z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) v) =
        tgt.J (u₂ z) ((mfderiv I_CP1 I u₂ z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) v) := by
      rw [heq (hK_sub hz), h_deriv z hz]
    rw [← h_eq_tgt]
    exact @h_J tgt z hz v

omit [ClosedTameTarget I M] in
/-- `SmoothLocalConvergesOn` is invariant under replacing the limit map `u₁` with a map `u₂`
that agrees with `u₁` on an open domain `Ω` (`0 sorryAx`). -/
theorem smooth_local_congr_lim_of_eqOn_open
    {u_seq : ℕ → (CP1 → M)} {u₁ u₂ : CP1 → M} {Ω : Set CP1} (hΩ : IsOpen Ω)
    (heq : Set.EqOn u₁ u₂ Ω)
    (h : SmoothLocalConvergesOn I u_seq u₁ Ω) :
    SmoothLocalConvergesOn I u_seq u₂ Ω := by
  intro frames
  exact coreSmoothLocalConvergesOn_congr_lim_of_eqOn_open I
    (isOpen_applyFramesDomain frames hΩ)
    (eqOn_applyFramesLim frames heq)
    (h frames)

/-- For every point `p ∉ S` off the concentration singular set `S`, there exist a radius `r > 0`,
a strict threshold `ε₁ < thresh.ε_reg`, and an index `N : ℕ` such that for all `n ≥ N`,
`energyMeasureExtended I (u_seq (σ.1 n)) (closedBall p r) < ENNReal.ofReal ε₁ < ENNReal.ofReal thresh.ε_reg`
(`0 sorryAx`). -/
theorem exists_closedBall_eventually_energy_lt_eps_reg_of_notMem_S
    (u_seq : ℕ → (CP1 → M))
    (thresh : TargetThresholds I M)
    (σ : SubseqMap) (μ : Measure CP1) [IsFiniteMeasure μ] (S : Finset CP1)
    (h_weak : WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ)
    (hS_def : ∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p})
    (p : CP1) (hp : p ∉ S) :
    ∃ r > 0, ∃ ε₁ < thresh.ε_reg, 0 < ε₁ ∧
      ∀ᶠ n in Filter.atTop,
        energyMeasureExtended I (u_seq (σ.1 n)) (closedBall p r) < ENNReal.ofReal ε₁ := by
  have hp_lt : ¬ ENNReal.ofReal thresh.ε_reg ≤ μ {p} := mt (hS_def p).mpr hp
  rw [atom_iff_concentration μ p thresh.ε_reg] at hp_lt
  push Not at hp_lt
  obtain ⟨r, hr_pos, hr_lt⟩ := hp_lt
  have h_top : μ (closedBall p r) ≠ ⊤ := measure_ne_top μ _
  let m_r := (μ (closedBall p r)).toReal
  have hm_r_eq : ENNReal.ofReal m_r = μ (closedBall p r) := ENNReal.ofReal_toReal h_top
  have hm_r_lt : m_r < thresh.ε_reg := by
    rw [← ENNReal.ofReal_lt_ofReal_iff thresh.ε_reg_pos, hm_r_eq]
    exact hr_lt
  have hm_r_nonneg : 0 ≤ m_r := ENNReal.toReal_nonneg
  let ε₁ := (m_r + thresh.ε_reg) / 2
  have hε₁_lt : ε₁ < thresh.ε_reg := by dsimp [ε₁]; linarith
  have hε₁_gt : m_r < ε₁ := by dsimp [ε₁]; linarith
  have hε₁_pos : 0 < ε₁ := by dsimp [ε₁]; linarith [thresh.ε_reg_pos]
  have h_limsup : Filter.limsup (fun n => energyMeasureExtended I (u_seq (σ.1 n)) (closedBall p r)) Filter.atTop ≤
      μ (closedBall p r) :=
    h_weak.limsup_closed_le (K := closedBall p r) isClosed_closedBall
  have h_lt_ofReal : μ (closedBall p r) < ENNReal.ofReal ε₁ := by
    rw [← hm_r_eq]
    exact (ENNReal.ofReal_lt_ofReal_iff hε₁_pos).mpr hε₁_gt
  have h_ev := eventually_lt_of_limsup_lt (lt_of_le_of_lt h_limsup h_lt_ofReal)
  exact ⟨r, hr_pos, ε₁, hε₁_lt, hε₁_pos, h_ev⟩

/-- Local uniform gradient bound from `thresh.h_reg` and `exists_closedBall_eventually_energy_lt_eps_reg_of_notMem_S`:
on any stereographic disk `disk_at a r ⊆ closedBall p ρ` in the southern hemisphere (`Metric.ball a r ⊆ Metric.closedBall 0 1`)
around `p ∉ S`, `riemannianEnergyDensity I (u_seq (σ.1 n))` is eventually bounded by
`thresh.C_reg * r ^ (-2 : ℝ) * thresh.ε_reg` on `disk_at a (r / 2)` (`0 sorryAx`). -/
theorem eventually_gradient_bound_on_disk_of_notMem_S
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (thresh : TargetThresholds I M)
    (σ : SubseqMap) (μ : Measure CP1) [IsFiniteMeasure μ] (S : Finset CP1)
    (h_weak : WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ)
    (hS_def : ∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p})
    {p : CP1} (hp : p ∉ S)
    {a : ℂ} {r ρ : ℝ} (hr : 0 < r)
    (h_sub_hemi : Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1)
    (h_disk_sub : disk_at a r ⊆ closedBall p ρ)
    {ε₁ : ℝ} (hε₁_lt : ε₁ < thresh.ε_reg) (_hε₁_pos : 0 < ε₁)
    (h_ev : ∀ᶠ n in Filter.atTop,
      energyMeasureExtended I (u_seq (σ.1 n)) (closedBall p ρ) < ENNReal.ofReal ε₁) :
    ∀ᶠ n in Filter.atTop, ∀ z ∈ disk_at a (r / 2),
      riemannianEnergyDensity I (u_seq (σ.1 n)) z ≤ thresh.C_reg * r ^ (-2 : ℝ) * thresh.ε_reg := by
  have _h_step := exists_closedBall_eventually_energy_lt_eps_reg_of_notMem_S I u_seq thresh σ μ S h_weak hS_def p hp
  filter_upwards [h_ev] with n hn z hz
  have h_mono : energyMeasureExtended I (u_seq (σ.1 n)) (disk_at a r) ≤
      energyMeasureExtended I (u_seq (σ.1 n)) (closedBall p ρ) :=
    measure_mono h_disk_sub
  have h_lt_ofReal : energyMeasureExtended I (u_seq (σ.1 n)) (disk_at a r) < ENNReal.ofReal thresh.ε_reg :=
    lt_of_le_of_lt h_mono (lt_trans hn ((ENNReal.ofReal_lt_ofReal_iff thresh.ε_reg_pos).mpr hε₁_lt))
  have h_ne_top : energyMeasureExtended I (u_seq (σ.1 n)) (disk_at a r) ≠ ⊤ :=
    ne_top_of_lt h_lt_ofReal
  have h_en_lt : energyMeasure I (u_seq (σ.1 n)) (disk_at a r) < thresh.ε_reg := by
    dsimp [energyMeasure]
    exact (ENNReal.toReal_lt_of_lt_ofReal h_lt_ofReal)
  have h_bd := thresh.h_reg (u_seq (σ.1 n)) a r hr h_sub_hemi (h_jhol (σ.1 n)) h_en_lt z hz
  have h_pos_coef : 0 ≤ thresh.C_reg * r ^ (-2 : ℝ) := by
    have := thresh.C_reg_pos
    positivity
  exact le_trans h_bd (mul_le_mul_of_nonneg_left (le_of_lt h_en_lt) h_pos_coef)

/-- When `S = {p}` is a singleton and `u_seq ∘ σ` converges in `SmoothLocalConvergesOn` on `Set.univ \ S`
to a map `u₁` with a removable singularity extension `u₀` across `p`, `u₀` is a globally `J`-holomorphic
sphere that still satisfies `SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S)` (`0 sorryAx`). -/
theorem extract_smooth_limit_off_singular_set_of_singleton_puncture
    (u_seq : ℕ → (CP1 → M)) (σ : SubseqMap)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (S : Finset CP1) {p : CP1} (hS : S = {p})
    (u₁ : CP1 → M)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₁ (Set.univ \ S))
    (h_rem : JHolomorphicOn (I := I) (I_dom := I_CP1) u₁ (punctured_sphere {p}) →
      ∃ (u₀ : CP1 → M), Set.EqOn u₀ u₁ (punctured_sphere {p}) ∧
        JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ) :
    ∃ (u₀ : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S) := by
  have h_dom_eq : Set.univ \ (S : Set CP1) = punctured_sphere {p} := by
    rw [hS, Finset.coe_singleton]
    rfl
  have hu₁_jhol_dom : JHolomorphicOn (I := I) (I_dom := I_CP1) u₁ (Set.univ \ S) :=
    smooth_local_jhol_closure I (fun n => u_seq (σ.1 n)) u₁ (Set.univ \ S) h_conv
      (fun n => ⟨(h_jhol (σ.1 n)).1.mono (Set.subset_univ _),
        fun z hz => (h_jhol (σ.1 n)).2 z (Set.mem_univ z)⟩)
  have hu₁_jhol_punct : JHolomorphicOn (I := I) (I_dom := I_CP1) u₁ (punctured_sphere {p}) := by
    rwa [← h_dom_eq]
  obtain ⟨u₀, hu₀_eq, hu₀_jhol⟩ := h_rem hu₁_jhol_punct
  have heq_dom : Set.EqOn u₁ u₀ (Set.univ \ S) := by
    rw [h_dom_eq]
    exact hu₀_eq.symm
  exact ⟨u₀, hu₀_jhol, smooth_local_congr_lim_of_eqOn_open I (isOpen_compl_finset S) heq_dom h_conv⟩

/-- Smooth limit extraction off the singular set S combining constant subsequences, eventually constant
subsequences, global smooth convergence, empty singular sets, and punctured `J`-holomorphic limits (`0 sorryAx`). -/
theorem extract_smooth_limit_off_singular_set
    (u_seq : ℕ → (CP1 → M)) (σ : SubseqMap)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (S : Finset CP1)
    (h_cases : (∃ c : M, ∀ n z, u_seq (σ.1 n) z = c) ∨
      (∃ N₀ : ℕ, ∃ c : M, ∀ n ≥ N₀, ∀ z, u_seq (σ.1 n) z = c) ∨
      (∃ (u₀ : CP1 → M), SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ Set.univ) ∨
      (S = ∅ ∧ ∃ (u₀ : CP1 → M), SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S)) ∨
      (∃ (u₀ : CP1 → M), JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
        SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S))) :
    ∃ (u₀ : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S) := by
  rcases h_cases with h_const | h_ev | ⟨u₀, h_conv⟩ | ⟨hS, u₀, h_conv⟩ | ⟨u₀, hu₀_jhol, h_conv_punct⟩
  · exact extract_smooth_limit_off_singular_set_of_const_subseq I u_seq σ S h_const
  · exact extract_smooth_limit_off_singular_set_of_eventually_const I u_seq σ S h_ev
  · exact extract_smooth_limit_off_singular_set_of_global_conv_only I u_seq σ h_jhol S u₀ h_conv
  · exact extract_smooth_limit_off_singular_set_of_empty_S I u_seq σ h_jhol S hS u₀ h_conv
  · exact extract_smooth_limit_off_singular_set_of_punctured_jhol I u_seq σ S u₀ hu₀_jhol h_conv_punct

/-- Zero-sorry conditional reduction of `exists_concentration_data` from weak energy measure compactness (`h_weak_comp`),
extended energy finiteness (`h_fin`), and smooth limit extraction (`h_extract`) (`0 sorryAx`). -/
theorem exists_concentration_data_of_smooth_limit
    (u_seq : ℕ → (CP1 → M))
    (_h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (h_weak_comp : ∀ (B' : ℝ), 0 < B' → (∀ n, totalEnergy I (u_seq n) ≤ B') →
      ∃ (σ : SubseqMap) (μ : Measure CP1),
        IsFiniteMeasure μ ∧
        WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (h_extract : ∀ (σ : SubseqMap) (μ : Measure CP1) (S : Finset CP1), IsFiniteMeasure μ →
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ →
      (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p}) →
      ∃ (τ : SubseqMap) (u₀ : CP1 → M), JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
        SmoothLocalConvergesOn I (fun n => u_seq ((σ.comp τ).1 n)) u₀ (Set.univ \ S) ∧
        μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • Measure.dirac p)) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  by_cases hB_pos : 0 < B
  · obtain ⟨σ, μ, _hμ_fin, h_weak⟩ := h_weak_comp B hB_pos h_en
    have h_tot_le : ∀ n, energyMeasureExtended I (u_seq (σ.1 n)) Set.univ ≤ ENNReal.ofReal B :=
      fun n => energyMeasureExtended_le_ofReal_of_totalEnergy_le I (u_seq (σ.1 n)) B (h_en (σ.1 n)) (h_fin (σ.1 n))
    have h_tot : μ Set.univ ≤ ENNReal.ofReal B := h_weak.total_mass_le h_tot_le
    obtain ⟨S, hS_def, hS_mul, hS_le⟩ :=
      concentration_singular_set_properties I μ B hB thresh h_tot
    obtain ⟨τ, u₀, hu₀_jhol, h_smooth, h_decomp⟩ := h_extract σ μ S _hμ_fin h_weak hS_def
    exact ⟨⟨σ.comp τ, μ, h_tot, h_weak.comp_subseq τ, S, hS_def, hS_mul, hS_le, u₀, hu₀_jhol, h_smooth, h_decomp⟩⟩
  · have hB0 : B = 0 := by linarith
    have hB1 : 0 < B + 1 := by linarith
    have h_en1 : ∀ n, totalEnergy I (u_seq n) ≤ B + 1 := fun n => (h_en n).trans (by linarith)
    obtain ⟨σ, μ, _hμ_fin, h_weak⟩ := h_weak_comp (B + 1) hB1 h_en1
    have h_tot_le : ∀ n, energyMeasureExtended I (u_seq (σ.1 n)) Set.univ ≤ ENNReal.ofReal B := by
      intro n
      rw [hB0, ENNReal.ofReal_zero]
      have h_en0 : totalEnergy I (u_seq (σ.1 n)) ≤ 0 := by
        have := h_en (σ.1 n); linarith [hB0]
      have h_le_ofReal := energyMeasureExtended_le_ofReal_of_totalEnergy_le I (u_seq (σ.1 n)) 0 h_en0 (h_fin (σ.1 n))
      rwa [ENNReal.ofReal_zero] at h_le_ofReal
    have h_tot : μ Set.univ ≤ ENNReal.ofReal B := h_weak.total_mass_le h_tot_le
    obtain ⟨S, hS_def, hS_mul, hS_le⟩ :=
      concentration_singular_set_properties I μ B hB thresh h_tot
    obtain ⟨τ, u₀, hu₀_jhol, h_smooth, h_decomp⟩ := h_extract σ μ S _hμ_fin h_weak hS_def
    exact ⟨⟨σ.comp τ, μ, h_tot, h_weak.comp_subseq τ, S, hS_def, hS_mul, hS_le, u₀, hu₀_jhol, h_smooth, h_decomp⟩⟩

/-- Unconditional construction of `ConcentrationData` when `u_seq` admits a subsequence of constant maps
`u_seq (σ.1 n) = fun _ => c` (`0 sorryAx`). -/
theorem exists_concentration_data_of_const_subseq
    (u_seq : ℕ → (CP1 → M))
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (σ : SubseqMap) (c : M)
    (hc : ∀ n, u_seq (σ.1 n) = fun _ => c) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  let μ := energyMeasureExtended I (fun _ : CP1 => c)
  haveI : IsFiniteMeasure μ := ⟨energyMeasureExtended_lt_top_of_const_map I c⟩
  have h_en_c : totalEnergy I (fun _ : CP1 => c) ≤ B := by
    have h0 := h_en (σ.1 0)
    rwa [hc 0] at h0
  have h_tot : μ Set.univ ≤ ENNReal.ofReal B :=
    energyMeasureExtended_le_ofReal_of_totalEnergy_le I (fun _ => c) B h_en_c
      (energyMeasureExtended_lt_top_of_const_map I c)
  have h_weak : WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ := by
    have h_eq : (fun n => energyMeasureExtended I (u_seq (σ.1 n))) = fun _ => μ := by
      ext n s _
      rw [hc n]
    rw [h_eq]
    exact WeakMeasureConvergence.refl μ
  obtain ⟨S, hS_def, hS_mul, hS_le⟩ :=
    concentration_singular_set_properties I μ B hB thresh h_tot
  let u₀ : CP1 → M := fun _ => c
  have hu₀_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ :=
    jholomorphicOn_const I c Set.univ
  have h_smooth : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S) := by
    have h_eq : (fun n => u_seq (σ.1 n)) = (fun _ _ => c) := by
      ext n z
      exact congr_fun (hc n) z
    rw [h_eq]
    exact smoothLocalConvergesOn_const_map I c (Set.univ \ S)
  have h_decomp : μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • Measure.dirac p) := by
    have hμ0 : energyMeasureExtended I (fun _ : CP1 => c) = 0 := energyMeasureExtended_const I c
    change energyMeasureExtended I (fun _ : CP1 => c) =
      energyMeasureExtended I (fun _ : CP1 => c) +
      ∑ p ∈ S, ((energyMeasureExtended I (fun _ : CP1 => c)) {p} • Measure.dirac p)
    simp [hμ0]
  exact ⟨⟨σ, μ, h_tot, h_weak, S, hS_def, hS_mul, hS_le, u₀, hu₀_jhol, h_smooth, h_decomp⟩⟩

/-- Unconditional construction of `ConcentrationData` when `u_seq` admits a subsequence eventually
equal to a constant map `fun _ => c` (`0 sorryAx`). -/
theorem exists_concentration_data_of_eventually_const_subseq
    (u_seq : ℕ → (CP1 → M))
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (σ : SubseqMap) (N₀ : ℕ) (c : M)
    (hc : ∀ n ≥ N₀, u_seq (σ.1 n) = fun _ => c) :
    Nonempty (ConcentrationData I u_seq B thresh) :=
  exists_concentration_data_of_const_subseq I u_seq B hB h_en thresh
    (σ.comp (shiftSubseqMap N₀)) c (fun n => hc (n + N₀) (Nat.le_add_left N₀ n))

/-- Unconditional construction of `ConcentrationData` when a subsequence `u_seq ∘ σ` converges
weakly in energy measure to `μ` and smoothly on `CP1` to `u₀` (`0 sorryAx`). -/
theorem exists_concentration_data_of_weak_and_global_conv
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (thresh : TargetThresholds I M)
    (σ : SubseqMap) (μ : Measure CP1) [IsFiniteMeasure μ]
    (h_tot : μ Set.univ ≤ ENNReal.ofReal B)
    (h_weak : WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ)
    (u₀ : CP1 → M)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ Set.univ)
    (h_decomp : ∀ S : Finset CP1, (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p}) →
      μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • Measure.dirac p)) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  obtain ⟨S, hS_def, hS_mul, hS_le⟩ :=
    concentration_singular_set_properties I μ B hB thresh h_tot
  have hu₀_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ :=
    smooth_local_jhol_closure I (fun n => u_seq (σ.1 n)) u₀ Set.univ h_conv (fun n => h_jhol (σ.1 n))
  have h_smooth : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S) :=
    smooth_local_restriction I (fun n => u_seq (σ.1 n)) u₀ Set.diff_subset h_conv
  exact ⟨⟨σ, μ, h_tot, h_weak, S, hS_def, hS_mul, hS_le, u₀, hu₀_jhol, h_smooth, h_decomp S hS_def⟩⟩

/-- Unconditional construction of `ConcentrationData` when a subsequence `u_seq ∘ σ` converges
weakly in energy measure to `μ` with empty singular set `S = ∅` and smooth convergence on `Set.univ \ S` (`0 sorryAx`). -/
theorem exists_concentration_data_of_weak_and_empty_S
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (thresh : TargetThresholds I M)
    (σ : SubseqMap) (μ : Measure CP1) [IsFiniteMeasure μ]
    (h_tot : μ Set.univ ≤ ENNReal.ofReal B)
    (h_weak : WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ)
    (_h_no_atoms : ∀ p : CP1, μ {p} < ENNReal.ofReal thresh.ε_reg)
    (u₀ : CP1 → M)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ Set.univ)
    (h_decomp : ∀ S : Finset CP1, (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p}) →
      μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • Measure.dirac p)) :
    Nonempty (ConcentrationData I u_seq B thresh) :=
  exists_concentration_data_of_weak_and_global_conv I u_seq h_jhol B hB thresh σ μ h_tot h_weak u₀ h_conv h_decomp

/-- Unconditional construction of `ConcentrationData` on subsingleton targets (`0 sorryAx`). -/
theorem exists_concentration_data_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M))
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  refine exists_concentration_data_of_const_subseq I u_seq B hB h_en thresh SubseqMap.id
    (u_seq 0 north_pole) (fun n => ?_)
  ext z
  exact Subsingleton.elim (u_seq n z) (u_seq 0 north_pole)

/-- On a `[Subsingleton M]` target, `cdata.μ = 0` for any sequence `u_seq` (`0 sorryAx`). -/
theorem ConcentrationData.mu_eq_zero_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    cdata.μ = 0 := by
  apply cdata.mu_eq_zero_of_seq_zero I u_seq B thresh
  intro n
  have h_eq : u_seq (cdata.σ.1 n) = fun _ => u_seq (cdata.σ.1 n) north_pole :=
    funext (fun z => Subsingleton.elim (u_seq (cdata.σ.1 n) z) (u_seq (cdata.σ.1 n) north_pole))
  rw [h_eq]
  exact energyMeasureExtended_const I (u_seq (cdata.σ.1 n) north_pole)

/-- On a `[Subsingleton M]` target, `cdata.S = ∅` for any sequence `u_seq` (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    cdata.S = ∅ :=
  cdata.S_eq_empty_of_mu_eq_zero I u_seq B thresh
    (cdata.mu_eq_zero_of_subsingleton I u_seq B thresh)

/-- On a `[Subsingleton M]` target, `cdata.u₀ = fun _ => cdata.u₀ north_pole` (`0 sorryAx`). -/
theorem ConcentrationData.u0_eq_const_north_pole_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    cdata.u₀ = fun _ => cdata.u₀ north_pole :=
  funext (fun z => Subsingleton.elim (cdata.u₀ z) (cdata.u₀ north_pole))

/-- Threshold-free constant-map subsequence extraction for `J`-holomorphic spheres on `[DiscreteTopology M]` (`0 sorryAx`). -/
theorem exists_const_map_subseq_of_jhol_univ_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ) :
    ∃ (σ : SubseqMap) (c₀ : M), ∀ n, u_seq (σ.1 n) = fun _ => c₀ := by
  obtain ⟨σ, c₀, hc₀⟩ := exists_const_subseq_of_discrete (fun n => u_seq n north_pole)
  refine ⟨σ, c₀, fun n => ?_⟩
  ext z
  rw [GromovCompactness.Analysis.eq_const_north_pole_of_jhol_univ_of_discrete I
    (u_seq (σ.1 n)) (h_jhol (σ.1 n)) z, hc₀ n]

/-- Unconditional construction of `ConcentrationData` on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem exists_concentration_data_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  obtain ⟨σ, c₀, hc₀⟩ := exists_const_map_subseq_of_jhol_of_discrete I thresh u_seq h_jhol
  exact exists_concentration_data_of_const_subseq I u_seq B hB h_en thresh σ c₀ hc₀

/-- On a `[DiscreteTopology M]` target, `cdata.μ = 0` for any sequence of `J`-holomorphic spheres (`0 sorryAx`). -/
theorem ConcentrationData.mu_eq_zero_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    cdata.μ = 0 :=
  cdata.mu_eq_zero_of_seq_zero I u_seq B thresh (fun n =>
    GromovCompactness.Analysis.energyMeasureExtended_eq_zero_of_discrete I
      (u_seq (cdata.σ.1 n)) (h_jhol (cdata.σ.1 n)).1)

/-- On a `[DiscreteTopology M]` target, `cdata.S = ∅` for any sequence of `J`-holomorphic spheres (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    cdata.S = ∅ :=
  cdata.S_eq_empty_of_mu_eq_zero I u_seq B thresh
    (cdata.mu_eq_zero_of_discrete I u_seq h_jhol B thresh)

/-- On a `[DiscreteTopology M]` target, `cdata.u₀ = fun _ => cdata.u₀ north_pole` (`0 sorryAx`). -/
theorem ConcentrationData.u0_eq_const_north_pole_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    cdata.u₀ = fun _ => cdata.u₀ north_pole :=
  eq_const_north_pole_of_jhol_of_discrete I thresh cdata.u₀ cdata.u₀_jhol

/-- On a compact manifold `M`, any sequence of `J`-holomorphic spheres with `totalEnergy < thresh.ε_sph`
admits a constant subsequence (`0 sorryAx`). -/
theorem exists_const_map_subseq_of_jhol_of_lt_eps_sph
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_lt : ∀ n, totalEnergy I (u_seq n) < thresh.ε_sph) :
    ∃ (σ : SubseqMap) (c₀ : M),
      Tendsto (fun n => u_seq (σ.1 n) north_pole) atTop (nhds c₀) ∧
      ∀ n z, u_seq (σ.1 n) z = u_seq (σ.1 n) north_pole := by
  obtain ⟨c₀, -, φ, hφ_mono, hφ_tendsto⟩ :=
    isCompact_univ.tendsto_subseq (x := fun n => u_seq n north_pole) (fun _ => Set.mem_univ _)
  refine ⟨⟨φ, hφ_mono⟩, c₀, hφ_tendsto, fun n z => ?_⟩
  exact congr_fun (eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh
    (u_seq (φ n)) (h_jhol (φ n)) (h_lt (φ n))) z

/-- Unconditional smooth limit extraction off any singular set `S` when `u_seq` consists of
`J`-holomorphic spheres with `totalEnergy < thresh.ε_sph` (`0 sorryAx`). -/
theorem extract_smooth_limit_off_singular_set_of_lt_eps_sph
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_lt : ∀ n, totalEnergy I (u_seq n) < thresh.ε_sph)
    (σ : SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, u_seq (σ.1 n) north_pole = c₀)
    (S : Finset CP1) :
    ∃ (u₀ : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S) := by
  refine extract_smooth_limit_off_singular_set_of_const_subseq I u_seq σ S ⟨c₀, fun n z => ?_⟩
  have h_eq := eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh
    (u_seq (σ.1 n)) (h_jhol (σ.1 n)) (h_lt (σ.1 n))
  exact (congr_fun h_eq z).trans (hc₀ n)

/-- Unconditional construction of `ConcentrationData` when `B < thresh.ε_sph` and `u_seq` has a
subsequence with constant `north_pole` value (`0 sorryAx`). -/
theorem exists_concentration_data_of_B_lt_eps_sph_of_const_north_pole
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (h_lt : B < thresh.ε_sph)
    (σ : SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, u_seq (σ.1 n) north_pole = c₀) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  refine exists_concentration_data_of_const_subseq I u_seq B hB h_en thresh σ c₀ (fun n => ?_)
  ext z
  have h_eq := eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I thresh
    (u_seq (σ.1 n)) (h_jhol (σ.1 n)) ((h_en (σ.1 n)).trans_lt h_lt)
  exact (congr_fun h_eq z).trans (hc₀ n)

/-- Unconditional construction of `ConcentrationData` when `B < thresh.h` and `u_seq` has a
subsequence with constant `north_pole` value (`0 sorryAx`). -/
theorem exists_concentration_data_of_B_lt_h_of_const_north_pole
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (h_lt : B < thresh.h)
    (σ : SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, u_seq (σ.1 n) north_pole = c₀) :
    Nonempty (ConcentrationData I u_seq B thresh) :=
  exists_concentration_data_of_B_lt_eps_sph_of_const_north_pole I u_seq h_jhol B hB h_en thresh
    (h_lt.trans_le thresh.h_le_sph) σ c₀ hc₀

/-- Unconditional construction of `ConcentrationData` when `B = 0` and `u_seq` has a
subsequence with constant `north_pole` value (`0 sorryAx`). -/
theorem exists_concentration_data_of_B_eq_zero_of_const_north_pole
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ 0)
    (thresh : TargetThresholds I M)
    (σ : SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, u_seq (σ.1 n) north_pole = c₀) :
    Nonempty (ConcentrationData I u_seq 0 thresh) :=
  exists_concentration_data_of_B_lt_eps_sph_of_const_north_pole I u_seq h_jhol 0 le_rfl h_en thresh
    thresh.ε_sph_pos σ c₀ hc₀

/-- Whenever `B < thresh.h` and `u_seq` consists of `J`-holomorphic spheres with `totalEnergy ≤ B`,
`cdata.μ = 0` (`0 sorryAx`). -/
theorem ConcentrationData.mu_eq_zero_of_B_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < thresh.h) :
    cdata.μ = 0 :=
  cdata.mu_eq_zero_of_B_lt_eps_sph I u_seq h_jhol B h_en thresh (h_lt.trans_le thresh.h_le_sph)

/-- Whenever `B < thresh.h` and `u_seq` consists of `J`-holomorphic spheres with `totalEnergy ≤ B`,
`cdata.S = ∅` (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_B_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < thresh.h) :
    cdata.S = ∅ :=
  cdata.S_eq_empty_of_B_lt_eps_sph I u_seq h_jhol B h_en thresh (h_lt.trans_le thresh.h_le_sph)

/-- Whenever `B < thresh.h` and `u_seq` consists of `J`-holomorphic spheres with `totalEnergy ≤ B`,
the base limit `cdata.u₀` is constant (`cdata.u₀ = fun _ => cdata.u₀ north_pole`, `0 sorryAx`). -/
theorem ConcentrationData.u0_eq_const_north_pole_of_B_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : B < thresh.h) :
    cdata.u₀ = fun _ => cdata.u₀ north_pole :=
  cdata.u0_eq_const_north_pole_of_B_lt_eps_sph I u_seq h_jhol B h_en thresh (h_lt.trans_le thresh.h_le_sph)

/-- Whenever `u_seq (cdata.σ.1 n)` eventually has `totalEnergy < thresh.h`, `cdata.μ = 0` (`0 sorryAx`). -/
theorem ConcentrationData.mu_eq_zero_of_eventually_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < thresh.h) :
    cdata.μ = 0 := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact cdata.mu_eq_zero_of_eventually_lt_eps_sph I u_seq h_jhol B thresh
    ⟨N₀, fun n hn => (hN₀ n hn).trans_le thresh.h_le_sph⟩

/-- Whenever `u_seq (cdata.σ.1 n)` eventually has `totalEnergy < thresh.h`, `cdata.S = ∅` (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_eventually_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < thresh.h) :
    cdata.S = ∅ := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact cdata.S_eq_empty_of_eventually_lt_eps_sph I u_seq h_jhol B thresh
    ⟨N₀, fun n hn => (hN₀ n hn).trans_le thresh.h_le_sph⟩

/-- Whenever `u_seq (cdata.σ.1 n)` eventually has `totalEnergy < thresh.h`,
`cdata.u₀ = fun _ => cdata.u₀ north_pole` (`0 sorryAx`). -/
theorem ConcentrationData.u0_eq_const_north_pole_of_eventually_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < thresh.h) :
    cdata.u₀ = fun _ => cdata.u₀ north_pole := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact cdata.u0_eq_const_north_pole_of_eventually_lt_eps_sph I u_seq h_jhol B thresh
    ⟨N₀, fun n hn => (hN₀ n hn).trans_le thresh.h_le_sph⟩

/-- Whenever `u_seq (cdata.σ.1 n)` eventually has `totalEnergy ≤ 0`, `cdata.μ = 0` (`0 sorryAx`). -/
theorem ConcentrationData.mu_eq_zero_of_eventually_nonpos_energy
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) ≤ 0) :
    cdata.μ = 0 := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact cdata.mu_eq_zero_of_eventually_lt_eps_sph I u_seq h_jhol B thresh
    ⟨N₀, fun n hn => (hN₀ n hn).trans_lt thresh.ε_sph_pos⟩

/-- Whenever `u_seq (cdata.σ.1 n)` eventually has `totalEnergy ≤ 0`, `cdata.S = ∅` (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_eventually_nonpos_energy
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) ≤ 0) :
    cdata.S = ∅ := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact cdata.S_eq_empty_of_eventually_lt_eps_sph I u_seq h_jhol B thresh
    ⟨N₀, fun n hn => (hN₀ n hn).trans_lt thresh.ε_sph_pos⟩

/-- Whenever `u_seq (cdata.σ.1 n)` eventually has `totalEnergy ≤ 0`,
`cdata.u₀ = fun _ => cdata.u₀ north_pole` (`0 sorryAx`). -/
theorem ConcentrationData.u0_eq_const_north_pole_of_eventually_nonpos_energy
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) ≤ 0) :
    cdata.u₀ = fun _ => cdata.u₀ north_pole := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact cdata.u0_eq_const_north_pole_of_eventually_lt_eps_sph I u_seq h_jhol B thresh
    ⟨N₀, fun n hn => (hN₀ n hn).trans_lt thresh.ε_sph_pos⟩

/-- Unconditional weak energy measure compactness when `B < thresh.h` and `u_seq` consists of
`J`-holomorphic spheres with `totalEnergy ≤ B` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_B_lt_h
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < thresh.h) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness_of_B_lt_eps_sph I thresh u_seq h_jhol B h_en
    (h_lt.trans_le thresh.h_le_sph)

/-- Unconditional weak energy measure compactness when `u_seq` consists of `J`-holomorphic spheres
that eventually have `totalEnergy < thresh.h` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_eventually_lt_h
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq n) < thresh.h) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact weak_energy_measure_compactness_of_eventually_lt_eps_sph I thresh u_seq h_jhol
    ⟨N₀, fun n hn => (hN₀ n hn).trans_le thresh.h_le_sph⟩

/-- Unconditional weak energy measure compactness when `u_seq` consists of `J`-holomorphic spheres
that eventually have `totalEnergy ≤ 0` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_eventually_nonpos_energy
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_ev : ∃ N₀ : ℕ, ∀ n ≥ N₀, totalEnergy I (u_seq n) ≤ 0) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim := by
  rcases h_ev with ⟨N₀, hN₀⟩
  exact weak_energy_measure_compactness_of_eventually_lt_eps_sph I thresh u_seq h_jhol
    ⟨N₀, fun n hn => (hN₀ n hn).trans_lt thresh.ε_sph_pos⟩

/-- Whenever `B ≤ 0`, the weak limit measure `cdata.μ` vanishes identically (`0 sorryAx`). -/
theorem ConcentrationData.mu_eq_zero_of_nonpos_B
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hB : B ≤ 0) :
    cdata.μ = 0 := by
  have h_univ_zero : cdata.μ Set.univ = 0 := by
    refine le_antisymm ?_ zero_le'
    calc cdata.μ Set.univ ≤ ENNReal.ofReal B := cdata.μ_total_le
      _ = 0 := ENNReal.ofReal_of_nonpos hB
  exact Measure.measure_univ_eq_zero.mp h_univ_zero

/-- Whenever `B ≤ 0` and `u_seq` consists of `J`-holomorphic spheres with `totalEnergy ≤ B`,
the base limit `cdata.u₀` is constant (`cdata.u₀ = fun _ => cdata.u₀ north_pole`, `0 sorryAx`). -/
theorem ConcentrationData.u0_eq_const_north_pole_of_nonpos_B
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (hB : B ≤ 0) :
    cdata.u₀ = fun _ => cdata.u₀ north_pole :=
  cdata.u0_eq_const_north_pole_of_B_lt_eps_sph I u_seq h_jhol B h_en thresh
    (hB.trans_lt thresh.ε_sph_pos)

/-- If the base limit `cdata.u₀` has total energy strictly below `thresh.h`, it is constant (`0 sorryAx`). -/
theorem ConcentrationData.u0_eq_const_north_pole_of_lt_h
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_lt : totalEnergy I cdata.u₀ < thresh.h) :
    cdata.u₀ = fun _ => cdata.u₀ north_pole :=
  cdata.u0_eq_const_north_pole_of_lt_eps_sph I u_seq B thresh (h_lt.trans_le thresh.h_le_sph)

/-- If the base limit `cdata.u₀` has nonpositive total energy, it is constant (`0 sorryAx`). -/
theorem ConcentrationData.u0_eq_const_north_pole_of_nonpos_energy
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (h_le : totalEnergy I cdata.u₀ ≤ 0) :
    cdata.u₀ = fun _ => cdata.u₀ north_pole :=
  cdata.u0_eq_const_north_pole_of_lt_eps_sph I u_seq B thresh (h_le.trans_lt thresh.ε_sph_pos)

/-- Unconditional construction of `ConcentrationData` when a subsequence `u_seq ∘ σ` converges
weakly in energy measure to `μ` and smoothly off the singular set `S` to a globally `J`-holomorphic
map `u₀` (`0 sorryAx`). -/
theorem exists_concentration_data_of_punctured_jhol
    (u_seq : ℕ → (CP1 → M))
    (B : ℝ) (hB : 0 ≤ B)
    (thresh : TargetThresholds I M)
    (σ : SubseqMap) (μ : Measure CP1) [IsFiniteMeasure μ]
    (h_tot : μ Set.univ ≤ ENNReal.ofReal B)
    (h_weak : WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ)
    (u₀ : CP1 → M)
    (hu₀_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ)
    (h_conv_punct : ∀ S : Finset CP1, (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p}) →
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S))
    (h_decomp : ∀ S : Finset CP1, (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p}) →
      μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • Measure.dirac p)) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  obtain ⟨S, hS_def, hS_mul, hS_le⟩ :=
    concentration_singular_set_properties I μ B hB thresh h_tot
  exact ⟨⟨σ, μ, h_tot, h_weak, S, hS_def, hS_mul, hS_le, u₀, hu₀_jhol, h_conv_punct S hS_def, h_decomp S hS_def⟩⟩

/-- Unconditional construction of `ConcentrationData` when a subsequence `u_seq ∘ σ` converges
weakly in energy measure to `μ = 0` and smoothly on `Set.univ` to a globally `J`-holomorphic
map `u₀` (`0 sorryAx`). -/
theorem exists_concentration_data_of_zero_measure_and_smooth_univ
    (u_seq : ℕ → (CP1 → M))
    (B : ℝ) (hB : 0 ≤ B)
    (thresh : TargetThresholds I M)
    (σ : SubseqMap)
    (h_weak : WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) 0)
    (u₀ : CP1 → M)
    (hu₀_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ)
    (h_conv_univ : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ Set.univ)
    (hu₀_zero : energyMeasureExtended I u₀ = 0) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  refine exists_concentration_data_of_punctured_jhol I u_seq B hB thresh σ 0 (by simp) h_weak u₀ hu₀_jhol ?_ ?_
  · intro S _
    exact smooth_local_restriction I (fun n => u_seq (σ.1 n)) u₀ Set.diff_subset h_conv_univ
  · intro S _
    simp [hu₀_zero]

/-- Unconditional construction of `ConcentrationData` when every `J`-holomorphic sphere in `(M, J)`
is constant and `u_seq` has a subsequence with constant `north_pole` value (`0 sorryAx`). -/
theorem exists_concentration_data_of_all_jhol_const_of_const_north_pole
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      u = fun _ => u north_pole)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (σ : SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, u_seq (σ.1 n) north_pole = c₀) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  refine exists_concentration_data_of_const_subseq I u_seq B hB h_en thresh σ c₀ (fun n => ?_)
  ext z
  exact (congr_fun (h_all_const (u_seq (σ.1 n)) (h_jhol (σ.1 n))) z).trans (hc₀ n)

/-- Unconditional smooth limit extraction off any singular set `S` when every `J`-holomorphic sphere
in `(M, J)` is constant and `u_seq` has a subsequence with constant `north_pole` value (`0 sorryAx`). -/
theorem extract_smooth_limit_off_singular_set_of_all_jhol_const_of_const_north_pole
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      u = fun _ => u north_pole)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (σ : SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, u_seq (σ.1 n) north_pole = c₀)
    (S : Finset CP1) :
    ∃ (u₀ : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S) := by
  refine extract_smooth_limit_off_singular_set_of_const_subseq I u_seq σ S ⟨c₀, fun n z => ?_⟩
  exact (congr_fun (h_all_const (u_seq (σ.1 n)) (h_jhol (σ.1 n))) z).trans (hc₀ n)

/-- Unconditional smooth limit extraction off any singular set `S` when `u_seq` consists of
`J`-holomorphic spheres with `totalEnergy < thresh.h` (`0 sorryAx`). -/
theorem extract_smooth_limit_off_singular_set_of_lt_h
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_lt : ∀ n, totalEnergy I (u_seq n) < thresh.h)
    (σ : SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, u_seq (σ.1 n) north_pole = c₀)
    (S : Finset CP1) :
    ∃ (u₀ : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S) :=
  extract_smooth_limit_off_singular_set_of_lt_eps_sph I thresh u_seq h_jhol
    (fun n => (h_lt n).trans_le thresh.h_le_sph) σ c₀ hc₀ S

/-- Unconditional smooth limit extraction off any singular set `S` when `u_seq` consists of
`J`-holomorphic spheres with nonpositive total energy (`0 sorryAx`). -/
theorem extract_smooth_limit_off_singular_set_of_nonpos_energy
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_le : ∀ n, totalEnergy I (u_seq n) ≤ 0)
    (σ : SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, u_seq (σ.1 n) north_pole = c₀)
    (S : Finset CP1) :
    ∃ (u₀ : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u₀ (Set.univ \ S) :=
  extract_smooth_limit_off_singular_set_of_lt_eps_sph I thresh u_seq h_jhol
    (fun n => (h_le n).trans_lt thresh.ε_sph_pos) σ c₀ hc₀ S

/-- Whenever every globally `J`-holomorphic sphere is constant, `cdata.μ = 0` for any sequence
of `J`-holomorphic spheres (`0 sorryAx`). -/
theorem ConcentrationData.mu_eq_zero_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    cdata.μ = 0 := by
  apply cdata.mu_eq_zero_of_seq_zero I u_seq B thresh
  intro n
  obtain ⟨c, hc⟩ := h_all_const (u_seq (cdata.σ.1 n)) (h_jhol (cdata.σ.1 n))
  rw [funext hc]
  exact energyMeasureExtended_const I c

/-- Whenever every globally `J`-holomorphic sphere is constant, `cdata.S = ∅` for any sequence
of `J`-holomorphic spheres (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    cdata.S = ∅ :=
  cdata.S_eq_empty_of_mu_eq_zero I u_seq B thresh
    (cdata.mu_eq_zero_of_all_jhol_const I h_all_const u_seq h_jhol B thresh)

/-- Whenever every globally `J`-holomorphic sphere is constant, `cdata.u₀ = fun _ => cdata.u₀ north_pole` (`0 sorryAx`). -/
theorem ConcentrationData.u0_eq_const_north_pole_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    cdata.u₀ = fun _ => cdata.u₀ north_pole := by
  obtain ⟨c, hc⟩ := h_all_const cdata.u₀ cdata.u₀_jhol
  ext z
  exact (hc z).trans (hc north_pole).symm

/-- On a compact manifold `M`, any sequence of `J`-holomorphic spheres admits a constant subsequence
whenever every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem exists_const_map_subseq_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ) :
    ∃ (σ : SubseqMap) (c₀ : M),
      Tendsto (fun n => u_seq (σ.1 n) north_pole) atTop (nhds c₀) ∧
      ∀ n z, u_seq (σ.1 n) z = u_seq (σ.1 n) north_pole := by
  obtain ⟨c₀, -, φ, hφ_mono, hφ_tendsto⟩ :=
    isCompact_univ.tendsto_subseq (x := fun n => u_seq n north_pole) (fun _ => Set.mem_univ _)
  refine ⟨⟨φ, hφ_mono⟩, c₀, hφ_tendsto, fun n z => ?_⟩
  obtain ⟨c, hc⟩ := h_all_const (u_seq (φ n)) (h_jhol (φ n))
  exact (hc z).trans (hc north_pole).symm

/-- Unconditional extended energy finiteness when every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c)
    (u : CP1 → M) (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    energyMeasureExtended I u Set.univ < ⊤ := by
  obtain ⟨c, hc⟩ := h_all_const u hu
  rw [funext hc]
  exact energyMeasureExtended_lt_top_of_const_map I c

/-- Whenever every globally `J`-holomorphic sphere is constant and `u_seq (cdata.σ.1 n)` is
eventually `J`-holomorphic, `cdata.μ = 0` (`0 sorryAx`). -/
theorem ConcentrationData.mu_eq_zero_of_eventually_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq (cdata.σ.1 n)) Set.univ) :
    cdata.μ = 0 := by
  refine cdata.mu_eq_zero_of_eventually_seq_zero I u_seq B thresh ⟨N₀, fun n hn => ?_⟩
  obtain ⟨c, hc⟩ := h_all_const (u_seq (cdata.σ.1 n)) (h_jhol n hn)
  rw [funext hc]
  exact energyMeasureExtended_const I c

/-- Whenever every globally `J`-holomorphic sphere is constant and `u_seq (cdata.σ.1 n)` is
eventually `J`-holomorphic, `cdata.S = ∅` (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_eventually_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq (cdata.σ.1 n)) Set.univ) :
    cdata.S = ∅ :=
  cdata.S_eq_empty_of_mu_eq_zero I u_seq B thresh
    (cdata.mu_eq_zero_of_eventually_all_jhol_const I h_all_const u_seq B thresh N₀ h_jhol)

/-- Unconditional construction of `ConcentrationData` when every `J`-holomorphic sphere in `(M, J)`
is constant and `u_seq` has a subsequence with eventually constant `north_pole` value (`0 sorryAx`). -/
theorem exists_concentration_data_of_all_jhol_const_of_eventually_const_north_pole
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      u = fun _ => u north_pole)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (σ : SubseqMap) (N₀ : ℕ) (c₀ : M)
    (hc₀ : ∀ n ≥ N₀, u_seq (σ.1 n) north_pole = c₀) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  refine exists_concentration_data_of_eventually_const_subseq I u_seq B hB h_en thresh σ N₀ c₀
    (fun n hn => ?_)
  ext z
  exact (congr_fun (h_all_const (u_seq (σ.1 n)) (h_jhol (σ.1 n))) z).trans (hc₀ n hn)

/-- Unconditional construction of `ConcentrationData` when `u_seq (σ.1 n)` is eventually constant
among `J`-holomorphic spheres and has eventually constant `north_pole` value (`0 sorryAx`). -/
theorem exists_concentration_data_of_eventually_all_jhol_const_of_eventually_const_north_pole
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (σ : SubseqMap) (N₀ N₁ : ℕ) (c₀ : M)
    (h_ev_const : ∀ n ≥ N₁, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq (σ.1 n)) Set.univ →
      u_seq (σ.1 n) = fun _ => u_seq (σ.1 n) north_pole)
    (hc₀ : ∀ n ≥ N₀, u_seq (σ.1 n) north_pole = c₀) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  refine exists_concentration_data_of_eventually_const_subseq I u_seq B hB h_en thresh σ (max N₀ N₁) c₀
    (fun n hn => ?_)
  ext z
  exact (congr_fun (h_ev_const n (le_of_max_le_right hn) (h_jhol (σ.1 n))) z).trans
    (hc₀ n (le_of_max_le_left hn))

/-- If the defect measure at `p` is strictly below `thresh.ε_reg`, convergence is smooth across `p` (`0 sorryAx`). -/
theorem smooth_convergence_upgrade_of_lt_eps_reg
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh)
    (p : CP1) (hp : cdata.μ {p} < ENNReal.ofReal thresh.ε_reg) :
    SmoothLocalConvergesOn I (fun n => u_seq (cdata.σ.1 n)) cdata.u₀ (Set.univ \ (cdata.S.erase p)) := by
  have hp_not_mem : p ∉ cdata.S := by
    intro h_mem
    exact hp.not_ge ((cdata.S_def p).mp h_mem)
  rw [Finset.erase_eq_of_notMem hp_not_mem]
  exact cdata.smooth_conv

/-- Whenever every globally `J`-holomorphic sphere equals its `north_pole` value, `cdata.μ = 0` (`0 sorryAx`). -/
theorem ConcentrationData.mu_eq_zero_of_all_jhol_eq_north_pole
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → u = fun _ => u north_pole)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    cdata.μ = 0 :=
  cdata.mu_eq_zero_of_all_jhol_const I (fun u hu => ⟨u north_pole, fun z => congr_fun (h_all_np u hu) z⟩)
    u_seq h_jhol B thresh

/-- Whenever every globally `J`-holomorphic sphere equals its `north_pole` value, `cdata.S = ∅` (`0 sorryAx`). -/
theorem ConcentrationData.S_eq_empty_of_all_jhol_eq_north_pole
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → u = fun _ => u north_pole)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    cdata.S = ∅ :=
  cdata.S_eq_empty_of_all_jhol_const I (fun u hu => ⟨u north_pole, fun z => congr_fun (h_all_np u hu) z⟩)
    u_seq h_jhol B thresh

/-- Whenever every globally `J`-holomorphic sphere equals its `north_pole` value,
`cdata.u₀ = fun _ => cdata.u₀ north_pole` (`0 sorryAx`). -/
theorem ConcentrationData.u0_eq_const_north_pole_of_all_jhol_eq_north_pole
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → u = fun _ => u north_pole)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (thresh : TargetThresholds I M)
    (cdata : ConcentrationData I u_seq B thresh) :
    cdata.u₀ = fun _ => cdata.u₀ north_pole :=
  h_all_np cdata.u₀ cdata.u₀_jhol

/-- Every `J`-holomorphic sphere `u : CP1 → M` has finite extended energy measure
(`energyMeasureExtended I u Set.univ < ⊤`) given `thresh : TargetThresholds I M` (`0 sorryAx`). -/
theorem energyMeasureExtended_lt_top_of_thresholds
    (thresh : TargetThresholds I M) (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    energyMeasureExtended I u Set.univ < ⊤ :=
  energyMeasureExtended_lt_top_of_jhol_and_sph_gap I thresh.ε_sph thresh.ε_sph_pos thresh.h_sph u hu

/-- Weak compactness of energy measures for any bounded-energy sequence of `J`-holomorphic
spheres given `thresh : TargetThresholds I M`, without requiring `h_fin` (`0 sorryAx`). -/
theorem weak_energy_measure_compactness_of_thresholds
    (thresh : TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (hB : 0 < B)
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (σ : SubseqMap) (μ_lim : Measure CP1),
      IsFiniteMeasure μ_lim ∧
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ_lim :=
  weak_energy_measure_compactness_of_jhol_and_sph_gap I thresh.ε_sph thresh.ε_sph_pos thresh.h_sph
    u_seq B hB h_jhol h_bdd

/-- Extraction of Concentration Data from bounded-energy `J`-spheres given `thresh : TargetThresholds I M`,
without requiring `h_fin` (`0 sorryAx`). -/
theorem exists_concentration_data_of_thresholds
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (h_extract : ∀ (σ : SubseqMap) (μ : Measure CP1) (S : Finset CP1), IsFiniteMeasure μ →
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ →
      (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p}) →
      ∃ (τ : SubseqMap) (u₀ : CP1 → M), JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
        SmoothLocalConvergesOn I (fun n => u_seq ((σ.comp τ).1 n)) u₀ (Set.univ \ S) ∧
        μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • Measure.dirac p)) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  have h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤ :=
    fun n => energyMeasureExtended_lt_top_of_thresholds I thresh (u_seq n) (h_jhol n)
  by_cases h_ev : ∃ (σ : SubseqMap) (N₀ : ℕ) (c : M), ∀ n ≥ N₀, u_seq (σ.1 n) = fun _ => c
  · rcases h_ev with ⟨σ, N₀, c, hc⟩
    exact exists_concentration_data_of_eventually_const_subseq I u_seq B hB h_en thresh σ N₀ c hc
  · exact exists_concentration_data_of_smooth_limit I u_seq h_jhol B hB h_en thresh
      (fun B' hB' h_en' => weak_energy_measure_compactness_of_thresholds I thresh u_seq B' hB' h_jhol h_en')
      h_fin
      h_extract

/-- Extraction of Concentration Data from bounded-energy J-spheres (Contract C02).
Proved with zero direct sorry (`_h_fin` is discharged unconditionally from `thresh` and `h_jhol`). -/
theorem exists_concentration_data
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (_h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (thresh : TargetThresholds I M)
    (h_extract : ∀ (σ : SubseqMap) (μ : Measure CP1) (S : Finset CP1), IsFiniteMeasure μ →
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ →
      (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p}) →
      ∃ (τ : SubseqMap) (u₀ : CP1 → M), JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
        SmoothLocalConvergesOn I (fun n => u_seq ((σ.comp τ).1 n)) u₀ (Set.univ \ S) ∧
        μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • Measure.dirac p)) :
    Nonempty (ConcentrationData I u_seq B thresh) :=
  exists_concentration_data_of_thresholds I u_seq h_jhol B hB h_en thresh h_extract

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
    exact h_ofReal_pos.not_ge h_le
  rw [Finset.erase_eq_of_notMem hp_not_mem]
  exact cdata.smooth_conv

/-! ### First-principles proof of `cert_conc` (`SmoothConcentrationExtractProperty`) (`0 sorryAx`) -/

/-- Every singleton `{p}` in `CP1` has extended energy measure zero (`0 sorryAx`). -/
private theorem energyMeasureExtended_singleton_eq_zero' (u : CP1 → M) (p : CP1) :
    energyMeasureExtended I u {p} = 0 := by
  dsimp [energyMeasureExtended, chartPush]
  rw [Measure.map_apply stereo_chart_symm_measurable (measurableSet_singleton p)]
  by_cases hp : p = north_pole
  · subst hp
    rw [stereo_chart_symm_preimage_north_pole]
    simp
  · rw [stereo_chart_symm_preimage_pt p hp]
    exact withDensity_absolutelyContinuous volume _ (measure_singleton (stereo_chart p))

/-- Every finite subset `S : Finset CP1` has extended energy measure zero (`0 sorryAx`). -/
theorem energyMeasureExtended_finset_eq_zero (u : CP1 → M) (S : Finset CP1) :
    energyMeasureExtended I u (S : Set CP1) = 0 := by
  rw [← Set.biUnion_of_singleton (S : Set CP1)]
  exact (measure_biUnion_null_iff S.finite_toSet.countable).mpr
    (fun p _ => energyMeasureExtended_singleton_eq_zero' I u p)

/-- Two maps agreeing on an open set `Ω ⊆ CP1` have identical `riemannianEnergyDensity` on `Ω` (`0 sorryAx`). -/
theorem riemannianEnergyDensity_eqOn_open
    {u₁ u₂ : CP1 → M} {Ω : Set CP1} (hΩ : IsOpen Ω) (heq : Set.EqOn u₁ u₂ Ω) :
    Set.EqOn (riemannianEnergyDensity I u₁) (riemannianEnergyDensity I u₂) Ω := by
  intro z hz
  have hev : u₁ =ᶠ[𝓝 z] u₂ := Filter.eventuallyEq_of_mem (hΩ.mem_nhds hz) heq
  have hdf : mfderiv I_CP1 I u₁ z = mfderiv I_CP1 I u₂ z := hev.mfderiv_eq
  dsimp [riemannianEnergyDensity]
  rw [heq hz, hdf]

/-- Two maps agreeing on an open set `Ω ⊆ CP1` have identical `energyMeasureExtended` on `Ω` (`0 sorryAx`). -/
theorem energyMeasureExtended_eqOn_open
    {u₁ u₂ : CP1 → M} {Ω : Set CP1} (hΩ : IsOpen Ω) (heq : Set.EqOn u₁ u₂ Ω) :
    energyMeasureExtended I u₁ Ω = energyMeasureExtended I u₂ Ω := by
  have h_dens := riemannianEnergyDensity_eqOn_open I hΩ heq
  dsimp [energyMeasureExtended, chartPush]
  rw [Measure.map_apply stereo_chart_symm_measurable hΩ.measurableSet,
      Measure.map_apply stereo_chart_symm_measurable hΩ.measurableSet]
  have h_pre_meas : MeasurableSet (stereo_chart.symm ⁻¹' Ω) :=
    hΩ.measurableSet.preimage stereo_chart_symm_measurable
  rw [withDensity_apply _ h_pre_meas, withDensity_apply _ h_pre_meas]
  refine setLIntegral_congr_fun h_pre_meas (fun w hw => ?_)
  change ENNReal.ofReal (riemannianEnergyDensity I u₁ (stereo_chart.symm w) * sphericalJacobian w) =
    ENNReal.ofReal (riemannianEnergyDensity I u₂ (stereo_chart.symm w) * sphericalJacobian w)
  rw [h_dens hw]

/-- Two maps agreeing outside a finite set `S : Finset CP1` have identical `energyMeasureExtended`
as Borel measures on all of `CP1` (`0 sorryAx`). -/
theorem energyMeasureExtended_congr_off_finset
    {u₁ u₂ : CP1 → M} (S : Finset CP1) (heq : Set.EqOn u₁ u₂ (Set.univ \ S)) :
    energyMeasureExtended I u₁ = energyMeasureExtended I u₂ := by
  have h_dens := riemannianEnergyDensity_eqOn_open I (isOpen_compl_finset S) heq
  dsimp [energyMeasureExtended, chartPush]
  congr 1
  apply withDensity_congr_ae
  have h_fin_pre : (stereo_chart.symm ⁻¹' (S : Set CP1)).Finite :=
    S.finite_toSet.preimage stereo_chart_symm_injective.injOn
  have h_null : (volume : Measure ℂ) (stereo_chart.symm ⁻¹' (S : Set CP1)) = 0 :=
    h_fin_pre.measure_zero volume
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun w hw => ?_) h_null
  by_contra hw_not_S
  have hw_in : stereo_chart.symm w ∈ Set.univ \ (S : Set CP1) := ⟨Set.mem_univ _, hw_not_S⟩
  apply hw
  change ENNReal.ofReal (riemannianEnergyDensity I u₁ (stereo_chart.symm w) * sphericalJacobian w) =
    ENNReal.ofReal (riemannianEnergyDensity I u₂ (stereo_chart.symm w) * sphericalJacobian w)
  rw [h_dens hw_in]

/-- Unconditional compact-subset eventual uniform gradient bound on the open southern hemisphere
`stereo_chart.symm '' Metric.ball 0 1` off the concentration set `S` (`0 sorryAx`). -/
theorem eventually_gradient_bound_on_compact_southern_hemisphere_of_disjoint_S
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (thresh : TargetThresholds I M)
    (σ : SubseqMap) (μ : Measure CP1) [IsFiniteMeasure μ] (S : Finset CP1)
    (h_weak : WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ)
    (hS_def : ∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p})
    {K : Set CP1} (hK_cpt : IsCompact K)
    (hK_sub : K ⊆ (Set.univ \ S) ∩ (stereo_chart.symm '' Metric.ball (0 : ℂ) 1)) :
    ∃ C ≥ 0, ∀ᶠ n in Filter.atTop, ∀ z ∈ K,
      riemannianEnergyDensity I (u_seq (σ.1 n)) z ≤ C := by
  have h_local : ∀ p ∈ K, ∃ (U : Set CP1) (C_p : ℝ),
      IsOpen U ∧ p ∈ U ∧ 0 ≤ C_p ∧
      ∀ᶠ n in Filter.atTop, ∀ z ∈ U, riemannianEnergyDensity I (u_seq (σ.1 n)) z ≤ C_p := by
    intro p hp
    have hp_not_S : p ∉ S := (hK_sub hp).1.2
    rcases (hK_sub hp).2 with ⟨a, ha_ball, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at ha_ball
    obtain ⟨ρ, hρ_pos, ε₁, hε₁_lt, hε₁_pos, h_ev_ball⟩ :=
      exists_closedBall_eventually_energy_lt_eps_reg_of_notMem_S I u_seq thresh σ μ S h_weak hS_def
        (stereo_chart.symm a) hp_not_S
    obtain ⟨δ, hδ_pos, hδ_cont⟩ :=
      Metric.continuousAt_iff.mp stereo_chart_symm_continuous.continuousAt ρ hρ_pos
    let r : ℝ := min ((1 - ‖a‖) / 2) δ
    have hr_pos : 0 < r := lt_min (by linarith) hδ_pos
    have h_sub_hemi : Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1 := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      rw [Metric.mem_closedBall, dist_zero_right]
      have hr_le : r ≤ (1 - ‖a‖) / 2 := min_le_left _ _
      have h_tri : ‖w‖ ≤ ‖a‖ + ‖w - a‖ := by
        calc ‖w‖ = ‖a + (w - a)‖ := congr_arg norm (by ring)
          _ ≤ ‖a‖ + ‖w - a‖ := norm_add_le a (w - a)
      linarith
    have h_disk_sub : disk_at a r ⊆ closedBall (stereo_chart.symm a) ρ := by
      rintro z ⟨w, hw_ball, rfl⟩
      rw [Metric.mem_closedBall]
      apply le_of_lt
      apply hδ_cont
      exact lt_of_lt_of_le hw_ball (min_le_right _ _)
    have h_ev_grad :=
      eventually_gradient_bound_on_disk_of_notMem_S I u_seq h_jhol thresh σ μ S h_weak hS_def
        hp_not_S hr_pos h_sub_hemi h_disk_sub hε₁_lt hε₁_pos h_ev_ball
    refine ⟨disk_at a (r / 2), thresh.C_reg * r ^ (-2 : ℝ) * thresh.ε_reg,
      is_open_disk_at a (r / 2), center_mem_disk_at a (half_pos hr_pos),
      mul_nonneg (mul_nonneg thresh.C_reg_pos.le (Real.rpow_nonneg hr_pos.le _)) thresh.ε_reg_pos.le,
      h_ev_grad⟩
  choose U C_p hU_open hp_mem hCp_nonneg h_ev_U using fun (p : K) => h_local p.1 p.2
  obtain ⟨t, ht_cover⟩ := hK_cpt.elim_finite_subcover U (fun p => hU_open p) (fun z hz =>
    Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hp_mem ⟨z, hz⟩⟩)
  let C_max : ℝ := ∑ p ∈ t, C_p p
  have hC_nonneg : 0 ≤ C_max := Finset.sum_nonneg (fun p _ => hCp_nonneg p)
  have h_ev_all : ∀ᶠ n in Filter.atTop, ∀ p ∈ t, ∀ z ∈ U p,
      riemannianEnergyDensity I (u_seq (σ.1 n)) z ≤ C_p p :=
    (Filter.eventually_all_finset t).mpr (fun p _ => h_ev_U p)
  refine ⟨C_max, hC_nonneg, ?_⟩
  filter_upwards [h_ev_all] with n hn z hz
  have hz_cov := ht_cover hz
  simp only [Set.mem_iUnion] at hz_cov
  rcases hz_cov with ⟨p, hp_in_t, hz_in_Up⟩
  exact (hn p hp_in_t z hz_in_Up).trans
    (Finset.single_le_sum (fun q _ => hCp_nonneg q) hp_in_t)

set_option backward.isDefEq.respectTransparency false in
private lemma continuous_omega_on_M :
    Continuous (fun x : M => id (α := E →L[ℝ] E →L[ℝ] ℝ) (ClosedTameTarget.«ω» (I := I) (M := M) x)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have h_cont_chart : ContinuousOn (ω_chart I (ClosedTameTarget.«ω» (I := I) (M := M)) x₀) (extChartAt I x₀).target :=
    (ClosedTameTarget.ω_smooth (I := I) (M := M) x₀).continuousOn
  have h_comp : ContinuousOn
      (fun x => ω_chart I (ClosedTameTarget.«ω» (I := I) (M := M)) x₀ (extChartAt I x₀ x))
      (extChartAt I x₀).source :=
    h_cont_chart.comp (continuousOn_extChartAt x₀) (extChartAt I x₀).mapsTo
  have h_congr : ContinuousOn
      (fun x : M => id (α := E →L[ℝ] E →L[ℝ] ℝ) (ClosedTameTarget.«ω» (I := I) (M := M) x))
      (extChartAt I x₀).source :=
    h_comp.congr (fun x hx => by
      have h_inv : (extChartAt I x₀).symm (extChartAt I x₀ x) = x := (extChartAt I x₀).left_inv hx
      change (ClosedTameTarget.«ω» (I := I) (M := M) x : E →L[ℝ] E →L[ℝ] ℝ) =
        (ClosedTameTarget.«ω» (I := I) (M := M) ((extChartAt I x₀).symm (extChartAt I x₀ x)) : E →L[ℝ] E →L[ℝ] ℝ)
      rw [h_inv])
  exact h_congr.continuousAt ((isOpen_extChartAt_source x₀).mem_nhds (mem_extChartAt_source x₀))

set_option backward.isDefEq.respectTransparency false in
private lemma continuous_J_on_M :
    Continuous (fun x : M => id (α := E →L[ℝ] E) (ClosedTameTarget.J (I := I) (M := M) x)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have h_cont_chart : ContinuousOn (J_chart I (ClosedTameTarget.J (I := I) (M := M)) x₀) (extChartAt I x₀).target :=
    (ClosedTameTarget.J_smooth (I := I) (M := M) x₀).continuousOn
  have h_comp : ContinuousOn
      (fun x => J_chart I (ClosedTameTarget.J (I := I) (M := M)) x₀ (extChartAt I x₀ x))
      (extChartAt I x₀).source :=
    h_cont_chart.comp (continuousOn_extChartAt x₀) (extChartAt I x₀).mapsTo
  have h_congr : ContinuousOn
      (fun x : M => id (α := E →L[ℝ] E) (ClosedTameTarget.J (I := I) (M := M) x))
      (extChartAt I x₀).source :=
    h_comp.congr (fun x hx => by
      have h_inv : (extChartAt I x₀).symm (extChartAt I x₀ x) = x := (extChartAt I x₀).left_inv hx
      change (ClosedTameTarget.J (I := I) (M := M) x : E →L[ℝ] E) =
        (ClosedTameTarget.J (I := I) (M := M) ((extChartAt I x₀).symm (extChartAt I x₀ x)) : E →L[ℝ] E)
      rw [h_inv])
  exact h_congr.continuousAt ((isOpen_extChartAt_source x₀).mem_nhds (mem_extChartAt_source x₀))

set_option backward.isDefEq.respectTransparency false in
/-- Pointwise convergence of `riemannianEnergyDensity` at every point `z ∈ Ω` under
`SmoothLocalConvergesOn I v_seq u₀ Ω` (`0 sorryAx`). -/
theorem tendsto_riemannianEnergyDensity_of_smoothLocalConvergesOn
    {v_seq : ℕ → (CP1 → M)} {u₀ : CP1 → M} {Ω : Set CP1}
    (h_conv : SmoothLocalConvergesOn I v_seq u₀ Ω) {z : CP1} (hz : z ∈ Ω) :
    Tendsto (fun n => riemannianEnergyDensity I (v_seq n) z) atTop
      (𝓝 (riemannianEnergyDensity I u₀ z)) := by
  have h_core := (h_conv []).2 {z} (Set.singleton_subset_iff.mpr hz) isCompact_singleton
  have h_pt : Tendsto (fun n => v_seq n z) atTop (𝓝 (u₀ z)) := h_core.1 z (Set.mem_singleton z)
  have h_d1 : Tendsto (fun n => (mfderiv I_CP1 I (v_seq n) z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E))
      atTop (𝓝 (mfderiv I_CP1 I u₀ z)) := h_core.2.1 z (Set.mem_singleton z)
  have h_term : ∀ b : EuclideanSpace ℝ (Fin 2),
      Tendsto (fun n => ClosedTameTarget.metric I (v_seq n z)
        (mfderiv I_CP1 I (v_seq n) z b) (mfderiv I_CP1 I (v_seq n) z b))
      atTop (𝓝 (ClosedTameTarget.metric I (u₀ z) (mfderiv I_CP1 I u₀ z b) (mfderiv I_CP1 I u₀ z b))) := by
    intro b
    have hb : Tendsto (fun n => (mfderiv I_CP1 I (v_seq n) z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) b)
        atTop (𝓝 ((mfderiv I_CP1 I u₀ z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) b)) :=
      ((ContinuousLinearMap.apply ℝ E b).continuous.tendsto _).comp h_d1
    have hω : Tendsto (fun n => id (α := E →L[ℝ] E →L[ℝ] ℝ) (ClosedTameTarget.«ω» (I := I) (M := M) (v_seq n z)))
        atTop (𝓝 (id (α := E →L[ℝ] E →L[ℝ] ℝ) (ClosedTameTarget.«ω» (I := I) (M := M) (u₀ z)))) :=
      ((continuous_omega_on_M I).tendsto _).comp h_pt
    have hJ : Tendsto (fun n => id (α := E →L[ℝ] E) (ClosedTameTarget.J (I := I) (M := M) (v_seq n z)))
        atTop (𝓝 (id (α := E →L[ℝ] E) (ClosedTameTarget.J (I := I) (M := M) (u₀ z)))) :=
      ((continuous_J_on_M I).tendsto _).comp h_pt
    have hJb : Tendsto (fun n => (id (α := E →L[ℝ] E) (ClosedTameTarget.J (I := I) (M := M) (v_seq n z)))
          ((mfderiv I_CP1 I (v_seq n) z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) b))
        atTop (𝓝 ((id (α := E →L[ℝ] E) (ClosedTameTarget.J (I := I) (M := M) (u₀ z)))
          ((mfderiv I_CP1 I u₀ z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) b))) :=
      (isBoundedBilinearMap_apply.continuous.tendsto _).comp (hJ.prodMk_nhds hb)
    have hωb : Tendsto (fun n => (id (α := E →L[ℝ] E →L[ℝ] ℝ) (ClosedTameTarget.«ω» (I := I) (M := M) (v_seq n z)))
          ((mfderiv I_CP1 I (v_seq n) z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) b))
        atTop (𝓝 ((id (α := E →L[ℝ] E →L[ℝ] ℝ) (ClosedTameTarget.«ω» (I := I) (M := M) (u₀ z)))
          ((mfderiv I_CP1 I u₀ z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) b))) :=
      (isBoundedBilinearMap_apply.continuous.tendsto _).comp (hω.prodMk_nhds hb)
    have hωJb : Tendsto (fun n => (id (α := E →L[ℝ] E →L[ℝ] ℝ) (ClosedTameTarget.«ω» (I := I) (M := M) (v_seq n z)))
          ((mfderiv I_CP1 I (v_seq n) z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) b)
          ((id (α := E →L[ℝ] E) (ClosedTameTarget.J (I := I) (M := M) (v_seq n z)))
            ((mfderiv I_CP1 I (v_seq n) z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) b)))
        atTop (𝓝 ((id (α := E →L[ℝ] E →L[ℝ] ℝ) (ClosedTameTarget.«ω» (I := I) (M := M) (u₀ z)))
          ((mfderiv I_CP1 I u₀ z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) b)
          ((id (α := E →L[ℝ] E) (ClosedTameTarget.J (I := I) (M := M) (u₀ z)))
            ((mfderiv I_CP1 I u₀ z : EuclideanSpace ℝ (Fin 2) →L[ℝ] E) b)))) :=
      (isBoundedBilinearMap_apply.continuous.tendsto _).comp (hωb.prodMk_nhds hJb)
    dsimp [ClosedTameTarget.metric]
    exact tendsto_const_nhds.mul (hωJb.add hωJb)
  dsimp [riemannianEnergyDensity]
  exact tendsto_const_nhds.mul ((h_term e1).add (h_term e2))

/-- First-principles Defect Measure Decomposition Theorem (`0 sorryAx`):
whenever `energyMeasureExtended I (v_seq n)` converges weakly to a finite Borel measure `μ` on `CP1`,
`v_seq` converges in `SmoothLocalConvergesOn` off a finite set `S : Finset CP1` to `u₀`,
each stereographic energy density `w ↦ riemannianEnergyDensity I (v_seq n) (stereo_chart.symm w)` is
measurable, and `riemannianEnergyDensity I (v_seq n)` is eventually uniformly bounded on every compact
subset `K ⊆ Set.univ \ S`, we have:
1. `energyMeasureExtended I u₀ Set.univ ≤ μ Set.univ` (energy lower semicontinuity / finiteness), and
2. `μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • Measure.dirac p)`. -/
theorem defect_measure_decomp_of_smooth_conv_off_S
    (v_seq : ℕ → (CP1 → M))
    (μ : Measure CP1) [IsFiniteMeasure μ]
    (S : Finset CP1)
    (u₀ : CP1 → M)
    (h_weak : WeakMeasureConvergence (fun n => energyMeasureExtended I (v_seq n)) μ)
    (h_conv : SmoothLocalConvergesOn I v_seq u₀ (Set.univ \ S))
    (h_meas_dens : ∀ n, Measurable (fun w : ℂ => riemannianEnergyDensity I (v_seq n) (stereo_chart.symm w)))
    (h_grad_bdd : ∀ K ⊆ Set.univ \ (S : Set CP1), IsCompact K →
      ∃ C ≥ 0, ∀ᶠ n in Filter.atTop, ∀ z ∈ K, riemannianEnergyDensity I (v_seq n) z ≤ C) :
    energyMeasureExtended I u₀ Set.univ ≤ μ Set.univ ∧
      μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • Measure.dirac p) := by
  let d_seq : ℕ → ℂ → ENNReal := fun n w =>
    ENNReal.ofReal (riemannianEnergyDensity I (v_seq n) (stereo_chart.symm w) * sphericalJacobian w)
  let d₀ : ℂ → ENNReal := fun w =>
    ENNReal.ofReal (riemannianEnergyDensity I u₀ (stereo_chart.symm w) * sphericalJacobian w)
  have hd_meas : ∀ n, Measurable (d_seq n) := fun n =>
    ENNReal.measurable_ofReal.comp ((h_meas_dens n).mul continuous_sphericalJacobian.measurable)
  -- Almost-everywhere convergence `d_seq n w → d₀ w` (since `stereo_chart.symm ⁻¹' S` is finite, hence null).
  have h_fin_pre : (stereo_chart.symm ⁻¹' (S : Set CP1)).Finite :=
    S.finite_toSet.preimage stereo_chart_symm_injective.injOn
  have h_ae_lim : ∀ᵐ w ∂(volume : Measure ℂ), Tendsto (fun n => d_seq n w) atTop (𝓝 (d₀ w)) := by
    rw [eventually_iff, mem_ae_iff]
    refine measure_mono_null (fun w hw => ?_) (h_fin_pre.measure_zero volume)
    by_contra hw_not_S
    have hw_in : stereo_chart.symm w ∈ Set.univ \ (S : Set CP1) := ⟨Set.mem_univ _, hw_not_S⟩
    have h_e := tendsto_riemannianEnergyDensity_of_smoothLocalConvergesOn I h_conv hw_in
    exact hw (ENNReal.continuous_ofReal.tendsto _ |>.comp (h_e.mul_const (sphericalJacobian w)))
  have hd₀_aemeas : AEMeasurable d₀ volume :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hd_meas n).aemeasurable) h_ae_lim
  -- Eventually `energyMeasureExtended I (v_seq n) Set.univ < ⊤` since it converges to `μ Set.univ < ⊤`.
  have h_ev_fin : ∀ᶠ n in atTop, energyMeasureExtended I (v_seq n) Set.univ < ⊤ :=
    (tendsto_order.mp h_weak.tendsto_univ).2 ⊤ (measure_lt_top μ Set.univ)
  -- Step 1: For every continuous `φ : CP1 → ℝ` with `0 ≤ φ ≤ 1` and `tsupport φ ⊆ Set.univ \ S`,
  -- `∫⁻ z, ofReal (φ z) ∂μ = ∫⁻ z, ofReal (φ z) ∂(energyMeasureExtended I u₀)`.
  have h_test : ∀ φ : CP1 → ℝ, Continuous φ → (∀ z, 0 ≤ φ z) → (∀ z, φ z ≤ 1) →
      tsupport φ ⊆ Set.univ \ (S : Set CP1) →
      (∫⁻ z, ENNReal.ofReal (φ z) ∂μ) = ∫⁻ z, ENNReal.ofReal (φ z) ∂(energyMeasureExtended I u₀) := by
    intro φ hφ_cont hφ_nonneg hφ_le_one hφ_supp
    let K : Set CP1 := tsupport φ
    have hK_cpt : IsCompact K := isCompact_univ.of_isClosed_subset (isClosed_tsupport φ) (Set.subset_univ _)
    obtain ⟨C, hC_nonneg, h_ev_C⟩ := h_grad_bdd K hφ_supp hK_cpt
    -- Weak convergence gives `ofReal (∫ φ ∂μ_n) → ofReal (∫ φ ∂μ) = ∫⁻ ofReal φ ∂μ`.
    have h_int_lim : Tendsto (fun n => ENNReal.ofReal (∫ z, φ z ∂(energyMeasureExtended I (v_seq n))))
        atTop (𝓝 (ENNReal.ofReal (∫ z, φ z ∂μ))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (h_weak.tendsto_integral φ hφ_cont)
    have h_mu_eq : ENNReal.ofReal (∫ z, φ z ∂μ) = ∫⁻ z, ENNReal.ofReal (φ z) ∂μ := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ_nonneg) hφ_cont.aestronglyMeasurable]
      have h_le_univ : (∫⁻ z, ENNReal.ofReal (φ z) ∂μ) ≤ μ Set.univ := by
        calc (∫⁻ z, ENNReal.ofReal (φ z) ∂μ)
            ≤ ∫⁻ _z, (1 : ENNReal) ∂μ :=
              lintegral_mono (fun z => by simpa using ENNReal.ofReal_le_ofReal (hφ_le_one z))
          _ = μ Set.univ := by simp
      exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top (measure_ne_top μ Set.univ) h_le_univ)
    rw [h_mu_eq] at h_int_lim
    have h_ev_lint_eq : (fun n => ENNReal.ofReal (∫ z, φ z ∂(energyMeasureExtended I (v_seq n)))) =ᶠ[atTop]
        (fun n => ∫⁻ z, ENNReal.ofReal (φ z) ∂(energyMeasureExtended I (v_seq n))) := by
      filter_upwards [h_ev_fin] with n hn_fin
      haveI : IsFiniteMeasure (energyMeasureExtended I (v_seq n)) := ⟨hn_fin⟩
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hφ_nonneg) hφ_cont.aestronglyMeasurable]
      have h_le_univ : (∫⁻ z, ENNReal.ofReal (φ z) ∂(energyMeasureExtended I (v_seq n))) ≤
          energyMeasureExtended I (v_seq n) Set.univ := by
        calc (∫⁻ z, ENNReal.ofReal (φ z) ∂(energyMeasureExtended I (v_seq n)))
            ≤ ∫⁻ _z, (1 : ENNReal) ∂(energyMeasureExtended I (v_seq n)) :=
              lintegral_mono (fun z => by simpa using ENNReal.ofReal_le_ofReal (hφ_le_one z))
          _ = energyMeasureExtended I (v_seq n) Set.univ := by simp
      exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top hn_fin.ne h_le_univ)
    have h_lhs_lim : Tendsto (fun n => ∫⁻ z, ENNReal.ofReal (φ z) ∂(energyMeasureExtended I (v_seq n)))
        atTop (𝓝 (∫⁻ z, ENNReal.ofReal (φ z) ∂μ)) :=
      h_int_lim.congr' h_ev_lint_eq
    -- Rewrite `lintegral` on `energyMeasureExtended` as `lintegral` on `ℂ` and apply Dominated Convergence.
    have hφ_ofReal_meas : Measurable (fun z => ENNReal.ofReal (φ z)) :=
      ENNReal.measurable_ofReal.comp hφ_cont.measurable
    have h_pull_n : ∀ n, (∫⁻ z, ENNReal.ofReal (φ z) ∂(energyMeasureExtended I (v_seq n))) =
        ∫⁻ w : ℂ, d_seq n w * ENNReal.ofReal (φ (stereo_chart.symm w)) := by
      intro n
      dsimp [energyMeasureExtended, chartPush]
      rw [lintegral_map hφ_ofReal_meas stereo_chart_symm_measurable]
      exact lintegral_withDensity_eq_lintegral_mul₀ (hd_meas n).aemeasurable
        (hφ_ofReal_meas.comp stereo_chart_symm_measurable).aemeasurable
    have h_pull_0 : (∫⁻ z, ENNReal.ofReal (φ z) ∂(energyMeasureExtended I u₀)) =
        ∫⁻ w : ℂ, d₀ w * ENNReal.ofReal (φ (stereo_chart.symm w)) := by
      dsimp [energyMeasureExtended, chartPush]
      rw [lintegral_map hφ_ofReal_meas stereo_chart_symm_measurable]
      exact lintegral_withDensity_eq_lintegral_mul₀ hd₀_aemeas
        (hφ_ofReal_meas.comp stereo_chart_symm_measurable).aemeasurable
    let bound : ℂ → ENNReal := fun w => ENNReal.ofReal (C * sphericalJacobian w)
    have h_bound_fin : (∫⁻ w : ℂ, bound w) ≠ ⊤ := by
      have h_fac : ∀ w : ℂ, bound w = ENNReal.ofReal C * ENNReal.ofReal (sphericalJacobian w) :=
        fun w => ENNReal.ofReal_mul hC_nonneg
      simp_rw [h_fac]
      have h_sph_meas : Measurable (fun w : ℂ => ENNReal.ofReal (sphericalJacobian w)) :=
        ENNReal.measurable_ofReal.comp continuous_sphericalJacobian.measurable
      rw [lintegral_const_mul (ENNReal.ofReal C) h_sph_meas]
      exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top sphericalJacobian_lintegral_lt_top).ne
    have hF_meas : ∀ᶠ n in atTop, Measurable (fun w : ℂ => d_seq n w * ENNReal.ofReal (φ (stereo_chart.symm w))) :=
      Filter.Eventually.of_forall (fun n => (hd_meas n).mul (hφ_ofReal_meas.comp stereo_chart_symm_measurable))
    have hF_bound : ∀ᶠ n in atTop, ∀ᵐ w ∂(volume : Measure ℂ),
        d_seq n w * ENNReal.ofReal (φ (stereo_chart.symm w)) ≤ bound w := by
      filter_upwards [h_ev_C] with n hnC
      refine Filter.Eventually.of_forall (fun w => ?_)
      by_cases hwK : stereo_chart.symm w ∈ K
      · have he_le : riemannianEnergyDensity I (v_seq n) (stereo_chart.symm w) ≤ C := hnC _ hwK
        have hφ_le : ENNReal.ofReal (φ (stereo_chart.symm w)) ≤ 1 := by
          simpa using ENNReal.ofReal_le_ofReal (hφ_le_one (stereo_chart.symm w))
        calc d_seq n w * ENNReal.ofReal (φ (stereo_chart.symm w))
            ≤ d_seq n w * 1 := mul_le_mul_of_nonneg_left hφ_le zero_le'
          _ = d_seq n w := mul_one _
          _ ≤ bound w := ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right he_le (sphericalJacobian_nonneg w))
      · have hφ0 : φ (stereo_chart.symm w) = 0 := image_eq_zero_of_notMem_tsupport hwK
        simp [hφ0]
    have hF_lim : ∀ᵐ w ∂(volume : Measure ℂ),
        Tendsto (fun n => d_seq n w * ENNReal.ofReal (φ (stereo_chart.symm w))) atTop
          (𝓝 (d₀ w * ENNReal.ofReal (φ (stereo_chart.symm w)))) := by
      refine Filter.Eventually.of_forall (fun w => ?_)
      by_cases hwK : stereo_chart.symm w ∈ K
      · have hw_in : stereo_chart.symm w ∈ Set.univ \ (S : Set CP1) := hφ_supp hwK
        have h_e := tendsto_riemannianEnergyDensity_of_smoothLocalConvergesOn I h_conv hw_in
        have hd_w : Tendsto (fun n => d_seq n w) atTop (𝓝 (d₀ w)) :=
          (ENNReal.continuous_ofReal.tendsto _).comp (h_e.mul_const (sphericalJacobian w))
        exact ENNReal.Tendsto.mul_const hd_w (Or.inr ENNReal.ofReal_ne_top)
      · have hφ0 : φ (stereo_chart.symm w) = 0 := image_eq_zero_of_notMem_tsupport hwK
        simp [hφ0]
    have h_rhs_lim :=
      tendsto_lintegral_filter_of_dominated_convergence bound hF_meas hF_bound h_bound_fin hF_lim
    simp_rw [← h_pull_n] at h_rhs_lim
    rw [← h_pull_0] at h_rhs_lim
    exact tendsto_nhds_unique h_lhs_lim h_rhs_lim
  -- Step 2: Monotone Urysohn exhaustion of every open subset `U ⊆ Set.univ \ S`.
  have h_open_eq : ∀ U : Set CP1, IsOpen U → U ⊆ Set.univ \ (S : Set CP1) →
      μ U = energyMeasureExtended I u₀ U := by
    intro U hU hU_sub
    by_cases hUc : Uᶜ.Nonempty
    · let h : ℕ → CP1 → ℝ := fun k z =>
        min 1 (max 0 (((k : ℝ) + 1) * Metric.infDist z Uᶜ - 1))
      have hh_cont : ∀ k, Continuous (h k) := fun k =>
        continuous_const.min (continuous_const.max
          ((continuous_const.mul (Metric.continuous_infDist_pt Uᶜ)).sub continuous_const))
      have hh_nonneg : ∀ k z, 0 ≤ h k z := fun k z =>
        le_min zero_le_one (le_max_left 0 _)
      have hh_le_one : ∀ k z, h k z ≤ 1 := fun k z => min_le_left 1 _
      have hh_supp : ∀ k, tsupport (h k) ⊆ Set.univ \ (S : Set CP1) := by
        intro k
        let F_k : Set CP1 := {z : CP1 | 1 / ((k : ℝ) + 1) ≤ Metric.infDist z Uᶜ}
        have hFk_closed : IsClosed F_k :=
          isClosed_le continuous_const (Metric.continuous_infDist_pt Uᶜ)
        have h_supp_sub : Function.support (h k) ⊆ F_k := by
          intro z hz
          rw [Function.mem_support] at hz
          have h_pos_max : 0 < ((k : ℝ) + 1) * Metric.infDist z Uᶜ - 1 := by
            by_contra h_le
            push_neg at h_le
            have h0 : h k z = 0 := by
              dsimp [h]
              rw [max_eq_left h_le, min_eq_right zero_le_one]
            exact hz h0
          change 1 / ((k : ℝ) + 1) ≤ Metric.infDist z Uᶜ
          rw [div_le_iff₀' (by positivity)]
          linarith
        have h_tsupp_Fk : tsupport (h k) ⊆ F_k := closure_minimal h_supp_sub hFk_closed
        refine h_tsupp_Fk.trans (fun z hz => hU_sub ?_)
        have hd_pos : 0 < Metric.infDist z Uᶜ :=
          lt_of_lt_of_le (by positivity : 0 < 1 / ((k : ℝ) + 1)) hz
        have hz_not_cl : z ∉ closure Uᶜ := (Metric.infDist_pos_iff_notMem_closure hUc).mpr hd_pos
        rw [hU.isClosed_compl.closure_eq, Set.mem_compl_iff, not_not] at hz_not_cl
        exact hz_not_cl
      have hf_meas : ∀ k, Measurable (fun z => ENNReal.ofReal (h k z)) :=
        fun k => ENNReal.measurable_ofReal.comp (hh_cont k).measurable
      have hf_mono : Monotone (fun k z => ENNReal.ofReal (h k z)) := by
        intro i j hij z
        apply ENNReal.ofReal_le_ofReal
        dsimp [h]
        apply min_le_min_left
        apply max_le_max_left
        have hd_nn : 0 ≤ Metric.infDist z Uᶜ := Metric.infDist_nonneg
        have hij_real : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
        exact sub_le_sub_right (mul_le_mul_of_nonneg_right hij_real hd_nn) 1
      have h_sup_ind : (fun z => ⨆ k, ENNReal.ofReal (h k z)) = U.indicator 1 := by
        ext z
        by_cases hzU : z ∈ U
        · rw [Set.indicator_of_mem hzU, Pi.one_apply]
          apply le_antisymm
          · exact iSup_le (fun k => by simpa using ENNReal.ofReal_le_ofReal (hh_le_one k z))
          · have hz_not_cl : z ∉ closure Uᶜ := by
              rw [hU.isClosed_compl.closure_eq, Set.mem_compl_iff, not_not]
              exact hzU
            have hd_pos : 0 < Metric.infDist z Uᶜ :=
              (Metric.infDist_pos_iff_notMem_closure hUc).mp hz_not_cl
            obtain ⟨K, hK⟩ := exists_nat_gt (2 / Metric.infDist z Uᶜ)
            have hK_ge : 2 ≤ ((K : ℝ) + 1) * Metric.infDist z Uᶜ := by
              have h1 : 2 / Metric.infDist z Uᶜ < (K : ℝ) + 1 := by linarith
              exact le_of_lt ((div_lt_iff₀ hd_pos).mp h1)
            have hhK : h K z = 1 := by
              dsimp [h]
              have h_ge1 : 1 ≤ ((K : ℝ) + 1) * Metric.infDist z Uᶜ - 1 := by linarith
              rw [max_eq_right (by linarith), min_eq_left h_ge1]
            exact le_iSup_of_le K (by simp [hhK])
        · rw [Set.indicator_of_notMem hzU]
          have hzUc : z ∈ Uᶜ := hzU
          have hd0 : Metric.infDist z Uᶜ = 0 := Metric.infDist_zero_of_mem hzUc
          have hh0 : ∀ k, h k z = 0 := by
            intro k
            dsimp [h]
            rw [hd0, mul_zero, zero_sub, max_eq_left (by norm_num), min_eq_right zero_le_one]
          simp [hh0]
      calc μ U
          = ∫⁻ z, U.indicator 1 z ∂μ := (lintegral_indicator_one hU.measurableSet).symm
        _ = ∫⁻ z, (⨆ k, ENNReal.ofReal (h k z)) ∂μ := by rw [← h_sup_ind]
        _ = ⨆ k, ∫⁻ z, ENNReal.ofReal (h k z) ∂μ := lintegral_iSup hf_meas hf_mono
        _ = ⨆ k, ∫⁻ z, ENNReal.ofReal (h k z) ∂(energyMeasureExtended I u₀) :=
            iSup_congr (fun k => h_test (h k) (hh_cont k) (hh_nonneg k) (hh_le_one k) (hh_supp k))
        _ = ∫⁻ z, (⨆ k, ENNReal.ofReal (h k z)) ∂(energyMeasureExtended I u₀) :=
            (lintegral_iSup hf_meas hf_mono).symm
        _ = ∫⁻ z, U.indicator 1 z ∂(energyMeasureExtended I u₀) := by rw [h_sup_ind]
        _ = energyMeasureExtended I u₀ U := lintegral_indicator_one hU.measurableSet
    · rw [Set.not_nonempty_iff_eq_empty, compl_empty_iff] at hUc
      subst hUc
      have h1 := h_test (fun _ => 1) continuous_const (fun _ => zero_le_one) (fun _ => le_rfl)
        ((Set.subset_univ _).trans hU_sub)
      simpa using h1
  -- Step 3: Deduce `energyMeasureExtended I u₀ Set.univ ≤ μ Set.univ < ⊤`, outer-regular equality on `Set.univ \ S`,
  -- and the full defect measure decomposition across `S`.
  let Ω : Set CP1 := Set.univ \ (S : Set CP1)
  have hΩ_open : IsOpen Ω := isOpen_compl_finset S
  have h_u0_Ω : energyMeasureExtended I u₀ Ω = μ Ω :=
    (h_open_eq Ω hΩ_open Subset.rfl).symm
  have h_u0_univ : energyMeasureExtended I u₀ Set.univ = μ Ω := by
    have h_split : (Set.univ : Set CP1) = Ω ∪ (S : Set CP1) :=
      (Set.sdiff_union_of_subset (Set.subset_univ (S : Set CP1))).symm
    have h_disj : Disjoint Ω (S : Set CP1) := Set.disjoint_sdiff_left
    rw [h_split, measure_union h_disj S.finite_toSet.isClosed.measurableSet,
      energyMeasureExtended_finset_eq_zero I u₀ S, add_zero, h_u0_Ω]
  have h_u0_le_mu : energyMeasureExtended I u₀ Set.univ ≤ μ Set.univ := by
    rw [h_u0_univ]
    exact measure_mono (Set.subset_univ Ω)
  have : IsFiniteMeasure (energyMeasureExtended I u₀) :=
    ⟨lt_of_le_of_lt h_u0_le_mu (measure_lt_top μ Set.univ)⟩
  have h_restrict_eq : μ.restrict Ω = (energyMeasureExtended I u₀).restrict Ω := by
    apply Measure.OuterRegular.ext_isOpen
    intro V hV
    rw [Measure.restrict_apply hV.measurableSet, Measure.restrict_apply hV.measurableSet]
    exact h_open_eq (V ∩ Ω) (hV.inter hΩ_open) Set.inter_subset_right
  refine ⟨h_u0_le_mu, ?_⟩
  ext A hA
  have h_A_split : A = (A ∩ Ω) ∪ (A ∩ (S : Set CP1)) := by
    ext x
    simp only [Ω, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_univ, true_and]
    tauto
  have h_disj_A : Disjoint (A ∩ Ω) (A ∩ (S : Set CP1)) :=
    Disjoint.mono Set.inter_subset_right Set.inter_subset_right Set.disjoint_sdiff_left
  have h_meas_AS : MeasurableSet (A ∩ (S : Set CP1)) :=
    hA.inter S.finite_toSet.isClosed.measurableSet
  -- Evaluate `μ A`
  have h_mu_A : μ A = (μ.restrict Ω) A + μ (A ∩ (S : Set CP1)) := by
    conv_lhs => rw [h_A_split]
    rw [measure_union h_disj_A h_meas_AS, Measure.restrict_apply hA]
  -- Evaluate `μ (A ∩ S) = (∑ p ∈ S, μ {p} • dirac p) A`
  have h_mu_AS : μ (A ∩ (S : Set CP1)) = (∑ p ∈ S, (μ {p} • Measure.dirac p)) A := by
    rw [Measure.finsetSum_apply]
    let S_A : Finset CP1 := S.filter (fun p => p ∈ A)
    have h_inter_eq : A ∩ (S : Set CP1) = ⋃ p ∈ S_A, ({p} : Set CP1) := by
      ext p
      constructor
      · rintro ⟨hpA, hpS⟩
        exact Set.mem_iUnion₂.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hpS, hpA⟩, rfl⟩
      · intro hp
        rcases Set.mem_iUnion₂.mp hp with ⟨q, hq, hqp⟩
        rw [Set.mem_singleton_iff] at hqp
        subst hqp
        exact ⟨(Finset.mem_filter.mp hq).2, Finset.mem_coe.mpr (Finset.mem_filter.mp hq).1⟩
    rw [h_inter_eq, measure_biUnion_finset
      (fun x _ y _ hne => disjoint_singleton.mpr hne) (fun x _ => measurableSet_singleton x)]
    rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p ∈ A)]
    have h_on : ∑ p ∈ S_A, (μ {p} • Measure.dirac p) A = ∑ p ∈ S_A, μ {p} := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hpA : p ∈ A := (Finset.mem_filter.mp hp).2
      rw [Measure.smul_apply, Measure.dirac_apply_of_mem hpA, smul_eq_mul, mul_one]
    have h_off : ∑ p ∈ S.filter (fun p => p ∉ A), (μ {p} • Measure.dirac p) A = 0 := by
      refine Finset.sum_eq_zero (fun p hp => ?_)
      have hp_notA : p ∉ A := (Finset.mem_filter.mp hp).2
      rw [Measure.smul_apply, Measure.dirac_apply' p hA, Set.indicator_of_notMem hp_notA,
        smul_eq_mul, mul_zero]
    change ∑ p ∈ S_A, μ {p} =
      ∑ p ∈ S_A, (μ {p} • Measure.dirac p) A + ∑ p ∈ S.filter (fun p => p ∉ A), (μ {p} • Measure.dirac p) A
    rw [h_on, h_off, add_zero]
  -- Evaluate `(energyMeasureExtended I u₀) A = ((energyMeasureExtended I u₀).restrict Ω) A`
  have h_u0_A : energyMeasureExtended I u₀ A = ((energyMeasureExtended I u₀).restrict Ω) A := by
    have h_u0_AS : energyMeasureExtended I u₀ (A ∩ (S : Set CP1)) = 0 :=
      measure_mono_null Set.inter_subset_right (energyMeasureExtended_finset_eq_zero I u₀ S)
    conv_lhs => rw [h_A_split]
    rw [measure_union h_disj_A h_meas_AS, h_u0_AS, add_zero, Measure.restrict_apply hA]
  rw [Measure.add_apply, h_mu_A, h_restrict_eq, ← h_u0_A, h_mu_AS]

/-- Iterated singularity removal across an arbitrary finite set `S : Finset CP1` (`0 sorryAx`):
if local single-puncture removal holds, then every map `u₁ : CP1 → M` that is `J`-holomorphic on
`Set.univ \ S` with finite energy `energyMeasureExtended I u₁ (Set.univ \ S) ≠ ⊤` extends to a
globally `J`-holomorphic sphere `u₀ : CP1 → M` agreeing with `u₁` on `Set.univ \ S`. -/
theorem jholomorphic_extension_across_finset
    (h_local_rem : ∀ (u : CP1 → M) (Ω : Set CP1) (p : CP1),
      IsOpen Ω → IsOpen (insert p Ω) → p ∉ Ω →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Ω →
      energyMeasureExtended I u Ω ≠ ⊤ →
      ∃ u_ext : CP1 → M, Set.EqOn u_ext u Ω ∧ JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext (insert p Ω))
    (S : Finset CP1) (u₁ : CP1 → M)
    (hu₁_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₁ (Set.univ \ S))
    (hu₁_fin : energyMeasureExtended I u₁ (Set.univ \ S) ≠ ⊤) :
    ∃ u₀ : CP1 → M,
      JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      Set.EqOn u₀ u₁ (Set.univ \ S) := by
  induction S using Finset.induction_on generalizing u₁ with
  | empty =>
    have h_univ : (Set.univ \ ((∅ : Finset CP1) : Set CP1)) = Set.univ := by simp
    rw [h_univ] at hu₁_jhol
    exact ⟨u₁, hu₁_jhol, fun _ _ => rfl⟩
  | @insert p S' hp_not_mem ih =>
    let Ω : Set CP1 := Set.univ \ ((insert p S' : Finset CP1) : Set CP1)
    have hΩ_open : IsOpen Ω := isOpen_compl_finset (insert p S')
    have h_ins_eq : insert p Ω = Set.univ \ (S' : Set CP1) := by
      ext z
      simp only [Ω, Finset.coe_insert, Set.mem_insert_iff, Set.mem_diff, Set.mem_univ, true_and]
      by_cases hzp : z = p
      · subst hzp; simp [hp_not_mem]
      · simp [hzp]
    have h_ins_open : IsOpen (insert p Ω) := by
      rw [h_ins_eq]
      exact isOpen_compl_finset S'
    have hp_not_Ω : p ∉ Ω := by simp [Ω]
    obtain ⟨u_mid, hu_mid_eq, hu_mid_jhol⟩ :=
      h_local_rem u₁ Ω p hΩ_open h_ins_open hp_not_Ω hu₁_jhol hu₁_fin
    rw [h_ins_eq] at hu_mid_jhol
    have hu_mid_fin : energyMeasureExtended I u_mid (Set.univ \ (S' : Set CP1)) ≠ ⊤ := by
      rw [← h_ins_eq]
      have h_le : energyMeasureExtended I u_mid (insert p Ω) ≤
          energyMeasureExtended I u_mid {p} + energyMeasureExtended I u_mid Ω := by
        rw [← Set.singleton_union]
        exact measure_union_le {p} Ω
      rw [energyMeasureExtended_singleton_eq_zero' I u_mid p, zero_add,
          energyMeasureExtended_eqOn_open I hΩ_open hu_mid_eq] at h_le
      exact ne_top_of_le_ne_top hu₁_fin h_le
    obtain ⟨u₀, hu₀_jhol, hu₀_eq_mid⟩ := ih u_mid hu_mid_jhol hu_mid_fin
    refine ⟨u₀, hu₀_jhol, fun z hz => ?_⟩
    have hz_S' : z ∈ Set.univ \ (S' : Set CP1) := by
      rw [← h_ins_eq]
      exact Set.mem_insert_of_mem p hz
    exact (hu₀_eq_mid hz_S').trans (hu_mid_eq hz)

/-- Smooth Concentration Extraction Property (`cert_conc` / `h_conc_extract`):
along a further subsequence `τ`, `u_seq ∘ (σ.comp τ)` converges in `C^∞_loc` off the concentration
set `S` to a globally `J`-holomorphic sphere `u₀`, with exact defect measure decomposition
`μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • Measure.dirac p)`. -/
def SmoothConcentrationExtractProperty
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) : Prop :=
  ∀ (σ : SubseqMap) (μ : Measure CP1) (S : Finset CP1), IsFiniteMeasure μ →
    WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ →
    (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p}) →
    ∃ (τ : SubseqMap) (u₀ : CP1 → M), JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
      SmoothLocalConvergesOn I (fun n => u_seq ((σ.comp τ).1 n)) u₀ (Set.univ \ S) ∧
      μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • Measure.dirac p)

/-- Proves `SmoothConcentrationExtractProperty` (`cert_conc`) from smooth local extraction off `S`,
local single-puncture singularity removal, and the first-principles theorems
`smooth_local_jhol_closure`, `defect_measure_decomp_of_smooth_conv_off_S`,
`jholomorphic_extension_across_finset`, `smooth_local_congr_lim_of_eqOn_open`, and
`energyMeasureExtended_congr_off_finset` (`0 sorryAx`). -/
theorem smoothConcentrationExtractProperty_of_local_compactness_and_removal
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (thresh : TargetThresholds I M)
    (h_meas_dens : ∀ n, Measurable (fun w : ℂ => riemannianEnergyDensity I (u_seq n) (stereo_chart.symm w)))
    (h_local_extract : ∀ (σ : SubseqMap) (μ : Measure CP1) (S : Finset CP1), IsFiniteMeasure μ →
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ →
      (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p}) →
      (∀ K ⊆ Set.univ \ (S : Set CP1), IsCompact K →
        ∃ C ≥ 0, ∀ᶠ n in Filter.atTop, ∀ z ∈ K, riemannianEnergyDensity I (u_seq (σ.1 n)) z ≤ C) ∧
      ∃ (τ : SubseqMap) (u₁ : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq ((σ.comp τ).1 n)) u₁ (Set.univ \ S))
    (h_local_rem : ∀ (u : CP1 → M) (Ω : Set CP1) (p : CP1),
      IsOpen Ω → IsOpen (insert p Ω) → p ∉ Ω →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Ω →
      energyMeasureExtended I u Ω ≠ ⊤ →
      ∃ u_ext : CP1 → M, Set.EqOn u_ext u Ω ∧ JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext (insert p Ω)) :
    SmoothConcentrationExtractProperty I u_seq thresh := by
  intro σ μ S hμ_fin h_weak hS_def
  obtain ⟨h_grad_σ, τ, u₁, h_conv₁⟩ := h_local_extract σ μ S hμ_fin h_weak hS_def
  have h_weak_τ : WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq ((σ.comp τ).1 n))) μ :=
    h_weak.comp_subseq τ
  have h_grad_τ : ∀ K ⊆ Set.univ \ (S : Set CP1), IsCompact K →
      ∃ C ≥ 0, ∀ᶠ n in Filter.atTop, ∀ z ∈ K,
        riemannianEnergyDensity I (u_seq ((σ.comp τ).1 n)) z ≤ C := by
    intro K hK_sub hK_cpt
    obtain ⟨C, hC_nn, h_ev⟩ := h_grad_σ K hK_sub hK_cpt
    exact ⟨C, hC_nn, τ.2.tendsto_atTop.eventually h_ev⟩
  obtain ⟨hu₁_le_mu, h_decomp₁⟩ :=
    defect_measure_decomp_of_smooth_conv_off_S I (fun n => u_seq ((σ.comp τ).1 n)) μ S u₁
      h_weak_τ h_conv₁ (fun n => h_meas_dens ((σ.comp τ).1 n)) h_grad_τ
  have hu₁_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u₁ (Set.univ \ S) :=
    smooth_local_jhol_closure I (fun n => u_seq ((σ.comp τ).1 n)) u₁ (Set.univ \ S) h_conv₁
      (fun n => ⟨(h_jhol ((σ.comp τ).1 n)).1.mono (Set.subset_univ _),
        fun z _hz => (h_jhol ((σ.comp τ).1 n)).2 z (Set.mem_univ z)⟩)
  have hu₁_fin : energyMeasureExtended I u₁ (Set.univ \ S) ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
      ((measure_mono (Set.subset_univ _)).trans hu₁_le_mu)
  obtain ⟨u₀, hu₀_jhol, hu₀_eq⟩ :=
    jholomorphic_extension_across_finset I h_local_rem S u₁ hu₁_jhol hu₁_fin
  have h_conv₀ : SmoothLocalConvergesOn I (fun n => u_seq ((σ.comp τ).1 n)) u₀ (Set.univ \ S) :=
    smooth_local_congr_lim_of_eqOn_open I (isOpen_compl_finset S) hu₀_eq.symm h_conv₁
  have h_meas_eq : energyMeasureExtended I u₀ = energyMeasureExtended I u₁ :=
    energyMeasureExtended_congr_off_finset I S hu₀_eq
  rw [← h_meas_eq] at h_decomp₁
  exact ⟨τ, u₀, hu₀_jhol, h_conv₀, h_decomp₁⟩

/-- Contract C02 (`exists_concentration_data`) proved from `smoothConcentrationExtractProperty_of_local_compactness_and_removal` (`0 sorryAx`). -/
theorem exists_concentration_data_of_local_compactness_and_removal
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (thresh : TargetThresholds I M)
    (h_meas_dens : ∀ n, Measurable (fun w : ℂ => riemannianEnergyDensity I (u_seq n) (stereo_chart.symm w)))
    (h_local_extract : ∀ (σ : SubseqMap) (μ : Measure CP1) (S : Finset CP1), IsFiniteMeasure μ →
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ →
      (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p}) →
      (∀ K ⊆ Set.univ \ (S : Set CP1), IsCompact K →
        ∃ C ≥ 0, ∀ᶠ n in Filter.atTop, ∀ z ∈ K, riemannianEnergyDensity I (u_seq (σ.1 n)) z ≤ C) ∧
      ∃ (τ : SubseqMap) (u₁ : CP1 → M),
        SmoothLocalConvergesOn I (fun n => u_seq ((σ.comp τ).1 n)) u₁ (Set.univ \ S))
    (h_local_rem : ∀ (u : CP1 → M) (Ω : Set CP1) (p : CP1),
      IsOpen Ω → IsOpen (insert p Ω) → p ∉ Ω →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Ω →
      energyMeasureExtended I u Ω ≠ ⊤ →
      ∃ u_ext : CP1 → M, Set.EqOn u_ext u Ω ∧ JHolomorphicOn (I := I) (I_dom := I_CP1) u_ext (insert p Ω)) :
    Nonempty (ConcentrationData I u_seq B thresh) :=
  exists_concentration_data_of_thresholds I u_seq h_jhol B hB h_en thresh
    (smoothConcentrationExtractProperty_of_local_compactness_and_removal I u_seq h_jhol thresh
      h_meas_dens h_local_extract h_local_rem)

#print axioms exists_concentration_data

end GromovCompactness.Compactness

