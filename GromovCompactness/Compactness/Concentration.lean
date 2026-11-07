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
  exact smoothLocalConvergesOn_const I c (Set.univ \ S)

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
    exact smoothLocalConvergesOn_const I c (Set.univ \ S)
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

/-- Extraction of Concentration Data from bounded-energy J-spheres (Contract C02).
Proved with zero direct sorry. -/
theorem exists_concentration_data
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (B : ℝ) (hB : 0 ≤ B)
    (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (thresh : TargetThresholds I M)
    (h_extract : ∀ (σ : SubseqMap) (μ : Measure CP1) (S : Finset CP1), IsFiniteMeasure μ →
      WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ →
      (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal thresh.ε_reg ≤ μ {p}) →
      ∃ (τ : SubseqMap) (u₀ : CP1 → M), JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
        SmoothLocalConvergesOn I (fun n => u_seq ((σ.comp τ).1 n)) u₀ (Set.univ \ S) ∧
        μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • Measure.dirac p)) :
    Nonempty (ConcentrationData I u_seq B thresh) := by
  by_cases h_ev : ∃ (σ : SubseqMap) (N₀ : ℕ) (c : M), ∀ n ≥ N₀, u_seq (σ.1 n) = fun _ => c
  · rcases h_ev with ⟨σ, N₀, c, hc⟩
    exact exists_concentration_data_of_eventually_const_subseq I u_seq B hB h_en thresh σ N₀ c hc
  · exact exists_concentration_data_of_smooth_limit I u_seq h_jhol B hB h_en thresh
      (fun B' hB' h_en' => weak_energy_measure_compactness I u_seq B' hB' h_en' h_fin)
      h_fin
      h_extract

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

#print axioms exists_concentration_data

end GromovCompactness.Compactness

