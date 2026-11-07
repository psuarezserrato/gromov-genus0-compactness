/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Analysis.Hofer
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EpsilonRegularity
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.SingularityRemoval

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory Filter GromovCompactness Finset

namespace GromovCompactness.Analysis

/-!
# Tasks B01 & B02: Universal Threshold and Calibrated Rescaling

This module formalizes:
1. `TargetThresholds` (Contract B01): Universal positive bubbling threshold constant
   $0 < h \le \min(\frac{1}{2}\varepsilon_{\mathrm{reg}}, \, \varepsilon_{\mathrm{sph}}, \, \frac{1}{2}\varepsilon_{\mathrm{neck}})$,
   packaged into an immutable structure.
2. `exists_target_thresholds_of_modules` (Contract B01): Conditional reduction theorem
   assembling the uniform constants $(\varepsilon_{\mathrm{reg}}, \varepsilon_{\mathrm{sph}}, \dots)$ from geometric modules.
   `exists_target_thresholds` (Contract B01): Top-level existence theorem assembling the reduction
   with upstream geometric results.
3. `CalibratedRescaling` (Contract B02): Moving centers $a_n \to 0$ and radii $\lambda_n \to 0$
   satisfying the exact calibration identity $E(u_n; D_{\lambda_n}(a_n)) = m_p - h/2$.
4. `exists_calibrated_rescaling_of_ivt` and `exists_calibrated_rescaling` (Contract B02):
   Extraction theorems via the Radial Intermediate Value Theorem (`RadialEnergyIVT`).

These structures and theorems are also exported/aliased in namespace `GromovCompactness.Bubbling`
to align with the blueprint bindings `b01:threshold_h` and `b02:calibration`.

References:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §2.2.
- Sergei Ivashkovich & Vsevolod Shevchishin, arXiv:math/9912046, §2.3.
- `gromov_compactness.pdf` §4.5, §4.6, & §6 (Stress Cases 5 & 6).
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/- =========================================================================
   SECTION 1: METRIC, TOPOLOGICAL, AND TENDSTO FOUNDATIONS (Zero-sorry)
   ========================================================================= -/

/-- Sequence 1 / (n + 1) converges to 0 at top. -/
lemma tendsto_inv_succ :
    Tendsto (fun (n : ℕ) => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Tendsto to zero for 1 / (n + 1) sequence on ℝ (alias). -/
lemma tendsto_one_div_succ_zero :
    Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_inv_succ

/-- Squeeze lemma for distances bounded by 1 / (n + 1). -/
lemma tendsto_dist_zero_of_le_inv_succ {X : Type*} [MetricSpace X]
    (x_seq : ℕ → X) (x₀ : X)
    (h_dist : ∀ n, dist (x_seq n) x₀ ≤ 1 / ((n : ℝ) + 1)) :
    Tendsto x_seq atTop (𝓝 x₀) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_inv_succ ?_ h_dist
  intro n
  exact dist_nonneg

/-- Squeeze lemma for positive scales bounded by 1 / (n + 1). -/
lemma tendsto_scale_zero_of_le_inv_succ
    (lam_seq : ℕ → ℝ) (h_pos : ∀ n, 0 < lam_seq n)
    (h_le : ∀ n, lam_seq n ≤ 1 / ((n : ℝ) + 1)) :
    Tendsto lam_seq atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_inv_succ ?_ h_le
  intro n
  exact (h_pos n).le

/-- The stereographic disk of radius 0 is empty. -/
lemma disk_at_zero (a : ℂ) : disk_at a 0 = ∅ := by
  dsimp [disk_at]
  rw [ball_zero]
  exact Set.image_empty _

/-- The energy measure of an empty set is 0. -/
lemma energyMeasure_empty (u : CP1 → M) : energyMeasure I u ∅ = 0 := by
  dsimp [energyMeasure, energyMeasureExtended, chartPush]
  simp

/-- The energy measure of a zero-radius disk vanishes. -/
lemma energyMeasure_disk_at_zero (u : CP1 → M) (a : ℂ) :
    energyMeasure I u (disk_at a 0) = 0 := by
  rw [disk_at_zero, energyMeasure_empty]

/- =========================================================================
   SECTION 2: MEASURE-THEORETIC DEFECT & CONCENTRATION FOUNDATIONS (Zero-sorry)
   ========================================================================= -/

section EnergyDefectFoundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Concentric closed balls of radius 1 / (n + 1) form an antitone sequence. -/
lemma antitone_closedBall_inv_succ (x : X) :
    Antitone (fun n : ℕ => closedBall x (1 / ((n : ℝ) + 1))) := by
  intro m n hmn
  apply closedBall_subset_closedBall
  have h1 : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by simp [hmn]
  have hpos : 0 < (m : ℝ) + 1 := by positivity
  exact one_div_le_one_div_of_le hpos h1

/-- Continuity from above: The measure of shrinking concentric closed balls converges to the singleton atom. -/
lemma tendsto_measure_closedBall_inv_succ (μ : Measure X) [IsFiniteMeasure μ] (x : X) :
    Filter.Tendsto (fun n : ℕ => μ (closedBall x (1 / ((n : ℝ) + 1))))
      Filter.atTop (nhds (μ {x})) := by
  have h_anti := antitone_closedBall_inv_succ x
  have h_meas : ∀ n : ℕ, NullMeasurableSet (closedBall x (1 / ((n : ℝ) + 1))) μ :=
    fun n => measurableSet_closedBall.nullMeasurableSet
  have h_inter : (⋂ n : ℕ, closedBall x (1 / ((n : ℝ) + 1))) = {x} := by
    ext y
    simp only [mem_iInter, mem_closedBall, mem_singleton_iff]
    constructor
    · intro h
      have h_zero : dist y x = 0 := by
        apply le_antisymm _ dist_nonneg
        have h_lim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        exact ge_of_tendsto h_lim (Filter.Eventually.of_forall h)
      exact dist_eq_zero.mp h_zero
    · rintro rfl n
      simp only [dist_self]
      positivity
  have h_finite : ∃ i : ℕ, μ (closedBall x (1 / ((i : ℝ) + 1))) ≠ ⊤ :=
    ⟨0, measure_ne_top μ _⟩
  have h_lim := tendsto_measure_iInter_atTop h_meas h_anti h_finite
  rw [h_inter] at h_lim
  exact h_lim

/-- Point concentration of measure is equivalent to the existence of an atom of mass ≥ ε₀. -/
theorem atom_iff_concentration (μ : Measure X) [IsFiniteMeasure μ] (x : X) (ε₀ : ℝ) :
    ENNReal.ofReal ε₀ ≤ μ {x} ↔ ∀ r > 0, ENNReal.ofReal ε₀ ≤ μ (closedBall x r) := by
  constructor
  · intro h r hr
    have h_sub : ({x} : Set X) ⊆ closedBall x r := by
      rw [Set.singleton_subset_iff, mem_closedBall, dist_self]
      exact hr.le
    exact le_trans h (measure_mono h_sub)
  · intro h
    have h_seq : ∀ n : ℕ, ENNReal.ofReal ε₀ ≤ μ (closedBall x (1 / ((n : ℝ) + 1))) := by
      intro n
      apply h
      positivity
    have h_lim := tendsto_measure_closedBall_inv_succ μ x
    exact ge_of_tendsto h_lim (Filter.Eventually.of_forall h_seq)

/-- Contract B01: Equivalence between defect atom and energy concentration.
When the regular part of the limit measure is atomless (e.g. continuous energy density
of a smooth J-holomorphic curve), the defect measure has an atom of mass ≥ ε₀ at x
if and only if every metric neighborhood of x concentrates energy ≥ ε₀. -/
theorem has_energy_defect_iff_concentration
    (μ_reg ν_defect : Measure X) [IsFiniteMeasure μ_reg] [IsFiniteMeasure ν_defect]
    (h_reg_null : ∀ x, μ_reg {x} = 0) (x : X) (ε₀ : ℝ) :
    ENNReal.ofReal ε₀ ≤ ν_defect {x} ↔
    ∀ r > 0, ENNReal.ofReal ε₀ ≤ (μ_reg + ν_defect) (closedBall x r) := by
  have h_sum_atom : (μ_reg + ν_defect) {x} = ν_defect {x} := by
    simp only [Measure.add_apply, h_reg_null x, zero_add]
  have h_equiv := atom_iff_concentration (X := X) (μ := μ_reg + ν_defect) x ε₀
  rw [h_sum_atom] at h_equiv
  exact h_equiv

end EnergyDefectFoundations

section CardinalityBounds

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Finite sum bound on atoms: Any finite set of atoms of mass ≥ ε₀ satisfies |S| * ε₀ ≤ E₀. -/
theorem card_le_of_atoms
    (μ : Measure α) (E₀ ε₀ : ℝ) (hE₀ : 0 ≤ E₀) (h_tot : μ univ ≤ ENNReal.ofReal E₀)
    (S : Finset α) (hS : ∀ x ∈ S, ENNReal.ofReal ε₀ ≤ μ {x}) :
    (S.card : ℝ) * ε₀ ≤ E₀ := by
  have h_meas : ∀ b ∈ S, MeasurableSet ({b} : Set α) :=
    fun b _ => measurableSet_singleton b
  have h_disj : (S : Set α).PairwiseDisjoint (fun x => ({x} : Set α)) := by
    intro x _ y _ hne
    exact disjoint_singleton.mpr hne
  have h_sum_eq := measure_biUnion_finset h_disj h_meas (μ := μ)
  have h_le_univ : μ (⋃ b ∈ S, ({b} : Set α)) ≤ μ (univ : Set α) :=
    measure_mono (subset_univ _)
  have h_sum_le : (∑ x ∈ S, μ {x}) ≤ μ (univ : Set α) := by
    rw [← h_sum_eq]
    exact h_le_univ
  have h_sum_bound : (∑ x ∈ S, μ {x}) ≤ ENNReal.ofReal E₀ :=
    h_sum_le.trans h_tot
  have h1 : ∑ x ∈ S, ENNReal.ofReal ε₀ ≤ ∑ x ∈ S, μ {x} :=
    sum_le_sum (fun x hx => hS x hx)
  rw [sum_const, nsmul_eq_mul] at h1
  have h_mul_le := h1.trans h_sum_bound
  have h_rw : (S.card : ENNReal) * ENNReal.ofReal ε₀ = ENNReal.ofReal ((S.card : ℝ) * ε₀) := by
    have h_c : (S.card : ENNReal) = ENNReal.ofReal (S.card : ℝ) := by simp
    rw [h_c, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  rw [h_rw] at h_mul_le
  exact (ENNReal.ofReal_le_ofReal_iff hE₀).mp h_mul_le

/-- Finiteness of the singular set of atoms of mass ≥ ε₀. -/
theorem finite_atoms_of_bounded_measure
    (μ : Measure α) (E₀ ε₀ : ℝ) (hε : 0 < ε₀) (hE₀ : 0 ≤ E₀)
    (h_tot : μ univ ≤ ENNReal.ofReal E₀) :
    {x : α | ENNReal.ofReal ε₀ ≤ μ {x}}.Finite := by
  by_contra h_inf
  have h_inf' : Set.Infinite {x : α | ENNReal.ofReal ε₀ ≤ μ {x}} := h_inf
  let N := Nat.ceil (E₀ / ε₀ + 1)
  obtain ⟨t, ht_sub, ht_card⟩ := h_inf'.exists_subset_card_eq N
  have ht_atoms : ∀ x ∈ t, ENNReal.ofReal ε₀ ≤ μ {x} := by
    intro x hx
    exact ht_sub (Finset.mem_coe.mp hx)
  have h_card_le := card_le_of_atoms μ E₀ ε₀ hE₀ h_tot t ht_atoms
  have h_div : (t.card : ℝ) ≤ E₀ / ε₀ := by
    exact (le_div_iff₀ hε).mpr (by linarith [mul_comm (t.card : ℝ) ε₀])
  have h_N_gt : E₀ / ε₀ < (N : ℝ) := by
    have h1 : E₀ / ε₀ < E₀ / ε₀ + 1 := by linarith
    have h2 : E₀ / ε₀ + 1 ≤ (Nat.ceil (E₀ / ε₀ + 1) : ℝ) := Nat.le_ceil _
    exact lt_of_lt_of_le h1 h2
  rw [ht_card] at h_div
  linarith

/-- The cardinality bound on the singular set of atoms: |S| ≤ E₀ / ε₀. -/
theorem atoms_card_le
    (μ : Measure α) (E₀ ε₀ : ℝ) (hε : 0 < ε₀) (hE₀ : 0 ≤ E₀)
    (h_tot : μ univ ≤ ENNReal.ofReal E₀)
    (h_fin : {x : α | ENNReal.ofReal ε₀ ≤ μ {x}}.Finite) :
    (h_fin.toFinset.card : ℝ) ≤ E₀ / ε₀ := by
  have hS : ∀ x ∈ h_fin.toFinset, ENNReal.ofReal ε₀ ≤ μ {x} := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    exact hx
  have h := card_le_of_atoms μ E₀ ε₀ hE₀ h_tot h_fin.toFinset hS
  exact (le_div_iff₀ hε).mpr (by linarith [mul_comm (h_fin.toFinset.card : ℝ) ε₀])

end CardinalityBounds

/- =========================================================================
   SECTION 3: UNIVERSAL BUBBLING THRESHOLD h > 0 (Contract B01, Zero-sorry)
   ========================================================================= -/

/-- TargetThresholds bundles the universal positive bubbling threshold `h > 0` (Contract B01).
It is bounded above by `min(ε_reg / 2, ε_sph, ε_neck / 2)` and fixed once for the target manifold,
bundled with proofs that the thresholds satisfy epsilon-regularity, sphere energy gap, and
cylinder exponential collar decay. -/
structure TargetThresholds (I : ModelWithCorners ℝ E H) (M : Type*)
    [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    [ClosedTameTarget I M] where
  ε_reg : ℝ
  ε_reg_pos : 0 < ε_reg
  C_reg : ℝ
  C_reg_pos : 0 < C_reg
  h_reg : ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_ : 0 < r),
    Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1 →
    JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
    energyMeasure I u (disk_at a r) < ε_reg →
    ∀ z ∈ disk_at a (r / 2),
      riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r)
  ε_sph : ℝ
  ε_sph_pos : 0 < ε_sph
  h_sph : ∀ (u : CP1 → M),
    JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
    (¬ ∃ c : M, ∀ z, u z = c) →
    ε_sph ≤ totalEnergy I u
  ε_neck : ℝ
  ε_neck_pos : 0 < ε_neck
  C_neck : ℝ
  C_neck_pos : 0 < C_neck
  a_decay : ℝ
  a_decay_pos : 0 < a_decay
  h_neck : ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
    0 < r → 2 * r < R →
    JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
    energyMeasure I u (annulus_at center r R) < ε_neck →
    ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
      energyMeasure I u (annulus_at center r₁ r₂) ≤
        C_neck * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R)
  h : ℝ
  h_pos : 0 < h
  h_le_reg : h ≤ ε_reg / 2
  h_le_sph : h ≤ ε_sph
  h_le_neck : h ≤ ε_neck / 2

/-- Construct `TargetThresholds` directly from the geometric constants. -/
noncomputable def make_target_thresholds
    (ε_reg C_reg : ℝ) (hε_reg : 0 < ε_reg) (hC_reg : 0 < C_reg)
    (h_reg : ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_ : 0 < r),
      Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1 →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (disk_at a r) < ε_reg →
      ∀ z ∈ disk_at a (r / 2),
        riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r))
    (ε_sph : ℝ) (hε_sph : 0 < ε_sph)
    (h_sph : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u)
    (C_neck a_decay ε_neck : ℝ) (hC_neck : 0 < C_neck) (ha_decay : 0 < a_decay) (hε_neck : 0 < ε_neck)
    (h_neck : ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          C_neck * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R)) :
    TargetThresholds I M :=
  let h := min (ε_reg / 2) (min ε_sph (ε_neck / 2))
  have h_pos : 0 < h := by
    have h1 : 0 < ε_reg / 2 := by linarith
    have h2 : 0 < ε_neck / 2 := by linarith
    exact lt_min h1 (lt_min hε_sph h2)
  have h_le_reg : h ≤ ε_reg / 2 := min_le_left _ _
  have h_le_sph : h ≤ ε_sph := le_trans (min_le_right _ _) (min_le_left _ _)
  have h_le_neck : h ≤ ε_neck / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  ⟨ε_reg, hε_reg, C_reg, hC_reg, h_reg,
   ε_sph, hε_sph, h_sph,
   ε_neck, hε_neck, C_neck, hC_neck, a_decay, ha_decay, h_neck,
   h, h_pos, h_le_reg, h_le_sph, h_le_neck⟩

/-- Conditional reduction theorem: Given the geometric modules A03, A07, and A10,
the universal positive bubbling threshold exists constructively.
Note (Conditional Reduction per COMPLETION_PLAN.md §0 & §2 P0-9):
Takes open geometric contract hypotheses and does not count as closing Contract B01 unconditionally. -/
theorem exists_target_thresholds_of_modules
    (ε_reg C_reg : ℝ) (h_reg_pos : 0 < ε_reg) (h_Creg_pos : 0 < C_reg)
    (h_reg : ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_ : 0 < r),
      Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1 →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (disk_at a r) < ε_reg →
      ∀ z ∈ disk_at a (r / 2),
        riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r))
    (ε_sph : ℝ) (h_sph_pos : 0 < ε_sph)
    (h_sph : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u)
    (C_neck a_decay ε_neck : ℝ)
    (h_Cneck_pos : 0 < C_neck) (h_a_pos : 0 < a_decay) (h_neck_pos : 0 < ε_neck)
    (h_neck : ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
      0 < r → 2 * r < R →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasure I u (annulus_at center r R) < ε_neck →
      ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
        energyMeasure I u (annulus_at center r₁ r₂) ≤
          C_neck * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R)) :
    Nonempty (TargetThresholds I M) :=
  ⟨make_target_thresholds I ε_reg C_reg h_reg_pos h_Creg_pos h_reg
     ε_sph h_sph_pos h_sph C_neck a_decay ε_neck h_Cneck_pos h_a_pos h_neck_pos h_neck⟩

/-- When `M` is a subsingleton, every map `CP1 → M` is constant with zero energy density and
`TargetThresholds I M` exists unconditionally with `0 sorryAx`. -/
theorem exists_target_thresholds_of_subsingleton
    (h_sub : Subsingleton M) :
    Nonempty (TargetThresholds I M) := by
  refine exists_target_thresholds_of_modules I 1 1 zero_lt_one zero_lt_one ?_
    1 zero_lt_one ?_ 1 1 1 zero_lt_one zero_lt_one zero_lt_one ?_
  · intro u a r hr _ _ _ z _
    have hc : u = fun _ => u north_pole := funext (fun w => h_sub.elim (u w) (u north_pole))
    have hd0 : riemannianEnergyDensity I u z = 0 := by
      rw [hc]
      exact energy_density_const_map I (u north_pole) z
    have h_en_nonneg : 0 ≤ energyMeasure I u (disk_at a r) := energy_nonneg I u (disk_at a r)
    have hr_pos : 0 ≤ 1 * r ^ (-2 : ℝ) := by positivity
    rw [hd0]
    exact mul_nonneg hr_pos h_en_nonneg
  · intro u _ h_nonconst
    exfalso
    exact h_nonconst ⟨u north_pole, fun z => h_sub.elim (u z) (u north_pole)⟩
  · intro u center r R _ _ _ _ r₁ r₂ _ _ _
    have hc : u = fun _ => u north_pole := funext (fun w => h_sub.elim (u w) (u north_pole))
    have h_en0 : ∀ s, energyMeasure I u s = 0 := by
      intro s
      rw [hc]
      exact energyMeasure_const I (u north_pole) s
    rw [h_en0, h_en0, mul_zero]

/-- On a discrete target `[DiscreteTopology M]`, `TargetThresholds I M` exists unconditionally with `0 sorryAx`. -/
theorem exists_target_thresholds_of_discrete [DiscreteTopology M] :
    Nonempty (TargetThresholds I M) := by
  obtain ⟨ε_reg, C_reg, hε_reg, hC_reg, h_reg⟩ := epsilon_regularity_of_discrete (M := M) I
  obtain ⟨ε_sph, hε_sph, h_sph⟩ := sphere_energy_gap_of_discrete (M := M) I
  obtain ⟨C_neck, a_decay, ε_neck, hC_neck, ha_decay, hε_neck, h_neck⟩ :=
    cylinder_exponential_decay_of_discrete (M := M) I
  exact exists_target_thresholds_of_modules I ε_reg C_reg hε_reg hC_reg
    (fun u a r hr _ => h_reg u a r hr)
    ε_sph hε_sph h_sph C_neck a_decay ε_neck hC_neck ha_decay hε_neck h_neck

/-- Conditional reduction of `exists_target_thresholds` from existentially packaged geometric
estimates (`epsilon_regularity`, `sphere_energy_gap`, `cylinder_exponential_decay`) (`0 sorryAx`). -/
theorem exists_target_thresholds_of_existentials
    (h_reg_ex : ∃ (ε_reg C_reg : ℝ), 0 < ε_reg ∧ 0 < C_reg ∧
      ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_ : 0 < r),
        Metric.ball a r ⊆ Metric.closedBall (0 : ℂ) 1 →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        energyMeasure I u (disk_at a r) < ε_reg →
        ∀ z ∈ disk_at a (r / 2),
          riemannianEnergyDensity I u z ≤ C_reg * r^(-2 : ℝ) * energyMeasure I u (disk_at a r))
    (h_sph_ex : ∃ (ε_sph : ℝ), 0 < ε_sph ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        (¬ ∃ c : M, ∀ z, u z = c) →
        ε_sph ≤ totalEnergy I u)
    (h_neck_ex : ∃ (C_neck a_decay ε_neck : ℝ), 0 < C_neck ∧ 0 < a_decay ∧ 0 < ε_neck ∧
      ∀ (u : CP1 → M) (center : ℂ) (r R : ℝ),
        0 < r → 2 * r < R →
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        energyMeasure I u (annulus_at center r R) < ε_neck →
        ∀ (r₁ r₂ : ℝ), r < r₁ → r₁ < r₂ → r₂ < R →
          energyMeasure I u (annulus_at center r₁ r₂) ≤
            C_neck * ((r / r₁)^a_decay + (r₂ / R)^a_decay) * energyMeasure I u (annulus_at center r R)) :
    Nonempty (TargetThresholds I M) := by
  obtain ⟨ε_reg, C_reg, hε_reg, hC_reg, h_reg⟩ := h_reg_ex
  obtain ⟨ε_sph, hε_sph, h_sph⟩ := h_sph_ex
  obtain ⟨C_neck, a_decay, ε_neck, hC_neck, ha_decay, hε_neck, h_neck⟩ := h_neck_ex
  exact exists_target_thresholds_of_modules I ε_reg C_reg hε_reg hC_reg h_reg
    ε_sph hε_sph h_sph C_neck a_decay ε_neck hC_neck ha_decay hε_neck h_neck

/-- When every globally `J`-holomorphic sphere `u : CP1 → M` is constant, `TargetThresholds I M`
exists unconditionally (`0 sorryAx`). -/
theorem exists_target_thresholds_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c) :
    Nonempty (TargetThresholds I M) :=
  exists_target_thresholds_of_existentials I
    (let ⟨ε_reg, C_reg, hε, hC, h_reg⟩ := epsilon_regularity_of_all_jhol_const (M := M) I
      (fun u hu => let ⟨c, hc⟩ := h_all_const u hu; ⟨c, funext hc⟩)
     ⟨ε_reg, C_reg, hε, hC, fun u a r hr _ => h_reg u a r hr⟩)
    (sphere_energy_gap_of_all_jhol_const (M := M) I h_all_const)
    (cylinder_exponential_decay_of_all_jhol_const (M := M) I
      (fun v hv => let ⟨_, hc⟩ := h_all_const v hv; funext (fun x => (hc x).trans (hc north_pole).symm)))

/-- Existence of target thresholds on any compact tame target manifold (Contract B01). -/
theorem exists_target_thresholds :
    Nonempty (TargetThresholds I M) :=
  exists_target_thresholds_of_existentials I
    (epsilon_regularity (M := M) I)
    (sphere_energy_gap (M := M) I)
    (cylinder_exponential_decay (M := M) I)

/- =========================================================================
   SECTION 4: HOFER RESCALING & GRADIENT BOUNDEDNESS (Zero-sorry)
   ========================================================================= -/

/-- Rescaled curve v(w) := u(stereo_chart.symm (a + λ * w)) on ℂ. -/
noncomputable def rescaled_curve (u : CP1 → M) (a : ℂ) (lam_scale : ℝ) (w : ℂ) : M :=
  u (stereo_chart.symm (a + lam_scale • w))

/-- Hofer's lemma applied to gradient blow-up produces moving centers and scales
such that rescaled maps have controlled gradients on expanding disks. -/
theorem hofer_gradient_rescaling
    (a₀ : ℂ) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (ϕ : ℂ → ℝ) (hϕ_cont : Continuous ϕ) (hϕ_nonneg : ∀ z, 0 ≤ ϕ z) :
    ∃ (ε' : ℝ) (_ : 0 < ε') (a' : ℂ),
      ε' ≤ ε₀ ∧ dist a' a₀ ≤ 2 * ε₀ ∧
      ε₀ * ϕ a₀ ≤ ε' * ϕ a' ∧
      ∀ z, dist a' z ≤ ε' → ϕ z ≤ 2 * ϕ a' := by
  obtain ⟨ε', hε'_pos, x', hε'_le, hx'_dist, h_prod, h_bound⟩ :=
    _root_.hofer a₀ ε₀ hε₀ hϕ_cont hϕ_nonneg
  exact ⟨ε', hε'_pos, x', hε'_le, hx'_dist, h_prod, h_bound⟩

/-- Metric inclusion for affine scalings: If |z| ≤ R and λ * R = ε' with λ ≥ 0,
then dist (a + λ • z) a ≤ ε'. -/
lemma hofer_rescaling_ball_inclusion (a : ℂ) (lam R ε' : ℝ)
    (h_eq : lam * R = ε') (h_pos : 0 ≤ lam) (z : ℂ) (hz : dist z 0 ≤ R) :
    dist (a + lam • z) a ≤ ε' := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg h_pos]
  rw [dist_zero_right] at hz
  calc
    lam * ‖z‖ ≤ lam * R := mul_le_mul_of_nonneg_left hz h_pos
    _ = ε' := h_eq

/-- Normalization identity: (1 / M) * M = 1 for M > 0. -/
lemma hofer_rescaling_calibration (M_val : ℝ) (hM : 0 < M_val) :
    (1 / M_val) * M_val = 1 :=
  one_div_mul_cancel hM.ne'

/-- Pointwise gradient bound on expanding balls under Hofer rescaling. -/
lemma hofer_rescaling_gradient_bound (a : ℂ) (M_val : ℝ) (hM : 0 < M_val) (ε' R : ℝ)
    (h_eq : (1 / M_val) * R = ε') (ϕ : ℂ → ℝ)
    (h_bound : ∀ y : ℂ, dist a y ≤ ε' → ϕ y ≤ 2 * M_val)
    (z : ℂ) (hz : dist z 0 ≤ R) :
    (1 / M_val) * ϕ (a + (1 / M_val : ℝ) • z) ≤ 2 := by
  have h_pos : 0 ≤ (1 / M_val : ℝ) := (one_div_pos.mpr hM).le
  have h_in : dist a (a + (1 / M_val : ℝ) • z) ≤ ε' := by
    rw [dist_comm]
    exact hofer_rescaling_ball_inclusion a (1 / M_val) R ε' h_eq h_pos z hz
  have h_le := h_bound (a + (1 / M_val : ℝ) • z) h_in
  calc
    (1 / M_val) * ϕ (a + (1 / M_val : ℝ) • z) ≤ (1 / M_val) * (2 * M_val) := mul_le_mul_of_nonneg_left h_le h_pos
    _ = ((1 / M_val) * M_val) * 2 := by ring
    _ = 1 * 2 := by rw [hofer_rescaling_calibration M_val hM]
    _ = 2 := by ring

/-- Single-step calibrated Hofer rescaling from Patrick Massot's `hofer` lemma. -/
lemma hofer_single_step (ϕ : ℂ → ℝ) (h_cont : Continuous ϕ) (h_nonneg : ∀ y, 0 ≤ ϕ y)
    (x : ℂ) (ε : ℝ) (hε : 0 < ε) (hx_pos : 0 < ϕ x) :
    ∃ (a : ℂ) (lam R : ℝ),
      dist a x ≤ 2 * ε ∧
      0 < lam ∧ 0 < R ∧
      ε * ϕ x ≤ R ∧
      lam * ϕ a = 1 ∧
      (∀ z : ℂ, dist z 0 ≤ R → lam * ϕ (a + lam • z) ≤ 2) := by
  obtain ⟨ε', hε'_pos, x', _, hx'_dist, h_prod, h_bound⟩ :=
    _root_.hofer x ε hε h_cont h_nonneg
  have h_phi_x'_pos : 0 < ϕ x' := by
    have h_pos_prod : 0 < ε * ϕ x := mul_pos hε hx_pos
    have h_le : ε * ϕ x ≤ ε' * ϕ x' := h_prod
    have h_pos2 : 0 < ε' * ϕ x' := lt_of_lt_of_le h_pos_prod h_le
    by_contra h_neg
    push_neg at h_neg
    have h_mul_nonpos : ε' * ϕ x' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hε'_pos.le h_neg
    linarith
  let M_val := ϕ x'
  let lam := 1 / M_val
  let R := ε' * M_val
  have hlam_pos : 0 < lam := one_div_pos.mpr h_phi_x'_pos
  have hR_pos : 0 < R := mul_pos hε'_pos h_phi_x'_pos
  have h_prod_eq : lam * R = ε' := by
    dsimp [lam, R, M_val]
    calc
      1 / ϕ x' * (ε' * ϕ x') = (1 / ϕ x' * ϕ x') * ε' := by ring
      _ = 1 * ε' := by rw [one_div_mul_cancel h_phi_x'_pos.ne']
      _ = ε' := by ring
  refine ⟨x', lam, R, hx'_dist, hlam_pos, hR_pos, ?_, ?_, ?_⟩
  · dsimp [R]
    exact h_prod
  · dsimp [lam, M_val]
    exact one_div_mul_cancel h_phi_x'_pos.ne'
  · intro z hz
    have h_pos : 0 ≤ lam := hlam_pos.le
    have h_in : dist x' (x' + lam • z) ≤ ε' := by
      rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg h_pos]
      rw [dist_zero_right] at hz
      calc
        lam * ‖z‖ ≤ lam * R := mul_le_mul_of_nonneg_left hz h_pos
        _ = ε' := h_prod_eq
    have h_le := h_bound (x' + lam • z) h_in
    calc
      lam * ϕ (x' + lam • z) ≤ lam * (2 * M_val) := mul_le_mul_of_nonneg_left h_le h_pos
      _ = (lam * M_val) * 2 := by ring
      _ = 1 * 2 := by
        dsimp [lam, M_val]
        rw [one_div_mul_cancel h_phi_x'_pos.ne']
      _ = 2 := by ring

/- =========================================================================
   SECTION 5: CALIBRATED RESCALING & RADIAL ENERGY IVT (Contract B02)
   ========================================================================= -/

/-- Calibrated Rescaling Data (Contract B02).
At an isolated concentration point `p ∈ CP1`, moving centers `a_n → 0` and scaling radii `λ_n → 0`
satisfy the calibrated energy identity `E(u_n; D_{λ_n}(a_n)) = m_defect - h / 2`. -/
structure CalibratedRescaling
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ) where
  a : ℕ → ℂ
  a_tendsto : Filter.Tendsto a Filter.atTop (nhds 0)
  «λ» : ℕ → ℝ
  scale_pos : ∀ n, 0 < «λ» n
  scale_tendsto : Filter.Tendsto «λ» Filter.atTop (nhds 0)
  calibrated_energy : ∀ n,
    energyMeasure I (u_seq n) (disk_at (a n) («λ» n)) = m_defect - thresh.h / 2

/-- A continuous radial function on [0, R] vanishing at 0 attains any intermediate value c ∈ (0, f R]. -/
lemma ivt_radial_energy_of_continuous (f : ℝ → ℝ) (R c : ℝ)
    (h_cont : ContinuousOn f (Icc 0 R))
    (h_zero : f 0 = 0) (hR : 0 < R) (hc_pos : 0 < c) (hc_le : c ≤ f R) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ f r = c := by
  have h_mem : c ∈ Icc (f 0) (f R) := by
    rw [h_zero]
    exact ⟨hc_pos.le, hc_le⟩
  have h_ivt := intermediate_value_Icc hR.le h_cont
  have h_in_image := h_ivt h_mem
  obtain ⟨r, ⟨hr0, hrR⟩, hfr⟩ := h_in_image
  refine ⟨r, ?_, hrR, hfr⟩
  by_contra hr_not_pos
  push_neg at hr_not_pos
  have hr_eq_zero : r = 0 := le_antisymm hr_not_pos hr0
  subst hr_eq_zero
  rw [h_zero] at hfr
  linarith

lemma monotone_ball_sub_inv_succ (a : ℂ) (r₀ : ℝ) :
    Monotone (fun n : ℕ => Metric.ball a (r₀ - 1 / ((n : ℝ) + 1))) := by
  intro m n hmn
  apply Metric.ball_subset_ball
  have h1 : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by simp [hmn]
  have hpos : 0 < (m : ℝ) + 1 := by positivity
  have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := one_div_le_one_div_of_le hpos h1
  linarith

lemma iUnion_ball_sub_inv_succ (a : ℂ) (r₀ : ℝ) :
    (⋃ n : ℕ, Metric.ball a (r₀ - 1 / ((n : ℝ) + 1))) = Metric.ball a r₀ := by
  ext w
  simp only [mem_iUnion, mem_ball]
  constructor
  · rintro ⟨n, hn⟩
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro hw
    have hdiff : 0 < r₀ - dist w a := by linarith
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdiff
    exact ⟨n, by linarith⟩

lemma antitone_ball_add_inv_succ (a : ℂ) (r₀ : ℝ) :
    Antitone (fun n : ℕ => Metric.ball a (r₀ + 1 / ((n : ℝ) + 1))) := by
  intro m n hmn
  apply Metric.ball_subset_ball
  have h1 : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by simp [hmn]
  have hpos : 0 < (m : ℝ) + 1 := by positivity
  have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := one_div_le_one_div_of_le hpos h1
  linarith

lemma iInter_ball_add_inv_succ (a : ℂ) (r₀ : ℝ) :
    (⋂ n : ℕ, Metric.ball a (r₀ + 1 / ((n : ℝ) + 1))) = Metric.closedBall a r₀ := by
  ext w
  simp only [mem_iInter, mem_ball, mem_closedBall]
  constructor
  · intro h
    have h_le : ∀ n : ℕ, dist w a - r₀ ≤ 1 / ((n : ℝ) + 1) := fun n => by linarith [h n]
    have h_lim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h_nonpos : dist w a - r₀ ≤ 0 := ge_of_tendsto h_lim (Filter.Eventually.of_forall h_le)
    linarith
  · intro hw n
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

lemma continuousAt_of_monotone_and_inv_succ_limits (F : ℝ → ℝ) (h_mono : Monotone F) (r₀ : ℝ)
    (h_left : Tendsto (fun n : ℕ => F (r₀ - 1 / ((n : ℝ) + 1))) atTop (𝓝 (F r₀)))
    (h_right : Tendsto (fun n : ℕ => F (r₀ + 1 / ((n : ℝ) + 1))) atTop (𝓝 (F r₀))) :
    ContinuousAt F r₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  rw [Metric.tendsto_atTop] at h_left h_right
  obtain ⟨N₁, hN₁⟩ := h_left ε hε
  obtain ⟨N₂, hN₂⟩ := h_right ε hε
  have h1 := hN₁ N₁ le_rfl
  have h2 := hN₂ N₂ le_rfl
  rw [Real.dist_eq, abs_lt] at h1 h2
  let δ := min (1 / ((N₁ : ℝ) + 1)) (1 / ((N₂ : ℝ) + 1))
  have hδ_pos : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ_pos, fun r hr => ?_⟩
  rw [Real.dist_eq, abs_lt] at hr ⊢
  have hδ1 : δ ≤ 1 / ((N₁ : ℝ) + 1) := min_le_left _ _
  have hδ2 : δ ≤ 1 / ((N₂ : ℝ) + 1) := min_le_right _ _
  have hr_ge : r₀ - 1 / ((N₁ : ℝ) + 1) ≤ r := by linarith
  have hr_le : r ≤ r₀ + 1 / ((N₂ : ℝ) + 1) := by linarith
  have hF_ge : F (r₀ - 1 / ((N₁ : ℝ) + 1)) ≤ F r := h_mono hr_ge
  have hF_le : F r ≤ F (r₀ + 1 / ((N₂ : ℝ) + 1)) := h_mono hr_le
  constructor <;> linarith

lemma continuous_measure_ball_toReal (ν : Measure ℂ) [IsFiniteMeasure ν] (a : ℂ)
    (h_sphere : ∀ r : ℝ, ν (Metric.sphere a r) = 0) :
    Continuous (fun r : ℝ => (ν (Metric.ball a r)).toReal) := by
  rw [continuous_iff_continuousAt]
  intro r₀
  have h_mono : Monotone (fun r : ℝ => (ν (Metric.ball a r)).toReal) := by
    intro r₁ r₂ hr
    exact ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (Metric.ball_subset_ball hr))
  apply continuousAt_of_monotone_and_inv_succ_limits _ h_mono r₀
  · have h_meas_lim := MeasureTheory.tendsto_measure_iUnion_atTop (μ := ν)
      (monotone_ball_sub_inv_succ a r₀)
    rw [iUnion_ball_sub_inv_succ a r₀] at h_meas_lim
    exact (ENNReal.continuousAt_toReal (measure_ne_top ν _)).tendsto.comp h_meas_lim
  · have h_meas : ∀ n : ℕ, NullMeasurableSet (Metric.ball a (r₀ + 1 / ((n : ℝ) + 1))) ν :=
      fun _ => measurableSet_ball.nullMeasurableSet
    have h_fin : ∃ i : ℕ, ν (Metric.ball a (r₀ + 1 / ((i : ℝ) + 1))) ≠ ⊤ :=
      ⟨0, measure_ne_top ν _⟩
    have h_meas_lim := MeasureTheory.tendsto_measure_iInter_atTop h_meas
      (antitone_ball_add_inv_succ a r₀) h_fin
    rw [iInter_ball_add_inv_succ a r₀] at h_meas_lim
    have h_cb_eq : ν (Metric.closedBall a r₀) = ν (Metric.ball a r₀) := by
      apply le_antisymm
      · rw [← Metric.ball_union_sphere]
        calc ν (Metric.ball a r₀ ∪ Metric.sphere a r₀)
          _ ≤ ν (Metric.ball a r₀) + ν (Metric.sphere a r₀) := measure_union_le _ _
          _ = ν (Metric.ball a r₀) := by rw [h_sphere r₀, add_zero]
      · exact measure_mono Metric.ball_subset_closedBall
    rw [h_cb_eq] at h_meas_lim
    exact (ENNReal.continuousAt_toReal (measure_ne_top ν _)).tendsto.comp h_meas_lim

/-- For any map `u : CP1 → M` with finite extended energy on `CP1`, the radial energy function
`r ↦ energyMeasure I u (disk_at a r)` is continuous on all of `ℝ` (Zero-sorry). -/
theorem continuous_energyMeasure_disk_at_of_finite (u : CP1 → M) (a : ℂ)
    (h_fin : energyMeasureExtended I u Set.univ ≠ ⊤) :
    Continuous (fun r : ℝ => energyMeasure I u (disk_at a r)) := by
  let ν : Measure ℂ := volume.withDensity (fun w =>
    ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w))
  have h_univ : energyMeasureExtended I u Set.univ = ν Set.univ := by
    dsimp [energyMeasureExtended, chartPush, ν]
    rw [Measure.map_apply stereo_chart_symm_measurable MeasurableSet.univ, Set.preimage_univ]
  haveI : IsFiniteMeasure ν := by
    refine ⟨lt_top_iff_ne_top.mpr ?_⟩
    rw [← h_univ]
    exact h_fin
  have h_sphere : ∀ r : ℝ, ν (Metric.sphere a r) = 0 := by
    intro r
    apply withDensity_absolutelyContinuous
    exact Measure.addHaar_sphere volume a r
  have h_eq : (fun r : ℝ => energyMeasure I u (disk_at a r)) =
      (fun r : ℝ => (ν (Metric.ball a r)).toReal) := by
    ext r
    dsimp [energyMeasure, energyMeasureExtended, chartPush, ν]
    rw [Measure.map_apply stereo_chart_symm_measurable (measurableSet_disk_at a r),
        stereo_chart_symm_preimage_disk_at]
  rw [h_eq]
  exact continuous_measure_ball_toReal ν a h_sphere

/-- Radial Intermediate Value Theorem for any finite-energy curve on `CP1` (Zero-sorry). -/
theorem radial_ivt_of_finite_energy (u : CP1 → M) (a : ℂ) (R c : ℝ)
    (h_fin : energyMeasureExtended I u Set.univ ≠ ⊤)
    (hR : 0 < R) (hc : 0 < c) (hle : c ≤ energyMeasure I u (disk_at a R)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ energyMeasure I u (disk_at a r) = c :=
  ivt_radial_energy_of_continuous (fun r => energyMeasure I u (disk_at a r)) R c
    (continuous_energyMeasure_disk_at_of_finite I u a h_fin).continuousOn
    (energyMeasure_disk_at_zero I u a) hR hc hle

/-- Radial Intermediate Value Theorem under continuity of disk energy measure. -/
lemma test_radial_ivt (u : CP1 → M) (a : ℂ) (R c : ℝ)
    (_h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (hR : 0 < R) (hc : 0 < c) (hle : c ≤ energyMeasure I u (disk_at a R))
    (h_cont : ContinuousOn (fun r => energyMeasure I u (disk_at a r)) (Icc 0 R)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ energyMeasure I u (disk_at a r) = c := by
  apply ivt_radial_energy_of_continuous (fun r => energyMeasure I u (disk_at a r)) R c h_cont
    (energyMeasure_disk_at_zero I u a) hR hc hle

/-- Intermediate value property for radial energy of smooth curves. -/
def RadialEnergyIVT : Prop :=
  ∀ (u : CP1 → M) (a : ℂ) (R c : ℝ),
    JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
    0 < R →
    0 < c →
    c ≤ energyMeasure I u (disk_at a R) →
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ energyMeasure I u (disk_at a r) = c

/-- If `0 < energyMeasure I u s`, then `energyMeasureExtended I u s ≠ ⊤` (`0 sorryAx`). -/
lemma energyMeasureExtended_ne_top_of_pos_energyMeasure
    (u : CP1 → M) (s : Set CP1) (h_pos : 0 < energyMeasure I u s) :
    energyMeasureExtended I u s ≠ ⊤ := by
  intro h_top
  dsimp [energyMeasure] at h_pos
  rw [h_top, ENNReal.toReal_top] at h_pos
  exact lt_irrefl 0 h_pos

/-- Whenever `energyMeasureExtended I u (disk_at a R) ≠ ⊤`, the radial energy function
`r ↦ energyMeasure I u (disk_at a r)` is continuous on `Icc 0 R` (`0 sorryAx`). -/
theorem continuousOn_energyMeasure_disk_at_Icc_of_ne_top
    (u : CP1 → M) (a : ℂ) (R : ℝ)
    (h_fin : energyMeasureExtended I u (disk_at a R) ≠ ⊤) :
    ContinuousOn (fun r : ℝ => energyMeasure I u (disk_at a r)) (Icc 0 R) := by
  let ν : Measure ℂ := volume.withDensity (fun w =>
    ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w))
  let ν_R : Measure ℂ := ν.restrict (Metric.ball a R)
  have h_disk_R : energyMeasureExtended I u (disk_at a R) = ν_R Set.univ := by
    dsimp [energyMeasureExtended, chartPush, ν_R, ν]
    rw [Measure.map_apply stereo_chart_symm_measurable (measurableSet_disk_at a R),
        stereo_chart_symm_preimage_disk_at, Measure.restrict_apply_univ]
  haveI : IsFiniteMeasure ν_R := by
    refine ⟨lt_top_iff_ne_top.mpr ?_⟩
    rw [← h_disk_R]
    exact h_fin
  have h_sphere : ∀ r : ℝ, ν_R (Metric.sphere a r) = 0 := by
    intro r
    have h_zero : ν (Metric.sphere a r) = 0 := by
      apply withDensity_absolutelyContinuous
      exact Measure.addHaar_sphere volume a r
    exact le_antisymm (le_trans (Measure.restrict_apply_le _ _) (le_of_eq h_zero)) zero_le'
  have h_cont_F : Continuous (fun r : ℝ => (ν_R (Metric.ball a r)).toReal) :=
    continuous_measure_ball_toReal ν_R a h_sphere
  refine h_cont_F.continuousOn.congr (fun r hr => ?_)
  dsimp [energyMeasure, energyMeasureExtended, chartPush, ν_R, ν]
  rw [Measure.map_apply stereo_chart_symm_measurable (measurableSet_disk_at a r),
      stereo_chart_symm_preimage_disk_at,
      Measure.restrict_apply measurableSet_ball,
      Set.inter_eq_left.mpr (Metric.ball_subset_ball hr.2)]

/-- Smooth `J`-holomorphic curves on `CP1` unconditionally satisfy `RadialEnergyIVT` (`0 sorryAx`). -/
theorem radialEnergyIVT_of_jhol : RadialEnergyIVT I (M := M) := by
  intro u a R c _hu hR hc hle
  have h_pos : 0 < energyMeasure I u (disk_at a R) := lt_of_lt_of_le hc hle
  have h_fin : energyMeasureExtended I u (disk_at a R) ≠ ⊤ :=
    energyMeasureExtended_ne_top_of_pos_energyMeasure I u (disk_at a R) h_pos
  exact ivt_radial_energy_of_continuous (fun r => energyMeasure I u (disk_at a r)) R c
    (continuousOn_energyMeasure_disk_at_Icc_of_ne_top I u a R h_fin)
    (energyMeasure_disk_at_zero I u a) hR hc hle

/-- Conditional Reduction of Contract B02 to Radial Energy IVT:
Under RadialEnergyIVT, exists_calibrated_rescaling holds constructively.
Note (Conditional Reduction per COMPLETION_PLAN.md §0 & §2 P0-9):
Requires the unproved `RadialEnergyIVT` hypothesis. -/
theorem exists_calibrated_rescaling_of_ivt
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (_hm : thresh.h ≤ m_defect)
    (h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n))
    (h_ivt : RadialEnergyIVT I (M := M)) :
    Nonempty (CalibratedRescaling I u_seq thresh m_defect) := by
  have hc_pos : 0 < m_defect - thresh.h / 2 := by
    have hh_pos := thresh.h_pos
    linarith
  have h_step : ∀ n : ℕ, ∃ (a_n : ℂ) (lam_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < lam_n ∧ lam_n ≤ 1 / ((n : ℝ) + 1) ∧
      energyMeasure I (u_seq n) (disk_at a_n lam_n) = m_defect - thresh.h / 2 := by
    intro n
    obtain ⟨a_n, R_n, ha_dist, hR_pos, hR_le, h_en⟩ := h_defect n
    obtain ⟨r, hr_pos, hr_le, hr_eq⟩ := h_ivt (u_seq n) a_n R_n (m_defect - thresh.h / 2)
      (h_jhol n) hR_pos hc_pos h_en
    exact ⟨a_n, r, ha_dist, hr_pos, hr_le.trans hR_le, hr_eq⟩
  choose a lam h_prop using h_step
  refine ⟨⟨a, ?_, lam, fun n => (h_prop n).2.1, ?_, fun n => (h_prop n).2.2.2⟩⟩
  · exact tendsto_dist_zero_of_le_inv_succ a 0 (fun n => (h_prop n).1)
  · exact tendsto_scale_zero_of_le_inv_succ lam (fun n => (h_prop n).2.1) (fun n => (h_prop n).2.2.1)

/-- Existence of calibrated moving centers and radii (Contract B02).
Under energy concentration at `0` with defect mass `m_defect`, the Intermediate Value
Theorem (`RadialEnergyIVT`) yields calibrated moving centers and scaling radii.
Note (Conditional Reduction per COMPLETION_PLAN.md §0 & §2 P0-9):
Formulated as a conditional reduction theorem requiring the radial IVT hypothesis; does not count
as closing Contract B02 unconditionally until the radial IVT is proved. -/
theorem exists_calibrated_rescaling
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n))
    (h_ivt : RadialEnergyIVT I (M := M)) :
    Nonempty (CalibratedRescaling I u_seq thresh m_defect) :=
  exists_calibrated_rescaling_of_ivt I u_seq thresh m_defect hm h_jhol h_defect h_ivt

/-- Existence of calibrated moving centers and radii for smooth `J`-holomorphic spheres
without requiring an external `RadialEnergyIVT` hypothesis (`0 sorryAx`). -/
theorem exists_calibrated_rescaling_of_jhol
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (h_jhol : ∀ (n : ℕ), JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n)) :
    Nonempty (CalibratedRescaling I u_seq thresh m_defect) :=
  exists_calibrated_rescaling_of_ivt I u_seq thresh m_defect hm h_jhol h_defect
    (radialEnergyIVT_of_jhol I)

/-- Existence of calibrated moving centers and radii for any sequence of maps `u_seq : ℕ → (CP1 → M)`
concentrating energy at `0`, without requiring `JHolomorphicOn` or `RadialEnergyIVT` (`0 sorryAx`). -/
theorem exists_calibrated_rescaling_of_defect
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (h_defect : ∀ (n : ℕ), ∃ (a_n : ℂ) (R_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < R_n ∧ R_n ≤ 1 / ((n : ℝ) + 1) ∧
      m_defect - thresh.h / 2 ≤ energyMeasure I (u_seq n) (disk_at a_n R_n)) :
    Nonempty (CalibratedRescaling I u_seq thresh m_defect) := by
  have hc_pos : 0 < m_defect - thresh.h / 2 := by
    have hh_pos := thresh.h_pos
    linarith
  have h_step : ∀ n : ℕ, ∃ (a_n : ℂ) (lam_n : ℝ),
      dist a_n 0 ≤ 1 / ((n : ℝ) + 1) ∧
      0 < lam_n ∧ lam_n ≤ 1 / ((n : ℝ) + 1) ∧
      energyMeasure I (u_seq n) (disk_at a_n lam_n) = m_defect - thresh.h / 2 := by
    intro n
    obtain ⟨a_n, R_n, ha_dist, hR_pos, hR_le, h_en⟩ := h_defect n
    have h_pos : 0 < energyMeasure I (u_seq n) (disk_at a_n R_n) := lt_of_lt_of_le hc_pos h_en
    have h_fin : energyMeasureExtended I (u_seq n) (disk_at a_n R_n) ≠ ⊤ :=
      energyMeasureExtended_ne_top_of_pos_energyMeasure I (u_seq n) (disk_at a_n R_n) h_pos
    obtain ⟨r, hr_pos, hr_le, hr_eq⟩ :=
      ivt_radial_energy_of_continuous (fun r => energyMeasure I (u_seq n) (disk_at a_n r)) R_n
        (m_defect - thresh.h / 2)
        (continuousOn_energyMeasure_disk_at_Icc_of_ne_top I (u_seq n) a_n R_n h_fin)
        (energyMeasure_disk_at_zero I (u_seq n) a_n) hR_pos hc_pos h_en
    exact ⟨a_n, r, ha_dist, hr_pos, hr_le.trans hR_le, hr_eq⟩
  choose a lam h_prop using h_step
  refine ⟨⟨a, ?_, lam, fun n => (h_prop n).2.1, ?_, fun n => (h_prop n).2.2.2⟩⟩
  · exact tendsto_dist_zero_of_le_inv_succ a 0 (fun n => (h_prop n).1)
  · exact tendsto_scale_zero_of_le_inv_succ lam (fun n => (h_prop n).2.1) (fun n => (h_prop n).2.2.1)

/-- Bubble limit curve energy lower bound: Every non-trivial bubble satisfies E(v_∞) ≥ ε_sph. -/
theorem bubble_energy_ge_sphere_gap
    (thresh : TargetThresholds I M) (v_lim : CP1 → M)
    (h_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v_lim Set.univ)
    (h_nonconst : ¬ ∃ c : M, ∀ z, v_lim z = c) :
    thresh.ε_sph ≤ totalEnergy I v_lim :=
  thresh.h_sph v_lim h_jhol h_nonconst

/-- If `u_seq` has a constant term `u_seq n₀ = fun _ => c` and `thresh.h / 2 < m_defect`, then
`CalibratedRescaling I u_seq thresh m_defect` is empty (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_exists_const_term_of_gt_half_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (h_gt : thresh.h / 2 < m_defect)
    (n₀ : ℕ) (c : M) (hc : u_seq n₀ = fun _ => c) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) := by
  refine ⟨fun res => ?_⟩
  have h_cal := res.calibrated_energy n₀
  have h_zero : energyMeasure I (u_seq n₀) (disk_at (res.a n₀) (res.«λ» n₀)) = 0 := by
    rw [hc]
    exact energyMeasure_const I c _
  linarith

/-- If `u_seq` has a constant term `u_seq n₀ = fun _ => c` and `thresh.h ≤ m_defect`, then
`CalibratedRescaling I u_seq thresh m_defect` is empty (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_exists_const_term
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (c : M) (hc : u_seq n₀ = fun _ => c) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) :=
  CalibratedRescaling.isEmpty_of_exists_const_term_of_gt_half_h I u_seq thresh m_defect
    (by linarith [thresh.h_pos]) n₀ c hc

/-- On a `[Subsingleton M]` target, `CalibratedRescaling I u_seq thresh m_defect` is empty whenever
`thresh.h ≤ m_defect` (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) :=
  CalibratedRescaling.isEmpty_of_exists_const_term I u_seq thresh m_defect hm
    0 (u_seq 0 north_pole) (funext (fun z => Subsingleton.elim (u_seq 0 z) (u_seq 0 north_pole)))

/-- On a `[DiscreteTopology M]` target, `CalibratedRescaling I u_seq thresh m_defect` is empty whenever
`thresh.h ≤ m_defect` and some term `u_seq n₀` is continuous (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_exists_continuous_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (h_cont : Continuous (u_seq n₀)) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) :=
  CalibratedRescaling.isEmpty_of_exists_const_term I u_seq thresh m_defect hm
    n₀ (u_seq n₀ north_pole) (funext (eq_const_north_pole_of_continuous_of_discrete (u_seq n₀) h_cont))

/-- Whenever every globally `J`-holomorphic sphere is constant and some term `u_seq n₀` is `J`-holomorphic,
`CalibratedRescaling I u_seq thresh m_defect` is empty for `thresh.h ≤ m_defect` (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n₀) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) := by
  obtain ⟨c, hc⟩ := h_all_const (u_seq n₀) hu₀
  exact CalibratedRescaling.isEmpty_of_exists_const_term I u_seq thresh m_defect hm n₀ c (funext hc)

/-- If `u_seq` is eventually constant and `thresh.h ≤ m_defect`, then
`CalibratedRescaling I u_seq thresh m_defect` is empty (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_eventually_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (h_ev : ∀ᶠ n in atTop, ∃ c : M, u_seq n = fun _ => c) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_ev
  obtain ⟨c, hc⟩ := hN N le_rfl
  exact CalibratedRescaling.isEmpty_of_exists_const_term I u_seq thresh m_defect hm N c hc

/-- Whenever `u_seq` is eventually `J`-holomorphic and every globally `J`-holomorphic sphere is constant,
`CalibratedRescaling I u_seq thresh m_defect` is empty for `thresh.h ≤ m_defect` (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (N₀ : ℕ) (h_jhol : ∀ n ≥ N₀, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) :=
  CalibratedRescaling.isEmpty_of_all_jhol_const I u_seq thresh m_defect hm N₀ (h_jhol N₀ le_rfl) h_all_const

/-- On a `[DiscreteTopology M]` target, `CalibratedRescaling I u_seq thresh m_defect` is empty whenever
`thresh.h ≤ m_defect` and `u_seq n` is eventually continuous (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_eventually_continuous_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (N₀ : ℕ) (h_cont : ∀ n ≥ N₀, Continuous (u_seq n)) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) :=
  CalibratedRescaling.isEmpty_of_exists_continuous_of_discrete I u_seq thresh m_defect hm N₀ (h_cont N₀ le_rfl)

/-- On a `[DiscreteTopology M]` target, `CalibratedRescaling I u_seq thresh m_defect` is empty whenever
`thresh.h ≤ m_defect` and some term `u_seq n₀` is `J`-holomorphic (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_jhol_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (n₀ : ℕ) (hu₀ : JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n₀) Set.univ) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) :=
  CalibratedRescaling.isEmpty_of_all_jhol_const I u_seq thresh m_defect hm n₀ hu₀
    (fun u hu => ⟨u north_pole, eq_const_north_pole_of_jhol_univ_of_discrete I u hu⟩)

/-- On a `[DiscreteTopology M]` target, `CalibratedRescaling I u_seq thresh m_defect` is empty whenever
`thresh.h ≤ m_defect` and `u_seq n` is eventually `J`-holomorphic (`0 sorryAx`). -/
theorem CalibratedRescaling.isEmpty_of_eventually_jhol_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect)
    (N₀ : ℕ) (h_jhol : ∀ n ≥ N₀, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ) :
    IsEmpty (CalibratedRescaling I u_seq thresh m_defect) :=
  CalibratedRescaling.isEmpty_of_jhol_of_discrete I u_seq thresh m_defect hm N₀ (h_jhol N₀ le_rfl)

end GromovCompactness.Analysis

/- =========================================================================
   SECTION 6: NAMESPACE GromovCompactness.Bubbling ALIASES
   ========================================================================= -/

namespace GromovCompactness.Bubbling

/-- Re-export of `TargetThresholds` in namespace `GromovCompactness.Bubbling` to match blueprint `b01:threshold_h`. -/
abbrev TargetThresholds := @GromovCompactness.Analysis.TargetThresholds

/-- Re-export of `CalibratedRescaling` in namespace `GromovCompactness.Bubbling` to match blueprint `b02:calibration`. -/
abbrev CalibratedRescaling := @GromovCompactness.Analysis.CalibratedRescaling

/-- Re-export of `RadialEnergyIVT` in namespace `GromovCompactness.Bubbling`. -/
abbrev RadialEnergyIVT := @GromovCompactness.Analysis.RadialEnergyIVT

/-- Re-export of `exists_target_thresholds_of_modules` in namespace `GromovCompactness.Bubbling`. -/
abbrev exists_target_thresholds_of_modules := @GromovCompactness.Analysis.exists_target_thresholds_of_modules

/-- Re-export of `exists_target_thresholds_of_subsingleton` in namespace `GromovCompactness.Bubbling`. -/
abbrev exists_target_thresholds_of_subsingleton := @GromovCompactness.Analysis.exists_target_thresholds_of_subsingleton

/-- Re-export of `exists_target_thresholds_of_discrete` in namespace `GromovCompactness.Bubbling`. -/
abbrev exists_target_thresholds_of_discrete := @GromovCompactness.Analysis.exists_target_thresholds_of_discrete

/-- Re-export of `exists_target_thresholds_of_all_jhol_const` in namespace `GromovCompactness.Bubbling`. -/
abbrev exists_target_thresholds_of_all_jhol_const := @GromovCompactness.Analysis.exists_target_thresholds_of_all_jhol_const

/-- Re-export of `exists_target_thresholds` in namespace `GromovCompactness.Bubbling`. -/
abbrev exists_target_thresholds := @GromovCompactness.Analysis.exists_target_thresholds

/-- Re-export of `radialEnergyIVT_of_jhol` in namespace `GromovCompactness.Bubbling`. -/
abbrev radialEnergyIVT_of_jhol := @GromovCompactness.Analysis.radialEnergyIVT_of_jhol

/-- Re-export of `exists_calibrated_rescaling_of_ivt` in namespace `GromovCompactness.Bubbling`. -/
abbrev exists_calibrated_rescaling_of_ivt := @GromovCompactness.Analysis.exists_calibrated_rescaling_of_ivt

/-- Re-export of `exists_calibrated_rescaling` in namespace `GromovCompactness.Bubbling`. -/
abbrev exists_calibrated_rescaling := @GromovCompactness.Analysis.exists_calibrated_rescaling

/-- Re-export of `exists_calibrated_rescaling_of_jhol` in namespace `GromovCompactness.Bubbling`. -/
abbrev exists_calibrated_rescaling_of_jhol := @GromovCompactness.Analysis.exists_calibrated_rescaling_of_jhol

/-- Re-export of `bubble_energy_ge_sphere_gap` in namespace `GromovCompactness.Bubbling`. -/
abbrev bubble_energy_ge_sphere_gap := @GromovCompactness.Analysis.bubble_energy_ge_sphere_gap

end GromovCompactness.Bubbling
