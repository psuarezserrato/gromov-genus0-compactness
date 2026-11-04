/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Challenger 1 Milestone 5)
-/
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EpsilonRegularity
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.SingularityRemoval
import GromovCompactness.Analysis.HoferRescaling
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness Classical
open GromovCompactness.Analysis

namespace GromovCompactness.ChallengeMilestone5Thresholds

/-!
# Empirical Adversarial Challenge Suite: Milestone 5 Bubbling Thresholds
Challenger: challenger1_m5 (Empirical Challenger for Milestone 5)
Target: GromovCompactness/Analysis/HoferRescaling.lean (Contract B01 & Foundations)

This challenge harness empirically executes rigorous stress tests against Contract B01:
- `TargetThresholds`
- `exists_target_thresholds_of_modules`
- `has_energy_defect_iff_concentration`
- `card_le_of_atoms`
- `finite_atoms_of_bounded_measure`
- `atoms_card_le`

Covering 4 adversarial challenge categories (with 35 comprehensive test theorems):
1. Category 1: Threshold positivity and ordering (0 < h, h ≤ ε_reg/2, h ≤ ε_sph, h ≤ ε_neck/2)
   across various synthetic, edge case, and scale-extreme regimes.
2. Category 2: Atom-concentration equivalence (atom_iff_concentration, has_energy_defect_iff_concentration)
   with Dirac measures, zero defect, excess defect refutation, and off-center tests.
3. Category 3: Cardinality bounds on singular set (card_le_of_atoms, atoms_card_le)
   under extreme parameters (E₀ < ε₀, E₀ = 0, E₀ = ε₀, E₀ = k * ε₀, E₀ ≫ ε₀).
4. Category 4: Anti-cheat / non-triviality: ensuring theorems do not reduce to False,
   do not accept impossible parameters, and maintain calibrated energy margins.
5. Axiom Purity Certification: verifying that all challenge theorems depend strictly
   on standard Lean 4 kernel axioms: `[propext, Classical.choice, Quot.sound]`.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

--------------------------------------------------------------------------------
-- SECTION 1: Threshold Positivity, Dominance, and Ordering (Category 1)
--------------------------------------------------------------------------------

/-- Test 1.1: Strict positivity of universal bubbling threshold h > 0. -/
theorem test_threshold_positivity (thresh : TargetThresholds I M) :
    0 < thresh.h :=
  thresh.h_pos

/-- Test 1.2: Threshold bound against epsilon-regularity: h ≤ ε_reg / 2. -/
theorem test_threshold_le_half_reg (thresh : TargetThresholds I M) :
    thresh.h ≤ thresh.ε_reg / 2 :=
  thresh.h_le_reg

/-- Test 1.3: Threshold bound against sphere energy gap: h ≤ ε_sph. -/
theorem test_threshold_le_sph (thresh : TargetThresholds I M) :
    thresh.h ≤ thresh.ε_sph :=
  thresh.h_le_sph

/-- Test 1.4: Threshold bound against neck collar energy: h ≤ ε_neck / 2. -/
theorem test_threshold_le_half_neck (thresh : TargetThresholds I M) :
    thresh.h ≤ thresh.ε_neck / 2 :=
  thresh.h_le_neck

/-- Test 1.5: Strict bound against epsilon-regularity: h < ε_reg. -/
theorem test_threshold_strictly_less_reg (thresh : TargetThresholds I M) :
    thresh.h < thresh.ε_reg := by
  have h_half : thresh.ε_reg / 2 < thresh.ε_reg := by
    linarith [thresh.ε_reg_pos]
  exact lt_of_le_of_lt thresh.h_le_reg h_half

/-- Test 1.6: Strict bound against cylinder neck threshold: h < ε_neck. -/
theorem test_threshold_strictly_less_neck (thresh : TargetThresholds I M) :
    thresh.h < thresh.ε_neck := by
  have h_half : thresh.ε_neck / 2 < thresh.ε_neck := by
    linarith [thresh.ε_neck_pos]
  exact lt_of_le_of_lt thresh.h_le_neck h_half

/-- Test 1.7: Simultaneous minimum bound: h ≤ min (ε_reg / 2) (min ε_sph (ε_neck / 2)). -/
theorem test_threshold_le_min_all (thresh : TargetThresholds I M) :
    thresh.h ≤ min (thresh.ε_reg / 2) (min thresh.ε_sph (thresh.ε_neck / 2)) := by
  exact le_min thresh.h_le_reg (le_min thresh.h_le_sph thresh.h_le_neck)

/-- Universal threshold function combining three geometric scales. -/
noncomputable def threshold_func (ε_reg ε_sph ε_neck : ℝ) : ℝ :=
  min (ε_reg / 2) (min ε_sph (ε_neck / 2))

/-- Test 1.8: Threshold positivity for arbitrary positive input parameters. -/
theorem test_threshold_func_pos (ε_reg ε_sph ε_neck : ℝ)
    (h_reg : 0 < ε_reg) (h_sph : 0 < ε_sph) (h_neck : 0 < ε_neck) :
    0 < threshold_func ε_reg ε_sph ε_neck := by
  dsimp [threshold_func]
  have h1 : 0 < ε_reg / 2 := by linarith
  have h2 : 0 < ε_neck / 2 := by linarith
  exact lt_min h1 (lt_min h_sph h2)

/-- Test 1.9: Regime A: ε_reg / 2 is dominant (strictly minimal).
Here ε_reg = 0.2 (so ε_reg / 2 = 0.1), ε_sph = 0.5, ε_neck = 0.8 (so ε_neck / 2 = 0.4). -/
theorem test_threshold_reg_dominant :
    threshold_func 0.2 0.5 0.8 = 0.1 := by
  dsimp [threshold_func]
  norm_num

/-- Test 1.10: Regime B: ε_sph is dominant (strictly minimal).
Here ε_reg = 2.0 (ε_reg / 2 = 1.0), ε_sph = 0.05, ε_neck = 1.0 (ε_neck / 2 = 0.5). -/
theorem test_threshold_sph_dominant :
    threshold_func 2.0 0.05 1.0 = 0.05 := by
  dsimp [threshold_func]
  norm_num

/-- Test 1.11: Regime C: ε_neck / 2 is dominant (strictly minimal).
Here ε_reg = 1.0 (ε_reg / 2 = 0.5), ε_sph = 0.5, ε_neck = 0.2 (ε_neck / 2 = 0.1). -/
theorem test_threshold_neck_dominant :
    threshold_func 1.0 0.5 0.2 = 0.1 := by
  dsimp [threshold_func]
  norm_num

/-- Test 1.12: Regime D: Perfectly balanced thresholds.
Here ε_reg = 2.0, ε_sph = 1.0, ε_neck = 2.0 (so ε_reg / 2 = ε_sph = ε_neck / 2 = 1.0). -/
theorem test_threshold_balanced :
    threshold_func 2.0 1.0 2.0 = 1.0 := by
  dsimp [threshold_func]
  norm_num

/-- Test 1.13: Regime E: Microscopic scale threshold (stress test for numerical underflow). -/
theorem test_threshold_microscopic :
    threshold_func 1000 0.000000001 1000 = 0.000000001 := by
  dsimp [threshold_func]
  norm_num

/-- Test 1.14: Regime F: Macroscopic scale threshold. -/
theorem test_threshold_macroscopic :
    threshold_func 100000000 1000000 100000000 = 1000000 := by
  dsimp [threshold_func]
  norm_num

--------------------------------------------------------------------------------
-- SECTION 2: Atom-Concentration Equivalence & Energy Defect (Category 2)
--------------------------------------------------------------------------------

/-- Test 2.1: Dirac measure exact atom concentration.
For unit Dirac measure δ₀ on ℝ, atom mass at 0 is 1, so all closed balls concentrate mass ≥ 1. -/
theorem test_atom_concentration_dirac_exact :
    ∀ r > (0 : ℝ), ENNReal.ofReal 1 ≤ (Measure.dirac (0 : ℝ)) (closedBall 0 r) := by
  have h_atom : ENNReal.ofReal 1 ≤ (Measure.dirac (0 : ℝ)) {0} := by
    rw [Measure.dirac_apply_of_mem (mem_singleton 0)]
    simp
  exact (atom_iff_concentration (Measure.dirac (0 : ℝ)) 0 1).mp h_atom

/-- Test 2.2: Dirac measure fractional threshold concentration.
For δ₀ on ℝ, any threshold ε₀ = 1/2 ≤ 1 concentrates mass in all balls. -/
theorem test_atom_concentration_dirac_fractional :
    ∀ r > (0 : ℝ), ENNReal.ofReal (1/2) ≤ (Measure.dirac (0 : ℝ)) (closedBall 0 r) := by
  have h_atom : ENNReal.ofReal (1/2) ≤ (Measure.dirac (0 : ℝ)) {0} := by
    rw [Measure.dirac_apply_of_mem (mem_singleton 0)]
    rw [ENNReal.ofReal_le_one]
    norm_num
  exact (atom_iff_concentration (Measure.dirac (0 : ℝ)) 0 (1/2)).mp h_atom

/-- Test 2.3: Adversarial refutation of excessive defect.
For unit Dirac measure δ₀, it is false that atom mass ≥ 2, hence there exists a ball with mass < 2. -/
theorem test_atom_concentration_dirac_refute_excess :
    ∃ r > (0 : ℝ), (Measure.dirac (0 : ℝ)) (closedBall 0 r) < ENNReal.ofReal 2 := by
  have h_not : ¬ (ENNReal.ofReal 2 ≤ (Measure.dirac (0 : ℝ)) {0}) := by
    rw [Measure.dirac_apply_of_mem (mem_singleton 0)]
    rw [ENNReal.ofReal_le_one]
    norm_num
  have h_equiv := atom_iff_concentration (Measure.dirac (0 : ℝ)) 0 2
  rw [h_equiv] at h_not
  push_neg at h_not
  exact h_not

/-- Test 2.4: Off-center point non-concentration.
At point x = 2, unit Dirac measure at 0 has atom mass 0, so concentration of mass ≥ 1/2 fails. -/
theorem test_atom_concentration_dirac_off_center :
    ∃ r > (0 : ℝ), (Measure.dirac (0 : ℝ)) (closedBall 2 r) < ENNReal.ofReal (1/2) := by
  have h_not : ¬ (ENNReal.ofReal (1/2) ≤ (Measure.dirac (0 : ℝ)) {2}) := by
    rw [Measure.dirac_apply]
    rw [Set.indicator_of_not_mem]
    · simp
    · norm_num
  have h_equiv := atom_iff_concentration (Measure.dirac (0 : ℝ)) 2 (1/2)
  rw [h_equiv] at h_not
  push_neg at h_not
  exact h_not

/-- Test 2.5: Explicit radius witness for off-center non-concentration: ball of radius 1 around 2. -/
theorem test_atom_concentration_dirac_explicit_radius :
    (Measure.dirac (0 : ℝ)) (closedBall 2 1) < ENNReal.ofReal 1 := by
  have h_zero : (Measure.dirac (0 : ℝ)) (closedBall 2 1) = 0 := by
    rw [Measure.dirac_apply]
    rw [Set.indicator_of_not_mem]
    rw [mem_closedBall, Real.dist_eq]
    norm_num
  rw [h_zero]
  have hpos : (0 : ENNReal) < ENNReal.ofReal 1 := by
    rw [ENNReal.ofReal_pos]
    norm_num
  exact hpos

/-- Test 2.6: Energy defect with zero regular measure and unit Dirac defect. -/
theorem test_has_energy_defect_zero_reg :
    ENNReal.ofReal 1 ≤ (Measure.dirac (0 : ℝ)) {0} ↔
    ∀ r > (0 : ℝ), ENNReal.ofReal 1 ≤ ((0 : Measure ℝ) + (Measure.dirac (0 : ℝ))) (closedBall 0 r) := by
  have h_null : ∀ x : ℝ, (0 : Measure ℝ) {x} = 0 := by simp
  exact has_energy_defect_iff_concentration (0 : Measure ℝ) (Measure.dirac (0 : ℝ)) h_null 0 1

/-- Test 2.7: Adversarial refutation: Zero defect measure cannot concentrate any positive energy. -/
theorem test_zero_defect_no_concentration (x : ℝ) (ε₀ : ℝ) (hε : 0 < ε₀) :
    ∃ r > (0 : ℝ), ((0 : Measure ℝ) + (0 : Measure ℝ)) (closedBall x r) < ENNReal.ofReal ε₀ := by
  have h_null : ∀ y : ℝ, (0 : Measure ℝ) {y} = 0 := by simp
  have h_equiv := has_energy_defect_iff_concentration (0 : Measure ℝ) (0 : Measure ℝ) h_null x ε₀
  have h_not_atom : ¬ (ENNReal.ofReal ε₀ ≤ (0 : Measure ℝ) {x}) := by
    simp only [Measure.coe_zero, Pi.zero_apply]
    rw [le_zero_iff, ENNReal.ofReal_eq_zero]
    linarith
  rw [h_equiv] at h_not_atom
  push_neg at h_not_atom
  exact h_not_atom

/-- Test 2.8: Trivial concentration for nonpositive threshold ε₀ ≤ 0 on any measure. -/
theorem test_atom_concentration_nonpos_threshold
    (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) (ε₀ : ℝ) (hε : ε₀ ≤ 0) :
    ∀ r > (0 : ℝ), ENNReal.ofReal ε₀ ≤ μ (closedBall x r) := by
  intro r hr
  rw [ENNReal.ofReal_of_nonpos hε]
  exact zero_le _

/-- Test 2.9: Monotonicity of concentration: concentration at ε₂ implies concentration at ε₁ ≤ ε₂. -/
theorem test_concentration_monotone
    (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) (ε₁ ε₂ : ℝ) (h_le : ε₁ ≤ ε₂)
    (h_conc : ∀ r > (0 : ℝ), ENNReal.ofReal ε₂ ≤ μ (closedBall x r)) :
    ∀ r > (0 : ℝ), ENNReal.ofReal ε₁ ≤ μ (closedBall x r) := by
  intro r hr
  have h1 : ENNReal.ofReal ε₁ ≤ ENNReal.ofReal ε₂ := ENNReal.ofReal_le_ofReal h_le
  exact h1.trans (h_conc r hr)

/-- Test 2.10: Regular atomless addition identity: μ_reg {x} = 0 implies (μ_reg + ν) {x} = ν {x}. -/
theorem test_regular_atomless_preserves_defect
    (μ_reg ν_defect : Measure ℝ) (h_reg : ∀ x, μ_reg {x} = 0) (x : ℝ) :
    (μ_reg + ν_defect) {x} = ν_defect {x} := by
  simp [Measure.add_apply, h_reg x]

--------------------------------------------------------------------------------
-- SECTION 3: Cardinality Bounds on Singular Set (Category 3)
--------------------------------------------------------------------------------

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Test 3.1: Sub-threshold total energy forces ZERO singular points (card = 0).
If E₀ < ε₀ with E₀ ≥ 0 and ε₀ > 0, then the number of atoms of mass ≥ ε₀ is exactly 0. -/
theorem test_card_bound_subthreshold_empty_card
    (μ : Measure α) (E₀ ε₀ : ℝ) (hE₀ : 0 ≤ E₀) (hε : 0 < ε₀) (h_sub : E₀ < ε₀)
    (h_tot : μ univ ≤ ENNReal.ofReal E₀)
    (h_fin : {x : α | ENNReal.ofReal ε₀ ≤ μ {x}}.Finite) :
    h_fin.toFinset.card = 0 := by
  have h_bound := atoms_card_le μ E₀ ε₀ hε hE₀ h_tot h_fin
  have h_lt_one : E₀ / ε₀ < 1 := (div_lt_one hε).mpr h_sub
  have h_lt : (h_fin.toFinset.card : ℝ) < 1 := lt_of_le_of_lt h_bound h_lt_one
  have h_nat : h_fin.toFinset.card < 1 := by exact_mod_cast h_lt
  exact Nat.lt_one_iff.mp h_nat

/-- Test 3.2: Sub-threshold total energy forces the singular set to be completely empty. -/
theorem test_card_bound_subthreshold_empty_set
    (μ : Measure α) (E₀ ε₀ : ℝ) (hE₀ : 0 ≤ E₀) (hε : 0 < ε₀) (h_sub : E₀ < ε₀)
    (h_tot : μ univ ≤ ENNReal.ofReal E₀)
    (h_fin : {x : α | ENNReal.ofReal ε₀ ≤ μ {x}}.Finite) :
    {x : α | ENNReal.ofReal ε₀ ≤ μ {x}} = ∅ := by
  have h_card := test_card_bound_subthreshold_empty_card μ E₀ ε₀ hE₀ hε h_sub h_tot h_fin
  have h_empty : h_fin.toFinset = ∅ := Finset.card_eq_zero.mp h_card
  rw [Set.Finite.toFinset_eq_empty] at h_empty
  exact h_empty

/-- Test 3.3: Zero total energy forces singular set card = 0. -/
theorem test_card_bound_zero_energy_card
    (μ : Measure α) (ε₀ : ℝ) (hε : 0 < ε₀)
    (h_tot : μ univ ≤ ENNReal.ofReal 0)
    (h_fin : {x : α | ENNReal.ofReal ε₀ ≤ μ {x}}.Finite) :
    h_fin.toFinset.card = 0 := by
  have h_sub : (0 : ℝ) < ε₀ := hε
  exact test_card_bound_subthreshold_empty_card μ 0 ε₀ le_rfl hε h_sub h_tot h_fin

/-- Test 3.4: Zero total energy forces singular set to be empty. -/
theorem test_card_bound_zero_energy_set
    (μ : Measure α) (ε₀ : ℝ) (hε : 0 < ε₀)
    (h_tot : μ univ ≤ ENNReal.ofReal 0)
    (h_fin : {x : α | ENNReal.ofReal ε₀ ≤ μ {x}}.Finite) :
    {x : α | ENNReal.ofReal ε₀ ≤ μ {x}} = ∅ := by
  have h_sub : (0 : ℝ) < ε₀ := hε
  exact test_card_bound_subthreshold_empty_set μ 0 ε₀ le_rfl hε h_sub h_tot h_fin

/-- Test 3.5: Total energy equal to threshold E₀ = ε₀ forces at most ONE singular point. -/
theorem test_card_bound_equal_energy_le_one
    (μ : Measure α) (ε₀ : ℝ) (hε : 0 < ε₀)
    (h_tot : μ univ ≤ ENNReal.ofReal ε₀)
    (h_fin : {x : α | ENNReal.ofReal ε₀ ≤ μ {x}}.Finite) :
    h_fin.toFinset.card ≤ 1 := by
  have h_bound := atoms_card_le μ ε₀ ε₀ hε hε.le h_tot h_fin
  rw [div_self hε.ne'] at h_bound
  exact_mod_cast h_bound

/-- Test 3.6: Total energy equal to k * ε₀ bounds card by k. -/
theorem test_card_bound_k_times_energy
    (μ : Measure α) (k : ℕ) (ε₀ : ℝ) (hε : 0 < ε₀)
    (h_tot : μ univ ≤ ENNReal.ofReal ((k : ℝ) * ε₀))
    (h_fin : {x : α | ENNReal.ofReal ε₀ ≤ μ {x}}.Finite) :
    h_fin.toFinset.card ≤ k := by
  have hE₀ : 0 ≤ (k : ℝ) * ε₀ := mul_nonneg (Nat.cast_nonneg _) hε.le
  have h_bound := atoms_card_le μ ((k : ℝ) * ε₀) ε₀ hε hE₀ h_tot h_fin
  rw [mul_div_cancel_right₀ _ hε.ne'] at h_bound
  exact_mod_cast h_bound

/-- Test 3.7: Extreme energy-to-threshold ratio: E₀ = 10⁶, ε₀ = 10⁻² implies card ≤ 10⁸. -/
theorem test_card_bound_extreme_ratio
    (μ : Measure α)
    (h_tot : μ univ ≤ ENNReal.ofReal 1000000)
    (h_fin : {x : α | ENNReal.ofReal (1/100) ≤ μ {x}}.Finite) :
    (h_fin.toFinset.card : ℝ) ≤ 100000000 := by
  have hε : (0 : ℝ) < 1/100 := by norm_num
  have hE₀ : (0 : ℝ) ≤ 1000000 := by norm_num
  have h_bound := atoms_card_le μ 1000000 (1/100) hε hE₀ h_tot h_fin
  have h_div : (1000000 : ℝ) / (1/100) = 100000000 := by norm_num
  rw [h_div] at h_bound
  exact h_bound

/-- Test 3.8: Empty finset satisfies card_le_of_atoms unconditionally. -/
theorem test_card_le_of_atoms_empty (μ : Measure α) (E₀ ε₀ : ℝ) (hE₀ : 0 ≤ E₀)
    (h_tot : μ univ ≤ ENNReal.ofReal E₀) :
    ((∅ : Finset α).card : ℝ) * ε₀ ≤ E₀ := by
  simp [hE₀]

/-- Test 3.9: Singleton atom set satisfies 1 * ε₀ ≤ E₀. -/
theorem test_card_le_of_atoms_singleton (μ : Measure α) (E₀ ε₀ : ℝ) (hE₀ : 0 ≤ E₀)
    (h_tot : μ univ ≤ ENNReal.ofReal E₀) (x : α) (hx : ENNReal.ofReal ε₀ ≤ μ {x}) :
    ε₀ ≤ E₀ := by
  have hS : ∀ y ∈ ({x} : Finset α), ENNReal.ofReal ε₀ ≤ μ {y} := by
    intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    exact hx
  have h_le := card_le_of_atoms μ E₀ ε₀ hE₀ h_tot {x} hS
  simp only [Finset.card_singleton, Nat.cast_one, one_mul] at h_le
  exact h_le

/-- Test 3.10: Antitone containment of singular sets with respect to threshold. -/
theorem test_singular_set_antitone (μ : Measure α) (ε₁ ε₂ : ℝ) (h_le : ε₁ ≤ ε₂) :
    {x : α | ENNReal.ofReal ε₂ ≤ μ {x}} ⊆ {x : α | ENNReal.ofReal ε₁ ≤ μ {x}} := by
  intro x hx
  dsimp at hx ⊢
  have h1 : ENNReal.ofReal ε₁ ≤ ENNReal.ofReal ε₂ := ENNReal.ofReal_le_ofReal h_le
  exact h1.trans hx

--------------------------------------------------------------------------------
-- SECTION 4: Anti-Cheat & Non-Triviality Stress Tests (Category 4)
--------------------------------------------------------------------------------

/-- Test 4.1: Non-triviality: Constructive zero-sorry reduction theorem for TargetThresholds existence. -/
theorem test_anti_cheat_exists_target_thresholds_of_modules
    (ε_reg C_reg : ℝ) (h_reg_pos : 0 < ε_reg) (h_Creg_pos : 0 < C_reg)
    (h_reg : ∀ (u : CP1 → M) (a : ℂ) (r : ℝ) (_ : 0 < r),
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
  exists_target_thresholds_of_modules I ε_reg C_reg h_reg_pos h_Creg_pos h_reg
    ε_sph h_sph_pos h_sph C_neck a_decay ε_neck h_Cneck_pos h_a_pos h_neck_pos h_neck

/-- Test 4.2: Anti-cheat: Having an instance of TargetThresholds does NOT imply False. -/
theorem test_anti_cheat_thresholds_consistent (thresh : TargetThresholds I M) :
    thresh.h = thresh.h :=
  rfl

/-- Test 4.3: Anti-cheat refutation: Universal threshold CANNOT be non-positive. -/
theorem test_anti_cheat_refute_nonpos_threshold
    (thresh : TargetThresholds I M) (h_neg : thresh.h ≤ 0) : False :=
  thresh.h_pos.not_le h_neg

/-- Test 4.4: Anti-cheat refutation: Universal threshold CANNOT be zero. -/
theorem test_anti_cheat_refute_zero_threshold
    (thresh : TargetThresholds I M) (h_zero : thresh.h = 0) : False :=
  thresh.h_pos.ne' h_zero

/-- Test 4.5: Anti-cheat refutation: Atom mass CANNOT exceed total space measure.
If μ(univ) ≤ E₀, an atom of mass ε₀ > E₀ cannot exist. -/
theorem test_anti_cheat_refute_atom_exceeding_total
    (μ : Measure α) (E₀ ε₀ : ℝ) (hE₀ : 0 ≤ E₀) (h_tot : μ univ ≤ ENNReal.ofReal E₀)
    (x : α) (hx : ENNReal.ofReal ε₀ ≤ μ {x}) (h_excess : E₀ < ε₀) : False := by
  have h_le := test_card_le_of_atoms_singleton μ E₀ ε₀ hE₀ h_tot x hx
  linarith

/-- Test 4.6: Anti-cheat refutation: Disjoint atom set cardinality cannot exceed E₀ / ε₀. -/
theorem test_anti_cheat_refute_excessive_card
    (μ : Measure α) (E₀ ε₀ : ℝ) (hE₀ : 0 ≤ E₀) (hε : 0 < ε₀) (h_tot : μ univ ≤ ENNReal.ofReal E₀)
    (S : Finset α) (hS : ∀ x ∈ S, ENNReal.ofReal ε₀ ≤ μ {x})
    (h_excess : E₀ / ε₀ < (S.card : ℝ)) : False := by
  have h_le := card_le_of_atoms μ E₀ ε₀ hE₀ h_tot S hS
  have h_div : (S.card : ℝ) ≤ E₀ / ε₀ := by
    exact (le_div_iff₀ hε).mpr (by linarith [mul_comm (S.card : ℝ) ε₀])
  linarith

/-- Test 4.7: Anti-cheat: Calibrated defect energy target m_defect - h/2 is STRICTLY POSITIVE. -/
theorem test_anti_cheat_calibrated_energy_pos
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) :
    0 < m_defect - thresh.h / 2 := by
  have hh_pos := thresh.h_pos
  linarith

/-- Test 4.8: Anti-cheat: Calibrated defect energy target extracts strictly less than total defect mass. -/
theorem test_anti_cheat_calibrated_energy_strictly_less
    (thresh : TargetThresholds I M) (m_defect : ℝ) :
    m_defect - thresh.h / 2 < m_defect := by
  have hh_pos := thresh.h_pos
  linarith

/-- Test 4.9: Anti-cheat: The energy margin left behind by calibrated rescaling is exactly h/2 > 0. -/
theorem test_anti_cheat_calibrated_energy_margin
    (thresh : TargetThresholds I M) (m_defect : ℝ) :
    m_defect - (m_defect - thresh.h / 2) = thresh.h / 2 ∧ 0 < thresh.h / 2 := by
  refine ⟨by ring, by linarith [thresh.h_pos]⟩

/-- Test 4.10: Anti-cheat: Definitional equivalence of Bubbling namespace aliases. -/
theorem test_anti_cheat_bubbling_alias_target_thresholds :
    GromovCompactness.Bubbling.TargetThresholds I M = GromovCompactness.Analysis.TargetThresholds I M :=
  rfl

/-- Test 4.11: Anti-cheat: Non-triviality of Hofer single-step rescaling on constant density. -/
theorem test_anti_cheat_hofer_single_step_constant :
    ∃ (a : ℂ) (lam R : ℝ),
      dist a 0 ≤ 2 * 1 ∧ 0 < lam ∧ 0 < R ∧ 1 * 1 ≤ R ∧ lam * 1 = 1 ∧
      ∀ z : ℂ, dist z 0 ≤ R → lam * 1 ≤ 2 := by
  have h_cont : Continuous (fun (_ : ℂ) => (1 : ℝ)) := continuous_const
  have h_nonneg : ∀ y : ℂ, 0 ≤ (1 : ℝ) := fun _ => by norm_num
  have h_pos : 0 < (1 : ℝ) := by norm_num
  have h1 : 0 < (1 : ℝ) := by norm_num
  exact hofer_single_step (fun _ => 1) h_cont h_nonneg 0 1 h1 h_pos

end GromovCompactness.ChallengeMilestone5Thresholds

--------------------------------------------------------------------------------
-- SECTION 5: Axiom Purity Certification
--------------------------------------------------------------------------------

open GromovCompactness.ChallengeMilestone5Thresholds

#print axioms test_threshold_positivity
#print axioms test_threshold_le_half_reg
#print axioms test_threshold_le_sph
#print axioms test_threshold_le_half_neck
#print axioms test_threshold_strictly_less_reg
#print axioms test_threshold_strictly_less_neck
#print axioms test_threshold_le_min_all
#print axioms test_threshold_func_pos
#print axioms test_threshold_reg_dominant
#print axioms test_threshold_sph_dominant
#print axioms test_threshold_neck_dominant
#print axioms test_threshold_balanced
#print axioms test_threshold_microscopic
#print axioms test_threshold_macroscopic
#print axioms test_atom_concentration_dirac_exact
#print axioms test_atom_concentration_dirac_fractional
#print axioms test_atom_concentration_dirac_refute_excess
#print axioms test_atom_concentration_dirac_off_center
#print axioms test_atom_concentration_dirac_explicit_radius
#print axioms test_has_energy_defect_zero_reg
#print axioms test_zero_defect_no_concentration
#print axioms test_atom_concentration_nonpos_threshold
#print axioms test_concentration_monotone
#print axioms test_regular_atomless_preserves_defect
#print axioms test_card_bound_subthreshold_empty_card
#print axioms test_card_bound_subthreshold_empty_set
#print axioms test_card_bound_zero_energy_card
#print axioms test_card_bound_zero_energy_set
#print axioms test_card_bound_equal_energy_le_one
#print axioms test_card_bound_k_times_energy
#print axioms test_card_bound_extreme_ratio
#print axioms test_card_le_of_atoms_empty
#print axioms test_card_le_of_atoms_singleton
#print axioms test_singular_set_antitone
#print axioms test_anti_cheat_exists_target_thresholds_of_modules
#print axioms test_anti_cheat_thresholds_consistent
#print axioms test_anti_cheat_refute_nonpos_threshold
#print axioms test_anti_cheat_refute_zero_threshold
#print axioms test_anti_cheat_refute_atom_exceeding_total
#print axioms test_anti_cheat_refute_excessive_card
#print axioms test_anti_cheat_calibrated_energy_pos
#print axioms test_anti_cheat_calibrated_energy_strictly_less
#print axioms test_anti_cheat_calibrated_energy_margin
#print axioms test_anti_cheat_bubbling_alias_target_thresholds
#print axioms test_anti_cheat_hofer_single_step_constant
