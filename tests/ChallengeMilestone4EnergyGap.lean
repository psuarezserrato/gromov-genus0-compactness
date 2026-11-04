/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Challenger 1 Milestone 4)
-/
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EpsilonRegularity
import GromovCompactness.Analysis.Monotonicity
import GromovCompactness.Analysis.EnergyGap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory GromovCompactness Classical
open GromovCompactness.Analysis

namespace GromovCompactness.ChallengeMilestone4EnergyGap

/-!
# Empirical Adversarial Challenge Suite: Milestone 4 Energy Gap
Challenger: challenger1_m4 (Empirical Challenger for Milestone 4)
Target: GromovCompactness/Analysis/EnergyGap.lean (Contracts A07 & Foundations)

This challenge harness empirically executes rigorous stress tests against all new
declarations in `EnergyGap.lean`:

1. Characterizations of Non-Constancy (`nonconstant_iff_exists_ne`, `exists_outside_of_nonconstant`):
   - Distinctness of geometric poles `north_pole ≠ south_pole`.
   - Concrete non-constant map to `ℝ` via coordinate projection.
   - Concrete non-constant map to discrete `Bool` space.
   - Non-constancy of identity map `id : CP1 → CP1`.
   - Contraposition on universal constants across general types.
   - Ball separation, radius shrinkage, and contrapositive inclusion.

2. Constant Map Energy Algebra:
   - Universal vanishing of Riemannian energy density at poles and generic chart points.
   - Identity `energyMeasureExtended = 0` on all subsets.
   - Vanishing of real energy measure on disks, annuli, circles, punctured spheres.
   - Vanishing of total energy for constant and conditionally-constant functions.
   - Homogeneity and linear scaling of zero energy.

3. Energy Non-Negativity & Subset Monotonicity:
   - Non-negativity for arbitrary curves.
   - Energy measure upper-bounded by total energy across disks, balls, and universal sets.
   - Sandwich/squeeze theorem: vanishing total energy forces vanishing local energy everywhere.
   - Exact two-sided sandwich for constant curves.

4. Modular Reduction Theorems:
   - Monotonicity reduction: quadratic scaling of gap constant $c \cdot r_0^2$ with concrete parameters.
   - Sharpness refutation: degenerate cases $c = 0$, $r_0 = 0$, $c < 0$ produce non-positive bounds.
   - Full reduction invocation with abstract monotonicity and exit hypotheses.
   - Stokes and diameter reduction invocation with concrete geometric tolerances.
   - Adversarial contrapositive deduction: energy below threshold forces constancy.
   - Strict positivity of total energy for non-constant curves.

5. Axiom Purity Certification:
   - Kernel verification that all 12 tested theorems depend strictly on standard Lean 4 axioms:
     `[propext, Classical.choice, Quot.sound]`.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

--------------------------------------------------------------------------------
-- SECTION 1: Characterizations of Non-Constancy & Boundary Separation
--------------------------------------------------------------------------------

/-- Test 1.1: Distinctness of the geometric north and south poles of CP1. -/
theorem test_north_pole_ne_south_pole : north_pole ≠ south_pole := by
  intro h
  have h_contra := congr_arg (fun (p : CP1) => p.1 2) h
  change (1 : ℝ) = -1 at h_contra
  norm_num at h_contra

/-- Test 1.2: Concrete non-constant map u : CP1 → ℝ via coordinate projection. -/
def realCoordMap (p : CP1) : ℝ := p.1 2

theorem test_realCoordMap_ne : realCoordMap north_pole ≠ realCoordMap south_pole := by
  dsimp [realCoordMap]
  change (1 : ℝ) ≠ -1
  norm_num

theorem test_nonconstant_realCoordMap : ¬ ∃ c : ℝ, ∀ z : CP1, realCoordMap z = c := by
  rw [nonconstant_iff_exists_ne]
  exact ⟨north_pole, south_pole, test_realCoordMap_ne⟩

theorem test_exists_ne_of_nonconstant_real : ∃ z w : CP1, realCoordMap z ≠ realCoordMap w :=
  exists_ne_of_nonconstant realCoordMap test_nonconstant_realCoordMap

/-- Test 1.3: Concrete non-constant map to discrete space Bool. -/
noncomputable def boolIndicatorMap (p : CP1) : Bool :=
  if p = north_pole then true else false

theorem test_boolIndicatorMap_ne : boolIndicatorMap north_pole ≠ boolIndicatorMap south_pole := by
  dsimp [boolIndicatorMap]
  rw [if_pos rfl]
  rw [if_neg (Ne.symm test_north_pole_ne_south_pole)]
  intro h
  cases h

theorem test_nonconstant_boolIndicatorMap : ¬ ∃ c : Bool, ∀ z : CP1, boolIndicatorMap z = c := by
  rw [nonconstant_iff_exists_ne]
  exact ⟨north_pole, south_pole, test_boolIndicatorMap_ne⟩

/-- Test 1.4: Concrete non-constancy of identity map id : CP1 → CP1. -/
theorem test_nonconstant_id_cp1 : ¬ ∃ c : CP1, ∀ z : CP1, id z = c := by
  rw [nonconstant_iff_exists_ne]
  exact ⟨north_pole, south_pole, test_north_pole_ne_south_pole⟩

theorem test_exists_ne_of_nonconstant_id : ∃ z w : CP1, (id : CP1 → CP1) z ≠ id w :=
  exists_ne_of_nonconstant id test_nonconstant_id_cp1

/-- Test 1.5: Contraposition of non-constancy for constant maps on any type. -/
theorem test_contraposition_constant (c : M) :
    ¬ (¬ ∃ c' : M, ∀ z : CP1, (fun _ => c) z = c') ∧
    ¬ (∃ z w : CP1, (fun _ => c) z ≠ (fun _ => c) w) := by
  have h_const : ∃ c' : M, ∀ z : CP1, (fun _ => c) z = c' := ⟨c, fun _ => rfl⟩
  have h_not_ne : ¬ ∃ z w : CP1, (fun _ => c) z ≠ (fun _ => c) w := by
    rintro ⟨z, w, hne⟩
    exact hne rfl
  exact ⟨not_not.mpr h_const, h_not_ne⟩

/-- Test 1.6: Equivalence between universal constancy and the absence of distinct value pairs. -/
theorem test_all_eq_iff_not_exists_ne {α β : Type*} (u : α → β) :
    (∀ z w : α, u z = u w) ↔ ¬ ∃ z w : α, u z ≠ u w := by
  constructor
  · intro h ⟨z, w, hne⟩
    exact hne (h z w)
  · intro h z w
    by_contra hne
    exact h ⟨z, w, hne⟩

/-- Test 1.7: Boundary separation and geometric ball exclusion from `exists_outside_of_nonconstant`. -/
theorem test_exists_outside_boundary_separation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (h : ¬ ∃ c : M, ∀ z, u z = c) :
    ∃ (x : M) (w : CP1), x ∈ Set.range u ∧ 0 < dist (u w) x ∧
      (u w ∉ Metric.ball x (dist (u w) x / 2)) ∧
      (u w ∉ Metric.ball x (dist (u w) x / 4)) ∧
      (∀ r, 0 < r → u w ∈ Metric.ball x r → dist (u w) x ≤ r) := by
  obtain ⟨x, w, hx, hpos, hout⟩ := exists_outside_of_nonconstant I u h
  refine ⟨x, w, hx, hpos, ?_, ?_, ?_⟩
  · apply hout (dist (u w) x / 2) (by linarith) (by linarith)
  · apply hout (dist (u w) x / 4) (by linarith) (by linarith)
  · intro r hr hmem
    rw [Metric.mem_ball] at hmem
    exact le_of_lt hmem

/-- Test 1.8: Sharpness of boundary ball exclusion for any two separated points. -/
theorem test_ball_exclusion_sharp (x y : M) (hpos : 0 < dist y x) :
    (∀ r, 0 < r → r < dist y x → y ∉ Metric.ball x r) ∧
    (y ∉ Metric.ball x (dist y x)) := by
  constructor
  · intro r hr hlt hmem
    rw [Metric.mem_ball] at hmem
    linarith
  · intro hmem
    rw [Metric.mem_ball] at hmem
    linarith

--------------------------------------------------------------------------------
-- SECTION 2: Energy Algebra of Constant Maps
--------------------------------------------------------------------------------

/-- Test 2.1: Pointwise Riemannian energy density vanishes at poles. -/
theorem test_riemannianEnergyDensity_const_poles (c : M) :
    riemannianEnergyDensity I (fun _ => c) north_pole = 0 ∧
    riemannianEnergyDensity I (fun _ => c) south_pole = 0 :=
  ⟨riemannianEnergyDensity_const I c north_pole,
   riemannianEnergyDensity_const I c south_pole⟩

/-- Test 2.2: Pointwise Riemannian energy density vanishes in stereographic charts. -/
theorem test_riemannianEnergyDensity_const_chart (c : M) (w : ℂ) :
    riemannianEnergyDensity I (fun _ => c) (stereo_chart.symm w) = 0 :=
  riemannianEnergyDensity_const I c (stereo_chart.symm w)

/-- Test 2.3: Extended energy measure of constant map vanishes identically on any set. -/
theorem test_energyMeasureExtended_const_all_sets (c : M) (s : Set CP1) :
    energyMeasureExtended I (fun _ : CP1 => c) s = 0 := by
  rw [energyMeasureExtended_const I c]
  rfl

/-- Test 2.4: Real energy measure vanishes on all geometric test sets. -/
theorem test_energyMeasure_const_geometric_sets (c : M) (a : ℂ) (r R : ℝ) (S : Set CP1) :
    energyMeasure I (fun _ => c) ∅ = 0 ∧
    energyMeasure I (fun _ => c) Set.univ = 0 ∧
    energyMeasure I (fun _ => c) (disk_at a r) = 0 ∧
    energyMeasure I (fun _ => c) (annulus_at a r R) = 0 ∧
    energyMeasure I (fun _ => c) (circle_at a r) = 0 ∧
    energyMeasure I (fun _ => c) (punctured_sphere S) = 0 := by
  refine ⟨energyMeasure_const I c ∅,
          energyMeasure_const I c Set.univ,
          energyMeasure_const I c (disk_at a r),
          energyMeasure_const I c (annulus_at a r R),
          energyMeasure_const I c (circle_at a r),
          energyMeasure_const I c (punctured_sphere S)⟩

/-- Test 2.5: Total energy vanishes identically on constants. -/
theorem test_totalEnergy_const_zero (c : M) :
    totalEnergy I (fun _ : CP1 => c) = 0 :=
  totalEnergy_const I c

/-- Test 2.6: Total energy vanishes on conditionally-defined constant curves. -/
theorem test_totalEnergy_ite_const (c : M) :
    totalEnergy I (fun z => if 1 = (1 : ℕ) then c else c) = 0 := by
  apply totalEnergy_eq_zero_of_forall_eq I _ c
  intro z
  simp

/-- Test 2.7: Linear scaling / homogeneity of zero energy for constant curves. -/
theorem test_energy_const_linear (c : M) (k : ℝ) :
    k * totalEnergy I (fun _ : CP1 => c) = 0 := by
  rw [totalEnergy_const I c, mul_zero]

--------------------------------------------------------------------------------
-- SECTION 3: Energy Non-Negativity & Subset Monotonicity
--------------------------------------------------------------------------------

/-- Test 3.1: Total energy is universally non-negative. -/
theorem test_totalEnergy_nonneg_universal (u : CP1 → M) :
    0 ≤ totalEnergy I u :=
  totalEnergy_nonneg I u

/-- Test 3.2: Energy measure on arbitrary geometric subsets is bounded by total energy. -/
theorem test_energyMeasure_le_totalEnergy_sets
    (u : CP1 → M) (h_fin : energyMeasureExtended I u Set.univ ≠ ⊤)
    (a : ℂ) (r : ℝ) (x : M) (r_ball : ℝ) :
    energyMeasure I u ∅ ≤ totalEnergy I u ∧
    energyMeasure I u Set.univ ≤ totalEnergy I u ∧
    energyMeasure I u (disk_at a r) ≤ totalEnergy I u ∧
    energyMeasure I u (u ⁻¹' Metric.ball x r_ball) ≤ totalEnergy I u := by
  refine ⟨energyMeasure_le_totalEnergy I u ∅ h_fin,
          energyMeasure_le_totalEnergy I u Set.univ h_fin,
          energyMeasure_le_totalEnergy I u (disk_at a r) h_fin,
          energyMeasure_le_totalEnergy I u (u ⁻¹' Metric.ball x r_ball) h_fin⟩

/-- Test 3.3: Squeeze theorem: vanishing total energy forces vanishing local energy on every set. -/
theorem test_energy_zero_sandwich (u : CP1 → M)
    (h_fin : energyMeasureExtended I u Set.univ ≠ ⊤)
    (h_zero : totalEnergy I u = 0) (A : Set CP1) :
    energyMeasure I u A = 0 := by
  have h_le : energyMeasure I u A ≤ 0 := by
    have h1 := energyMeasure_le_totalEnergy I u A h_fin
    rw [h_zero] at h1
    exact h1
  have h_ge : 0 ≤ energyMeasure I u A := energy_nonneg I u A
  exact le_antisymm h_le h_ge

/-- Test 3.4: Exact two-sided sandwich for constant curves. -/
theorem test_energy_const_sandwich (c : M) :
    0 ≤ totalEnergy I (fun _ : CP1 => c) ∧
    totalEnergy I (fun _ : CP1 => c) ≤ 0 := by
  refine ⟨totalEnergy_nonneg I (fun _ => c), by rw [totalEnergy_const I c]⟩

--------------------------------------------------------------------------------
-- SECTION 4: Modular Reduction Theorems (Adversarial Stress Harness)
--------------------------------------------------------------------------------

/-- Test 4.1: Gap constant scaling c * r₀^2 is strictly positive for any positive constants. -/
theorem test_monotonicity_gap_constant_scaling (c r₀ : ℝ) (hc : 0 < c) (hr₀ : 0 < r₀) :
    0 < c * r₀^2 := by positivity

/-- Test 4.2: Concrete evaluation of the gap constant on standard metric scales. -/
theorem test_monotonicity_gap_concrete_instances :
    (1 : ℝ) * 1^2 = 1 ∧
    (4 : ℝ) * (1 / 2)^2 = 1 ∧
    (100 : ℝ) * (1 / 10)^2 = 1 ∧
    (2 : ℝ) * 3^2 = 18 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Test 4.3 (Sharpness Refutation): Gap positivity fails degenerately when c = 0. -/
theorem test_monotonicity_gap_degenerate_c_zero (r₀ : ℝ) :
    (0 : ℝ) * r₀^2 = 0 := by
  ring

/-- Test 4.4 (Sharpness Refutation): Gap positivity fails degenerately when r₀ = 0. -/
theorem test_monotonicity_gap_degenerate_r0_zero (c : ℝ) :
    c * (0 : ℝ)^2 = 0 := by
  ring

/-- Test 4.5 (Sharpness Refutation): Gap positivity fails when c is strictly negative. -/
theorem test_monotonicity_gap_degenerate_c_neg (c r₀ : ℝ) (hc : c < 0) (hr₀ : r₀ ≠ 0) :
    c * r₀^2 < 0 := by
  have hr2 : 0 < r₀^2 := sq_pos_of_ne_zero hr₀
  exact mul_neg_of_neg_of_pos hc hr2

/-- Test 4.6: Modular invocation of `sphere_energy_gap_of_monotonicity_and_exit`. -/
theorem test_sphere_energy_gap_of_monotonicity_and_exit_invocation
    (c r₀ : ℝ) (hc : 0 < c) (hr₀ : 0 < r₀)
    (h_mono : ∀ (u : CP1 → M) (x : M) (r : ℝ),
      0 < r → r ≤ r₀ →
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      (∃ z, u z ∉ Metric.ball x r) →
      c * r^2 ≤ energyMeasure I u (u ⁻¹' (Metric.ball x r)))
    (h_exit : ∀ (u : CP1 → M) (x : M),
      x ∈ Set.range u →
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ∃ z, u z ∉ Metric.ball x r₀)
    (h_en_le : ∀ (u : CP1 → M) (s : Set CP1),
      energyMeasure I u s ≤ totalEnergy I u) :
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u :=
  sphere_energy_gap_of_monotonicity_and_exit I c r₀ hc hr₀ h_mono h_exit h_en_le

/-- Test 4.7: Modular invocation of `sphere_energy_gap_of_stokes_and_diameter`. -/
theorem test_sphere_energy_gap_of_stokes_and_diameter_invocation
    (ε_diam : ℝ) (hε : 0 < ε_diam) (r_inj : ℝ) (hr_inj : 0 < r_inj)
    (h_diam : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      totalEnergy I u < ε_diam →
      Metric.diam (Set.range u) < r_inj)
    (h_stokes : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      Metric.diam (Set.range u) < r_inj →
      totalEnergy I u = 0)
    (h_const_of_zero : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      totalEnergy I u = 0 →
      ∃ c : M, ∀ z, u z = c) :
    ∃ (ε_sph : ℝ), 0 < ε_sph ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u :=
  sphere_energy_gap_of_stokes_and_diameter I ε_diam hε r_inj hr_inj h_diam h_stokes h_const_of_zero

/-- Test 4.8: Adversarial Contrapositive Deduction:
Any J-holomorphic sphere with energy strictly below the gap threshold MUST be constant. -/
theorem test_energy_gap_contrapositive
    (ε_sph : ℝ) (hε : 0 < ε_sph)
    (h_gap : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u)
    (u : CP1 → M) (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_low_energy : totalEnergy I u < ε_sph) :
    ∃ c : M, ∀ z, u z = c := by
  by_contra h_nonconst
  have h_ge := h_gap u hu h_nonconst
  linarith

/-- Test 4.9: Strict positivity of total energy for non-constant spheres under energy gap. -/
theorem test_nonconstant_energy_strictly_positive
    (ε_sph : ℝ) (hε : 0 < ε_sph)
    (h_gap : ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      (¬ ∃ c : M, ∀ z, u z = c) →
      ε_sph ≤ totalEnergy I u)
    (u : CP1 → M) (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ)
    (h_nonconst : ¬ ∃ c : M, ∀ z, u z = c) :
    0 < totalEnergy I u := by
  have h_ge := h_gap u hu h_nonconst
  linarith

--------------------------------------------------------------------------------
-- SECTION 5: Axiom Purity Certification
--------------------------------------------------------------------------------

-- Target declarations from EnergyGap.lean
#print axioms nonconstant_iff_exists_ne
#print axioms exists_ne_of_nonconstant
#print axioms exists_outside_of_nonconstant
#print axioms riemannianEnergyDensity_const
#print axioms energyMeasureExtended_const
#print axioms energyMeasure_const
#print axioms totalEnergy_const
#print axioms totalEnergy_eq_zero_of_forall_eq
#print axioms totalEnergy_nonneg
#print axioms energyMeasure_le_totalEnergy
#print axioms sphere_energy_gap_of_monotonicity_and_exit
#print axioms sphere_energy_gap_of_stokes_and_diameter

-- Adversarial challenge suite theorems
#print axioms test_exists_outside_boundary_separation
#print axioms test_energy_zero_sandwich
#print axioms test_energy_gap_contrapositive
#print axioms test_nonconstant_energy_strictly_positive

end GromovCompactness.ChallengeMilestone4EnergyGap
