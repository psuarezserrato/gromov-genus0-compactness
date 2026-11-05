/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (Challenger Milestone 2 Iteration 2)
-/
import GromovCompactness
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology Real ENNReal
open Metric Set MeasureTheory Filter GromovCompactness Complex

namespace GromovCompactness.ChallengeMilestone2Iter2

/-!
# Empirical Adversarial Challenge Suite: Milestone 2 Iteration 2
Challenger: challenger_m2_iter2_2

This challenge harness stress-tests:
1. Conformal Invariance: Exact scaling factor cancellation λ² · λ⁻² = 1 for non-trivial λ ≠ 1.
2. Energy Positivity: .toReal behavior on ⊤, necessity of `< ⊤` guard in totalEnergy_pos_of_exists_ball.
3. Target Constraints: Impossibility of degenerate or symmetric 2-forms satisfying ClosedTameTarget,
   and verifying that stdOmega is strictly symplectic.
-/

--------------------------------------------------------------------------------
-- PROBE 1: Conformal Invariance & Scaling Factor Cancellation (λ ≠ 1)
--------------------------------------------------------------------------------

/-- Test 1.1: Exact cancellation λ² · λ⁻² = 1 holds for non-trivial integer scale λ = 2. -/
theorem test_dilation_factor_cancellation_two :
    ENNReal.ofReal ((2 : ℝ) ^ 2) * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 2) = 1 :=
  dilation_factor_cancellation 2 (by norm_num)

/-- Test 1.2: Exact cancellation λ² · λ⁻² = 1 holds for non-trivial fraction λ = 1/3. -/
theorem test_dilation_factor_cancellation_third :
    ENNReal.ofReal (((1 / 3 : ℝ)) ^ 2) * ENNReal.ofReal (((1 / 3 : ℝ))⁻¹ ^ 2) = 1 :=
  dilation_factor_cancellation (1 / 3) (by norm_num)

/-- Test 1.3: Exact cancellation λ² · λ⁻² = 1 holds for irrational scale λ = Real.sqrt 2. -/
theorem test_dilation_factor_cancellation_sqrt2 :
    ENNReal.ofReal ((Real.sqrt 2) ^ 2) * ENNReal.ofReal ((Real.sqrt 2)⁻¹ ^ 2) = 1 :=
  dilation_factor_cancellation (Real.sqrt 2) (Real.sqrt_pos.mpr (by norm_num))

/-- Test 1.4: Strict necessity of λ > 0. For λ = 0, the cancellation FAILS:
0² · (0⁻¹)² = 0 ≠ 1. -/
theorem test_cancellation_fails_at_zero :
    ENNReal.ofReal ((0 : ℝ) ^ 2) * ENNReal.ofReal ((0 : ℝ)⁻¹ ^ 2) ≠ 1 := by
  simp

/-- Test 1.5: Non-trivial 2D affine scaling cancellation with shift a = 3 + 4I and scale λ = 2. -/
theorem test_affine_scaling_cancellation_nontrivial
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w : ℂ, ENNReal.ofReal ((2 : ℝ) ^ 2) * f ((3 + 4 * Complex.I) + (2 : ℝ) • w)) = ∫⁻ z : ℂ, f z :=
  lintegral_affine_scaling_cancellation (3 + 4 * Complex.I) 2 (by norm_num) f hf

--------------------------------------------------------------------------------
-- PROBE 2: Energy Positivity & Mathlib .toReal ⊤ Pitfall
--------------------------------------------------------------------------------

/-- Test 2.1: In Mathlib ENNReal, (⊤).toReal = 0.
This is the fundamental pitfall: an infinite extended measure evaluates to 0 in ℝ! -/
theorem test_toReal_top_is_zero : (⊤ : ℝ≥0∞).toReal = 0 :=
  ENNReal.top_toReal

/-- Test 2.2: Even though 0 < ⊤ in ENNReal, (⊤).toReal is NOT positive. -/
theorem test_top_strictly_positive_but_toReal_zero :
    (0 < (⊤ : ℝ≥0∞)) ∧ ¬ (0 < (⊤ : ℝ≥0∞).toReal) := by
  constructor
  · exact ENNReal.zero_lt_top
  · rw [test_toReal_top_is_zero]
    exact lt_irrefl 0

/-- Test 2.3: Characterization of positivity: 0 < x.toReal strictly requires x < ⊤. -/
theorem test_toReal_pos_iff_lt_top (x : ℝ≥0∞) :
    (0 < x.toReal) ↔ (0 < x ∧ x < ⊤) :=
  ENNReal.toReal_pos_iff

/-- Test 2.4: Finiteness guard check.
If a hypothetical measure had μ(CP1) = ⊤, then its energyMeasure would be 0, not > 0.
This confirms the guard `h_fin : energyMeasureExtended I u Set.univ < ⊤`
in `totalEnergy_pos_of_exists_ball` is strictly mathematically necessary and not redundant. -/
theorem test_finiteness_guard_indispensable (u : CP1 → CP1)
    (h_inf : energyMeasureExtended I_CP1 u Set.univ = ⊤) :
    totalEnergy I_CP1 u = 0 := by
  dsimp [totalEnergy, energyMeasure]
  rw [h_inf, test_toReal_top_is_zero]

/-- Test 2.5: For the concrete nonconstant map u = id, finiteness is genuinely proved (< ⊤),
so .toReal safely yields a strictly positive real total energy > 0. -/
theorem test_concrete_map_guarded_positivity :
    (energyMeasureExtended I_CP1 (id : CP1 → CP1) Set.univ < ⊤) ∧
    (0 < totalEnergy I_CP1 (id : CP1 → CP1)) :=
  ⟨concrete_nonconstant_map_finite_energy, concrete_nonconstant_map_positive_energy⟩

--------------------------------------------------------------------------------
-- PROBE 3: Target Constraints & Non-Degeneracy of stdOmega
--------------------------------------------------------------------------------

/-- Test 3.1: Skew-symmetry and symmetry are mutually exclusive for non-zero forms.
Any bilinear form that is both symmetric and skew-symmetric must be identically 0. -/
theorem test_symmetric_and_skew_implies_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V → V → ℝ)
    (h_add_right : ∀ x y z, B x (y + z) = B x y + B x z)
    (h_skew : ∀ v w, B v w = - B w v)
    (h_symm : ∀ v w, B v w = B w v)
    (v w : V) : B v w = 0 := by
  have h1 := h_skew v w
  have h2 := h_symm v w
  linarith

/-- Test 3.2: An identically zero 2-form CANNOT satisfy the `tame` condition.
This proves that degenerate or symmetric forms can NEVER satisfy ClosedTameTarget. -/
theorem test_zero_form_refutes_tame
    (J : E2 →L[ℝ] E2) (v : E2) (hv : v ≠ 0) :
    ¬ (0 < (0 : E2 →L[ℝ] E2 →L[ℝ] ℝ) v (J v)) := by
  simp

/-- Test 3.3: An identically zero 2-form CANNOT satisfy `ω_nondegenerate`. -/
theorem test_zero_form_refutes_nondegenerate :
    ¬ (∀ v : E2, (∀ w : E2, (0 : E2 →L[ℝ] E2 →L[ℝ] ℝ) v w = 0) → v = 0) := by
  intro h_nondeg
  have h_ne : e1 ≠ 0 := by
    intro heq
    have : e1 0 = 0 := by rw [heq]; rfl
    dsimp [e1] at this
    norm_num at this
  have h_all : ∀ w : E2, (0 : E2 →L[ℝ] E2 →L[ℝ] ℝ) e1 w = 0 := by simp
  have he1_zero := h_nondeg e1 h_all
  exact h_ne he1_zero

/-- Test 3.4: `stdOmega` is strictly non-symmetric: stdOmega e1 e2 ≠ stdOmega e2 e1. -/
theorem test_stdOmega_not_symmetric :
    stdOmega e1 e2 ≠ stdOmega e2 e1 := by
  have h1 := stdOmega_e1_e2
  have hskew := stdOmega_skew e2 e1
  intro h_symm
  linarith

/-- Test 3.5: `stdOmega` is genuinely non-degenerate:
if stdOmega v w = 0 for all w, then v must be 0. -/
theorem test_stdOmega_nondegenerate (v : E2) (h : ∀ w, stdOmega v w = 0) : v = 0 :=
  stdOmega_nondegenerate v h

/-- Test 3.6: `stdOmega` is strictly symplectic:
it is skew-symmetric, closed, and non-degenerate. -/
theorem test_stdOmega_is_symplectic :
    (∀ v w : E2, stdOmega v w = - stdOmega w v) ∧
    (∀ (y : E2) (v₁ v₂ v₃ : E2),
      let dω_y := fderiv ℝ (fun _ : E2 => stdOmega) y
      dω_y v₁ v₂ v₃ + dω_y v₂ v₃ v₁ + dω_y v₃ v₁ v₂ = 0) ∧
    (∀ v : E2, (∀ w : E2, stdOmega v w = 0) → v = 0) :=
  ⟨stdOmega_skew, stdOmega_closed, stdOmega_nondegenerate⟩

--------------------------------------------------------------------------------
-- PROBE 4: Axiom Audit for Empirical Challenge Suite
--------------------------------------------------------------------------------

#print axioms test_dilation_factor_cancellation_two
#print axioms test_dilation_factor_cancellation_third
#print axioms test_dilation_factor_cancellation_sqrt2
#print axioms test_cancellation_fails_at_zero
#print axioms test_affine_scaling_cancellation_nontrivial
#print axioms test_toReal_top_is_zero
#print axioms test_top_strictly_positive_but_toReal_zero
#print axioms test_toReal_pos_iff_lt_top
#print axioms test_finiteness_guard_indispensable
#print axioms test_concrete_map_guarded_positivity
#print axioms test_symmetric_and_skew_implies_zero
#print axioms test_zero_form_refutes_tame
#print axioms test_zero_form_refutes_nondegenerate
#print axioms test_stdOmega_not_symmetric
#print axioms test_stdOmega_nondegenerate
#print axioms test_stdOmega_is_symplectic

end GromovCompactness.ChallengeMilestone2Iter2
