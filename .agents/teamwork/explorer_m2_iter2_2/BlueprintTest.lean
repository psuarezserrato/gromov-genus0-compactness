import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Complex.Module
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Measure.WithDensity
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere

open MeasureTheory Metric Set Complex GromovCompactness
open scoped ENNReal

namespace BlueprintVerification

/-!
# Phase 5 Milestone 2 Iteration 2: Authentic Change of Variables & Trace Scaling
Machine-checked blueprint for Task P0-2.
-/

/- =========================================================================
   LEMMA 1: Pointwise Algebraic Trace Scaling for C-Linear Maps
   ========================================================================= -/

/-- General bilinear Dirichlet trace scaling under a C-linear map on ℝ² ≅ ℂ.
The quadratic trace scales by exactly the determinant a² + b² = |φ'(w)|². -/
theorem c_linear_dirichlet_trace_scaling
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V → V → ℝ) (hB_add_left : ∀ x y z, B (x + y) z = B x z + B y z)
    (hB_add_right : ∀ x y z, B x (y + z) = B x y + B x z)
    (hB_smul_left : ∀ c x y, B (c • x) y = c * B x y)
    (hB_smul_right : ∀ c x y, B x (c • y) = c * B x y)
    (T : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] V)
    (a b : ℝ)
    (K : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hKe1 : K e1 = a • e1 + b • e2)
    (hKe2 : K e2 = (-b) • e1 + a • e2) :
    B (T (K e1)) (T (K e1)) + B (T (K e2)) (T (K e2)) =
    (a^2 + b^2) * (B (T e1) (T e1) + B (T e2) (T e2)) := by
  have h1 : T (K e1) = a • T e1 + b • T e2 := by
    rw [hKe1, _root_.map_add, _root_.map_smul, _root_.map_smul]
  have h2 : T (K e2) = (-b) • T e1 + a • T e2 := by
    rw [hKe2, _root_.map_add, _root_.map_smul, _root_.map_smul]
  rw [h1, h2]
  simp only [hB_add_left, hB_add_right, hB_smul_left, hB_smul_right]
  ring

/-- Specialization to dilation by factor l > 0:
the Dirichlet energy density scales by exactly l². -/
theorem dilation_trace_scaling
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V → V → ℝ) (hB_add_left : ∀ x y z, B (x + y) z = B x z + B y z)
    (hB_add_right : ∀ x y z, B x (y + z) = B x y + B x z)
    (hB_smul_left : ∀ c x y, B (c • x) y = c * B x y)
    (hB_smul_right : ∀ c x y, B x (c • y) = c * B x y)
    (T : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] V)
    (l : ℝ)
    (K : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hKe1 : K e1 = l • e1)
    (hKe2 : K e2 = l • e2) :
    B (T (K e1)) (T (K e1)) + B (T (K e2)) (T (K e2)) =
    l^2 * (B (T e1) (T e1) + B (T e2) (T e2)) := by
  have hKe1' : K e1 = l • e1 + (0 : ℝ) • e2 := by rw [hKe1, zero_smul, add_zero]
  have hKe2' : K e2 = (-(0 : ℝ)) • e1 + l • e2 := by rw [hKe2, neg_zero, zero_smul, zero_add]
  have h := c_linear_dirichlet_trace_scaling B hB_add_left hB_add_right hB_smul_left hB_smul_right
    T l 0 K hKe1' hKe2'
  simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero] at h
  exact h

/- =========================================================================
   LEMMA 2: Transformation of Lebesgue Measure on ℂ
   ========================================================================= -/

/-- Translation invariance of Lebesgue volume on ℂ:
Measure.map (· + a) volume = volume. -/
theorem volume_map_translation (a : ℂ) :
    Measure.map (fun w => w + a) (volume : Measure ℂ) = volume :=
  map_add_right_eq_self volume a

/-- Scaling of Lebesgue volume on ℂ under real homothety w ↦ l • w:
Measure.map (l • ·) volume = (l⁻¹)^2 • volume. -/
theorem volume_map_homothety (l : ℝ) (hl : 0 < l) :
    Measure.map (fun w => l • w) (volume : Measure ℂ) =
    ENNReal.ofReal (l⁻¹ ^ 2) • volume := by
  have h_ne : l ≠ 0 := ne_of_gt hl
  have h_haar := Measure.map_addHaar_smul (μ := (volume : Measure ℂ)) h_ne
  rw [Complex.finrank_real_complex] at h_haar
  rw [h_haar]
  congr 1
  rw [_root_.abs_of_pos (inv_pos.mpr (pow_pos hl 2))]
  rw [inv_pow]

/-- Determinant of complex scalar multiplication as a real linear map on ℂ:
LinearMap.det (LinearMap.mulLeft ℝ c) = normSq c. -/
theorem det_mulLeft_complex (c : ℂ) :
    LinearMap.det (LinearMap.mulLeft ℝ c) = normSq c := by
  let b := Complex.basisOneI
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b (LinearMap.mulLeft ℝ c) = ![![c.re, -c.im], ![c.im, c.re]] := by
    ext i j
    simp only [LinearMap.toMatrix_apply, LinearMap.mulLeft_apply]
    fin_cases i <;> fin_cases j
    · simp [b]
    · simp [b]
    · simp [b]
    · simp [b]
  rw [hM]
  rw [Matrix.det_fin_two]
  simp [normSq, mul_comm]

/-- Rotation invariance of Lebesgue volume on ℂ:
For any unit complex number c (e.g. c = exp(iθ)), multiplication by c preserves volume. -/
theorem volume_map_rotation (c : ℂ) (hc : normSq c = 1) :
    Measure.map (fun w => c * w) (volume : Measure ℂ) = volume := by
  have h_lin : (fun w => c * w) = (LinearMap.mulLeft ℝ c : ℂ →ₗ[ℝ] ℂ) := rfl
  rw [h_lin]
  have h_det_ne : LinearMap.det (LinearMap.mulLeft ℝ c) ≠ 0 := by
    rw [det_mulLeft_complex, hc]
    norm_num
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) h_det_ne]
  rw [det_mulLeft_complex, hc, inv_one, abs_one, ENNReal.ofReal_one, one_smul]

/-- Affine transformation of Lebesgue volume on ℂ:
For w ↦ a + l • w, the pushforward measure scales by (l⁻¹)^2. -/
theorem volume_map_affine (a : ℂ) (l : ℝ) (hl : 0 < l) :
    Measure.map (fun w => a + l • w) (volume : Measure ℂ) =
    ENNReal.ofReal (l⁻¹ ^ 2) • volume := by
  have heq : (fun w => a + l • w) = (fun w => w + a) ∘ (fun w => l • w) := by
    ext w
    dsimp
    rw [add_comm]
  rw [heq]
  have h_meas_smul : Measurable (fun (w : ℂ) => l • w) :=
    continuous_const_smul l |>.measurable
  have h_meas_trans : Measurable (fun (w : ℂ) => w + a) :=
    continuous_add_right a |>.measurable
  rw [← Measure.map_map h_meas_trans h_meas_smul]
  rw [volume_map_homothety l hl]
  rw [Measure.map_smul]
  rw [volume_map_translation a]

/- =========================================================================
   LEMMA 3: Change of Variables Integral Identity on ℂ
   ========================================================================= -/

/-- Integral change-of-variables under dilation w ↦ l • w:
∫ f(l • w) dw = l⁻² ∫ f(z) dz. -/
theorem lintegral_comp_homothety (f : ℂ → ℝ≥0∞) (hf : Measurable f)
    (l : ℝ) (hl : 0 < l) :
    (∫⁻ w, f (l • w)) = ENNReal.ofReal (l⁻¹ ^ 2) * ∫⁻ z, f z := by
  have h_meas : Measurable (fun (w : ℂ) => l • w) :=
    continuous_const_smul l |>.measurable
  rw [← lintegral_map hf h_meas]
  rw [volume_map_homothety l hl]
  rw [lintegral_smul_measure]

/- =========================================================================
   LEMMA 4: Exact Product Cancellation of Derivative and Measure Factors
   ========================================================================= -/

/-- Exact cancellation:
The quadratic derivative scaling l² and the measure scaling l⁻² cancel identically:
l² * l⁻² = 1. -/
theorem dilation_factor_cancellation (l : ℝ) (hl : 0 < l) :
    ENNReal.ofReal (l ^ 2) * ENNReal.ofReal (l⁻¹ ^ 2) = 1 := by
  rw [← ENNReal.ofReal_mul (sq_nonneg l)]
  have h_inv : l ^ 2 * l⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hl), one_pow]
  rw [h_inv, ENNReal.ofReal_one]

/-- The integral of the rescaled energy density equals the original integral:
∫ (l² * f(l • w)) dw = ∫ f(z) dz. -/
theorem lintegral_scaled_density_eq (f : ℂ → ℝ≥0∞) (hf : Measurable f)
    (l : ℝ) (hl : 0 < l) :
    (∫⁻ w, ENNReal.ofReal (l ^ 2) * f (l • w)) = ∫⁻ z, f z := by
  rw [lintegral_const_mul' _ _ (by norm_num)]
  rw [lintegral_comp_homothety f hf l hl]
  rw [← mul_assoc]
  rw [dilation_factor_cancellation l hl]
  rw [one_mul]

end BlueprintVerification

#print axioms BlueprintVerification.c_linear_dirichlet_trace_scaling
#print axioms BlueprintVerification.dilation_trace_scaling
#print axioms BlueprintVerification.volume_map_translation
#print axioms BlueprintVerification.volume_map_homothety
#print axioms BlueprintVerification.det_mulLeft_complex
#print axioms BlueprintVerification.volume_map_rotation
#print axioms BlueprintVerification.volume_map_affine
#print axioms BlueprintVerification.lintegral_comp_homothety
#print axioms BlueprintVerification.dilation_factor_cancellation
#print axioms BlueprintVerification.lintegral_scaled_density_eq
