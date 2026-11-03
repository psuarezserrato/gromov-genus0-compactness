import Mathlib.Data.Complex.Basic

structure MoebiusMatrix where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

/-- The cross-ratio matrix sending (z₁, z₂, z₃) to (0, 1, ∞). -/
def cross_ratio_matrix (z₁ z₂ z₃ : ℂ)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) : MoebiusMatrix where
  a := z₂ - z₃
  b := -z₁ * (z₂ - z₃)
  c := z₂ - z₁
  d := -z₃ * (z₂ - z₁)
  det_ne_zero := by
    have hdet : (z₂ - z₃) * (-z₃ * (z₂ - z₁)) - (-z₁ * (z₂ - z₃)) * (z₂ - z₁) =
                (z₂ - z₃) * (z₂ - z₁) * (z₁ - z₃) := by ring
    rw [hdet]
    have h_sub1 : z₂ - z₃ ≠ 0 := sub_ne_zero.mpr h23
    have h_sub2 : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
    have h_sub3 : z₁ - z₃ ≠ 0 := sub_ne_zero.mpr h13
    exact mul_ne_zero (mul_ne_zero h_sub1 h_sub2) h_sub3

theorem cross_ratio_eval_z1 (z₁ z₂ z₃ : ℂ)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    let M := cross_ratio_matrix z₁ z₂ z₃ h12 h13 h23
    M.a * z₁ + M.b = 0 := by
  dsimp [cross_ratio_matrix]
  ring

theorem cross_ratio_eval_z2 (z₁ z₂ z₃ : ℂ)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    let M := cross_ratio_matrix z₁ z₂ z₃ h12 h13 h23
    M.a * z₂ + M.b = M.c * z₂ + M.d ∧ M.c * z₂ + M.d ≠ 0 := by
  dsimp [cross_ratio_matrix]
  constructor
  · ring
  · have h_factor : (z₂ - z₁) * z₂ + -z₃ * (z₂ - z₁) = (z₂ - z₁) * (z₂ - z₃) := by ring
    rw [h_factor]
    have h_sub1 : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
    have h_sub2 : z₂ - z₃ ≠ 0 := sub_ne_zero.mpr h23
    exact mul_ne_zero h_sub1 h_sub2

theorem cross_ratio_eval_z3 (z₁ z₂ z₃ : ℂ)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    let M := cross_ratio_matrix z₁ z₂ z₃ h12 h13 h23
    M.c * z₃ + M.d = 0 := by
  dsimp [cross_ratio_matrix]
  ring
