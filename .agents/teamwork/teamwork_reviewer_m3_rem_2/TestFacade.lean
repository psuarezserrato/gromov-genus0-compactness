import GromovCompactness.Geometry.Sphere

open GromovCompactness

theorem affine_scaling_toHomeo_is_constant_dummy (a₁ a₂ : ℂ) (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    (affine_scaling a₁ s₁ h₁).toHomeo = (affine_scaling a₂ s₂ h₂).toHomeo := rfl

theorem affine_scaling_toHomeo_is_refl (a : ℂ) (s : ℝ) (h : 0 < s) :
    (affine_scaling a s h).toHomeo = Homeomorph.refl CP1 := rfl
