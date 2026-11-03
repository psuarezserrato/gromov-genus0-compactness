import GromovCompactness.Geometry.Sphere
open GromovCompactness

theorem affine_scaling_toHomeo_is_refl (a : ℂ) (scale : ℝ) (hscale : 0 < scale) :
    (affine_scaling a scale hscale).toHomeo = Homeomorph.refl CP1 := by
  rfl

theorem affine_scaling_toHomeo_is_id_toHomeo (a : ℂ) (scale : ℝ) (hscale : 0 < scale) :
    (affine_scaling a scale hscale).toHomeo = MoebiusFrame.id.toHomeo := by
  rfl
