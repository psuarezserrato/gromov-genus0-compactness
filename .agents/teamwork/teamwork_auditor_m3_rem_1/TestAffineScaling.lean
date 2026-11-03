import GromovCompactness.Geometry.Sphere
open GromovCompactness

theorem affine_scaling_fixes_all (z : CP1) :
    (affine_scaling 0 2 (by norm_num)).toHomeo z = z := by
  rfl

#print affine_scaling_fixes_all
