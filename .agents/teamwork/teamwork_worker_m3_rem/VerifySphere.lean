import GromovCompactness.Geometry.Sphere
import GromovCompactness.Geometry.Target

open GromovCompactness Metric Set

namespace VerifyRemediation

-- 1. Inversion is non-identity and swaps poles
example : inv_homeo ≠ Homeomorph.refl CP1 :=
  inv_homeo_ne_id

example : inv_homeo north_pole = south_pole ∧ inv_homeo south_pole = north_pole :=
  inv_homeo_swaps_poles

-- 2. Genuine stereographic disks exclude north pole unconditionally
example (a : ℂ) (r : ℝ) : north_pole ∉ disk_at a r :=
  north_pole_not_mem_disk_at a r

example (a : ℂ) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : disk_at a r₁ ⊆ disk_at a r₂ :=
  disk_at_mono a h

example (a : ℂ) (r : ℝ) : IsOpen (disk_at a r) :=
  is_open_disk_at a r

-- 3. Transitivity of Moebius matrices
example (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃) :
    ∃ (M : MoebiusMatrix),
      ProjEquiv (M.act v₁) w₁ ∧
      ProjEquiv (M.act v₂) w₂ ∧
      ProjEquiv (M.act v₃) w₃ :=
  exists_unique_moebius_three_points v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13

-- 4. Actions on OnePoint ℂ
example (a : ℂ) (scale : ℝ) (hscale : 0 < scale) (z : ℂ) :
    MoebiusMatrix.eval (MoebiusMatrix.affine_scaling a scale hscale) (OnePoint.some z) =
    OnePoint.some (a + (scale : ℂ) * z) :=
  MoebiusMatrix.eval_affine_scaling a scale hscale z

example (z : ℂ) (hz : z ≠ 0) :
    MoebiusMatrix.eval MoebiusMatrix.inversion (OnePoint.some z) = OnePoint.some (1 / z) :=
  MoebiusMatrix.eval_inversion_coe z hz

example (θ : ℝ) (z : ℂ) :
    MoebiusMatrix.eval (MoebiusMatrix.rotation θ) (OnePoint.some z) =
    OnePoint.some (Complex.exp (Complex.I * θ) * z) :=
  MoebiusMatrix.eval_rotation θ z

end VerifyRemediation
