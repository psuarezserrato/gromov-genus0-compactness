import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere

open GromovCompactness Set Metric

section AdversarialTests

-- 1. Test affine_scaling and dil_homeo
theorem test_dil_homeo_moves_equator :
    let p : CP1 := ⟨!₂[1, 0, 0], by
      simp only [mem_sphere_zero_iff_norm]
      rw [EuclideanSpace.norm_eq]
      simp [Fin.sum_univ_three]⟩
    (dil_homeo 2 (by norm_num) p).1 0 ≠ p.1 0 := by
  intro p
  change (dil_fun 2 p.1) 0 ≠ p.1 0
  rw [dil_fun_0]
  have hp0 : p.1 0 = 1 := rfl
  have hp2 : p.1 2 = 0 := rfl
  rw [hp0, hp2]
  dsimp [D_val]
  intro h
  norm_num at h

theorem test_affine_scaling_ne_refl :
    (affine_scaling 0 2 (by norm_num)).toHomeo ≠ Homeomorph.refl CP1 :=
  affine_scaling_toHomeo_ne_id 0 2 (by norm_num) (by norm_num)

theorem test_affine_scaling_ne_id_frame :
    (affine_scaling 0 2 (by norm_num)).toHomeo ≠ MoebiusFrame.id.toHomeo :=
  affine_scaling_toHomeo_ne_id_frame 0 2 (by norm_num) (by norm_num)

-- 2. Test inversion
theorem test_inversion_swaps_poles :
    inversion.toHomeo north_pole = south_pole ∧ inversion.toHomeo south_pole = north_pole :=
  inv_homeo_swaps_poles

theorem test_inversion_ne_id :
    inversion.toHomeo ≠ Homeomorph.refl CP1 :=
  inv_homeo_ne_id

-- 3. Test three-point uniqueness and existence modulo PglEquiv
theorem test_three_points_structure :
    ∀ (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
      (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
      (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃),
      ∃ (M : MoebiusMatrix),
        (ProjEquiv (M.act v₁) w₁ ∧
         ProjEquiv (M.act v₂) w₂ ∧
         ProjEquiv (M.act v₃) w₃) ∧
        (∀ (M' : MoebiusMatrix),
          ProjEquiv (M'.act v₁) w₁ →
          ProjEquiv (M'.act v₂) w₂ →
          ProjEquiv (M'.act v₃) w₃ →
          PglEquiv M M') :=
  exists_unique_moebius_three_points

-- 4. Test disk_at geometry
theorem test_disk_at_excludes_north_pole (a : ℂ) (r : ℝ) :
    north_pole ∉ disk_at a r :=
  north_pole_not_mem_disk_at a r

end AdversarialTests
