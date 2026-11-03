import GromovCompactness.Geometry.Sphere

open GromovCompactness

namespace TestChallengeAction

/-!
# Empirical and Adversarial Challenge Suite for MoebiusFrame and affine_scaling
-/

/-- Equatorial test point $p = (1, 0, 0) \in S^2 \cong \mathrm{CP1}$. -/
def test_point_x : CP1 :=
  ⟨!₂[1, 0, 0], by
    simp only [mem_sphere_zero_iff_norm]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three]⟩

/- =========================================================================
   1. Challenge affine_scaling Non-Triviality and Point Movement
   ========================================================================= -/

/-- Scale = 2 strictly moves the equatorial test point $(1, 0, 0)$. -/
theorem challenge_scaling_two_moves_point :
    (affine_scaling 0 2 (by norm_num)).toHomeo test_point_x ≠ test_point_x := by
  intro h
  have h_coord : ((affine_scaling 0 2 (by norm_num)).toHomeo test_point_x).1 2 = test_point_x.1 2 := by
    rw [h]
  change (dil_fun 2 test_point_x.1) 2 = test_point_x.1 2 at h_coord
  rw [dil_fun_2] at h_coord
  have hp2 : test_point_x.1 2 = 0 := rfl
  rw [hp2] at h_coord
  dsimp [D_val] at h_coord
  have h_val : ((1 - (2:ℝ)^2) + (1 + (2:ℝ)^2) * 0) / ((1 + (2:ℝ)^2) + (1 - (2:ℝ)^2) * 0) = -3/5 := by
    norm_num
  rw [h_val] at h_coord
  norm_num at h_coord

/-- Scale = 1/2 strictly moves the equatorial test point $(1, 0, 0)$. -/
theorem challenge_scaling_half_moves_point :
    (affine_scaling 0 (1/2) (by norm_num)).toHomeo test_point_x ≠ test_point_x := by
  intro h
  have h_coord : ((affine_scaling 0 (1/2) (by norm_num)).toHomeo test_point_x).1 2 = test_point_x.1 2 := by
    rw [h]
  change (dil_fun (1/2) test_point_x.1) 2 = test_point_x.1 2 at h_coord
  rw [dil_fun_2] at h_coord
  have hp2 : test_point_x.1 2 = 0 := rfl
  rw [hp2] at h_coord
  dsimp [D_val] at h_coord
  have h_val : ((1 - (1/2:ℝ)^2) + (1 + (1/2:ℝ)^2) * 0) / ((1 + (1/2:ℝ)^2) + (1 - (1/2:ℝ)^2) * 0) = 3/5 := by
    norm_num
  rw [h_val] at h_coord
  norm_num at h_coord

/-- Dilation strictly fixes the north pole for any scale $\lambda > 0$. -/
theorem challenge_scaling_fixes_north_pole (scale : ℝ) (hscale : 0 < scale) :
    (affine_scaling 0 scale hscale).toHomeo north_pole = north_pole := by
  ext i
  fin_cases i
  · change (dil_fun scale north_pole.1) 0 = north_pole.1 0
    rw [dil_fun_0]
    have hp0 : north_pole.1 0 = 0 := rfl
    rw [hp0]
    simp
  · change (dil_fun scale north_pole.1) 1 = north_pole.1 1
    rw [dil_fun_1]
    have hp1 : north_pole.1 1 = 0 := rfl
    rw [hp1]
    simp
  · change (dil_fun scale north_pole.1) 2 = north_pole.1 2
    rw [dil_fun_2]
    have hp2 : north_pole.1 2 = 1 := rfl
    rw [hp2]
    dsimp [D_val]
    have h_num : (1 - scale^2) + (1 + scale^2) * 1 = 2 := by ring
    have h_den : (1 + scale^2) + (1 - scale^2) * 1 = 2 := by ring
    rw [h_num, h_den]
    norm_num

/-- Dilation strictly fixes the south pole for any scale $\lambda > 0$. -/
theorem challenge_scaling_fixes_south_pole (scale : ℝ) (hscale : 0 < scale) :
    (affine_scaling 0 scale hscale).toHomeo south_pole = south_pole := by
  ext i
  fin_cases i
  · change (dil_fun scale south_pole.1) 0 = south_pole.1 0
    rw [dil_fun_0]
    have hp0 : south_pole.1 0 = 0 := rfl
    rw [hp0]
    simp
  · change (dil_fun scale south_pole.1) 1 = south_pole.1 1
    rw [dil_fun_1]
    have hp1 : south_pole.1 1 = 0 := rfl
    rw [hp1]
    simp
  · change (dil_fun scale south_pole.1) 2 = south_pole.1 2
    rw [dil_fun_2]
    have hp2 : south_pole.1 2 = -1 := rfl
    rw [hp2]
    dsimp [D_val]
    have h_num : (1 - scale^2) + (1 + scale^2) * (-1) = -2 * scale^2 := by ring
    have h_den : (1 + scale^2) + (1 - scale^2) * (-1) = 2 * scale^2 := by ring
    rw [h_num, h_den]
    have hs2 : scale^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hscale)
    have : (-2 * scale^2) / (2 * scale^2) = -1 := by
      calc (-2 * scale^2) / (2 * scale^2)
        _ = - ( (2 * scale^2) / (2 * scale^2) ) := by ring
        _ = - 1 := by rw [div_self (mul_ne_zero (by norm_num) hs2)]
    rw [this]

/- =========================================================================
   2. Challenge Inversion Non-Triviality
   ========================================================================= -/

/-- Inversion swaps north pole and south pole. -/
theorem challenge_inversion_swaps_poles :
    inversion.toHomeo north_pole = south_pole := by
  apply Subtype.ext
  ext i; fin_cases i
  · rfl
  · change -(0 : ℝ) = 0
    ring
  · rfl

/-- Inversion strictly moves the north pole. -/
theorem challenge_inversion_moves_north_pole :
    inversion.toHomeo north_pole ≠ north_pole := by
  intro h
  have h2 : (inversion.toHomeo north_pole).1 2 = north_pole.1 2 := by rw [h]
  change (-1 : ℝ) = 1 at h2
  norm_num at h2

/- =========================================================================
   3. Challenge Anti-Facade Theorems
   ========================================================================= -/

theorem challenge_anti_facade_scale_two :
    (affine_scaling 0 2 (by norm_num)).toHomeo ≠ Homeomorph.refl CP1 :=
  affine_scaling_toHomeo_ne_id 0 2 (by norm_num) (by norm_num)

theorem challenge_anti_facade_scale_two_frame :
    (affine_scaling 0 2 (by norm_num)).toHomeo ≠ MoebiusFrame.id.toHomeo :=
  affine_scaling_toHomeo_ne_id_frame 0 2 (by norm_num) (by norm_num)

theorem challenge_anti_facade_scale_half :
    (affine_scaling 0 (1/2) (by norm_num)).toHomeo ≠ Homeomorph.refl CP1 :=
  affine_scaling_toHomeo_ne_id 0 (1/2) (by norm_num) (by norm_num)

theorem challenge_anti_facade_scale_half_frame :
    (affine_scaling 0 (1/2) (by norm_num)).toHomeo ≠ MoebiusFrame.id.toHomeo :=
  affine_scaling_toHomeo_ne_id_frame 0 (1/2) (by norm_num) (by norm_num)

/- =========================================================================
   4. Challenge Groupoid Properties of MoebiusFrame
   ========================================================================= -/

theorem challenge_comp_id (ϕ : MoebiusFrame) :
    MoebiusFrame.comp ϕ MoebiusFrame.id = ϕ :=
  MoebiusFrame.comp_id ϕ

theorem challenge_id_comp (ϕ : MoebiusFrame) :
    MoebiusFrame.comp MoebiusFrame.id ϕ = ϕ :=
  MoebiusFrame.id_comp ϕ

theorem challenge_comp_assoc (ϕ₁ ϕ₂ ϕ₃ : MoebiusFrame) :
    MoebiusFrame.comp (MoebiusFrame.comp ϕ₁ ϕ₂) ϕ₃ =
    MoebiusFrame.comp ϕ₁ (MoebiusFrame.comp ϕ₂ ϕ₃) :=
  MoebiusFrame.comp_assoc ϕ₁ ϕ₂ ϕ₃

theorem challenge_inv_comp_toHomeo (ϕ : MoebiusFrame) :
    (MoebiusFrame.comp (MoebiusFrame.inv ϕ) ϕ).toHomeo = MoebiusFrame.id.toHomeo :=
  MoebiusFrame.inv_comp_toHomeo ϕ

theorem challenge_comp_inv_toHomeo (ϕ : MoebiusFrame) :
    (MoebiusFrame.comp ϕ (MoebiusFrame.inv ϕ)).toHomeo = MoebiusFrame.id.toHomeo :=
  MoebiusFrame.comp_inv_toHomeo ϕ

theorem challenge_inv_comp_matrix (ϕ : MoebiusFrame) :
    PglEquiv (MoebiusFrame.comp (MoebiusFrame.inv ϕ) ϕ).matrix MoebiusMatrix.id :=
  MoebiusFrame.inv_comp_matrix ϕ

theorem challenge_comp_inv_matrix (ϕ : MoebiusFrame) :
    PglEquiv (MoebiusFrame.comp ϕ (MoebiusFrame.inv ϕ)).matrix MoebiusMatrix.id :=
  MoebiusFrame.comp_inv_matrix ϕ

/- =========================================================================
   5. Concrete Groupoid Cancellation Test for Scaling
   ========================================================================= -/

noncomputable def scaling_two : MoebiusFrame := affine_scaling 0 2 (by norm_num)

theorem challenge_scaling_two_inv_cancels_homeo :
    (MoebiusFrame.comp (MoebiusFrame.inv scaling_two) scaling_two).toHomeo test_point_x = test_point_x := by
  have h := challenge_inv_comp_toHomeo scaling_two
  rw [h]
  rfl

theorem challenge_scaling_two_comp_inv_cancels_homeo :
    (MoebiusFrame.comp scaling_two (MoebiusFrame.inv scaling_two)).toHomeo test_point_x = test_point_x := by
  have h := challenge_comp_inv_toHomeo scaling_two
  rw [h]
  rfl

theorem challenge_scaling_two_inv_cancels_matrix :
    PglEquiv (MoebiusFrame.comp (MoebiusFrame.inv scaling_two) scaling_two).matrix MoebiusMatrix.id :=
  challenge_inv_comp_matrix scaling_two

theorem challenge_scaling_two_comp_inv_cancels_matrix :
    PglEquiv (MoebiusFrame.comp scaling_two (MoebiusFrame.inv scaling_two)).matrix MoebiusMatrix.id :=
  challenge_comp_inv_matrix scaling_two

/- =========================================================================
   6. Challenge Three-Point Normalization Theorem
   ========================================================================= -/

theorem challenge_three_points_normalization (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃) :
    ∃ (M : MoebiusMatrix),
      (ProjEquiv (M.act v₁) w₁ ∧
       ProjEquiv (M.act v₂) w₂ ∧
       ProjEquiv (M.act v₃) w₃) ∧
      (∀ (M' : MoebiusMatrix),
        ProjEquiv (M'.act v₁) w₁ →
        ProjEquiv (M'.act v₂) w₂ →
        ProjEquiv (M'.act v₃) w₃ →
        PglEquiv M M') :=
  exists_unique_moebius_three_points v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13

end TestChallengeAction

#print axioms TestChallengeAction.challenge_scaling_two_moves_point
#print axioms TestChallengeAction.challenge_scaling_half_moves_point
#print axioms TestChallengeAction.challenge_scaling_fixes_north_pole
#print axioms TestChallengeAction.challenge_scaling_fixes_south_pole
#print axioms TestChallengeAction.challenge_inversion_swaps_poles
#print axioms TestChallengeAction.challenge_inversion_moves_north_pole
#print axioms TestChallengeAction.challenge_anti_facade_scale_two
#print axioms TestChallengeAction.challenge_anti_facade_scale_two_frame
#print axioms TestChallengeAction.challenge_anti_facade_scale_half
#print axioms TestChallengeAction.challenge_anti_facade_scale_half_frame
#print axioms TestChallengeAction.challenge_comp_id
#print axioms TestChallengeAction.challenge_id_comp
#print axioms TestChallengeAction.challenge_comp_assoc
#print axioms TestChallengeAction.challenge_inv_comp_toHomeo
#print axioms TestChallengeAction.challenge_comp_inv_toHomeo
#print axioms TestChallengeAction.challenge_inv_comp_matrix
#print axioms TestChallengeAction.challenge_comp_inv_matrix
#print axioms TestChallengeAction.challenge_scaling_two_inv_cancels_homeo
#print axioms TestChallengeAction.challenge_scaling_two_comp_inv_cancels_homeo
#print axioms TestChallengeAction.challenge_scaling_two_inv_cancels_matrix
#print axioms TestChallengeAction.challenge_scaling_two_comp_inv_cancels_matrix
#print axioms TestChallengeAction.challenge_three_points_normalization
