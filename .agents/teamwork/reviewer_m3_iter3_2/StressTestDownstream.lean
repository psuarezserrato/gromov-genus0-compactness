import GromovCompactness.Geometry.Sphere

open GromovCompactness

-- 1. Test anti-facade: prove that setting scale = 2 leads to a contradiction with Homeomorph.refl CP1
theorem test_scaling_not_refl :
    ¬ ((affine_scaling 0 2 (by norm_num)).toHomeo = Homeomorph.refl CP1) := by
  exact affine_scaling_toHomeo_ne_id 0 2 (by norm_num) (by norm_num)

theorem test_scaling_not_id_frame :
    ¬ ((affine_scaling 0 2 (by norm_num)).toHomeo = MoebiusFrame.id.toHomeo) := by
  exact affine_scaling_toHomeo_ne_id_frame 0 2 (by norm_num) (by norm_num)

-- 2. Test groupoid rewrite ergonomics in downstream expressions
def test_curve (u : CP1 → ℝ) (ϕ : MoebiusFrame) : CP1 → ℝ :=
  u ∘ ϕ.toHomeo

theorem test_comp_id_eval (u : CP1 → ℝ) (ϕ : MoebiusFrame) :
    test_curve u (ϕ.comp MoebiusFrame.id) = test_curve u ϕ := by
  dsimp [test_curve]
  rw [MoebiusFrame.comp_id]

theorem test_id_comp_eval (u : CP1 → ℝ) (ϕ : MoebiusFrame) :
    test_curve u (MoebiusFrame.id.comp ϕ) = test_curve u ϕ := by
  dsimp [test_curve]
  rw [MoebiusFrame.id_comp]

theorem test_comp_assoc_eval (u : CP1 → ℝ) (ϕ₁ ϕ₂ ϕ₃ : MoebiusFrame) :
    test_curve u ((ϕ₁.comp ϕ₂).comp ϕ₃) = test_curve u (ϕ₁.comp (ϕ₂.comp ϕ₃)) := by
  dsimp [test_curve]
  rw [MoebiusFrame.comp_assoc]

theorem test_inv_comp_eval (u : CP1 → ℝ) (ϕ : MoebiusFrame) :
    test_curve u (ϕ.inv.comp ϕ) = u := by
  dsimp [test_curve]
  rw [MoebiusFrame.inv_comp]
  rfl

theorem test_comp_inv_eval (u : CP1 → ℝ) (ϕ : MoebiusFrame) :
    test_curve u (ϕ.comp ϕ.inv) = u := by
  dsimp [test_curve]
  rw [MoebiusFrame.comp_inv]
  rfl

-- 3. Test uniqueness of 3-point normalization
theorem test_three_point_gauge_fixing (v₁ v₂ v₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃) :
    ∃ (M : MoebiusMatrix),
      (ProjEquiv (M.act v₁) (1, 0) ∧
       ProjEquiv (M.act v₂) (0, 1) ∧
       ProjEquiv (M.act v₃) (1, 1)) ∧
      (∀ M', ProjEquiv (M'.act v₁) (1, 0) →
             ProjEquiv (M'.act v₂) (0, 1) →
             ProjEquiv (M'.act v₃) (1, 1) →
             PglEquiv M M') := by
  have hw12 : ¬ ProjEquiv (1, 0) (0, 1) := by
    intro h; dsimp [ProjEquiv] at h; norm_num at h
  have hw23 : ¬ ProjEquiv (0, 1) (1, 1) := by
    intro h; dsimp [ProjEquiv] at h; norm_num at h
  have hw13 : ¬ ProjEquiv (1, 0) (1, 1) := by
    intro h; dsimp [ProjEquiv] at h; norm_num at h
  exact exists_unique_moebius_three_points v₁ v₂ v₃ (1, 0) (0, 1) (1, 1) hv12 hv23 hv13 hw12 hw23 hw13
