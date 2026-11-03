# Iteration 3 Remediation Blueprint: Sphere.lean (F02)

## Goal
Integrate verified zero-sorry solutions from Explorers 1, 2, and 3 into `GromovCompactness/Geometry/Sphere.lean` to achieve a 100% CLEAN verdict from the Forensic Auditor and APPROVE from all reviewers.

## 1. Eliminate the Facade in `affine_scaling.toHomeo` (Explorer 1)
From `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_iter3_1/Scratch.lean`:
1. Add the stereographic dilation formula components:
   - `D_val (l : ℝ) (t : ℝ) : ℝ := (1 + l^2) + (1 - l^2) * t`
   - `D_val_pos`, `D_val_ne_zero`
   - `dil_fun (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3)`
   - `dil_fun_preserves_sphere`
   - `dil_fun_comp_inv`, `dil_fun_inv_comp`
   - `dil_homeo (l : ℝ) (hl : 0 < l) : CP1 ≃ₜ CP1`
   - `dil_homeo_is_smooth`, `dil_homeo_symm_is_smooth`
   - `dil_homeo_ne_id`
2. In `affine_scaling`:
   ```lean
   noncomputable def affine_scaling (a : ℂ) (scale : ℝ) (hscale : 0 < scale) : MoebiusFrame where
     matrix := MoebiusMatrix.affine_scaling a scale hscale
     toHomeo := dil_homeo scale hscale
     is_smooth := dil_homeo_is_smooth scale hscale
     is_smooth_symm := dil_homeo_symm_is_smooth scale hscale
   ```
3. Add the anti-facade verification theorems:
   - `theorem affine_scaling_toHomeo_ne_id (a : ℂ) (scale : ℝ) (hscale : 0 < scale) (hne : scale ≠ 1) : (affine_scaling a scale hscale).toHomeo ≠ Homeomorph.refl CP1`
   - `theorem affine_scaling_toHomeo_ne_id_frame (a : ℂ) (scale : ℝ) (hscale : 0 < scale) (hne : scale ≠ 1) : (affine_scaling a scale hscale).toHomeo ≠ MoebiusFrame.id.toHomeo`

## 2. Restore Uniqueness in `exists_unique_moebius_three_points` (Explorer 3)
From `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_iter3_3/exists_unique_moebius.patch`:
1. Define projective matrix equivalence:
   ```lean
   def PglEquiv (M₁ M₂ : MoebiusMatrix) : Prop :=
     ∀ p : ℂ × ℂ, ProjEquiv (M₁.act p) (M₂.act p)
   ```
2. Add lemmas:
   - `adj_mul_act_standard_1`, `2`, `3`
   - `projEquiv_adj_mul_iff`
   - `act_mul_frame_w1`, `w2`, `w3`
   - `projEquiv_of_frame_action`
   - `moebius_three_points_unique`
3. Update `exists_unique_moebius_three_points`:
   ```lean
   theorem exists_unique_moebius_three_points (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
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
           PglEquiv M M')
   ```
   Proved 100% with zero sorry using `general_three_point_eval_1, 2, 3` and `moebius_three_points_unique`.

## 3. Add Groupoid Identity Lemmas (Explorer 2)
From `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_iter3_2/VerifyMoebiusFrame.lean`:
Add:
- `moebius_frame_comp_id` / `moebius_frame_id_comp`
- `moebius_frame_comp_assoc`
- `moebius_frame_inv_comp_toHomeo` / `moebius_frame_comp_inv_toHomeo`
- `moebius_frame_inv_comp_matrix` / `moebius_frame_comp_inv_matrix`
- `MoebiusMatrix.ext` and `MoebiusFrame.ext`

## 4. Verification Steps
1. Build: `lake build GromovCompactness.Geometry.Target GromovCompactness.Geometry.Sphere` (exit code 0).
2. Axioms: `#print axioms` must yield strictly `[propext, Classical.choice, Quot.sound]`.
3. Check 0 sorry: `grep -n "sorry" GromovCompactness/Geometry/Sphere.lean` must return 0 matches.
4. Verify anti-facade: ensure `affine_scaling_toHomeo_ne_id` compiles and proves non-identity.
