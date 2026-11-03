import GromovCompactness.Geometry.Sphere
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

open GromovCompactness

namespace ChallengeHarness

/-!
# Milestone 3 Remediation Adversarial Challenge Harness (F02: Sphere.lean)

This harness empirically tests:
1. Non-degeneracy of `MoebiusMatrix`:
   - `affine_scaling a scale hscale ≠ MoebiusMatrix.id` when $a \ne 0$ or $\text{scale} \ne 1$.
   - `inversion`: non-identity, swaps $0$ and $\infty$, determinant $-1 \ne 0$.
   - `rotation θ`: non-identity when $\theta = \pi / 2$, determinant $e^{i\theta} \ne 0$, rotates $(1, 0)$ to $(0, 1)$.
2. Smooth homeomorphisms on $S^2$:
   - `inv_homeo ≠ Homeomorph.refl CP1` and `inv_homeo north_pole = south_pole`.
   - `rot_homeo (π/2)` maps $(1, 0, 0)$ to $(0, 1, 0)$ and is not identity.
3. Integrity of 3-point transitivity and disk geometry:
   - `exists_unique_moebius_three_points` has no circular `h_trans` hypothesis.
   - `disk_at` excludes `north_pole` for all $r$, even $r = 1000$.
   - Disks are open and contain their stereographic center for $r > 0$.
-/

/- =========================================================================
   1. AUXILIARY COMPLEX & TRIGONOMETRIC LEMMAS
   ========================================================================= -/

lemma exp_I_pi_div_two : Complex.exp (Complex.I * (Real.pi / 2 : ℝ)) = Complex.I := by
  have h_eq : (Complex.I * (Real.pi / 2 : ℝ)) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h_eq, Complex.exp_mul_I]
  have hcos : Complex.cos ((Real.pi / 2 : ℝ) : ℂ) = 0 := by
    rw [← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
  have hsin : Complex.sin ((Real.pi / 2 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one]
  rw [hcos, hsin, zero_add, one_mul]

lemma c_equiv_e2_one : c_equiv_e2 1 = !₂[1, 0] := by
  ext i; fin_cases i
  · change ((Complex.orthonormalBasisOneI.repr 1) 0 : ℝ) = 1
    simp [Complex.orthonormalBasisOneI]
  · change ((Complex.orthonormalBasisOneI.repr 1) 1 : ℝ) = 0
    simp [Complex.orthonormalBasisOneI]

lemma c_equiv_e2_I : c_equiv_e2 Complex.I = !₂[0, 1] := by
  ext i; fin_cases i
  · change ((Complex.orthonormalBasisOneI.repr Complex.I) 0 : ℝ) = 0
    simp [Complex.orthonormalBasisOneI]
  · change ((Complex.orthonormalBasisOneI.repr Complex.I) 1 : ℝ) = 1
    simp [Complex.orthonormalBasisOneI]

/- =========================================================================
   2. NON-DEGENERACY OF MoebiusMatrix: affine_scaling
   ========================================================================= -/

-- 2.1: affine_scaling is NOT identity when translation a ≠ 0
theorem challenge_affine_scaling_ne_id_of_a_ne_zero
    (a : ℂ) (scale : ℝ) (hscale : 0 < scale) (ha : a ≠ 0) :
    MoebiusMatrix.affine_scaling a scale hscale ≠ MoebiusMatrix.id := by
  intro h
  have hb := congr_arg MoebiusMatrix.b h
  dsimp [MoebiusMatrix.affine_scaling, MoebiusMatrix.id] at hb
  exact ha hb

-- 2.2: affine_scaling is NOT identity when scale ≠ 1
theorem challenge_affine_scaling_ne_id_of_scale_ne_one
    (a : ℂ) (scale : ℝ) (hscale : 0 < scale) (hscale1 : scale ≠ 1) :
    MoebiusMatrix.affine_scaling a scale hscale ≠ MoebiusMatrix.id := by
  intro h
  have ha := congr_arg MoebiusMatrix.a h
  dsimp [MoebiusMatrix.affine_scaling, MoebiusMatrix.id] at ha
  have h_re := congr_arg Complex.re ha
  simp only [Complex.ofReal_re, Complex.one_re] at h_re
  exact hscale1 h_re

-- 2.3: affine_scaling has verified non-zero determinant scale
theorem challenge_affine_scaling_det
    (a : ℂ) (scale : ℝ) (hscale : 0 < scale) :
    let M := MoebiusMatrix.affine_scaling a scale hscale
    M.a * M.d - M.b * M.c = (scale : ℂ) ∧ M.a * M.d - M.b * M.c ≠ 0 := by
  intro M
  have hdet : M.a * M.d - M.b * M.c = (scale : ℂ) := by
    dsimp [M, MoebiusMatrix.affine_scaling]; ring
  refine ⟨hdet, ?_⟩
  rw [hdet]
  exact Complex.ofReal_ne_zero.mpr hscale.ne'

-- 2.4: affine_scaling correctly acts on ℂ: z ↦ a + scale * z
theorem challenge_affine_scaling_eval_action
    (a : ℂ) (scale : ℝ) (hscale : 0 < scale) (z : ℂ) :
    MoebiusMatrix.eval (MoebiusMatrix.affine_scaling a scale hscale) (OnePoint.some z) =
      OnePoint.some (a + (scale : ℂ) * z) :=
  MoebiusMatrix.eval_affine_scaling a scale hscale z

-- 2.5: affine_scaling fixes ∞
theorem challenge_affine_scaling_eval_infty
    (a : ℂ) (scale : ℝ) (hscale : 0 < scale) :
    MoebiusMatrix.eval (MoebiusMatrix.affine_scaling a scale hscale) OnePoint.infty =
      OnePoint.infty :=
  MoebiusMatrix.eval_affine_scaling_infty a scale hscale

/- =========================================================================
   3. NON-DEGENERACY OF MoebiusMatrix: inversion
   ========================================================================= -/

-- 3.1: inversion is NOT the identity matrix
theorem challenge_inversion_ne_id :
    MoebiusMatrix.inversion ≠ MoebiusMatrix.id := by
  intro h
  have ha := congr_arg MoebiusMatrix.a h
  dsimp [MoebiusMatrix.inversion, MoebiusMatrix.id] at ha
  norm_num at ha

-- 3.2: inversion determinant is exactly -1 ≠ 0
theorem challenge_inversion_det :
    let M := MoebiusMatrix.inversion
    M.a * M.d - M.b * M.c = -1 ∧ M.a * M.d - M.b * M.c ≠ 0 := by
  intro M
  have hdet : M.a * M.d - M.b * M.c = -1 := by
    dsimp [M, MoebiusMatrix.inversion]; ring
  refine ⟨hdet, ?_⟩
  rw [hdet]
  norm_num

-- 3.3: inversion swaps 0 and ∞: eval inversion 0 = ∞
theorem challenge_inversion_eval_zero :
    MoebiusMatrix.eval MoebiusMatrix.inversion (OnePoint.some 0) = OnePoint.infty :=
  MoebiusMatrix.eval_inversion_zero

-- 3.4: inversion swaps 0 and ∞: eval inversion ∞ = 0
theorem challenge_inversion_eval_infty :
    MoebiusMatrix.eval MoebiusMatrix.inversion OnePoint.infty = OnePoint.some 0 :=
  MoebiusMatrix.eval_inversion_infty

-- 3.5: inversion on non-zero z ∈ ℂ acts as 1/z
theorem challenge_inversion_eval_coe (z : ℂ) (hz : z ≠ 0) :
    MoebiusMatrix.eval MoebiusMatrix.inversion (OnePoint.some z) = OnePoint.some (1 / z) :=
  MoebiusMatrix.eval_inversion_coe z hz

/- =========================================================================
   4. NON-DEGENERACY OF MoebiusMatrix: rotation
   ========================================================================= -/

-- 4.1: rotation (π/2) is NOT the identity matrix
theorem challenge_rotation_pi_div_two_ne_id :
    MoebiusMatrix.rotation (Real.pi / 2) ≠ MoebiusMatrix.id := by
  intro h
  have ha := congr_arg MoebiusMatrix.a h
  dsimp [MoebiusMatrix.rotation, MoebiusMatrix.id] at ha
  rw [exp_I_pi_div_two] at ha
  have him := congr_arg Complex.im ha
  simp only [Complex.I_im, Complex.one_im] at him
  exact one_ne_zero him

-- 4.2: rotation θ has determinant exp(iθ) ≠ 0
theorem challenge_rotation_det (θ : ℝ) :
    let M := MoebiusMatrix.rotation θ
    M.a * M.d - M.b * M.c = Complex.exp (Complex.I * θ) ∧ M.a * M.d - M.b * M.c ≠ 0 := by
  intro M
  have hdet : M.a * M.d - M.b * M.c = Complex.exp (Complex.I * θ) := by
    dsimp [M, MoebiusMatrix.rotation]; ring
  refine ⟨hdet, ?_⟩
  rw [hdet]
  exact Complex.exp_ne_zero _

-- 4.3: rotation (π/2) maps 1 to I in ℂ (corresponding to (1,0) ↦ (0,1) via c_equiv_e2)
theorem challenge_rotation_eval_one :
    MoebiusMatrix.eval (MoebiusMatrix.rotation (Real.pi / 2)) (OnePoint.some 1) =
      OnePoint.some Complex.I := by
  have h := MoebiusMatrix.eval_rotation (Real.pi / 2) 1
  rw [mul_one] at h
  rw [h, exp_I_pi_div_two]

-- 4.4: In ℝ², rotation (π/2) via c_equiv_e2 sends (1, 0) to (0, 1)
theorem challenge_rotation_plane_action :
    c_equiv_e2 1 = !₂[1, 0] ∧
    c_equiv_e2 Complex.I = !₂[0, 1] ∧
    MoebiusMatrix.eval (MoebiusMatrix.rotation (Real.pi / 2)) (OnePoint.some 1) =
      OnePoint.some Complex.I :=
  ⟨c_equiv_e2_one, c_equiv_e2_I, challenge_rotation_eval_one⟩

-- 4.5: rotation fixes ∞
theorem challenge_rotation_eval_infty (θ : ℝ) :
    MoebiusMatrix.eval (MoebiusMatrix.rotation θ) OnePoint.infty = OnePoint.infty :=
  MoebiusMatrix.eval_rotation_infty θ

/- =========================================================================
   5. SMOOTH HOMEOMORPHISMS ON S²: inv_homeo
   ========================================================================= -/

-- 5.1: inv_homeo is NOT the identity homeomorphism of CP1
theorem challenge_inv_homeo_ne_id :
    inv_homeo ≠ Homeomorph.refl CP1 :=
  inv_homeo_ne_id

-- 5.2: inv_homeo swaps north pole and south pole
theorem challenge_inv_homeo_swaps_north_to_south :
    inv_homeo north_pole = south_pole :=
  inv_homeo_swaps_poles.1

theorem challenge_inv_homeo_swaps_south_to_north :
    inv_homeo south_pole = north_pole :=
  inv_homeo_swaps_poles.2

-- 5.3: inv_homeo is an involution: inv_homeo ∘ inv_homeo = id
theorem challenge_inv_homeo_involutive (z : CP1) :
    inv_homeo (inv_homeo z) = z :=
  inv_homeo.left_inv z

/- =========================================================================
   6. SMOOTH HOMEOMORPHISMS ON S²: rot_homeo
   ========================================================================= -/

def point_x : CP1 :=
  ⟨!₂[1, 0, 0], by
    simp only [mem_sphere_zero_iff_norm]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three]⟩

def point_y : CP1 :=
  ⟨!₂[0, 1, 0], by
    simp only [mem_sphere_zero_iff_norm]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three]⟩

lemma rot_lin_pi_div_two_apply :
    rot_lin (Real.pi / 2) !₂[1, 0, 0] = !₂[0, 1, 0] := by
  ext i; fin_cases i
  · change 1 * Real.cos (Real.pi / 2) - 0 * Real.sin (Real.pi / 2) = 0
    rw [Real.cos_pi_div_two, mul_zero, zero_mul, sub_zero]
  · change 1 * Real.sin (Real.pi / 2) + 0 * Real.cos (Real.pi / 2) = 1
    rw [Real.sin_pi_div_two, mul_one, zero_mul, add_zero]
  · rfl

-- 6.1: rot_homeo (π/2) maps (1, 0, 0) to (0, 1, 0) on S²
theorem challenge_rot_homeo_maps_x_to_y :
    rot_homeo (Real.pi / 2) point_x = point_y := by
  apply Subtype.ext
  exact rot_lin_pi_div_two_apply

-- 6.2: rot_homeo (π/2) is NOT the identity homeomorphism of CP1
theorem challenge_rot_homeo_pi_div_two_ne_id :
    rot_homeo (Real.pi / 2) ≠ Homeomorph.refl CP1 := by
  intro h
  have h_app : rot_homeo (Real.pi / 2) point_x = Homeomorph.refl CP1 point_x := by rw [h]
  rw [challenge_rot_homeo_maps_x_to_y] at h_app
  change point_y = point_x at h_app
  have h_coord := congr_arg (fun (p : CP1) => p.1 0) h_app
  change (0 : ℝ) = 1 at h_coord
  norm_num at h_coord

-- 6.3: rot_homeo group homomorphism law: rot(θ₁) ∘ rot(θ₂) = rot(θ₁ + θ₂)
theorem challenge_rot_homeo_comp (θ₁ θ₂ : ℝ) (z : CP1) :
    rot_homeo θ₁ (rot_homeo θ₂ z) = rot_homeo (θ₁ + θ₂) z := by
  apply Subtype.ext
  exact rot_lin_comp θ₁ θ₂ z.1

-- 6.4: rot_homeo at 0 is identity
theorem challenge_rot_homeo_zero (z : CP1) :
    rot_homeo 0 z = z := by
  apply Subtype.ext
  exact rot_lin_zero z.1

/- =========================================================================
   7. DISK GEOMETRY & TOPOLOGY ON S²
   ========================================================================= -/

-- 7.1: north_pole ∉ disk_at a r for arbitrarily large r = 1000
theorem challenge_north_pole_not_mem_large_disk (a : ℂ) :
    north_pole ∉ disk_at a 1000 :=
  north_pole_not_mem_disk_at a 1000

-- 7.2: disk_at a r is always an open set in CP1
theorem challenge_disk_at_is_open (a : ℂ) (r : ℝ) :
    IsOpen (disk_at a r) :=
  is_open_disk_at a r

-- 7.3: disk_at a r contains its center for r > 0
theorem challenge_disk_at_contains_center (a : ℂ) {r : ℝ} (hr : 0 < r) :
    stereo_chart.symm a ∈ disk_at a r :=
  center_mem_disk_at a hr

-- 7.4: Monotonicity of disks: r₁ ≤ r₂ → disk_at a r₁ ⊆ disk_at a r₂
theorem challenge_disk_at_mono (a : ℂ) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    disk_at a r₁ ⊆ disk_at a r₂ :=
  disk_at_mono a h

/- =========================================================================
   8. THREE-POINT TRANSITIVITY (NON-CIRCULAR AUDIT)
   ========================================================================= -/

-- 8.1: exists_unique_moebius_three_points exists without circular h_trans
-- We construct 3 distinct source points and 3 distinct target points in CP1
-- and verify that exists_unique_moebius_three_points returns an authentic MoebiusMatrix
def test_v1 : ℂ × ℂ := (1, 0)
def test_v2 : ℂ × ℂ := (0, 1)
def test_v3 : ℂ × ℂ := (1, 1)

def test_w1 : ℂ × ℂ := (1, 1)
def test_w2 : ℂ × ℂ := (0, 1)
def test_w3 : ℂ × ℂ := (1, 0)

lemma test_hv12 : ¬ ProjEquiv test_v1 test_v2 := by
  intro h; dsimp [ProjEquiv, test_v1, test_v2] at h; norm_num at h

lemma test_hv23 : ¬ ProjEquiv test_v2 test_v3 := by
  intro h; dsimp [ProjEquiv, test_v2, test_v3] at h; norm_num at h

lemma test_hv13 : ¬ ProjEquiv test_v1 test_v3 := by
  intro h; dsimp [ProjEquiv, test_v1, test_v3] at h; norm_num at h

lemma test_hw12 : ¬ ProjEquiv test_w1 test_w2 := by
  intro h; dsimp [ProjEquiv, test_w1, test_w2] at h; norm_num at h

lemma test_hw23 : ¬ ProjEquiv test_w2 test_w3 := by
  intro h; dsimp [ProjEquiv, test_w2, test_w3] at h; norm_num at h

lemma test_hw13 : ¬ ProjEquiv test_w1 test_w3 := by
  intro h; dsimp [ProjEquiv, test_w1, test_w3] at h; norm_num at h

theorem challenge_three_point_transitivity_non_circular :
    ∃ (M : MoebiusMatrix),
      ProjEquiv (M.act test_v1) test_w1 ∧
      ProjEquiv (M.act test_v2) test_w2 ∧
      ProjEquiv (M.act test_v3) test_w3 :=
  exists_unique_moebius_three_points test_v1 test_v2 test_v3 test_w1 test_w2 test_w3
    test_hv12 test_hv23 test_hv13 test_hw12 test_hw23 test_hw13

end ChallengeHarness

/- =========================================================================
   AXIOM AUDIT CHECK
   ========================================================================= -/

#print axioms ChallengeHarness.challenge_affine_scaling_ne_id_of_a_ne_zero
#print axioms ChallengeHarness.challenge_affine_scaling_ne_id_of_scale_ne_one
#print axioms ChallengeHarness.challenge_affine_scaling_det
#print axioms ChallengeHarness.challenge_affine_scaling_eval_action
#print axioms ChallengeHarness.challenge_affine_scaling_eval_infty
#print axioms ChallengeHarness.challenge_inversion_ne_id
#print axioms ChallengeHarness.challenge_inversion_det
#print axioms ChallengeHarness.challenge_inversion_eval_zero
#print axioms ChallengeHarness.challenge_inversion_eval_infty
#print axioms ChallengeHarness.challenge_inversion_eval_coe
#print axioms ChallengeHarness.challenge_rotation_pi_div_two_ne_id
#print axioms ChallengeHarness.challenge_rotation_det
#print axioms ChallengeHarness.challenge_rotation_eval_one
#print axioms ChallengeHarness.challenge_rotation_plane_action
#print axioms ChallengeHarness.challenge_inv_homeo_ne_id
#print axioms ChallengeHarness.challenge_inv_homeo_swaps_north_to_south
#print axioms ChallengeHarness.challenge_inv_homeo_involutive
#print axioms ChallengeHarness.challenge_rot_homeo_maps_x_to_y
#print axioms ChallengeHarness.challenge_rot_homeo_pi_div_two_ne_id
#print axioms ChallengeHarness.challenge_rot_homeo_comp
#print axioms ChallengeHarness.challenge_rot_homeo_zero
#print axioms ChallengeHarness.challenge_north_pole_not_mem_large_disk
#print axioms ChallengeHarness.challenge_disk_at_is_open
#print axioms ChallengeHarness.challenge_disk_at_contains_center
#print axioms ChallengeHarness.challenge_disk_at_mono
#print axioms ChallengeHarness.challenge_three_point_transitivity_non_circular
