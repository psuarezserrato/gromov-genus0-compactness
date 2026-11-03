import GromovCompactness.Geometry.Sphere
import GromovCompactness.Geometry.Target

open GromovCompactness

namespace Verification

/- =========================================================================
   1. EMPIRICAL VERIFICATION OF PERSISTENT FACADE IN AFFINE_SCALING
   ========================================================================= -/

/-- Proof that affine_scaling.toHomeo is definitionally identical to the identity homeomorphism. -/
theorem affine_scaling_toHomeo_is_refl (a : ℂ) (s : ℝ) (hs : 0 < s) :
    (affine_scaling a s hs).toHomeo = Homeomorph.refl CP1 :=
  rfl

/-- Proof that affine_scaling.toHomeo discards the scaling parameter s. -/
theorem affine_scaling_fixes_all_points (z : CP1) :
    (affine_scaling 0 2 (by norm_num)).toHomeo z = z :=
  rfl

/-- Proof that affine_scaling.toHomeo is constant across different parameters. -/
theorem affine_scaling_toHomeo_constant (a₁ a₂ : ℂ) (s₁ s₂ : ℝ) (h₁ : 0 < s₁) (h₂ : 0 < s₂) :
    (affine_scaling a₁ s₁ h₁).toHomeo = (affine_scaling a₂ s₂ h₂).toHomeo :=
  rfl

/- =========================================================================
   2. VERIFICATION OF GENUINE COMPONENTS IN INVERSION AND ROTATION
   ========================================================================= -/

/-- Inversion swaps north and south poles. -/
theorem inversion_genuine_swap :
    inversion.toHomeo north_pole = south_pole ∧ inversion.toHomeo south_pole = north_pole :=
  inv_homeo_swaps_poles

/-- Inversion is demonstrably not the identity. -/
theorem inversion_not_id :
    inversion.toHomeo ≠ Homeomorph.refl CP1 :=
  inv_homeo_ne_id

/-- Rotation by π moves (1, 0, 0) to (-1, 0, 0). -/
theorem rotation_pi_genuine :
    (rotation Real.pi).matrix.a = -1 := by
  dsimp [rotation, MoebiusMatrix.rotation]
  rw [mul_comm, Complex.exp_pi_mul_I]

/- =========================================================================
   3. GROUPOID IDENTITY THEOREMS FOR MOEBIUSFRAME AND MOEBIUSMATRIX
   ========================================================================= -/

/-- Extensionality lemma for MoebiusMatrix. -/
theorem MoebiusMatrix.ext {M₁ M₂ : MoebiusMatrix}
    (ha : M₁.a = M₂.a) (hb : M₁.b = M₂.b) (hc : M₁.c = M₂.c) (hd : M₁.d = M₂.d) : M₁ = M₂ := by
  cases M₁; cases M₂
  dsimp at ha hb hc hd
  subst ha hb hc hd
  rfl

/-- Extensionality lemma for MoebiusFrame. -/
theorem MoebiusFrame.ext {ϕ₁ ϕ₂ : MoebiusFrame}
    (h_mat : ϕ₁.matrix = ϕ₂.matrix)
    (h_homeo : ϕ₁.toHomeo = ϕ₂.toHomeo) : ϕ₁ = ϕ₂ := by
  cases ϕ₁; cases ϕ₂
  dsimp at h_mat h_homeo
  subst h_mat h_homeo
  rfl

/-- Groupoid identity theorem: right identity ϕ ∘ id = ϕ. -/
theorem moebius_frame_comp_id (ϕ : MoebiusFrame) :
    MoebiusFrame.comp ϕ MoebiusFrame.id = ϕ := by
  apply MoebiusFrame.ext
  · apply MoebiusMatrix.ext <;> dsimp [MoebiusFrame.comp, MoebiusFrame.id, MoebiusMatrix.comp, MoebiusMatrix.mul, MoebiusMatrix.id] <;> ring
  · apply Homeomorph.ext; intro x; rfl

/-- Groupoid identity theorem: left identity id ∘ ϕ = ϕ. -/
theorem moebius_frame_id_comp (ϕ : MoebiusFrame) :
    MoebiusFrame.comp MoebiusFrame.id ϕ = ϕ := by
  apply MoebiusFrame.ext
  · apply MoebiusMatrix.ext <;> dsimp [MoebiusFrame.comp, MoebiusFrame.id, MoebiusMatrix.comp, MoebiusMatrix.mul, MoebiusMatrix.id] <;> ring
  · apply Homeomorph.ext; intro x; rfl

/-- Groupoid associativity: (ϕ₁ ∘ ϕ₂) ∘ ϕ₃ = ϕ₁ ∘ (ϕ₂ ∘ ϕ₃). -/
theorem moebius_frame_comp_assoc (ϕ₁ ϕ₂ ϕ₃ : MoebiusFrame) :
    MoebiusFrame.comp (MoebiusFrame.comp ϕ₁ ϕ₂) ϕ₃ =
    MoebiusFrame.comp ϕ₁ (MoebiusFrame.comp ϕ₂ ϕ₃) := by
  apply MoebiusFrame.ext
  · apply MoebiusMatrix.ext <;> dsimp [MoebiusFrame.comp, MoebiusMatrix.comp, MoebiusMatrix.mul] <;> ring
  · apply Homeomorph.ext; intro x; rfl

/-- Groupoid inverse law on homeomorphisms: ϕ⁻¹ ∘ ϕ = id. -/
theorem moebius_frame_inv_comp_toHomeo (ϕ : MoebiusFrame) :
    (MoebiusFrame.comp (MoebiusFrame.inv ϕ) ϕ).toHomeo = MoebiusFrame.id.toHomeo := by
  apply Homeomorph.ext; intro x
  exact ϕ.toHomeo.left_inv x

/-- Groupoid inverse law on homeomorphisms: ϕ ∘ ϕ⁻¹ = id. -/
theorem moebius_frame_comp_inv_toHomeo (ϕ : MoebiusFrame) :
    (MoebiusFrame.comp ϕ (MoebiusFrame.inv ϕ)).toHomeo = MoebiusFrame.id.toHomeo := by
  apply Homeomorph.ext; intro x
  exact ϕ.toHomeo.right_inv x

/-- Groupoid inverse law on matrices: ϕ⁻¹ ∘ ϕ ~ id (modulo PGL projective equivalence). -/
theorem moebius_frame_inv_comp_matrix (ϕ : MoebiusFrame) :
    PglEquiv (MoebiusFrame.comp (MoebiusFrame.inv ϕ) ϕ).matrix MoebiusMatrix.id := by
  intro p
  dsimp [MoebiusFrame.comp, MoebiusFrame.inv, MoebiusMatrix.comp, MoebiusMatrix.inv]
  rw [act_comp]
  have h := act_adj_cancel ϕ.matrix p
  dsimp [MoebiusMatrix.id, MoebiusMatrix.act]
  have hid : ((1 : ℂ) * p.1 + (0 : ℂ) * p.2, (0 : ℂ) * p.1 + (1 : ℂ) * p.2) = p := by
    ext <;> ring
  rw [hid]
  exact h

/-- Groupoid inverse law on matrices: ϕ ∘ ϕ⁻¹ ~ id (modulo PGL projective equivalence). -/
theorem moebius_frame_comp_inv_matrix (ϕ : MoebiusFrame) :
    PglEquiv (MoebiusFrame.comp ϕ (MoebiusFrame.inv ϕ)).matrix MoebiusMatrix.id := by
  intro p
  dsimp [MoebiusFrame.comp, MoebiusFrame.inv, MoebiusMatrix.comp, MoebiusMatrix.inv]
  rw [act_comp]
  dsimp [MoebiusMatrix.adj, MoebiusMatrix.act, ProjEquiv, MoebiusMatrix.id]
  have h1 : ϕ.matrix.a * (ϕ.matrix.d * p.1 + -ϕ.matrix.b * p.2) + ϕ.matrix.b * (-ϕ.matrix.c * p.1 + ϕ.matrix.a * p.2) =
            (ϕ.matrix.a * ϕ.matrix.d - ϕ.matrix.b * ϕ.matrix.c) * p.1 := by ring
  have h2 : ϕ.matrix.c * (ϕ.matrix.d * p.1 + -ϕ.matrix.b * p.2) + ϕ.matrix.d * (-ϕ.matrix.c * p.1 + ϕ.matrix.a * p.2) =
            (ϕ.matrix.a * ϕ.matrix.d - ϕ.matrix.b * ϕ.matrix.c) * p.2 := by ring
  rw [h1, h2]
  ring

/- =========================================================================
   4. AUTHENTIC SPHERICAL ACTION FORMULA FOR AFFINE SCALING
   ========================================================================= -/

/-- The exact rational map formula on S² for general affine scaling z ↦ a + s z
    strictly preserves the unit sphere equation: (x')² + (y')² + (t')² = 1. -/
theorem sphere_affine_scaling_algebra (x y t s a1 a2 : ℝ) (h_sphere : x^2 + y^2 + t^2 = 1) :
    let u := a1 * (1 - t) + s * x
    let v := a2 * (1 - t) + s * y
    let D := (a1^2 + a2^2) * (1 - t) + 2 * s * (a1 * x + a2 * y) + s^2 * (1 + t) + (1 - t)
    let t_num := (a1^2 + a2^2) * (1 - t) + 2 * s * (a1 * x + a2 * y) + s^2 * (1 + t) - (1 - t)
    (2 * u)^2 + (2 * v)^2 + t_num^2 = D^2 := by
  intro u v D t_num
  have h_sq : x^2 + y^2 = (1 - t) * (1 + t) := by linear_combination h_sphere
  dsimp [u, v, D, t_num]
  linear_combination 4 * s^2 * h_sq

end Verification
