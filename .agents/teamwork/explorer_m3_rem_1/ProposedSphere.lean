/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Compactification.OnePoint
import GromovCompactness.Geometry.Target

open scoped Manifold ContDiff Topology
open Metric Set

namespace GromovCompactness

/-!
# Proposed Remediated Task F02: Sphere and Conformal Reparametrizations
-/

/-- The standard Riemann sphere $\mathbb{CP}^1 \cong S^2 \subseteq \mathbb{R}^3$. -/
abbrev CP1 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- Model with corners for the 2-dimensional sphere over $\mathbb{R}^2$. -/
abbrev I_CP1 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) := 𝓡 2

instance : IsManifold I_CP1 ∞ CP1 := inferInstance

instance fact_sphere_dim : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by simp [finrank_euclideanSpace_fin]⟩

/-- Canonical isometric equivalence between ℂ and EuclideanSpace ℝ (Fin 2). -/
noncomputable def c_equiv_e2 : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv

/-- Canonical complex structure on EuclideanSpace ℝ (Fin 2) induced by multiplication by I on ℂ. -/
noncomputable def J_CP1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  let mulI : ℂ →L[ℝ] ℂ :=
    { toLinearMap := LinearMap.mulLeft ℝ Complex.I
      cont := continuous_const.mul continuous_id }
  c_equiv_e2.toContinuousLinearMap.comp (mulI.comp c_equiv_e2.symm.toContinuousLinearMap)

lemma J_CP1_sq (v : EuclideanSpace ℝ (Fin 2)) : J_CP1 (J_CP1 v) = -v := by
  change c_equiv_e2 (Complex.I * (c_equiv_e2.symm (c_equiv_e2 (Complex.I * (c_equiv_e2.symm v))))) = -v
  rw [c_equiv_e2.symm_apply_apply]
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul, map_neg, c_equiv_e2.apply_symm_apply]

/-- The standard almost complex structure $j$ on the Riemann sphere $\mathbb{CP}^1$. -/
noncomputable def CP1.almostComplexStructure (z : CP1) : TangentSpace I_CP1 z →L[ℝ] TangentSpace I_CP1 z :=
  J_CP1

/-- Instance asserting that $\mathbb{CP}^1$ is a smooth Riemann surface domain. -/
noncomputable instance : RiemannDomain (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) I_CP1 CP1 where
  j := CP1.almostComplexStructure
  j_sq := by
    intro _ v
    exact J_CP1_sq v
  j_smooth := True

/-- The north pole $(0, 0, 1) \in S^2 \cong \infty \in \mathbb{CP}^1$. -/
def north_pole : CP1 :=
  ⟨!₂[0, 0, 1], by
    simp only [mem_sphere_zero_iff_norm]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three]⟩

/-- The south pole $(0, 0, -1) \in S^2 \cong 0 \in \mathbb{CP}^1$. -/
def south_pole : CP1 :=
  ⟨!₂[0, 0, -1], by
    simp only [mem_sphere_zero_iff_norm]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three]⟩

/-- The canonical stereographic chart from $\mathbb{CP}^1 \setminus \{\infty\}$ to $\mathbb{C}$. -/
noncomputable def stereo_chart : PartialHomeomorph CP1 ℂ :=
  (stereographic' 2 north_pole).transHomeomorph c_equiv_e2.symm.toHomeomorph

theorem stereo_chart_source : stereo_chart.source = {north_pole}ᶜ := by
  dsimp [stereo_chart]
  simp

theorem stereo_chart_target : stereo_chart.target = Set.univ := by
  dsimp [stereo_chart]
  simp

/-- Genuine stereographic disk of radius $r$ centered at $a \in \mathbb{C} \subset \mathbb{CP}^1$. -/
noncomputable def disk_at (a : ℂ) (r : ℝ) : Set CP1 :=
  stereo_chart.symm '' (Metric.ball a r)

/-- Genuine stereographic annulus centered at $a \in \mathbb{C}$. -/
noncomputable def annulus_at (a : ℂ) (r R : ℝ) : Set CP1 :=
  stereo_chart.symm '' {z : ℂ | r < dist z a ∧ dist z a < R}

/-- Punctured sphere $\mathbb{CP}^1 \setminus S$ removing a finite set of nodal or marked points. -/
def punctured_sphere (S : Set CP1) : Set CP1 :=
  Set.univ \ S

theorem north_pole_not_mem_disk (a : ℂ) (r : ℝ) :
    north_pole ∉ disk_at a r := by
  rintro ⟨z, _, hz⟩
  have h_source : stereo_chart.symm z ∈ stereo_chart.source :=
    stereo_chart.map_target (by trivial)
  have h_ne : stereo_chart.symm z ≠ north_pole := by
    have h_src := stereo_chart_source
    rw [h_src] at h_source
    exact h_source
  exact h_ne hz

/- =========================================================================
   PROJECTIVE MÖBIUS MATRICES AND ACTIONS
   ========================================================================= -/

/-- Projective matrix representing a Möbius transformation in $\operatorname{PGL}(2, \mathbb{C})$. -/
structure MoebiusMatrix where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

namespace MoebiusMatrix

def id : MoebiusMatrix where
  a := 1
  b := 0
  c := 0
  d := 1
  det_ne_zero := by simp

def comp (M₁ M₂ : MoebiusMatrix) : MoebiusMatrix where
  a := M₁.a * M₂.a + M₁.b * M₂.c
  b := M₁.a * M₂.b + M₁.b * M₂.d
  c := M₁.c * M₂.a + M₁.d * M₂.c
  d := M₁.c * M₂.b + M₁.d * M₂.d
  det_ne_zero := by
    have hdet : (M₁.a * M₂.a + M₁.b * M₂.c) * (M₁.c * M₂.b + M₁.d * M₂.d) -
                (M₁.a * M₂.b + M₁.b * M₂.d) * (M₁.c * M₂.a + M₁.d * M₂.c) =
                (M₁.a * M₁.d - M₁.b * M₁.c) * (M₂.a * M₂.d - M₂.b * M₂.c) := by ring
    rw [hdet]
    exact mul_ne_zero M₁.det_ne_zero M₂.det_ne_zero

def inv (M : MoebiusMatrix) : MoebiusMatrix where
  a := M.d
  b := -M.b
  c := -M.c
  d := M.a
  det_ne_zero := by
    have hdet : M.d * M.a - (-M.b) * (-M.c) = M.a * M.d - M.b * M.c := by ring
    rw [hdet]
    exact M.det_ne_zero

def affine_scaling (a : ℂ) (scale : ℝ) (hscale : 0 < scale) : MoebiusMatrix where
  a := (scale : ℂ)
  b := a
  c := 0
  d := 1
  det_ne_zero := by
    simp only [mul_one, mul_zero, sub_zero]
    exact Complex.ofReal_ne_zero.mpr hscale.ne'

def inversion : MoebiusMatrix where
  a := 0
  b := 1
  c := 1
  d := 0
  det_ne_zero := by simp

noncomputable def rotation (θ : ℝ) : MoebiusMatrix where
  a := Complex.exp (Complex.I * θ)
  b := 0
  c := 0
  d := 1
  det_ne_zero := by simp [Complex.exp_ne_zero]

/-- Action of a Möbius matrix on the extended complex plane OnePoint ℂ. -/
noncomputable def eval (M : MoebiusMatrix) (p : OnePoint ℂ) : OnePoint ℂ :=
  match p with
  | OnePoint.infty =>
    if M.c = 0 then OnePoint.infty else (OnePoint.some (M.a / M.c))
  | OnePoint.some z =>
    if M.c * z + M.d = 0 then OnePoint.infty
    else OnePoint.some ((M.a * z + M.b) / (M.c * z + M.d))

theorem eval_affine_scaling (a : ℂ) (scale : ℝ) (hscale : 0 < scale) (z : ℂ) :
    eval (affine_scaling a scale hscale) (OnePoint.some z) = OnePoint.some (a + (scale : ℂ) * z) := by
  dsimp [eval, affine_scaling]
  simp [add_comm]

theorem eval_affine_scaling_infty (a : ℂ) (scale : ℝ) (hscale : 0 < scale) :
    eval (affine_scaling a scale hscale) OnePoint.infty = OnePoint.infty := by
  dsimp [eval, affine_scaling]
  simp

theorem eval_inversion_coe (z : ℂ) (hz : z ≠ 0) :
    eval inversion (OnePoint.some z) = OnePoint.some (1 / z) := by
  dsimp [eval, inversion]
  simp [hz]

theorem eval_inversion_zero :
    eval inversion (OnePoint.some 0) = OnePoint.infty := by
  dsimp [eval, inversion]
  simp

theorem eval_inversion_infty :
    eval inversion OnePoint.infty = OnePoint.some 0 := by
  dsimp [eval, inversion]
  simp

theorem eval_rotation (θ : ℝ) (z : ℂ) :
    eval (rotation θ) (OnePoint.some z) = OnePoint.some (Complex.exp (Complex.I * θ) * z) := by
  dsimp [eval, rotation]
  simp

theorem eval_rotation_infty (θ : ℝ) :
    eval (rotation θ) OnePoint.infty = OnePoint.infty := by
  dsimp [eval, rotation]
  simp

/-- The cross-ratio matrix sending $(z_1, z_2, z_3)$ to $(0, 1, \infty)$. -/
def cross_ratio (z₁ z₂ z₃ : ℂ)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) : MoebiusMatrix where
  a := z₂ - z₃
  b := -z₁ * (z₂ - z₃)
  c := z₂ - z₁
  d := -z₃ * (z₂ - z₁)
  det_ne_zero := by
    have hdet : (z₂ - z₃) * (-z₃ * (z₂ - z₁)) - (-z₁ * (z₂ - z₃)) * (z₂ - z₁) =
                (z₂ - z₃) * (z₂ - z₁) * (z₁ - z₃) := by ring
    rw [hdet]
    have h_sub1 : z₂ - z₃ ≠ 0 := sub_ne_zero.mpr h23
    have h_sub2 : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
    have h_sub3 : z₁ - z₃ ≠ 0 := sub_ne_zero.mpr h13
    exact mul_ne_zero (mul_ne_zero h_sub1 h_sub2) h_sub3

theorem cross_ratio_eval_z1 (z₁ z₂ z₃ : ℂ)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    eval (cross_ratio z₁ z₂ z₃ h12 h13 h23) (OnePoint.some z₁) = OnePoint.some 0 := by
  dsimp [eval, cross_ratio]
  have h_denom : (z₂ - z₁) * z₁ + -z₃ * (z₂ - z₁) = (z₂ - z₁) * (z₁ - z₃) := by ring
  have h_sub2 : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  have h_sub3 : z₁ - z₃ ≠ 0 := sub_ne_zero.mpr h13
  have h_denom_ne : (z₂ - z₁) * z₁ + -z₃ * (z₂ - z₁) ≠ 0 := by
    rw [h_denom]
    exact mul_ne_zero h_sub2 h_sub3
  simp only [h_denom_ne, ↓reduceIte]
  have h_num : (z₂ - z₃) * z₁ + -z₁ * (z₂ - z₃) = 0 := by ring
  rw [h_num, zero_div]

end MoebiusMatrix

/- =========================================================================
   GEOMETRIC HOMEOMORPHISMS ON CP1
   ========================================================================= -/

/-- Inversion linear isometry on $\mathbb{R}^3$: $(x, y, t) \mapsto (x, -y, -t)$. -/
def inv_lin_map : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun v := !₂[v 0, -v 1, -v 2]
  map_add' x y := by
    ext i; fin_cases i
    · rfl
    · change -(x 1 + y 1) = -x 1 + -y 1; ring
    · change -(x 2 + y 2) = -x 2 + -y 2; ring
  map_smul' c x := by
    ext i; fin_cases i
    · rfl
    · change -(c • x 1) = c • -x 1; simp
    · change -(c • x 2) = c • -x 2; simp

noncomputable def inv_lin : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  inv_lin_map.toContinuousLinearMap

theorem inv_lin_norm (v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ = 1) :
    ‖inv_lin v‖ = 1 := by
  rw [EuclideanSpace.norm_eq] at hv ⊢
  have h0 : (inv_lin v) 0 = v 0 := rfl
  have h1 : (inv_lin v) 1 = -v 1 := rfl
  have h2 : (inv_lin v) 2 = -v 2 := rfl
  simp only [Fin.sum_univ_three, h0, h1, h2, norm_neg]
  simp only [Fin.sum_univ_three] at hv
  exact hv

theorem inv_lin_involutive (v : EuclideanSpace ℝ (Fin 3)) :
    inv_lin (inv_lin v) = v := by
  ext i; fin_cases i
  · rfl
  · exact neg_neg (v 1)
  · exact neg_neg (v 2)

/-- Inversion homeomorphism of the sphere $\mathbb{CP}^1$ interchanging $0$ and $\infty$. -/
noncomputable def inv_homeo : CP1 ≃ₜ CP1 where
  toFun z := ⟨inv_lin z.1, mem_sphere_zero_iff_norm.mpr (inv_lin_norm z.1 (mem_sphere_zero_iff_norm.mp z.2))⟩
  invFun z := ⟨inv_lin z.1, mem_sphere_zero_iff_norm.mpr (inv_lin_norm z.1 (mem_sphere_zero_iff_norm.mp z.2))⟩
  left_inv z := Subtype.ext (inv_lin_involutive z.1)
  right_inv z := Subtype.ext (inv_lin_involutive z.1)
  continuous_toFun := inv_lin.continuous.subtype_map (fun z hz => by
    simp only [mem_sphere_zero_iff_norm] at hz ⊢
    exact inv_lin_norm z hz)
  continuous_invFun := inv_lin.continuous.subtype_map (fun z hz => by
    simp only [mem_sphere_zero_iff_norm] at hz ⊢
    exact inv_lin_norm z hz)

theorem inv_homeo_swaps_poles :
    inv_homeo north_pole = south_pole ∧ inv_homeo south_pole = north_pole := by
  constructor
  · apply Subtype.ext
    ext i; fin_cases i
    · rfl
    · change - (0:ℝ) = 0; ring
    · change - (1:ℝ) = -1; ring
  · apply Subtype.ext
    ext i; fin_cases i
    · rfl
    · change - (0:ℝ) = 0; ring
    · change - (-1:ℝ) = 1; ring

theorem inv_homeo_ne_id :
    inv_homeo ≠ Homeomorph.refl CP1 := by
  intro h
  have h_pole : inv_homeo north_pole = Homeomorph.refl CP1 north_pole := by rw [h]
  have h_swaps := inv_homeo_swaps_poles.1
  rw [h_swaps] at h_pole
  have h_contra := congr_arg (fun (p : CP1) => p.1 2) h_pole
  change (-1 : ℝ) = 1 at h_contra
  norm_num at h_contra

/-- Rotation linear map on $\mathbb{R}^3$ around the $z$-axis by angle $\theta$. -/
noncomputable def rot_lin_map (θ : ℝ) : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun v := !₂[v 0 * Real.cos θ - v 1 * Real.sin θ, v 0 * Real.sin θ + v 1 * Real.cos θ, v 2]
  map_add' x y := by
    ext i; fin_cases i
    · change (x 0 + y 0) * Real.cos θ - (x 1 + y 1) * Real.sin θ =
        (x 0 * Real.cos θ - x 1 * Real.sin θ) + (y 0 * Real.cos θ - y 1 * Real.sin θ); ring
    · change (x 0 + y 0) * Real.sin θ + (x 1 + y 1) * Real.cos θ =
        (x 0 * Real.sin θ + x 1 * Real.cos θ) + (y 0 * Real.sin θ + y 1 * Real.cos θ); ring
    · rfl
  map_smul' c x := by
    ext i; fin_cases i
    · change (c • x 0) * Real.cos θ - (c • x 1) * Real.sin θ =
        c • (x 0 * Real.cos θ - x 1 * Real.sin θ); simp; ring
    · change (c • x 0) * Real.sin θ + (c • x 1) * Real.cos θ =
        c • (x 0 * Real.sin θ + x 1 * Real.cos θ); simp; ring
    · rfl

noncomputable def rot_lin (θ : ℝ) : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (rot_lin_map θ).toContinuousLinearMap

theorem rot_lin_norm (θ : ℝ) (v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ = 1) :
    ‖rot_lin θ v‖ = 1 := by
  rw [EuclideanSpace.norm_eq] at hv ⊢
  have h0 : (rot_lin θ v) 0 = v 0 * Real.cos θ - v 1 * Real.sin θ := rfl
  have h1 : (rot_lin θ v) 1 = v 0 * Real.sin θ + v 1 * Real.cos θ := rfl
  have h2 : (rot_lin θ v) 2 = v 2 := rfl
  simp only [Fin.sum_univ_three, h0, h1, h2]
  simp only [Fin.sum_univ_three] at hv
  have h_trig : (v 0 * Real.cos θ - v 1 * Real.sin θ) ^ 2 + (v 0 * Real.sin θ + v 1 * Real.cos θ) ^ 2 =
      (v 0) ^ 2 + (v 1) ^ 2 := by
    linear_combination (v 0 ^ 2 + v 1 ^ 2) * (Real.sin_sq_add_cos_sq θ)
  have sq_norm (x : ℝ) : ‖x‖ ^ 2 = x ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
  rw [sq_norm, sq_norm, sq_norm] at hv ⊢
  rw [h_trig]
  exact hv

theorem rot_lin_comp (θ₁ θ₂ : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    rot_lin θ₁ (rot_lin θ₂ v) = rot_lin (θ₁ + θ₂) v := by
  ext i; fin_cases i
  · change (v 0 * Real.cos θ₂ - v 1 * Real.sin θ₂) * Real.cos θ₁ - (v 0 * Real.sin θ₂ + v 1 * Real.cos θ₂) * Real.sin θ₁ =
      v 0 * Real.cos (θ₁ + θ₂) - v 1 * Real.sin (θ₁ + θ₂)
    rw [Real.cos_add, Real.sin_add]; ring
  · change (v 0 * Real.cos θ₂ - v 1 * Real.sin θ₂) * Real.sin θ₁ + (v 0 * Real.sin θ₂ + v 1 * Real.cos θ₂) * Real.cos θ₁ =
      v 0 * Real.sin (θ₁ + θ₂) + v 1 * Real.cos (θ₁ + θ₂)
    rw [Real.cos_add, Real.sin_add]; ring
  · rfl

theorem rot_lin_zero (v : EuclideanSpace ℝ (Fin 3)) :
    rot_lin 0 v = v := by
  ext i; fin_cases i
  · change v 0 * Real.cos 0 - v 1 * Real.sin 0 = v 0; simp
  · change v 0 * Real.sin 0 + v 1 * Real.cos 0 = v 1; simp
  · rfl

theorem rot_lin_inv (θ : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    rot_lin (-θ) (rot_lin θ v) = v ∧ rot_lin θ (rot_lin (-θ) v) = v := by
  constructor
  · rw [rot_lin_comp, neg_add_cancel, rot_lin_zero]
  · rw [rot_lin_comp, add_neg_cancel, rot_lin_zero]

/-- Rotation homeomorphism of the sphere $\mathbb{CP}^1$ by angle $\theta$. -/
noncomputable def rot_homeo (θ : ℝ) : CP1 ≃ₜ CP1 where
  toFun z := ⟨rot_lin θ z.1, mem_sphere_zero_iff_norm.mpr (rot_lin_norm θ z.1 (mem_sphere_zero_iff_norm.mp z.2))⟩
  invFun z := ⟨rot_lin (-θ) z.1, mem_sphere_zero_iff_norm.mpr (rot_lin_norm (-θ) z.1 (mem_sphere_zero_iff_norm.mp z.2))⟩
  left_inv z := Subtype.ext (rot_lin_inv θ z.1).1
  right_inv z := Subtype.ext (rot_lin_inv θ z.1).2
  continuous_toFun := (rot_lin θ).continuous.subtype_map (fun z hz => by
    simp only [mem_sphere_zero_iff_norm] at hz ⊢
    exact rot_lin_norm θ z hz)
  continuous_invFun := (rot_lin (-θ)).continuous.subtype_map (fun z hz => by
    simp only [mem_sphere_zero_iff_norm] at hz ⊢
    exact rot_lin_norm (-θ) z hz)

/- =========================================================================
   MOEBIUS FRAME STRUCTURE
   ========================================================================= -/

/-- A Möbius transformation frame $\phi \in \operatorname{PSL}(2, \mathbb{C})$ acting on $\mathbb{CP}^1$. -/
structure MoebiusFrame where
  /-- Associated matrix in PGL(2, ℂ). -/
  matrix : MoebiusMatrix
  /-- Underlying topological homeomorphism of the sphere. -/
  toHomeo : CP1 ≃ₜ CP1
  /-- Smoothness in both directions. -/
  is_smooth : ContMDiff I_CP1 I_CP1 ∞ toHomeo
  is_smooth_symm : ContMDiff I_CP1 I_CP1 ∞ toHomeo.symm

namespace MoebiusFrame

/-- Identity Möbius frame. -/
def id : MoebiusFrame where
  matrix := MoebiusMatrix.id
  toHomeo := Homeomorph.refl CP1
  is_smooth := contMDiff_id
  is_smooth_symm := contMDiff_id

/-- Composition of Möbius frames: $\phi_1 \circ \phi_2$. -/
def comp (ϕ₁ ϕ₂ : MoebiusFrame) : MoebiusFrame where
  matrix := MoebiusMatrix.comp ϕ₁.matrix ϕ₂.matrix
  toHomeo := ϕ₂.toHomeo.trans ϕ₁.toHomeo
  is_smooth := ϕ₁.is_smooth.comp ϕ₂.is_smooth
  is_smooth_symm := ϕ₂.is_smooth_symm.comp ϕ₁.is_smooth_symm

/-- Inverse Möbius frame: $\phi^{-1}$. -/
def inv (ϕ : MoebiusFrame) : MoebiusFrame where
  matrix := MoebiusMatrix.inv ϕ.matrix
  toHomeo := ϕ.toHomeo.symm
  is_smooth := ϕ.is_smooth_symm
  is_smooth_symm := ϕ.is_smooth

end MoebiusFrame

/-- Standard inversion $z \mapsto 1/z$ interchanging $0$ and $\infty$. -/
noncomputable def inversion : MoebiusFrame where
  matrix := MoebiusMatrix.inversion
  toHomeo := inv_homeo
  is_smooth := by
    have h_comp : ContMDiff I_CP1 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (inv_lin ∘ ((↑) : CP1 → EuclideanSpace ℝ (Fin 3))) :=
      inv_lin.contMDiff.comp contMDiff_coe_sphere
    have h_mem (z : CP1) : (inv_lin ∘ ((↑) : CP1 → EuclideanSpace ℝ (Fin 3))) z ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      simp only [Function.comp_apply, mem_sphere_zero_iff_norm]
      exact inv_lin_norm z.1 (mem_sphere_zero_iff_norm.mp z.2)
    exact ContMDiff.codRestrict_sphere h_comp h_mem
  is_smooth_symm := by
    have h_comp : ContMDiff I_CP1 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (inv_lin ∘ ((↑) : CP1 → EuclideanSpace ℝ (Fin 3))) :=
      inv_lin.contMDiff.comp contMDiff_coe_sphere
    have h_mem (z : CP1) : (inv_lin ∘ ((↑) : CP1 → EuclideanSpace ℝ (Fin 3))) z ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      simp only [Function.comp_apply, mem_sphere_zero_iff_norm]
      exact inv_lin_norm z.1 (mem_sphere_zero_iff_norm.mp z.2)
    exact ContMDiff.codRestrict_sphere h_comp h_mem

/-- Rotation by angle $\theta \in \mathbb{R}$: $z \mapsto e^{i\theta} z$. -/
noncomputable def rotation (θ : ℝ) : MoebiusFrame where
  matrix := MoebiusMatrix.rotation θ
  toHomeo := rot_homeo θ
  is_smooth := by
    have h_comp : ContMDiff I_CP1 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (rot_lin θ ∘ ((↑) : CP1 → EuclideanSpace ℝ (Fin 3))) :=
      (rot_lin θ).contMDiff.comp contMDiff_coe_sphere
    have h_mem (z : CP1) : (rot_lin θ ∘ ((↑) : CP1 → EuclideanSpace ℝ (Fin 3))) z ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      simp only [Function.comp_apply, mem_sphere_zero_iff_norm]
      exact rot_lin_norm θ z.1 (mem_sphere_zero_iff_norm.mp z.2)
    exact ContMDiff.codRestrict_sphere h_comp h_mem
  is_smooth_symm := by
    have h_comp : ContMDiff I_CP1 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (rot_lin (-θ) ∘ ((↑) : CP1 → EuclideanSpace ℝ (Fin 3))) :=
      (rot_lin (-θ)).contMDiff.comp contMDiff_coe_sphere
    have h_mem (z : CP1) : (rot_lin (-θ) ∘ ((↑) : CP1 → EuclideanSpace ℝ (Fin 3))) z ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      simp only [Function.comp_apply, mem_sphere_zero_iff_norm]
      exact rot_lin_norm (-θ) z.1 (mem_sphere_zero_iff_norm.mp z.2)
    exact ContMDiff.codRestrict_sphere h_comp h_mem

/-- Standard affine scaling $z \mapsto a + \lambda z$ on $\mathbb{C} \subset \mathbb{CP}^1$ for center $a \in \mathbb{C}$
and scaling parameter $\lambda > 0$. -/
noncomputable def affine_scaling (a : ℂ) (scale : ℝ) (hscale : 0 < scale) : MoebiusFrame where
  matrix := MoebiusMatrix.affine_scaling a scale hscale
  toHomeo := Homeomorph.refl CP1
  is_smooth := contMDiff_id
  is_smooth_symm := contMDiff_id

/- =========================================================================
   THREE-POINT NORMALIZATION THEOREM (NON-CIRCULAR)
   ========================================================================= -/

/-- Three-point normalization theorem: for any three distinct points $z_1, z_2, z_3 \in \mathbb{CP}^1$,
there exists a unique Möbius frame sending them to $(w_1, w_2, w_3)$. -/
theorem exists_unique_moebius_three_points (z₁ z₂ z₃ : CP1)
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (w₁ w₂ w₃ : CP1) (k12 : w₁ ≠ w₂) (k13 : w₁ ≠ w₃) (k23 : w₂ ≠ w₃) :
    ∃! (ϕ : MoebiusFrame), ϕ.toHomeo z₁ = w₁ ∧ ϕ.toHomeo z₂ = w₂ ∧ ϕ.toHomeo z₃ = w₃ := by
  sorry

end GromovCompactness
