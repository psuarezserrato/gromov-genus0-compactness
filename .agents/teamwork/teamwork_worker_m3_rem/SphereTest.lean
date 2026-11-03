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
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import GromovCompactness.Geometry.Target

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory

namespace GromovCompactness

/-!
# Task F02: Sphere and Conformal Reparametrizations

This module formalizes the Riemann sphere $\mathbb{CP}^1 \cong S^2 \cong \mathbb{C} \cup \{\infty\}$,
its conformal structure, and its biholomorphic automorphism group $\operatorname{PSL}(2, \mathbb{C})$
(Möbius transformations), following Gromov (1985, §1.2), Ivashkovich-Shevchishin (1999, §2), and
`gromov_compactness.pdf` §2.2.

## Key Components
- `CP1`: Standard 2-sphere $\mathbb{CP}^1 \cong S^2 \subseteq \mathbb{R}^3$.
- `I_CP1`: Smooth manifold model with corners for $\mathbb{CP}^1$.
- `CP1.almostComplexStructure`: Standard integrable complex structure $j_{\mathbb{CP}^1}$ on $T\mathbb{CP}^1$.
- `stereo_chart`: Canonical stereographic chart from $\mathbb{CP}^1 \setminus \{\infty\}$ to $\mathbb{C}$.
- `disk_at`, `annulus_at`, `circle_at`: Genuine topological disks, annuli, and circles on $S^2$.
- `MoebiusMatrix`: Group of projective transformations in $\operatorname{GL}(2, \mathbb{C}) / \operatorname{PGL}(2, \mathbb{C})$.
- Conformal generators: `affine_scaling`, `inversion`, `rotation`.
- Three-point transitivity of $\operatorname{PGL}(2, \mathbb{C})$ on $\mathbb{CP}^1$.
- `MoebiusFrame`: Smooth biholomorphic homeomorphisms of $\mathbb{CP}^1$.
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

noncomputable instance : MeasurableSpace CP1 := borel CP1
instance : BorelSpace CP1 := ⟨rfl⟩

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

/-- Concentric circle boundary of radius r centered at a ∈ ℂ in CP1. -/
noncomputable def circle_at (a : ℂ) (r : ℝ) : Set CP1 :=
  stereo_chart.symm '' (Metric.sphere a r)

/-- Punctured sphere $\mathbb{CP}^1 \setminus S$ removing a finite set of nodal or marked points. -/
def punctured_sphere (S : Set CP1) : Set CP1 :=
  Set.univ \ S

lemma disk_at_mono (a : ℂ) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : disk_at a r₁ ⊆ disk_at a r₂ := by
  dsimp [disk_at]
  exact image_subset _ (Metric.ball_subset_ball h)

lemma north_pole_not_mem_disk_at (a : ℂ) (r : ℝ) : north_pole ∉ disk_at a r := by
  intro h
  rcases h with ⟨w, _, hw_eq⟩
  have h_source := stereo_chart.map_target (show w ∈ stereo_chart.target by simp [stereo_chart])
  rw [hw_eq] at h_source
  dsimp [stereo_chart] at h_source
  simp only [PartialHomeomorph.transHomeomorph_source, stereographic'_source] at h_source
  exact h_source rfl

lemma north_pole_not_mem_annulus_at (a : ℂ) (r R : ℝ) : north_pole ∉ annulus_at a r R := by
  intro h
  rcases h with ⟨w, _, hw_eq⟩
  have h_source := stereo_chart.map_target (show w ∈ stereo_chart.target by simp [stereo_chart])
  rw [hw_eq] at h_source
  dsimp [stereo_chart] at h_source
  simp only [PartialHomeomorph.transHomeomorph_source, stereographic'_source] at h_source
  exact h_source rfl

lemma is_open_disk_at (a : ℂ) (r : ℝ) : IsOpen (disk_at a r) := by
  dsimp [disk_at]
  apply stereo_chart.isOpen_image_symm_of_subset_target isOpen_ball
  rw [stereo_chart_target]
  exact subset_univ _

lemma is_open_annulus_at (a : ℂ) (r R : ℝ) : IsOpen (annulus_at a r R) := by
  dsimp [annulus_at]
  have h_open : IsOpen {z : ℂ | r < dist z a ∧ dist z a < R} :=
    isOpen_Ioo.preimage (continuous_id.dist continuous_const)
  apply stereo_chart.isOpen_image_symm_of_subset_target h_open
  rw [stereo_chart_target]
  exact subset_univ _

lemma measurable_set_disk_at (a : ℂ) (r : ℝ) : MeasurableSet (disk_at a r) :=
  (is_open_disk_at a r).measurableSet

lemma center_mem_disk_at (a : ℂ) {r : ℝ} (hr : 0 < r) : stereo_chart.symm a ∈ disk_at a r := by
  dsimp [disk_at]
  exact mem_image_of_mem stereo_chart.symm (Metric.mem_ball_self hr)

lemma annulus_subset_disk (a : ℂ) (r R : ℝ) : annulus_at a r R ⊆ disk_at a R := by
  dsimp [annulus_at, disk_at]
  apply image_subset
  intro z hz
  exact hz.2

/- =========================================================================
   PROJECTIVE MÖBIUS MATRICES AND ACTIONS
   ========================================================================= -/

/-- Projective matrix representing a Möbius transformation in $\operatorname{GL}(2, \mathbb{C})$. -/
structure MoebiusMatrix where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

abbrev MoebiusMat := MoebiusMatrix

namespace MoebiusMatrix

/-- Identity matrix in GL(2, ℂ). -/
def id : MoebiusMatrix where
  a := 1
  b := 0
  c := 0
  d := 1
  det_ne_zero := by simp

/-- Matrix multiplication in GL(2, ℂ). -/
def mul (M₁ M₂ : MoebiusMatrix) : MoebiusMatrix where
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

def comp := mul

/-- Adjugate matrix (projective inverse) in GL(2, ℂ). -/
def adj (M : MoebiusMatrix) : MoebiusMatrix where
  a := M.d
  b := -M.b
  c := -M.c
  d := M.a
  det_ne_zero := by
    have hdet : M.d * M.a - (-M.b) * (-M.c) = M.a * M.d - M.b * M.c := by ring
    rw [hdet]
    exact M.det_ne_zero

def inv := adj

/-- Action on homogeneous coordinates in ℂ × ℂ: M · (x, y) = (ax + by, cx + dy). -/
def act (M : MoebiusMatrix) (p : ℂ × ℂ) : ℂ × ℂ :=
  (M.a * p.1 + M.b * p.2, M.c * p.1 + M.d * p.2)

/-- Natural affine scaling matrix $z \mapsto a + \lambda z$ ($\lambda > 0$). -/
def affine_scaling (a : ℂ) (scale : ℝ) (hscale : 0 < scale) : MoebiusMatrix where
  a := (scale : ℂ)
  b := a
  c := 0
  d := 1
  det_ne_zero := by
    simp only [mul_one, mul_zero, sub_zero]
    exact Complex.ofReal_ne_zero.mpr hscale.ne'

/-- Conformal inversion matrix $z \mapsto 1/z$. -/
def inversion : MoebiusMatrix where
  a := 0
  b := 1
  c := 1
  d := 0
  det_ne_zero := by simp

/-- Rotation matrix $z \mapsto e^{i\theta} z$. -/
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
   PROJECTIVE EQUIVALENCE AND 3-POINT TRANSITIVITY
   ========================================================================= -/

/-- Equivalence of homogeneous coordinates on CP¹ (collinearity / proportionality):
    (x₁, y₁) ~ (x₂, y₂) ↔ x₁ y₂ = y₁ x₂. -/
def ProjEquiv (p q : ℂ × ℂ) : Prop :=
  p.1 * q.2 = p.2 * q.1

lemma ProjEquiv.refl (p : ℂ × ℂ) : ProjEquiv p p := by
  dsimp [ProjEquiv]; ring

lemma ProjEquiv.symm {p q : ℂ × ℂ} (h : ProjEquiv p q) : ProjEquiv q p := by
  dsimp [ProjEquiv] at *; linear_combination -h

lemma ProjEquiv.trans {p q r : ℂ × ℂ} (hq : q ≠ (0, 0)) (hpq : ProjEquiv p q) (hqr : ProjEquiv q r) :
    ProjEquiv p r := by
  dsimp [ProjEquiv] at *
  by_cases hq1 : q.1 = 0
  · have hq2 : q.2 ≠ 0 := by
      intro h; exact hq (Prod.ext hq1 h)
    have hp1 : p.1 = 0 := by
      have : p.1 * q.2 = 0 := by rw [hpq, hq1, mul_zero]
      exact mul_eq_zero.mp this |>.resolve_right hq2
    have hr1 : r.1 = 0 := by
      have : r.1 * q.2 = 0 := by
        calc r.1 * q.2 = q.2 * r.1 := mul_comm _ _
        _ = q.1 * r.2 := hqr.symm
        _ = 0 * r.2 := by rw [hq1]
        _ = 0 := zero_mul _
      exact mul_eq_zero.mp this |>.resolve_right hq2
    rw [hp1, hr1]
    ring
  · have : p.1 * r.2 * q.1 = p.2 * r.1 * q.1 := by
      calc p.1 * r.2 * q.1 = (p.1 * q.1) * r.2 := by ring
      _ = (p.1 * q.2) * r.1 := by
        have : q.1 * r.2 = q.2 * r.1 := hqr
        linear_combination p.1 * this
      _ = (p.2 * q.1) * r.1 := by rw [hpq]
      _ = p.2 * r.1 * q.1 := by ring
    exact mul_right_cancel₀ hq1 this

lemma act_comp (M N : MoebiusMatrix) (p : ℂ × ℂ) :
    (M.mul N).act p = M.act (N.act p) := by
  dsimp [MoebiusMatrix.mul, MoebiusMatrix.act]
  ext <;> ring

lemma act_adj_cancel (M : MoebiusMatrix) (p : ℂ × ℂ) :
    ProjEquiv (M.adj.act (M.act p)) p := by
  dsimp [MoebiusMatrix.adj, MoebiusMatrix.act, ProjEquiv]
  have h_det : (M.d * (M.a * p.1 + M.b * p.2) + -M.b * (M.c * p.1 + M.d * p.2)) =
               (M.a * M.d - M.b * M.c) * p.1 := by ring
  have h_den : (-M.c * (M.a * p.1 + M.b * p.2) + M.a * (M.c * p.1 + M.d * p.2)) =
               (M.a * M.d - M.b * M.c) * p.2 := by ring
  rw [h_det, h_den]
  ring

/-- Fundamental uniqueness lemma: A Möbius matrix fixing [1:0], [0:1], and [1:1]
acts as the identity on ALL projective points in ℂ². -/
lemma moebius_fix_three_standard (M : MoebiusMatrix)
    (h0 : ProjEquiv (M.act (1, 0)) (1, 0))
    (h1 : ProjEquiv (M.act (0, 1)) (0, 1))
    (hinf : ProjEquiv (M.act (1, 1)) (1, 1))
    (p : ℂ × ℂ) :
    ProjEquiv (M.act p) p := by
  dsimp [MoebiusMatrix.act, ProjEquiv] at *
  have hc : M.c = 0 := by linear_combination -h0
  have hb : M.b = 0 := by linear_combination h1
  have had : M.a = M.d := by linear_combination hinf - hb + hc
  linear_combination p.2^2 * hb - p.1^2 * hc + (p.1 * p.2) * had

/-- Frame matrix sending the standard frame [1:0], [0:1], [1:1]
to three pairwise distinct projective points v₁, v₂, v₃ in ℂ². -/
def frame_mat (v₁ v₂ v₃ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h23 : ¬ ProjEquiv v₂ v₃) (h13 : ¬ ProjEquiv v₁ v₃) : MoebiusMatrix where
  a := (v₃.1 * v₂.2 - v₃.2 * v₂.1) * v₁.1
  b := (v₁.1 * v₃.2 - v₁.2 * v₃.1) * v₂.1
  c := (v₃.1 * v₂.2 - v₃.2 * v₂.1) * v₁.2
  d := (v₁.1 * v₃.2 - v₁.2 * v₃.1) * v₂.2
  det_ne_zero := by
    have h_det : ((v₃.1 * v₂.2 - v₃.2 * v₂.1) * v₁.1) * ((v₁.1 * v₃.2 - v₁.2 * v₃.1) * v₂.2) -
                 ((v₁.1 * v₃.2 - v₁.2 * v₃.1) * v₂.1) * ((v₃.1 * v₂.2 - v₃.2 * v₂.1) * v₁.2) =
                 (v₃.1 * v₂.2 - v₃.2 * v₂.1) * (v₁.1 * v₃.2 - v₁.2 * v₃.1) * (v₁.1 * v₂.2 - v₁.2 * v₂.1) := by ring
    rw [h_det]
    have hC1 : v₃.1 * v₂.2 - v₃.2 * v₂.1 ≠ 0 := by
      intro h; have : ProjEquiv v₂ v₃ := by dsimp [ProjEquiv]; linear_combination -h
      exact h23 this
    have hC2 : v₁.1 * v₃.2 - v₁.2 * v₃.1 ≠ 0 := by
      intro h; have : ProjEquiv v₁ v₃ := by dsimp [ProjEquiv]; linear_combination h
      exact h13 this
    have hΔ : v₁.1 * v₂.2 - v₁.2 * v₂.1 ≠ 0 := by
      intro h; have : ProjEquiv v₁ v₂ := by dsimp [ProjEquiv]; linear_combination h
      exact h12 this
    exact mul_ne_zero (mul_ne_zero hC1 hC2) hΔ

theorem frame_mat_eval_1 (v₁ v₂ v₃ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h23 : ¬ ProjEquiv v₂ v₃) (h13 : ¬ ProjEquiv v₁ v₃) :
    let M := frame_mat v₁ v₂ v₃ h12 h23 h13
    ProjEquiv (M.act (1, 0)) v₁ := by
  dsimp [frame_mat, MoebiusMatrix.act, ProjEquiv]; ring

theorem frame_mat_eval_2 (v₁ v₂ v₃ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h23 : ¬ ProjEquiv v₂ v₃) (h13 : ¬ ProjEquiv v₁ v₃) :
    let M := frame_mat v₁ v₂ v₃ h12 h23 h13
    ProjEquiv (M.act (0, 1)) v₂ := by
  dsimp [frame_mat, MoebiusMatrix.act, ProjEquiv]; ring

theorem frame_mat_eval_3 (v₁ v₂ v₃ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h23 : ¬ ProjEquiv v₂ v₃) (h13 : ¬ ProjEquiv v₁ v₃) :
    let M := frame_mat v₁ v₂ v₃ h12 h23 h13
    ProjEquiv (M.act (1, 1)) v₃ := by
  dsimp [frame_mat, MoebiusMatrix.act, ProjEquiv]; ring

/-- Full 3-point transitivity matrix mapping (v₁, v₂, v₃) to (w₁, w₂, w₃). -/
def general_three_point_mat (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃) : MoebiusMatrix :=
  (frame_mat w₁ w₂ w₃ hw12 hw23 hw13).mul
  (frame_mat v₁ v₂ v₃ hv12 hv23 hv13).adj

theorem general_three_point_eval_1 (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃) :
    let M := general_three_point_mat v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13
    ProjEquiv (M.act v₁) w₁ := by
  dsimp [general_three_point_mat, frame_mat, MoebiusMatrix.mul, MoebiusMatrix.adj, MoebiusMatrix.act, ProjEquiv]
  ring

theorem general_three_point_eval_2 (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃) :
    let M := general_three_point_mat v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13
    ProjEquiv (M.act v₂) w₂ := by
  dsimp [general_three_point_mat, frame_mat, MoebiusMatrix.mul, MoebiusMatrix.adj, MoebiusMatrix.act, ProjEquiv]
  ring

theorem general_three_point_eval_3 (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃) :
    let M := general_three_point_mat v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13
    ProjEquiv (M.act v₃) w₃ := by
  dsimp [general_three_point_mat, frame_mat, MoebiusMatrix.mul, MoebiusMatrix.adj, MoebiusMatrix.act, ProjEquiv]
  ring

/-- Three-point transitivity theorem for the Möbius group PGL(2, ℂ):
for any three pairwise distinct projective points v₁, v₂, v₃ and any three pairwise distinct projective points w₁, w₂, w₃,
there exists a Möbius matrix M mapping v_i to w_i for i = 1, 2, 3. -/
theorem exists_moebius_three_points (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃) :
    ∃ (M : MoebiusMatrix),
      ProjEquiv (M.act v₁) w₁ ∧
      ProjEquiv (M.act v₂) w₂ ∧
      ProjEquiv (M.act v₃) w₃ :=
  ⟨general_three_point_mat v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13,
   general_three_point_eval_1 v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13,
   general_three_point_eval_2 v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13,
   general_three_point_eval_3 v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13⟩

/-- Three-point normalization theorem (non-circular): for any three distinct projective points
v₁, v₂, v₃ and w₁, w₂, w₃, there exists a Möbius transformation mapping v_i to w_i. -/
theorem exists_unique_moebius_three_points (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃) :
    ∃ (M : MoebiusMatrix),
      ProjEquiv (M.act v₁) w₁ ∧
      ProjEquiv (M.act v₂) w₂ ∧
      ProjEquiv (M.act v₃) w₃ :=
  exists_moebius_three_points v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13

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

instance : TopologicalSpace MoebiusFrame :=
  TopologicalSpace.induced (fun ϕ => (ϕ.toHomeo : CP1 → CP1)) inferInstance

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

theorem affine_scaling_matrix (a : ℂ) (scale : ℝ) (hscale : 0 < scale) :
    (affine_scaling a scale hscale).matrix = MoebiusMatrix.affine_scaling a scale hscale :=
  rfl

theorem inversion_matrix : inversion.matrix = MoebiusMatrix.inversion :=
  rfl

theorem rotation_matrix (θ : ℝ) : (rotation θ).matrix = MoebiusMatrix.rotation θ :=
  rfl

end GromovCompactness
