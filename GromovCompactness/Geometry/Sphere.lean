import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import GromovCompactness.Geometry.Target

open scoped Manifold ContDiff Topology RealInnerProductSpace
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
noncomputable abbrev I_CP1 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) := 𝓡 2

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
  j_smooth := by
    intro _
    exact contDiffOn_const

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
noncomputable def stereo_chart : OpenPartialHomeomorph CP1 ℂ :=
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
  exact Set.image_mono (Metric.ball_subset_ball h)

lemma north_pole_not_mem_disk_at (a : ℂ) (r : ℝ) : north_pole ∉ disk_at a r := by
  intro h
  rcases h with ⟨w, _, hw_eq⟩
  have h_source := stereo_chart.map_target (show w ∈ stereo_chart.target by simp [stereo_chart])
  rw [hw_eq] at h_source
  dsimp [stereo_chart] at h_source
  simp only [OpenPartialHomeomorph.transHomeomorph_source, stereographic'_source] at h_source
  exact h_source rfl

lemma north_pole_not_mem_annulus_at (a : ℂ) (r R : ℝ) : north_pole ∉ annulus_at a r R := by
  intro h
  rcases h with ⟨w, _, hw_eq⟩
  have h_source := stereo_chart.map_target (show w ∈ stereo_chart.target by simp [stereo_chart])
  rw [hw_eq] at h_source
  dsimp [stereo_chart] at h_source
  simp only [OpenPartialHomeomorph.transHomeomorph_source, stereographic'_source] at h_source
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
  apply Set.image_mono
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

/-- Equivalence of Moebius matrices in PGL(2, ℂ): they act identically on all projective points. -/
def PglEquiv (M N : MoebiusMatrix) : Prop :=
  ∀ p : ℂ × ℂ, ProjEquiv (M.act p) (N.act p)

lemma PglEquiv.refl (M : MoebiusMatrix) : PglEquiv M M :=
  fun p => ProjEquiv.refl (M.act p)

lemma PglEquiv.symm {M N : MoebiusMatrix} (h : PglEquiv M N) : PglEquiv N M :=
  fun p => ProjEquiv.symm (h p)

lemma projEquiv_zero_left (q : ℂ × ℂ) : ProjEquiv (0, 0) q := by
  dsimp [ProjEquiv]; ring

lemma ne_zero_of_not_projEquiv {p q : ℂ × ℂ} (h : ¬ ProjEquiv p q) : p ≠ (0, 0) := by
  intro hp; subst hp; exact h (projEquiv_zero_left q)

lemma adj_mul_act_standard_1 (A B : MoebiusMatrix) (w : ℂ × ℂ) (hw : w ≠ (0, 0))
    (hA : ProjEquiv (A.act (1, 0)) w) (hB : ProjEquiv (B.act (1, 0)) w) :
    ProjEquiv ((B.adj.mul A).act (1, 0)) (1, 0) := by
  have hAB : ProjEquiv (A.act (1, 0)) (B.act (1, 0)) :=
    ProjEquiv.trans hw hA (ProjEquiv.symm hB)
  dsimp [MoebiusMatrix.mul, MoebiusMatrix.adj, MoebiusMatrix.act, ProjEquiv] at *
  linear_combination hAB

lemma adj_mul_act_standard_2 (A B : MoebiusMatrix) (w : ℂ × ℂ) (hw : w ≠ (0, 0))
    (hA : ProjEquiv (A.act (0, 1)) w) (hB : ProjEquiv (B.act (0, 1)) w) :
    ProjEquiv ((B.adj.mul A).act (0, 1)) (0, 1) := by
  have hAB : ProjEquiv (A.act (0, 1)) (B.act (0, 1)) :=
    ProjEquiv.trans hw hA (ProjEquiv.symm hB)
  dsimp [MoebiusMatrix.mul, MoebiusMatrix.adj, MoebiusMatrix.act, ProjEquiv] at *
  linear_combination hAB

lemma adj_mul_act_standard_3 (A B : MoebiusMatrix) (w : ℂ × ℂ) (hw : w ≠ (0, 0))
    (hA : ProjEquiv (A.act (1, 1)) w) (hB : ProjEquiv (B.act (1, 1)) w) :
    ProjEquiv ((B.adj.mul A).act (1, 1)) (1, 1) := by
  have hAB : ProjEquiv (A.act (1, 1)) (B.act (1, 1)) :=
    ProjEquiv.trans hw hA (ProjEquiv.symm hB)
  dsimp [MoebiusMatrix.mul, MoebiusMatrix.adj, MoebiusMatrix.act, ProjEquiv] at *
  linear_combination hAB

lemma projEquiv_adj_mul_iff (A B : MoebiusMatrix) (q : ℂ × ℂ) :
    ProjEquiv ((B.adj.mul A).act q) q ↔ ProjEquiv (A.act q) (B.act q) := by
  dsimp [MoebiusMatrix.mul, MoebiusMatrix.adj, MoebiusMatrix.act, ProjEquiv]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

lemma act_mul_frame_w1 (M : MoebiusMatrix) (v₁ v₂ v₃ w₁ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h23 : ¬ ProjEquiv v₂ v₃) (h13 : ¬ ProjEquiv v₁ v₃)
    (hM : ProjEquiv (M.act v₁) w₁) :
    let F := frame_mat v₁ v₂ v₃ h12 h23 h13
    ProjEquiv ((M.mul F).act (1, 0)) w₁ := by
  dsimp [frame_mat, MoebiusMatrix.mul, MoebiusMatrix.act, ProjEquiv] at *
  linear_combination (v₃.1 * v₂.2 - v₃.2 * v₂.1) * hM

lemma act_mul_frame_w2 (M : MoebiusMatrix) (v₁ v₂ v₃ w₂ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h23 : ¬ ProjEquiv v₂ v₃) (h13 : ¬ ProjEquiv v₁ v₃)
    (hM : ProjEquiv (M.act v₂) w₂) :
    let F := frame_mat v₁ v₂ v₃ h12 h23 h13
    ProjEquiv ((M.mul F).act (0, 1)) w₂ := by
  dsimp [frame_mat, MoebiusMatrix.mul, MoebiusMatrix.act, ProjEquiv] at *
  linear_combination (v₁.1 * v₃.2 - v₁.2 * v₃.1) * hM

lemma act_mul_frame_w3 (M : MoebiusMatrix) (v₁ v₂ v₃ w₃ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h23 : ¬ ProjEquiv v₂ v₃) (h13 : ¬ ProjEquiv v₁ v₃)
    (hM : ProjEquiv (M.act v₃) w₃) :
    let F := frame_mat v₁ v₂ v₃ h12 h23 h13
    ProjEquiv ((M.mul F).act (1, 1)) w₃ := by
  dsimp [frame_mat, MoebiusMatrix.mul, MoebiusMatrix.act, ProjEquiv] at *
  linear_combination (v₁.1 * v₂.2 - v₁.2 * v₂.1) * hM

lemma projEquiv_of_frame_action (M₁ M₂ F : MoebiusMatrix) (p : ℂ × ℂ)
    (hMF : ProjEquiv ((M₁.mul F).act (F.adj.act p)) ((M₂.mul F).act (F.adj.act p))) :
    ProjEquiv (M₁.act p) (M₂.act p) := by
  have h_id : ((M₁.mul F).act (F.adj.act p)).1 * ((M₂.mul F).act (F.adj.act p)).2 -
              ((M₁.mul F).act (F.adj.act p)).2 * ((M₂.mul F).act (F.adj.act p)).1 =
              (F.a * F.d - F.b * F.c) * (F.a * F.d - F.b * F.c) *
              ((M₁.act p).1 * (M₂.act p).2 - (M₁.act p).2 * (M₂.act p).1) := by
    dsimp [MoebiusMatrix.mul, MoebiusMatrix.adj, MoebiusMatrix.act]
    ring
  have h_mf : ((M₁.mul F).act (F.adj.act p)).1 * ((M₂.mul F).act (F.adj.act p)).2 -
              ((M₁.mul F).act (F.adj.act p)).2 * ((M₂.mul F).act (F.adj.act p)).1 = 0 := by
    dsimp [ProjEquiv] at hMF
    linear_combination hMF
  have h_eq : (F.a * F.d - F.b * F.c) * (F.a * F.d - F.b * F.c) *
              ((M₁.act p).1 * (M₂.act p).2 - (M₁.act p).2 * (M₂.act p).1) = 0 := by
    rw [← h_id, h_mf]
  have h_sq_ne : (F.a * F.d - F.b * F.c) * (F.a * F.d - F.b * F.c) ≠ 0 := by
    have hd : F.a * F.d - F.b * F.c ≠ 0 := F.det_ne_zero
    exact mul_ne_zero hd hd
  have h_sub : (M₁.act p).1 * (M₂.act p).2 - (M₁.act p).2 * (M₂.act p).1 = 0 := by
    cases mul_eq_zero.mp h_eq with
    | inl hsq => exact False.elim (h_sq_ne hsq)
    | inr hsub => exact hsub
  dsimp [ProjEquiv]
  exact sub_eq_zero.mp h_sub

/-- Three-point uniqueness theorem in PGL(2, ℂ): any two Möbius matrices mapping
the same three distinct projective points (v₁, v₂, v₃) to (w₁, w₂, w₃) are
projectively equivalent on all points in CP¹. -/
theorem moebius_three_points_unique (M₁ M₂ : MoebiusMatrix)
    (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃)
    (hM1_1 : ProjEquiv (M₁.act v₁) w₁)
    (hM1_2 : ProjEquiv (M₁.act v₂) w₂)
    (hM1_3 : ProjEquiv (M₁.act v₃) w₃)
    (hM2_1 : ProjEquiv (M₂.act v₁) w₁)
    (hM2_2 : ProjEquiv (M₂.act v₂) w₂)
    (hM2_3 : ProjEquiv (M₂.act v₃) w₃) :
    PglEquiv M₁ M₂ := by
  let F := frame_mat v₁ v₂ v₃ hv12 hv23 hv13
  let A := M₁.mul F
  let B := M₂.mul F
  let T := B.adj.mul A
  have hw1 : w₁ ≠ (0, 0) := ne_zero_of_not_projEquiv hw12
  have hw2 : w₂ ≠ (0, 0) := ne_zero_of_not_projEquiv hw23
  have hw3 : w₃ ≠ (0, 0) := ne_zero_of_not_projEquiv (fun h => hw13 (ProjEquiv.symm h))
  have hAw1 : ProjEquiv (A.act (1, 0)) w₁ := act_mul_frame_w1 M₁ v₁ v₂ v₃ w₁ hv12 hv23 hv13 hM1_1
  have hBw1 : ProjEquiv (B.act (1, 0)) w₁ := act_mul_frame_w1 M₂ v₁ v₂ v₃ w₁ hv12 hv23 hv13 hM2_1
  have hT0 : ProjEquiv (T.act (1, 0)) (1, 0) := adj_mul_act_standard_1 A B w₁ hw1 hAw1 hBw1
  have hAw2 : ProjEquiv (A.act (0, 1)) w₂ := act_mul_frame_w2 M₁ v₁ v₂ v₃ w₂ hv12 hv23 hv13 hM1_2
  have hBw2 : ProjEquiv (B.act (0, 1)) w₂ := act_mul_frame_w2 M₂ v₁ v₂ v₃ w₂ hv12 hv23 hv13 hM2_2
  have hT1 : ProjEquiv (T.act (0, 1)) (0, 1) := adj_mul_act_standard_2 A B w₂ hw2 hAw2 hBw2
  have hAw3 : ProjEquiv (A.act (1, 1)) w₃ := act_mul_frame_w3 M₁ v₁ v₂ v₃ w₃ hv12 hv23 hv13 hM1_3
  have hBw3 : ProjEquiv (B.act (1, 1)) w₃ := act_mul_frame_w3 M₂ v₁ v₂ v₃ w₃ hv12 hv23 hv13 hM2_3
  have hTinf : ProjEquiv (T.act (1, 1)) (1, 1) := adj_mul_act_standard_3 A B w₃ hw3 hAw3 hBw3
  have hT_fix : ∀ q, ProjEquiv (T.act q) q := moebius_fix_three_standard T hT0 hT1 hTinf
  intro p
  apply projEquiv_of_frame_action M₁ M₂ F p
  have hTq := hT_fix (F.adj.act p)
  exact (projEquiv_adj_mul_iff A B (F.adj.act p)).mp hTq

/-- Three-point normalization theorem: for any three distinct projective points
v₁, v₂, v₃ and w₁, w₂, w₃, there exists a unique (up to PGL equivalence) Möbius transformation
mapping v_i to w_i. -/
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
        PglEquiv M M') := by
  obtain ⟨M, h1, h2, h3⟩ := exists_moebius_three_points v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13
  refine ⟨M, ⟨h1, h2, h3⟩, fun M' h1' h2' h3' => ?_⟩
  exact moebius_three_points_unique M M' v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13 h1 h2 h3 h1' h2' h3'

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
   AUTHENTIC SPHERICAL DILATION HOMEOMORPHISM ON S² (CP1)
   ========================================================================= -/

/-- The denominator function $D_\lambda(t) = (1+\lambda^2) + (1-\lambda^2)t$. -/
def D_val (l : ℝ) (t : ℝ) : ℝ :=
  (1 + l^2) + (1 - l^2) * t

/-- The denominator $D_\lambda(t)$ is strictly positive for all $t \in [-1, 1]$ whenever $\lambda > 0$. -/
theorem D_val_pos (l : ℝ) (hl : 0 < l) (t : ℝ) (ht1 : -1 ≤ t) (ht2 : t ≤ 1) :
    0 < D_val l t := by
  dsimp [D_val]
  have h_dec : (1 + l^2) + (1 - l^2) * t = (1 - t) * l^2 + (1 + t) := by ring
  rw [h_dec]
  by_cases h : t = -1
  · subst h
    have : (1 - -1 : ℝ) * l^2 + (1 + -1) = 2 * l^2 := by ring
    rw [this]
    positivity
  · have ht_lt : -1 < t := lt_of_le_of_ne ht1 (Ne.symm h)
    have h1 : 0 < 1 + t := by linarith
    have h2 : 0 ≤ (1 - t) * l^2 := by
      have : 0 ≤ 1 - t := by linarith
      positivity
    linarith

/-- The third coordinate of any point on the unit sphere satisfies $-1 \le z_2 \le 1$. -/
theorem cp1_coord_two_bounds (z : CP1) : -1 ≤ z.1 2 ∧ z.1 2 ≤ 1 := by
  have hz : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  rw [EuclideanSpace.norm_eq] at hz
  have h_pos : 0 ≤ ‖z.1 0‖ ^ 2 + ‖z.1 1‖ ^ 2 + ‖z.1 2‖ ^ 2 := by positivity
  have h_sq := congr_arg (fun x => x^2) hz
  simp only [Fin.sum_univ_three] at h_sq
  rw [Real.sq_sqrt h_pos] at h_sq
  have h_norm_sq (x : ℝ) : ‖x‖ ^ 2 = x ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
  rw [h_norm_sq, h_norm_sq, h_norm_sq] at h_sq
  norm_num at h_sq
  have h_le : (z.1 2)^2 ≤ 1 := by
    have : 0 ≤ (z.1 0)^2 := sq_nonneg _
    have : 0 ≤ (z.1 1)^2 := sq_nonneg _
    linarith
  have h_abs : |z.1 2| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    linarith
  exact abs_le.mp h_abs

/-- The denominator $D_\lambda(z_2)$ is strictly positive for all points $z \in \mathrm{CP1}$. -/
theorem cp1_D_val_pos (l : ℝ) (hl : 0 < l) (z : CP1) : 0 < D_val l (z.1 2) :=
  D_val_pos l hl (z.1 2) (cp1_coord_two_bounds z).1 (cp1_coord_two_bounds z).2

/-- The denominator $D_\lambda(z_2)$ is non-zero for all points $z \in \mathrm{CP1}$. -/
theorem cp1_D_val_ne_zero (l : ℝ) (hl : 0 < l) (z : CP1) : D_val l (z.1 2) ≠ 0 :=
  ne_of_gt (cp1_D_val_pos l hl z)

/-- Coordinate projections on CP1 are continuous. -/
lemma continuous_cp1_coord (i : Fin 3) : Continuous (fun (z : CP1) => z.1 i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp continuous_subtype_val

/-- Dilation vector mapping on $\mathbb{R}^3$. -/
noncomputable def dil_fun (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  let D := D_val l (v 2)
  !₂[(2 * l * v 0) / D, (2 * l * v 1) / D, ((1 - l^2) + (1 + l^2) * v 2) / D]

theorem dil_fun_0 (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    (dil_fun l v) 0 = (2 * l * v 0) / D_val l (v 2) := rfl

theorem dil_fun_1 (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    (dil_fun l v) 1 = (2 * l * v 1) / D_val l (v 2) := rfl

theorem dil_fun_2 (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    (dil_fun l v) 2 = ((1 - l^2) + (1 + l^2) * v 2) / D_val l (v 2) := rfl

/-- Denominator product cancellation identity: $D_l(t) \cdot D_{1/l}(t') = 4$. -/
theorem dil_denom_mul (l : ℝ) (hl : l ≠ 0) (t : ℝ) (hD : D_val l t ≠ 0) :
    D_val l t * D_val l⁻¹ (((1 - l^2) + (1 + l^2) * t) / D_val l t) = 4 := by
  dsimp [D_val] at hD ⊢
  have hl2 : l^2 ≠ 0 := pow_ne_zero 2 hl
  have h_inv : l⁻¹ ^ 2 = (l^2)⁻¹ := by rw [inv_pow]
  rw [h_inv]
  field_simp
  ring

theorem dil_fun_inv_apply_0 (l : ℝ) (hl : l ≠ 0) (v : EuclideanSpace ℝ (Fin 3)) (hD : D_val l (v 2) ≠ 0) :
    (dil_fun l⁻¹ (dil_fun l v)) 0 = v 0 := by
  rw [dil_fun_0, dil_fun_0, dil_fun_2]
  have h_denom := dil_denom_mul l hl (v 2) hD
  have h_denom' : D_val l⁻¹ (((1 - l^2) + (1 + l^2) * v 2) / D_val l (v 2)) = 4 / D_val l (v 2) := by
    rw [← h_denom]
    exact (mul_div_cancel_left₀ (D_val l⁻¹ (((1 - l^2) + (1 + l^2) * v 2) / D_val l (v 2))) hD).symm
  rw [h_denom']
  have h_ll : l⁻¹ * l = 1 := inv_mul_cancel₀ hl
  have : 2 * l⁻¹ * (2 * l * v 0 / D_val l (v 2)) = (4 * v 0) / D_val l (v 2) := by
    calc 2 * l⁻¹ * (2 * l * v 0 / D_val l (v 2))
      _ = (4 * (l⁻¹ * l) * v 0) / D_val l (v 2) := by ring
      _ = (4 * 1 * v 0) / D_val l (v 2) := by rw [h_ll]
      _ = (4 * v 0) / D_val l (v 2) := by ring
  rw [this]
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  rw [div_div_div_comm, div_self hD, div_one]
  exact mul_div_cancel_left₀ (v 0) h4

theorem dil_fun_inv_apply_1 (l : ℝ) (hl : l ≠ 0) (v : EuclideanSpace ℝ (Fin 3)) (hD : D_val l (v 2) ≠ 0) :
    (dil_fun l⁻¹ (dil_fun l v)) 1 = v 1 := by
  rw [dil_fun_1, dil_fun_1, dil_fun_2]
  have h_denom := dil_denom_mul l hl (v 2) hD
  have h_denom' : D_val l⁻¹ (((1 - l^2) + (1 + l^2) * v 2) / D_val l (v 2)) = 4 / D_val l (v 2) := by
    rw [← h_denom]
    exact (mul_div_cancel_left₀ (D_val l⁻¹ (((1 - l^2) + (1 + l^2) * v 2) / D_val l (v 2))) hD).symm
  rw [h_denom']
  have h_ll : l⁻¹ * l = 1 := inv_mul_cancel₀ hl
  have : 2 * l⁻¹ * (2 * l * v 1 / D_val l (v 2)) = (4 * v 1) / D_val l (v 2) := by
    calc 2 * l⁻¹ * (2 * l * v 1 / D_val l (v 2))
      _ = (4 * (l⁻¹ * l) * v 1) / D_val l (v 2) := by ring
      _ = (4 * 1 * v 1) / D_val l (v 2) := by rw [h_ll]
      _ = (4 * v 1) / D_val l (v 2) := by ring
  rw [this]
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  rw [div_div_div_comm, div_self hD, div_one]
  exact mul_div_cancel_left₀ (v 1) h4

theorem dil_fun_inv_apply_2 (l : ℝ) (hl : l ≠ 0) (v : EuclideanSpace ℝ (Fin 3)) (hD : D_val l (v 2) ≠ 0) :
    (dil_fun l⁻¹ (dil_fun l v)) 2 = v 2 := by
  rw [dil_fun_2, dil_fun_2]
  have h_denom := dil_denom_mul l hl (v 2) hD
  have h_denom' : D_val l⁻¹ (((1 - l^2) + (1 + l^2) * v 2) / D_val l (v 2)) = 4 / D_val l (v 2) := by
    rw [← h_denom]
    exact (mul_div_cancel_left₀ (D_val l⁻¹ (((1 - l^2) + (1 + l^2) * v 2) / D_val l (v 2))) hD).symm
  rw [h_denom']
  have hl2 : l^2 ≠ 0 := pow_ne_zero 2 hl
  have h_inv : l⁻¹ ^ 2 = (l^2)⁻¹ := by rw [inv_pow]
  have h_num : (1 - l⁻¹ ^ 2) + (1 + l⁻¹ ^ 2) * (((1 - l^2) + (1 + l^2) * v 2) / D_val l (v 2)) =
      (4 * v 2) / D_val l (v 2) := by
    rw [h_inv]
    dsimp [D_val] at hD ⊢
    field_simp
    ring
  rw [h_num]
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  rw [div_div_div_comm, div_self hD, div_one]
  exact mul_div_cancel_left₀ (v 2) h4

/-- The inverse mapping of $f_\lambda$ on $\mathbb{R}^3$ is $f_{1/\lambda}$. -/
theorem dil_fun_inv_apply (l : ℝ) (hl : l ≠ 0) (v : EuclideanSpace ℝ (Fin 3)) (hD : D_val l (v 2) ≠ 0) :
    dil_fun l⁻¹ (dil_fun l v) = v := by
  ext i; fin_cases i
  · exact dil_fun_inv_apply_0 l hl v hD
  · exact dil_fun_inv_apply_1 l hl v hD
  · exact dil_fun_inv_apply_2 l hl v hD

/-- Sum of squares preservation on the unit sphere. -/
theorem dil_fun_norm_sq (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) (hv : (v 0)^2 + (v 1)^2 + (v 2)^2 = 1)
    (hD : D_val l (v 2) ≠ 0) :
    (dil_fun l v 0)^2 + (dil_fun l v 1)^2 + (dil_fun l v 2)^2 = 1 := by
  rw [dil_fun_0, dil_fun_1, dil_fun_2]
  have h_num : (2 * l * v 0)^2 + (2 * l * v 1)^2 + ((1 - l^2) + (1 + l^2) * v 2)^2 =
      (D_val l (v 2))^2 := by
    dsimp [D_val]
    linear_combination 4 * l^2 * hv
  have h_div : ((2 * l * v 0) / D_val l (v 2))^2 + ((2 * l * v 1) / D_val l (v 2))^2 +
      (((1 - l^2) + (1 + l^2) * v 2) / D_val l (v 2))^2 =
      ((2 * l * v 0)^2 + (2 * l * v 1)^2 + ((1 - l^2) + (1 + l^2) * v 2)^2) / (D_val l (v 2))^2 := by
    ring
  rw [h_div, h_num]
  exact div_self (pow_ne_zero 2 hD)

/-- $f_\lambda$ maps the unit sphere to the unit sphere: $\|f_\lambda(v)\| = 1$. -/
theorem dil_fun_norm (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) (hv : ‖v‖ = 1)
    (hD : D_val l (v 2) ≠ 0) : ‖dil_fun l v‖ = 1 := by
  rw [EuclideanSpace.norm_eq] at hv ⊢
  have h_sum : (v 0)^2 + (v 1)^2 + (v 2)^2 = 1 := by
    have h_sq := congr_arg (fun x => x^2) hv
    simp only [Fin.sum_univ_three] at h_sq
    have h_pos : 0 ≤ ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 + ‖v 2‖ ^ 2 := by positivity
    rw [Real.sq_sqrt h_pos] at h_sq
    have h_norm_sq (x : ℝ) : ‖x‖ ^ 2 = x ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
    rw [h_norm_sq, h_norm_sq, h_norm_sq] at h_sq
    norm_num at h_sq
    exact h_sq
  have h_dil_sum := dil_fun_norm_sq l v h_sum hD
  simp only [Fin.sum_univ_three]
  have h_norm_sq (x : ℝ) : ‖x‖ ^ 2 = x ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
  rw [h_norm_sq, h_norm_sq, h_norm_sq]
  rw [h_dil_sum]
  exact Real.sqrt_one

/-- The mapping $z \mapsto f_\lambda(z)$ is continuous on $S^2 = \mathrm{CP1}$. -/
theorem continuous_dil_fun_on_cp1 (l : ℝ) (hl : 0 < l) :
    Continuous (fun (z : CP1) => dil_fun l z.1) := by
  dsimp [dil_fun]
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp ?_
  apply continuous_pi
  intro i
  fin_cases i
  · -- coordinate 0
    change Continuous (fun (z : CP1) => (2 * l * z.1 0) / D_val l (z.1 2))
    apply Continuous.div
    · exact continuous_const.mul (continuous_cp1_coord 0)
    · dsimp [D_val]
      exact continuous_const.add (continuous_const.mul (continuous_cp1_coord 2))
    · intro z
      exact cp1_D_val_ne_zero l hl z
  · -- coordinate 1
    change Continuous (fun (z : CP1) => (2 * l * z.1 1) / D_val l (z.1 2))
    apply Continuous.div
    · exact continuous_const.mul (continuous_cp1_coord 1)
    · dsimp [D_val]
      exact continuous_const.add (continuous_const.mul (continuous_cp1_coord 2))
    · intro z
      exact cp1_D_val_ne_zero l hl z
  · -- coordinate 2
    change Continuous (fun (z : CP1) => ((1 - l^2) + (1 + l^2) * z.1 2) / D_val l (z.1 2))
    apply Continuous.div
    · exact continuous_const.add (continuous_const.mul (continuous_cp1_coord 2))
    · dsimp [D_val]
      exact continuous_const.add (continuous_const.mul (continuous_cp1_coord 2))
    · intro z
      exact cp1_D_val_ne_zero l hl z

/-- Genuine spherical dilation homeomorphism of $\mathbb{CP}^1 \cong S^2$. -/
noncomputable def dil_homeo (l : ℝ) (hl : 0 < l) : CP1 ≃ₜ CP1 where
  toFun z := ⟨dil_fun l z.1, mem_sphere_zero_iff_norm.mpr (dil_fun_norm l z.1 (mem_sphere_zero_iff_norm.mp z.2) (cp1_D_val_ne_zero l hl z))⟩
  invFun z := ⟨dil_fun l⁻¹ z.1, mem_sphere_zero_iff_norm.mpr (dil_fun_norm l⁻¹ z.1 (mem_sphere_zero_iff_norm.mp z.2) (cp1_D_val_ne_zero l⁻¹ (inv_pos.mpr hl) z))⟩
  left_inv z := Subtype.ext (dil_fun_inv_apply l (ne_of_gt hl) z.1 (cp1_D_val_ne_zero l hl z))
  right_inv z := Subtype.ext (by
    have h_inv_inv : (l⁻¹)⁻¹ = l := inv_inv l
    have h_apply := dil_fun_inv_apply l⁻¹ (ne_of_gt (inv_pos.mpr hl)) z.1 (cp1_D_val_ne_zero l⁻¹ (inv_pos.mpr hl) z)
    rw [h_inv_inv] at h_apply
    exact h_apply)
  continuous_toFun := Continuous.subtype_mk (continuous_dil_fun_on_cp1 l hl) (fun z =>
    mem_sphere_zero_iff_norm.mpr (dil_fun_norm l z.1 (mem_sphere_zero_iff_norm.mp z.2) (cp1_D_val_ne_zero l hl z)))
  continuous_invFun := Continuous.subtype_mk (continuous_dil_fun_on_cp1 l⁻¹ (inv_pos.mpr hl)) (fun z =>
    mem_sphere_zero_iff_norm.mpr (dil_fun_norm l⁻¹ z.1 (mem_sphere_zero_iff_norm.mp z.2) (cp1_D_val_ne_zero l⁻¹ (inv_pos.mpr hl) z)))

/-- Dilation homeomorphism is strictly non-identity when $\lambda \ne 1$. -/
theorem dil_homeo_ne_id (l : ℝ) (hl : 0 < l) (hne : l ≠ 1) :
    dil_homeo l hl ≠ Homeomorph.refl CP1 := by
  intro h
  let p : CP1 := ⟨!₂[1, 0, 0], by
    simp only [mem_sphere_zero_iff_norm]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three]⟩
  have hp : dil_homeo l hl p = Homeomorph.refl CP1 p := by rw [h]
  have h_coord : (dil_homeo l hl p).1 2 = (Homeomorph.refl CP1 p).1 2 := by rw [hp]
  change (dil_fun l p.1) 2 = p.1 2 at h_coord
  rw [dil_fun_2] at h_coord
  have hp2 : p.1 2 = 0 := rfl
  rw [hp2] at h_coord
  dsimp [D_val] at h_coord
  have h_simp : (1 - l^2 + (1 + l^2) * 0) / (1 + l^2 + (1 - l^2) * 0) = (1 - l^2) / (1 + l^2) := by ring
  rw [h_simp] at h_coord
  have h_pos : 0 < 1 + l^2 := by positivity
  have h_zero : 1 - l^2 = 0 := div_eq_zero_iff.mp h_coord |>.resolve_right (ne_of_gt h_pos)
  have hl_sq : l^2 = 1 := by linarith
  have hl_one : l = 1 := by nlinarith
  exact hne hl_one

/-- Coordinate projections on EuclideanSpace are smooth ($C^\infty$). -/
lemma contDiffAt_euclidean_coord (i : Fin 3) (v : EuclideanSpace ℝ (Fin 3)) :
    ContDiffAt ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) => x i) v :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt

/-- $f_\lambda$ is smooth ($C^\infty$) at any point with non-zero denominator. -/
theorem contDiffAt_dil_fun (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) (hD : D_val l (v 2) ≠ 0) :
    ContDiffAt ℝ ∞ (dil_fun l) v := by
  let E := EuclideanSpace.equiv (Fin 3) ℝ
  have h_eq : dil_fun l = E.symm ∘ (E ∘ dil_fun l) := by
    ext x
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [h_eq]
  apply ContDiff.comp_contDiffAt v E.symm.contDiff
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · -- coordinate 0
    change ContDiffAt ℝ ∞ (fun x => (2 * l * x 0) / D_val l (x 2)) v
    apply ContDiffAt.div
    · exact contDiffAt_const.mul (contDiffAt_euclidean_coord 0 v)
    · dsimp [D_val]
      exact contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_euclidean_coord 2 v))
    · exact hD
  · -- coordinate 1
    change ContDiffAt ℝ ∞ (fun x => (2 * l * x 1) / D_val l (x 2)) v
    apply ContDiffAt.div
    · exact contDiffAt_const.mul (contDiffAt_euclidean_coord 1 v)
    · dsimp [D_val]
      exact contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_euclidean_coord 2 v))
    · exact hD
  · -- coordinate 2
    change ContDiffAt ℝ ∞ (fun x => ((1 - l^2) + (1 + l^2) * x 2) / D_val l (x 2)) v
    apply ContDiffAt.div
    · exact contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_euclidean_coord 2 v))
    · dsimp [D_val]
      exact contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_euclidean_coord 2 v))
    · exact hD

/-- Forward map is $C^\infty$ smooth manifold map on $\mathbb{CP}^1$. -/
theorem dil_homeo_is_smooth (l : ℝ) (hl : 0 < l) :
    ContMDiff I_CP1 I_CP1 ∞ (dil_homeo l hl) := by
  have h_comp : ContMDiff I_CP1 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (dil_fun l ∘ ((↑) : CP1 → EuclideanSpace ℝ (Fin 3))) := by
    intro z
    have hg := contDiffAt_dil_fun l z.1 (cp1_D_val_ne_zero l hl z)
    have hf := (contMDiff_coe_sphere (m := ∞) (n := 2)).contMDiffAt (x := z)
    exact hg.comp_contMDiffAt hf
  have h_mem (z : CP1) : (dil_fun l ∘ ((↑) : CP1 → EuclideanSpace ℝ (Fin 3))) z ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    simp only [Function.comp_apply, mem_sphere_zero_iff_norm]
    exact dil_fun_norm l z.1 (mem_sphere_zero_iff_norm.mp z.2) (cp1_D_val_ne_zero l hl z)
  exact ContMDiff.codRestrict_sphere (n := 2) h_comp h_mem

/-- Inverse map is $C^\infty$ smooth manifold map on $\mathbb{CP}^1$. -/
theorem dil_homeo_symm_is_smooth (l : ℝ) (hl : 0 < l) :
    ContMDiff I_CP1 I_CP1 ∞ (dil_homeo l hl).symm := by
  exact dil_homeo_is_smooth l⁻¹ (inv_pos.mpr hl)


/- =========================================================================
   PROJECTIVE EQUIVALENCE AND ONEPOINT ℂ EVALUATION RIGIDITY
   ========================================================================= -/

/-- Homogeneous coordinate lift from `OnePoint ℂ` to `ℂ × ℂ \ {(0, 0)}`. -/
def onePointToProj (p : OnePoint ℂ) : ℂ × ℂ :=
  match p with
  | OnePoint.infty => (1, 0)
  | OnePoint.some z => (z, 1)

theorem onePointToProj_ne_zero (p : OnePoint ℂ) : onePointToProj p ≠ (0, 0) := by
  match p with
  | OnePoint.infty =>
    intro h
    have h1 : (1 : ℂ) = 0 := congr_arg Prod.fst h
    exact one_ne_zero h1
  | OnePoint.some z =>
    intro h
    have h2 : (1 : ℂ) = 0 := congr_arg Prod.snd h
    exact one_ne_zero h2

theorem not_projEquiv_onePointToProj {p q : OnePoint ℂ} (hne : p ≠ q) :
    ¬ ProjEquiv (onePointToProj p) (onePointToProj q) := by
  match p, q with
  | OnePoint.infty, OnePoint.infty => exact False.elim (hne rfl)
  | OnePoint.infty, OnePoint.some w =>
    dsimp [onePointToProj, ProjEquiv]
    intro h
    have h1 : (1 : ℂ) = 0 := by linear_combination h
    exact one_ne_zero h1
  | OnePoint.some z, OnePoint.infty =>
    dsimp [onePointToProj, ProjEquiv]
    intro h
    have h1 : (1 : ℂ) = 0 := by linear_combination -h
    exact one_ne_zero h1
  | OnePoint.some z, OnePoint.some w =>
    dsimp [onePointToProj, ProjEquiv]
    intro h
    have hzw : z = w := by linear_combination h
    exact hne (congr_arg OnePoint.some hzw)

theorem projEquiv_act_onePointToProj_eval (M : MoebiusMatrix) (p : OnePoint ℂ) :
    ProjEquiv (M.act (onePointToProj p)) (onePointToProj (M.eval p)) := by
  match p with
  | OnePoint.infty =>
    dsimp [onePointToProj, MoebiusMatrix.act, MoebiusMatrix.eval]
    by_cases hc : M.c = 0
    · simp [hc, onePointToProj, ProjEquiv]
    · simp [hc, onePointToProj, ProjEquiv]
      exact (mul_div_cancel₀ M.a hc).symm
  | OnePoint.some z =>
    dsimp [onePointToProj, MoebiusMatrix.act, MoebiusMatrix.eval]
    by_cases hden : M.c * z + M.d = 0
    · simp only [hden, ↓reduceIte, onePointToProj, ProjEquiv]
      linear_combination -hden
    · simp only [hden, ↓reduceIte, onePointToProj, ProjEquiv]
      have h1 : (M.a * z + M.b * 1) * 1 = M.a * z + M.b := by ring
      have h2 : (M.c * z + M.d * 1) * ((M.a * z + M.b) / (M.c * z + M.d)) =
                (M.c * z + M.d) * ((M.a * z + M.b) / (M.c * z + M.d)) := by ring
      rw [h1, h2]
      exact (mul_div_cancel₀ (M.a * z + M.b) hden).symm

theorem MoebiusMatrix.eval_id (p : OnePoint ℂ) :
    MoebiusMatrix.id.eval p = p := by
  match p with
  | OnePoint.infty =>
    dsimp [MoebiusMatrix.eval, MoebiusMatrix.id]
    simp
  | OnePoint.some z =>
    dsimp [MoebiusMatrix.eval, MoebiusMatrix.id]
    simp

theorem MoebiusMatrix.eval_id_fun :
    MoebiusMatrix.id.eval = _root_.id := by
  funext p
  exact MoebiusMatrix.eval_id p

theorem pglEquiv_id_iff (M : MoebiusMatrix) :
    PglEquiv M MoebiusMatrix.id ↔ (M.b = 0 ∧ M.c = 0 ∧ M.a = M.d) := by
  constructor
  · intro h
    have h0 := h (1, 0)
    have h1 := h (0, 1)
    have h11 := h (1, 1)
    dsimp [MoebiusMatrix.act, MoebiusMatrix.id, ProjEquiv] at h0 h1 h11
    refine ⟨?_, ?_, ?_⟩
    · linear_combination h1
    · linear_combination -h0
    · linear_combination h11 - h1 - h0
  · rintro ⟨hb, hc, had⟩ p
    dsimp [MoebiusMatrix.act, MoebiusMatrix.id, ProjEquiv]
    linear_combination p.2 ^ 2 * hb - p.1 ^ 2 * hc + (p.1 * p.2) * had

theorem PglEquiv.eval_eq_of_id {M : MoebiusMatrix} (h : PglEquiv M MoebiusMatrix.id)
    (p : OnePoint ℂ) : M.eval p = p := by
  obtain ⟨hb, hc, had⟩ := (pglEquiv_id_iff M).mp h
  have hd_ne : M.d ≠ 0 := by
    intro hd0
    have hdet := M.det_ne_zero
    rw [had, hd0, hb, hc] at hdet
    ring_nf at hdet
    exact hdet rfl
  match p with
  | OnePoint.infty =>
    dsimp [MoebiusMatrix.eval]
    simp [hc]
  | OnePoint.some z =>
    dsimp [MoebiusMatrix.eval]
    have hden : M.c * z + M.d = M.d := by rw [hc, zero_mul, zero_add]
    have hnum : M.a * z + M.b = M.d * z := by rw [had, hb, add_zero]
    rw [hden, hnum]
    simp [hd_ne]

lemma act_ne_zero (M : MoebiusMatrix) {v : ℂ × ℂ} (hv : v ≠ (0, 0)) :
    M.act v ≠ (0, 0) := by
  intro h
  have hdet := M.det_ne_zero
  dsimp [MoebiusMatrix.act] at h
  have h1 : M.a * v.1 + M.b * v.2 = 0 := congr_arg Prod.fst h
  have h2 : M.c * v.1 + M.d * v.2 = 0 := congr_arg Prod.snd h
  have hv1 : (M.a * M.d - M.b * M.c) * v.1 = 0 := by
    linear_combination M.d * h1 - M.b * h2
  have hv2 : (M.a * M.d - M.b * M.c) * v.2 = 0 := by
    linear_combination -M.c * h1 + M.a * h2
  cases mul_eq_zero.mp hv1 with
  | inl hd => exact hdet hd
  | inr hv1' =>
    cases mul_eq_zero.mp hv2 with
    | inl hd => exact hdet hd
    | inr hv2' => exact hv (Prod.ext hv1' hv2')

lemma act_projEquiv (M : MoebiusMatrix) {v w : ℂ × ℂ} (h : ProjEquiv v w) :
    ProjEquiv (M.act v) (M.act w) := by
  dsimp [MoebiusMatrix.act, ProjEquiv] at *
  linear_combination (M.a * M.d - M.b * M.c) * h

lemma projEquiv_onePointToProj_inj {p q : OnePoint ℂ}
    (h : ProjEquiv (onePointToProj p) (onePointToProj q)) : p = q := by
  by_contra hne
  exact not_projEquiv_onePointToProj hne h

theorem eval_comp (M₁ M₂ : MoebiusMatrix) (p : OnePoint ℂ) :
    (MoebiusMatrix.comp M₁ M₂).eval p = M₁.eval (M₂.eval p) := by
  apply projEquiv_onePointToProj_inj
  have h1 := (projEquiv_act_onePointToProj_eval (MoebiusMatrix.comp M₁ M₂) p).symm
  have h2 : ProjEquiv ((MoebiusMatrix.comp M₁ M₂).act (onePointToProj p))
                      (M₁.act (M₂.act (onePointToProj p))) := by
    dsimp [MoebiusMatrix.comp]; rw [act_comp]; exact ProjEquiv.refl _
  have h3 : ProjEquiv (M₁.act (M₂.act (onePointToProj p)))
                      (M₁.act (onePointToProj (M₂.eval p))) :=
    act_projEquiv M₁ (projEquiv_act_onePointToProj_eval M₂ p)
  have h4 := projEquiv_act_onePointToProj_eval M₁ (M₂.eval p)
  have n2 : M₂.act (onePointToProj p) ≠ (0, 0) :=
    act_ne_zero M₂ (onePointToProj_ne_zero p)
  have n1 : (MoebiusMatrix.comp M₁ M₂).act (onePointToProj p) ≠ (0, 0) :=
    act_ne_zero (MoebiusMatrix.comp M₁ M₂) (onePointToProj_ne_zero p)
  have n3 : M₁.act (M₂.act (onePointToProj p)) ≠ (0, 0) :=
    act_ne_zero M₁ n2
  have n4 : M₁.act (onePointToProj (M₂.eval p)) ≠ (0, 0) :=
    act_ne_zero M₁ (onePointToProj_ne_zero _)
  exact ProjEquiv.trans n4 (ProjEquiv.trans n3 (ProjEquiv.trans n1 h1 h2) h3) h4

theorem eval_inv_eval (M : MoebiusMatrix) (p : OnePoint ℂ) :
    (MoebiusMatrix.inv M).eval (M.eval p) = p := by
  apply projEquiv_onePointToProj_inj
  have h1 : ProjEquiv (onePointToProj ((MoebiusMatrix.inv M).eval (M.eval p)))
                      ((MoebiusMatrix.inv M).act (onePointToProj (M.eval p))) :=
    (projEquiv_act_onePointToProj_eval (MoebiusMatrix.inv M) (M.eval p)).symm
  have h2 : ProjEquiv ((MoebiusMatrix.inv M).act (onePointToProj (M.eval p)))
                      ((MoebiusMatrix.inv M).act (M.act (onePointToProj p))) :=
    act_projEquiv (MoebiusMatrix.inv M) (projEquiv_act_onePointToProj_eval M p).symm
  have h3 : ProjEquiv ((MoebiusMatrix.inv M).act (M.act (onePointToProj p)))
                      (onePointToProj p) := by
    change ProjEquiv (M.adj.act (M.act (onePointToProj p))) (onePointToProj p)
    exact act_adj_cancel M (onePointToProj p)
  have n1 : (MoebiusMatrix.inv M).act (onePointToProj (M.eval p)) ≠ (0, 0) :=
    act_ne_zero (MoebiusMatrix.inv M) (onePointToProj_ne_zero _)
  have n2 : (MoebiusMatrix.inv M).act (M.act (onePointToProj p)) ≠ (0, 0) :=
    act_ne_zero (MoebiusMatrix.inv M) (act_ne_zero M (onePointToProj_ne_zero p))
  exact ProjEquiv.trans n2 (ProjEquiv.trans n1 h1 h2) h3

/- =========================================================================
   STEREOGRAPHIC AFFINE SCALING AND CP1 MOEBIUS MAPPING
   ========================================================================= -/

/-- Map from `CP1` to the one-point compactification `OnePoint ℂ` via stereographic projection. -/
noncomputable def cp1ToOnePoint (z : CP1) : OnePoint ℂ :=
  open Classical in if z = north_pole then OnePoint.infty else OnePoint.some (stereo_chart z)

theorem south_pole_neg_north : (south_pole : CP1) = - (north_pole : CP1) := by
  ext i; fin_cases i
  · change (!₂[0, 0, -1] : EuclideanSpace ℝ (Fin 3)) 0 = (- (!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3))) 0; simp
  · change (!₂[0, 0, -1] : EuclideanSpace ℝ (Fin 3)) 1 = (- (!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3))) 1; simp
  · change (!₂[0, 0, -1] : EuclideanSpace ℝ (Fin 3)) 2 = (- (!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3))) 2; simp

theorem stereo_chart_south_pole : stereo_chart south_pole = 0 := by
  rw [south_pole_neg_north]
  dsimp [stereo_chart, stereographic']
  simp

theorem north_pole_ne_south_pole : (north_pole : CP1) ≠ south_pole := by
  intro h
  have h2 : (north_pole : EuclideanSpace ℝ (Fin 3)) 2 = (south_pole : EuclideanSpace ℝ (Fin 3)) 2 :=
    congr_arg (fun (p : CP1) => p.1 2) h
  change (1 : ℝ) = -1 at h2
  norm_num at h2

theorem south_pole_ne_north_pole : (south_pole : CP1) ≠ north_pole :=
  north_pole_ne_south_pole.symm

noncomputable def stereo_U : (ℝ ∙ (north_pole : EuclideanSpace ℝ (Fin 3)))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2 (ne_zero_of_mem_unit_sphere north_pole)).repr

noncomputable def stereo_iso : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (north_pole : EuclideanSpace ℝ (Fin 3)))ᗮ :=
  Complex.orthonormalBasisOneI.repr.trans stereo_U.symm

noncomputable def stereo_vec (a : ℂ) : EuclideanSpace ℝ (Fin 3) := (stereo_iso a).1

theorem stereo_vec_add (a b : ℂ) : stereo_vec (a + b) = stereo_vec a + stereo_vec b := by
  dsimp [stereo_vec, stereo_iso]; simp

theorem stereo_vec_smul (c : ℝ) (a : ℂ) : stereo_vec ((c : ℂ) * a) = c • stereo_vec a := by
  dsimp [stereo_vec, stereo_iso]
  have h : Complex.orthonormalBasisOneI.repr ((c : ℂ) * a) = c • Complex.orthonormalBasisOneI.repr a := by
    ext i; fin_cases i <;> simp
  rw [h]; simp

theorem stereo_vec_coord_2 (a : ℂ) : stereo_vec a 2 = 0 := by
  let v : EuclideanSpace ℝ (Fin 3) := (stereo_iso a).1
  have h : ⟪(north_pole : EuclideanSpace ℝ (Fin 3)), v⟫ = 0 := by
    have hmem := (stereo_iso a).2
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hmem
    exact hmem
  have h_np : (north_pole : EuclideanSpace ℝ (Fin 3)) = EuclideanSpace.single 2 1 := by
    ext i; fin_cases i <;> rfl
  have h2 : ⟪EuclideanSpace.single 2 (1:ℝ), v⟫ = 0 := by
    rw [← h_np]; exact h
  have h_inner := EuclideanSpace.inner_single_left (2 : Fin 3) (1 : ℝ) v
  rw [h_inner] at h2
  simp only [starRingEnd_apply, star_trivial, one_mul] at h2
  exact h2

theorem stereo_inner_isometry (a b : ℂ) :
    stereo_vec a 0 * stereo_vec b 0 + stereo_vec a 1 * stereo_vec b 1 = ⟪a, b⟫ := by
  have h_inner : ⟪stereo_vec a, stereo_vec b⟫ =
      stereo_vec a 0 * stereo_vec b 0 + stereo_vec a 1 * stereo_vec b 1 + stereo_vec a 2 * stereo_vec b 2 := by
    simp [inner, Fin.sum_univ_three]; ring
  have h2a := stereo_vec_coord_2 a
  have h2b := stereo_vec_coord_2 b
  rw [h2a, h2b, mul_zero, add_zero] at h_inner
  have h_iso : ⟪stereo_vec a, stereo_vec b⟫ = ⟪stereo_iso a, stereo_iso b⟫ := rfl
  rw [LinearIsometryEquiv.inner_map_map] at h_iso
  rw [← h_iso, h_inner]

theorem inner_comb_norm_sq (a w : ℂ) (l : ℝ) :
    ‖a + (l : ℂ) * w‖^2 = ‖a‖^2 + 2 * l * ⟪a, w⟫ + l^2 * ‖w‖^2 := by
  have h_smul : (l : ℂ) * w = l • w := by simp
  have h_norm (z : ℂ) : ‖z‖^2 = ⟪z, z⟫ := by
    rw [pow_two, real_inner_self_eq_norm_mul_norm]
  rw [h_smul, h_norm, real_inner_add_add_self, h_norm, h_norm]
  rw [inner_smul_right, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial, inner_smul_right]
  ring

theorem norm_sq_target (a w : ℂ) (l : ℝ) :
    ‖a + (l : ℂ) * w‖^2 = ‖a‖^2 + 2 * l * (stereo_vec a 0 * stereo_vec w 0 + stereo_vec a 1 * stereo_vec w 1) + l^2 * ‖w‖^2 := by
  rw [inner_comb_norm_sq, stereo_inner_isometry]

theorem stereo_vec_norm_sq (a : ℂ) : (stereo_vec a 0)^2 + (stereo_vec a 1)^2 = ‖a‖^2 := by
  have h_self := stereo_inner_isometry a a
  have h_norm : ‖a‖^2 = ⟪a, a⟫ := by
    rw [pow_two, real_inner_self_eq_norm_mul_norm]
  rw [pow_two, pow_two, h_self, ← h_norm]

noncomputable def D_aff (a : ℂ) (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  let s := stereo_vec a
  (1 - v 2) * (4 + (s 0^2 + s 1^2)) + 4 * l * (s 0 * v 0 + s 1 * v 1) + 4 * l^2 * (1 + v 2)

noncomputable def N0 (a : ℂ) (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  let s := stereo_vec a
  4 * ((1 - v 2) * s 0 + 2 * l * v 0)

noncomputable def N1 (a : ℂ) (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  let s := stereo_vec a
  4 * ((1 - v 2) * s 1 + 2 * l * v 1)

noncomputable def N2 (a : ℂ) (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  let s := stereo_vec a
  (1 - v 2) * ((s 0^2 + s 1^2) - 4) + 4 * l * (s 0 * v 0 + s 1 * v 1) + 4 * l^2 * (1 + v 2)

theorem aff_norm_identity (a : ℂ) (l : ℝ) (v : EuclideanSpace ℝ (Fin 3))
    (hv : (v 0)^2 + (v 1)^2 + (v 2)^2 = 1) :
    (N0 a l v)^2 + (N1 a l v)^2 + (N2 a l v)^2 = (D_aff a l v)^2 := by
  dsimp [N0, N1, N2, D_aff]
  linear_combination 64 * l^2 * hv

theorem D_aff_sub_N2 (a : ℂ) (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    D_aff a l v - N2 a l v = 8 * (1 - v 2) := by
  dsimp [D_aff, N2]; ring

theorem D_aff_ne_zero (a : ℂ) (l : ℝ) (hl : 0 < l) (v : EuclideanSpace ℝ (Fin 3))
    (hv : (v 0)^2 + (v 1)^2 + (v 2)^2 = 1) :
    D_aff a l v ≠ 0 := by
  intro hD
  have h_norm := aff_norm_identity a l v hv
  rw [hD, zero_pow (by norm_num : 2 ≠ 0)] at h_norm
  have hN2 : N2 a l v = 0 := by
    have h_sq0 : 0 ≤ (N0 a l v)^2 := sq_nonneg _
    have h_sq1 : 0 ≤ (N1 a l v)^2 := sq_nonneg _
    have h_sq2 : 0 ≤ (N2 a l v)^2 := sq_nonneg _
    have h_N2_sq : (N2 a l v)^2 = 0 := by linarith
    exact sq_eq_zero_iff.mp h_N2_sq
  have h_diff := D_aff_sub_N2 a l v
  rw [hD, hN2, sub_zero] at h_diff
  have hv2 : v 2 = 1 := by linarith
  have h_D_at_1 : D_aff a l v = 8 * l^2 := by
    dsimp [D_aff]; rw [hv2]
    have h_v0 : v 0 = 0 := by
      have h_sum := hv; rw [hv2] at h_sum
      have h0 : (v 0)^2 = 0 := by nlinarith [sq_nonneg (v 1)]
      exact sq_eq_zero_iff.mp h0
    have h_v1 : v 1 = 0 := by
      have h_sum := hv; rw [hv2] at h_sum
      have h1 : (v 1)^2 = 0 := by nlinarith [sq_nonneg (v 0)]
      exact sq_eq_zero_iff.mp h1
    rw [h_v0, h_v1]; ring
  rw [hD] at h_D_at_1
  have h_pos : 8 * l^2 > 0 := by positivity
  linarith

noncomputable def aff_fun (a : ℂ) (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  !₂[N0 a l v / D_aff a l v, N1 a l v / D_aff a l v, N2 a l v / D_aff a l v]

theorem aff_fun_north_pole (a : ℂ) (l : ℝ) (hl : 0 < l) :
    aff_fun a l north_pole.1 = north_pole.1 := by
  ext i; fin_cases i
  · change N0 a l north_pole.1 / D_aff a l north_pole.1 = 0
    dsimp [N0, north_pole]
    have h_num : 4 * ((1 - (1:ℝ)) * (stereo_vec a 0) + 2 * l * 0) = 0 := by ring
    rw [h_num, zero_div]
  · change N1 a l north_pole.1 / D_aff a l north_pole.1 = 0
    dsimp [N1, north_pole]
    have h_num : 4 * ((1 - (1:ℝ)) * (stereo_vec a 1) + 2 * l * 0) = 0 := by ring
    rw [h_num, zero_div]
  · change N2 a l north_pole.1 / D_aff a l north_pole.1 = 1
    dsimp [N2, D_aff, north_pole]
    have h_num : (1 - (1:ℝ)) * (stereo_vec a 0^2 + stereo_vec a 1^2 - 4) + 4 * l * (stereo_vec a 0 * 0 + stereo_vec a 1 * 0) + 4 * l^2 * (1 + 1) = 8 * l^2 := by ring
    have h_den : (1 - (1:ℝ)) * (4 + (stereo_vec a 0^2 + stereo_vec a 1^2)) + 4 * l * (stereo_vec a 0 * 0 + stereo_vec a 1 * 0) + 4 * l^2 * (1 + 1) = 8 * l^2 := by ring
    rw [h_num, h_den]
    have h_pos : 8 * l^2 ≠ 0 := by positivity
    exact div_self h_pos

theorem contDiffAt_aff_fun (a : ℂ) (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) (hD : D_aff a l v ≠ 0) :
    ContDiffAt ℝ ∞ (aff_fun a l) v := by
  let E := EuclideanSpace.equiv (Fin 3) ℝ
  have h_eq : aff_fun a l = E.symm ∘ (E ∘ aff_fun a l) := by
    ext x; simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [h_eq]
  apply ContDiff.comp_contDiffAt v E.symm.contDiff
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun x => N0 a l x / D_aff a l x) v
    apply ContDiffAt.div
    · refine contDiffAt_const.mul ((contDiffAt_const.sub (contDiffAt_euclidean_coord 2 v)).mul contDiffAt_const |>.add
        (contDiffAt_const.mul (contDiffAt_euclidean_coord 0 v)))
    · refine (contDiffAt_const.sub (contDiffAt_euclidean_coord 2 v)).mul contDiffAt_const |>.add
        (contDiffAt_const.mul ((contDiffAt_const.mul (contDiffAt_euclidean_coord 0 v)).add (contDiffAt_const.mul (contDiffAt_euclidean_coord 1 v)))) |>.add
        (contDiffAt_const.mul (contDiffAt_const.add (contDiffAt_euclidean_coord 2 v)))
    · exact hD
  · change ContDiffAt ℝ ∞ (fun x => N1 a l x / D_aff a l x) v
    apply ContDiffAt.div
    · refine contDiffAt_const.mul ((contDiffAt_const.sub (contDiffAt_euclidean_coord 2 v)).mul contDiffAt_const |>.add
        (contDiffAt_const.mul (contDiffAt_euclidean_coord 1 v)))
    · refine (contDiffAt_const.sub (contDiffAt_euclidean_coord 2 v)).mul contDiffAt_const |>.add
        (contDiffAt_const.mul ((contDiffAt_const.mul (contDiffAt_euclidean_coord 0 v)).add (contDiffAt_const.mul (contDiffAt_euclidean_coord 1 v)))) |>.add
        (contDiffAt_const.mul (contDiffAt_const.add (contDiffAt_euclidean_coord 2 v)))
    · exact hD
  · change ContDiffAt ℝ ∞ (fun x => N2 a l x / D_aff a l x) v
    apply ContDiffAt.div
    · refine (contDiffAt_const.sub (contDiffAt_euclidean_coord 2 v)).mul contDiffAt_const |>.add
        (contDiffAt_const.mul ((contDiffAt_const.mul (contDiffAt_euclidean_coord 0 v)).add (contDiffAt_const.mul (contDiffAt_euclidean_coord 1 v)))) |>.add
        (contDiffAt_const.mul (contDiffAt_const.add (contDiffAt_euclidean_coord 2 v)))
    · refine (contDiffAt_const.sub (contDiffAt_euclidean_coord 2 v)).mul contDiffAt_const |>.add
        (contDiffAt_const.mul ((contDiffAt_const.mul (contDiffAt_euclidean_coord 0 v)).add (contDiffAt_const.mul (contDiffAt_euclidean_coord 1 v)))) |>.add
        (contDiffAt_const.mul (contDiffAt_const.add (contDiffAt_euclidean_coord 2 v)))
    · exact hD

theorem continuous_aff_fun_on_cp1 (a : ℂ) (l : ℝ) (hl : 0 < l) :
    Continuous (fun (z : CP1) => aff_fun a l z.1) := by
  dsimp [aff_fun]
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp ?_
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun (z : CP1) => N0 a l z.1 / D_aff a l z.1)
    apply Continuous.div
    · dsimp [N0]
      refine continuous_const.mul ((continuous_const.sub (continuous_cp1_coord 2)).mul continuous_const |>.add
        (continuous_const.mul (continuous_cp1_coord 0)))
    · dsimp [D_aff]
      refine (continuous_const.sub (continuous_cp1_coord 2)).mul continuous_const |>.add
        (continuous_const.mul ((continuous_const.mul (continuous_cp1_coord 0)).add (continuous_const.mul (continuous_cp1_coord 1)))) |>.add
        (continuous_const.mul (continuous_const.add (continuous_cp1_coord 2)))
    · intro z
      have hz_norm : (z.1 0)^2 + (z.1 1)^2 + (z.1 2)^2 = 1 := by
        have hz := mem_sphere_zero_iff_norm.mp z.2
        rw [EuclideanSpace.norm_eq] at hz
        have h_sq := congr_arg (fun x => x^2) hz
        simp only [Fin.sum_univ_three] at h_sq
        have h_pos : 0 ≤ ‖z.1 0‖ ^ 2 + ‖z.1 1‖ ^ 2 + ‖z.1 2‖ ^ 2 := by positivity
        rw [Real.sq_sqrt h_pos] at h_sq
        have h_norm_sq (x : ℝ) : ‖x‖ ^ 2 = x ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
        rw [h_norm_sq, h_norm_sq, h_norm_sq] at h_sq
        norm_num at h_sq; exact h_sq
      exact D_aff_ne_zero a l hl z.1 hz_norm
  · change Continuous (fun (z : CP1) => N1 a l z.1 / D_aff a l z.1)
    apply Continuous.div
    · dsimp [N1]
      refine continuous_const.mul ((continuous_const.sub (continuous_cp1_coord 2)).mul continuous_const |>.add
        (continuous_const.mul (continuous_cp1_coord 1)))
    · dsimp [D_aff]
      refine (continuous_const.sub (continuous_cp1_coord 2)).mul continuous_const |>.add
        (continuous_const.mul ((continuous_const.mul (continuous_cp1_coord 0)).add (continuous_const.mul (continuous_cp1_coord 1)))) |>.add
        (continuous_const.mul (continuous_const.add (continuous_cp1_coord 2)))
    · intro z
      have hz_norm : (z.1 0)^2 + (z.1 1)^2 + (z.1 2)^2 = 1 := by
        have hz := mem_sphere_zero_iff_norm.mp z.2
        rw [EuclideanSpace.norm_eq] at hz
        have h_sq := congr_arg (fun x => x^2) hz
        simp only [Fin.sum_univ_three] at h_sq
        have h_pos : 0 ≤ ‖z.1 0‖ ^ 2 + ‖z.1 1‖ ^ 2 + ‖z.1 2‖ ^ 2 := by positivity
        rw [Real.sq_sqrt h_pos] at h_sq
        have h_norm_sq (x : ℝ) : ‖x‖ ^ 2 = x ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
        rw [h_norm_sq, h_norm_sq, h_norm_sq] at h_sq
        norm_num at h_sq; exact h_sq
      exact D_aff_ne_zero a l hl z.1 hz_norm
  · change Continuous (fun (z : CP1) => N2 a l z.1 / D_aff a l z.1)
    apply Continuous.div
    · dsimp [N2]
      refine (continuous_const.sub (continuous_cp1_coord 2)).mul continuous_const |>.add
        (continuous_const.mul ((continuous_const.mul (continuous_cp1_coord 0)).add (continuous_const.mul (continuous_cp1_coord 1)))) |>.add
        (continuous_const.mul (continuous_const.add (continuous_cp1_coord 2)))
    · dsimp [D_aff]
      refine (continuous_const.sub (continuous_cp1_coord 2)).mul continuous_const |>.add
        (continuous_const.mul ((continuous_const.mul (continuous_cp1_coord 0)).add (continuous_const.mul (continuous_cp1_coord 1)))) |>.add
        (continuous_const.mul (continuous_const.add (continuous_cp1_coord 2)))
    · intro z
      have hz_norm : (z.1 0)^2 + (z.1 1)^2 + (z.1 2)^2 = 1 := by
        have hz := mem_sphere_zero_iff_norm.mp z.2
        rw [EuclideanSpace.norm_eq] at hz
        have h_sq := congr_arg (fun x => x^2) hz
        simp only [Fin.sum_univ_three] at h_sq
        have h_pos : 0 ≤ ‖z.1 0‖ ^ 2 + ‖z.1 1‖ ^ 2 + ‖z.1 2‖ ^ 2 := by positivity
        rw [Real.sq_sqrt h_pos] at h_sq
        have h_norm_sq (x : ℝ) : ‖x‖ ^ 2 = x ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
        rw [h_norm_sq, h_norm_sq, h_norm_sq] at h_sq
        norm_num at h_sq; exact h_sq
      exact D_aff_ne_zero a l hl z.1 hz_norm

theorem check_symm_simp (a : ℂ) :
    ((stereo_chart.symm a : CP1) : EuclideanSpace ℝ (Fin 3)) =
    (‖a‖^2 + 4)⁻¹ • ((4 : ℝ) • stereo_vec a + (‖a‖^2 - 4) • (north_pole : EuclideanSpace ℝ (Fin 3))) := by
  have h1 : stereo_chart.symm a = (stereographic (norm_eq_of_mem_sphere north_pole)).symm (stereo_iso a) := by
    dsimp [stereo_chart, stereographic', stereo_iso, c_equiv_e2, stereo_U]; rfl
  rw [h1]
  change (stereoInvFun (norm_eq_of_mem_sphere north_pole) (stereo_iso a) : EuclideanSpace ℝ (Fin 3)) = _
  rw [stereoInvFun_apply, stereo_iso.norm_map a]; rfl

theorem check_symm_coord_0 (w : ℂ) :
    ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 0 = (4 * stereo_vec w 0) / (‖w‖^2 + 4) := by
  rw [check_symm_simp]; dsimp [north_pole]; simp [div_eq_inv_mul]

theorem check_symm_coord_1 (w : ℂ) :
    ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 1 = (4 * stereo_vec w 1) / (‖w‖^2 + 4) := by
  rw [check_symm_simp]; dsimp [north_pole]; simp [div_eq_inv_mul]

theorem check_symm_coord_2 (w : ℂ) :
    ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 2 = (‖w‖^2 - 4) / (‖w‖^2 + 4) := by
  rw [check_symm_simp]
  have h_s2 : stereo_vec w 2 = 0 := stereo_vec_coord_2 w
  dsimp [north_pole]
  have h2 : (stereo_vec w 2) = 0 := h_s2
  simp [h2, div_eq_inv_mul]

theorem ring_match_0 (sa0 sw0 a_sq w_sq sy l : ℝ)
    (h_pos : w_sq + 4 ≠ 0) :
    let v2 := (w_sq - 4) / (w_sq + 4)
    let v0 := 4 * sw0 / (w_sq + 4)
    let D := (1 - v2) * (4 + a_sq) + 4 * l * (4 * sy / (w_sq + 4)) + 4 * l^2 * (1 + v2)
    let N0 := 4 * ((1 - v2) * sa0 + 2 * l * v0)
    N0 / D = 4 * (sa0 + l * sw0) / (4 + a_sq + 2 * l * sy + l^2 * w_sq) := by
  intro v2 v0 D N0
  dsimp [D, N0, v2, v0]
  have h_D : (1 - (w_sq - 4) / (w_sq + 4)) * (4 + a_sq) + 4 * l * (4 * sy / (w_sq + 4)) + 4 * l^2 * (1 + (w_sq - 4) / (w_sq + 4)) =
      8 * (4 + a_sq + 2 * l * sy + l^2 * w_sq) / (w_sq + 4) := by
    field_simp; ring
  have h_N0 : 4 * ((1 - (w_sq - 4) / (w_sq + 4)) * sa0 + 2 * l * (4 * sw0 / (w_sq + 4))) =
      32 * (sa0 + l * sw0) / (w_sq + 4) := by
    field_simp; ring
  rw [h_D, h_N0]
  have h_cancel : (32 * (sa0 + l * sw0) / (w_sq + 4)) / (8 * (4 + a_sq + 2 * l * sy + l ^ 2 * w_sq) / (w_sq + 4)) =
      (32 * (sa0 + l * sw0)) / (8 * (4 + a_sq + 2 * l * sy + l ^ 2 * w_sq)) := by
    rw [div_div_div_comm, div_self h_pos, div_one]
  rw [h_cancel]
  have h32 : 32 * (sa0 + l * sw0) = 8 * (4 * (sa0 + l * sw0)) := by ring
  rw [h32]
  exact mul_div_mul_left _ _ (by norm_num : (8:ℝ) ≠ 0)

theorem ring_match_1 (sa1 sw1 a_sq w_sq sy l : ℝ)
    (h_pos : w_sq + 4 ≠ 0) :
    let v2 := (w_sq - 4) / (w_sq + 4)
    let v1 := 4 * sw1 / (w_sq + 4)
    let D := (1 - v2) * (4 + a_sq) + 4 * l * (4 * sy / (w_sq + 4)) + 4 * l^2 * (1 + v2)
    let N1 := 4 * ((1 - v2) * sa1 + 2 * l * v1)
    N1 / D = 4 * (sa1 + l * sw1) / (4 + a_sq + 2 * l * sy + l^2 * w_sq) := by
  intro v2 v1 D N1
  dsimp [D, N1, v2, v1]
  have h_D : (1 - (w_sq - 4) / (w_sq + 4)) * (4 + a_sq) + 4 * l * (4 * sy / (w_sq + 4)) + 4 * l^2 * (1 + (w_sq - 4) / (w_sq + 4)) =
      8 * (4 + a_sq + 2 * l * sy + l^2 * w_sq) / (w_sq + 4) := by
    field_simp; ring
  have h_N1 : 4 * ((1 - (w_sq - 4) / (w_sq + 4)) * sa1 + 2 * l * (4 * sw1 / (w_sq + 4))) =
      32 * (sa1 + l * sw1) / (w_sq + 4) := by
    field_simp; ring
  rw [h_D, h_N1]
  have h_cancel : (32 * (sa1 + l * sw1) / (w_sq + 4)) / (8 * (4 + a_sq + 2 * l * sy + l ^ 2 * w_sq) / (w_sq + 4)) =
      (32 * (sa1 + l * sw1)) / (8 * (4 + a_sq + 2 * l * sy + l ^ 2 * w_sq)) := by
    rw [div_div_div_comm, div_self h_pos, div_one]
  rw [h_cancel]
  have h32 : 32 * (sa1 + l * sw1) = 8 * (4 * (sa1 + l * sw1)) := by ring
  rw [h32]
  exact mul_div_mul_left _ _ (by norm_num : (8:ℝ) ≠ 0)

theorem ring_match_2 (a_sq w_sq sy l : ℝ)
    (h_pos : w_sq + 4 ≠ 0) :
    let v2 := (w_sq - 4) / (w_sq + 4)
    let D := (1 - v2) * (4 + a_sq) + 4 * l * (4 * sy / (w_sq + 4)) + 4 * l^2 * (1 + v2)
    let N2 := (1 - v2) * (a_sq - 4) + 4 * l * (4 * sy / (w_sq + 4)) + 4 * l^2 * (1 + v2)
    N2 / D = ((a_sq + 2 * l * sy + l^2 * w_sq) - 4) / (4 + a_sq + 2 * l * sy + l^2 * w_sq) := by
  intro v2 D N2
  dsimp [D, N2, v2]
  have h_D : (1 - (w_sq - 4) / (w_sq + 4)) * (4 + a_sq) + 4 * l * (4 * sy / (w_sq + 4)) + 4 * l^2 * (1 + (w_sq - 4) / (w_sq + 4)) =
      8 * (4 + a_sq + 2 * l * sy + l^2 * w_sq) / (w_sq + 4) := by
    field_simp; ring
  have h_N2 : (1 - (w_sq - 4) / (w_sq + 4)) * (a_sq - 4) + 4 * l * (4 * sy / (w_sq + 4)) + 4 * l^2 * (1 + (w_sq - 4) / (w_sq + 4)) =
      8 * ((a_sq + 2 * l * sy + l^2 * w_sq) - 4) / (w_sq + 4) := by
    field_simp; ring
  rw [h_D, h_N2]
  have h_cancel : (8 * ((a_sq + 2 * l * sy + l^2 * w_sq) - 4) / (w_sq + 4)) / (8 * (4 + a_sq + 2 * l * sy + l ^ 2 * w_sq) / (w_sq + 4)) =
      (8 * ((a_sq + 2 * l * sy + l^2 * w_sq) - 4)) / (8 * (4 + a_sq + 2 * l * sy + l ^ 2 * w_sq)) := by
    rw [div_div_div_comm, div_self h_pos, div_one]
  rw [h_cancel]
  exact mul_div_mul_left _ _ (by norm_num : (8:ℝ) ≠ 0)

theorem aff_fun_stereo_chart_symm (a : ℂ) (l : ℝ) (hl : 0 < l) (w : ℂ) :
    aff_fun a l (stereo_chart.symm w).1 = ((stereo_chart.symm (a + (l : ℂ) * w) : CP1) : EuclideanSpace ℝ (Fin 3)) := by
  ext i
  fin_cases i
  · -- coord 0
    change N0 a l (stereo_chart.symm w).1 / D_aff a l (stereo_chart.symm w).1 = ((stereo_chart.symm (a + (l : ℂ) * w) : CP1) : EuclideanSpace ℝ (Fin 3)) 0
    rw [check_symm_coord_0 (a + (l : ℂ) * w)]
    have h_w_pos : ‖w‖^2 + 4 ≠ 0 := by positivity
    have h_m0 := ring_match_0 (stereo_vec a 0) (stereo_vec w 0) (‖a‖^2) (‖w‖^2)
      (stereo_vec a 0 * stereo_vec w 0 + stereo_vec a 1 * stereo_vec w 1) l h_w_pos
    dsimp at h_m0
    have hv2 : ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 2 = (‖w‖^2 - 4) / (‖w‖^2 + 4) := check_symm_coord_2 w
    have hv0 : ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 0 = 4 * stereo_vec w 0 / (‖w‖^2 + 4) := check_symm_coord_0 w
    have hv1 : ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 1 = 4 * stereo_vec w 1 / (‖w‖^2 + 4) := check_symm_coord_1 w
    have ha_sq : (stereo_vec a 0)^2 + (stereo_vec a 1)^2 = ‖a‖^2 := stereo_vec_norm_sq a
    have h_dot : stereo_vec a 0 * ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 0 +
        stereo_vec a 1 * ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 1 =
        4 * (stereo_vec a 0 * stereo_vec w 0 + stereo_vec a 1 * stereo_vec w 1) / (‖w‖^2 + 4) := by
      rw [hv0, hv1]; ring
    have h_D_eq : D_aff a l (stereo_chart.symm w).1 =
        (1 - (‖w‖^2 - 4) / (‖w‖^2 + 4)) * (4 + ‖a‖^2) +
        4 * l * (4 * (stereo_vec a 0 * stereo_vec w 0 + stereo_vec a 1 * stereo_vec w 1) / (‖w‖^2 + 4)) +
        4 * l^2 * (1 + (‖w‖^2 - 4) / (‖w‖^2 + 4)) := by
      dsimp [D_aff]; rw [ha_sq, hv2, h_dot]
    have h_N0_eq : N0 a l (stereo_chart.symm w).1 =
        4 * ((1 - (‖w‖^2 - 4) / (‖w‖^2 + 4)) * stereo_vec a 0 + 2 * l * (4 * stereo_vec w 0 / (‖w‖^2 + 4))) := by
      dsimp [N0]; rw [hv2, hv0]
    rw [h_D_eq, h_N0_eq, h_m0]
    have h_target_norm : ‖a + (l : ℂ) * w‖^2 = ‖a‖^2 + 2 * l * (stereo_vec a 0 * stereo_vec w 0 + stereo_vec a 1 * stereo_vec w 1) + l^2 * ‖w‖^2 :=
      norm_sq_target a w l
    rw [h_target_norm]
    have h_add : stereo_vec (a + (l : ℂ) * w) 0 = stereo_vec a 0 + l * stereo_vec w 0 := by
      rw [stereo_vec_add, stereo_vec_smul]; rfl
    rw [h_add]; ring
  · -- coord 1
    change N1 a l (stereo_chart.symm w).1 / D_aff a l (stereo_chart.symm w).1 = ((stereo_chart.symm (a + (l : ℂ) * w) : CP1) : EuclideanSpace ℝ (Fin 3)) 1
    rw [check_symm_coord_1 (a + (l : ℂ) * w)]
    have h_w_pos : ‖w‖^2 + 4 ≠ 0 := by positivity
    have h_m1 := ring_match_1 (stereo_vec a 1) (stereo_vec w 1) (‖a‖^2) (‖w‖^2)
      (stereo_vec a 0 * stereo_vec w 0 + stereo_vec a 1 * stereo_vec w 1) l h_w_pos
    dsimp at h_m1
    have hv2 : ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 2 = (‖w‖^2 - 4) / (‖w‖^2 + 4) := check_symm_coord_2 w
    have hv0 : ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 0 = 4 * stereo_vec w 0 / (‖w‖^2 + 4) := check_symm_coord_0 w
    have hv1 : ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 1 = 4 * stereo_vec w 1 / (‖w‖^2 + 4) := check_symm_coord_1 w
    have ha_sq : (stereo_vec a 0)^2 + (stereo_vec a 1)^2 = ‖a‖^2 := stereo_vec_norm_sq a
    have h_dot : stereo_vec a 0 * ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 0 +
        stereo_vec a 1 * ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 1 =
        4 * (stereo_vec a 0 * stereo_vec w 0 + stereo_vec a 1 * stereo_vec w 1) / (‖w‖^2 + 4) := by
      rw [hv0, hv1]; ring
    have h_D_eq : D_aff a l (stereo_chart.symm w).1 =
        (1 - (‖w‖^2 - 4) / (‖w‖^2 + 4)) * (4 + ‖a‖^2) +
        4 * l * (4 * (stereo_vec a 0 * stereo_vec w 0 + stereo_vec a 1 * stereo_vec w 1) / (‖w‖^2 + 4)) +
        4 * l^2 * (1 + (‖w‖^2 - 4) / (‖w‖^2 + 4)) := by
      dsimp [D_aff]; rw [ha_sq, hv2, h_dot]
    have h_N1_eq : N1 a l (stereo_chart.symm w).1 =
        4 * ((1 - (‖w‖^2 - 4) / (‖w‖^2 + 4)) * stereo_vec a 1 + 2 * l * (4 * stereo_vec w 1 / (‖w‖^2 + 4))) := by
      dsimp [N1]; rw [hv2, hv1]
    rw [h_D_eq, h_N1_eq, h_m1]
    have h_target_norm : ‖a + (l : ℂ) * w‖^2 = ‖a‖^2 + 2 * l * (stereo_vec a 0 * stereo_vec w 0 + stereo_vec a 1 * stereo_vec w 1) + l^2 * ‖w‖^2 :=
      norm_sq_target a w l
    rw [h_target_norm]
    have h_add : stereo_vec (a + (l : ℂ) * w) 1 = stereo_vec a 1 + l * stereo_vec w 1 := by
      rw [stereo_vec_add, stereo_vec_smul]; rfl
    rw [h_add]; ring
  · -- coord 2
    change N2 a l (stereo_chart.symm w).1 / D_aff a l (stereo_chart.symm w).1 = ((stereo_chart.symm (a + (l : ℂ) * w) : CP1) : EuclideanSpace ℝ (Fin 3)) 2
    rw [check_symm_coord_2 (a + (l : ℂ) * w)]
    have h_w_pos : ‖w‖^2 + 4 ≠ 0 := by positivity
    have h_m2 := ring_match_2 (‖a‖^2) (‖w‖^2)
      (stereo_vec a 0 * stereo_vec w 0 + stereo_vec a 1 * stereo_vec w 1) l h_w_pos
    dsimp at h_m2
    have hv2 : ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 2 = (‖w‖^2 - 4) / (‖w‖^2 + 4) := check_symm_coord_2 w
    have hv0 : ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 0 = 4 * stereo_vec w 0 / (‖w‖^2 + 4) := check_symm_coord_0 w
    have hv1 : ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 1 = 4 * stereo_vec w 1 / (‖w‖^2 + 4) := check_symm_coord_1 w
    have ha_sq : (stereo_vec a 0)^2 + (stereo_vec a 1)^2 = ‖a‖^2 := stereo_vec_norm_sq a
    have h_dot : stereo_vec a 0 * ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 0 +
        stereo_vec a 1 * ((stereo_chart.symm w : CP1) : EuclideanSpace ℝ (Fin 3)) 1 =
        4 * (stereo_vec a 0 * stereo_vec w 0 + stereo_vec a 1 * stereo_vec w 1) / (‖w‖^2 + 4) := by
      rw [hv0, hv1]; ring
    have h_D_eq : D_aff a l (stereo_chart.symm w).1 =
        (1 - (‖w‖^2 - 4) / (‖w‖^2 + 4)) * (4 + ‖a‖^2) +
        4 * l * (4 * (stereo_vec a 0 * stereo_vec w 0 + stereo_vec a 1 * stereo_vec w 1) / (‖w‖^2 + 4)) +
        4 * l^2 * (1 + (‖w‖^2 - 4) / (‖w‖^2 + 4)) := by
      dsimp [D_aff]; rw [ha_sq, hv2, h_dot]
    have h_N2_eq : N2 a l (stereo_chart.symm w).1 =
        (1 - (‖w‖^2 - 4) / (‖w‖^2 + 4)) * (‖a‖^2 - 4) +
        4 * l * (4 * (stereo_vec a 0 * stereo_vec w 0 + stereo_vec a 1 * stereo_vec w 1) / (‖w‖^2 + 4)) +
        4 * l^2 * (1 + (‖w‖^2 - 4) / (‖w‖^2 + 4)) := by
      dsimp [N2]; rw [ha_sq, hv2, h_dot]
    rw [h_D_eq, h_N2_eq, h_m2]
    have h_target_norm : ‖a + (l : ℂ) * w‖^2 = ‖a‖^2 + 2 * l * (stereo_vec a 0 * stereo_vec w 0 + stereo_vec a 1 * stereo_vec w 1) + l^2 * ‖w‖^2 :=
      norm_sq_target a w l
    rw [h_target_norm]; ring

noncomputable def aff_toFun (a : ℂ) (l : ℝ) (z : CP1) : CP1 :=
  open Classical in
  if z = north_pole then north_pole
  else stereo_chart.symm (a + (l : ℂ) * stereo_chart z)

theorem aff_toFun_north_pole (a : ℂ) (l : ℝ) :
    aff_toFun a l north_pole = north_pole := by
  dsimp [aff_toFun]; exact if_pos rfl

theorem aff_toFun_stereo_chart_symm (a : ℂ) (l : ℝ) (w : ℂ) :
    aff_toFun a l (stereo_chart.symm w) = stereo_chart.symm (a + (l : ℂ) * w) := by
  dsimp [aff_toFun]
  have h_ne : stereo_chart.symm w ≠ north_pole := by
    intro h
    have h_source := stereo_chart.map_target (show w ∈ stereo_chart.target by simp [stereo_chart])
    rw [h] at h_source
    dsimp [stereo_chart] at h_source
    simp only [OpenPartialHomeomorph.transHomeomorph_source, stereographic'_source] at h_source
    exact h_source rfl
  rw [if_neg h_ne]
  congr 1
  have hw : stereo_chart (stereo_chart.symm w) = w :=
    stereo_chart.right_inv (show w ∈ stereo_chart.target by simp [stereo_chart])
  rw [hw]

theorem aff_toFun_inv (a : ℂ) (l : ℝ) (hl : 0 < l) (z : CP1) :
    aff_toFun (- ((l⁻¹ : ℝ) : ℂ) * a) l⁻¹ (aff_toFun a l z) = z := by
  by_cases hz : z = north_pole
  · subst hz
    rw [aff_toFun_north_pole, aff_toFun_north_pole]
  · have h_src : z ∈ stereo_chart.source := by
      rw [stereo_chart_source]; exact hz
    have h_in : aff_toFun a l z = stereo_chart.symm (a + (l : ℂ) * stereo_chart z) := by
      dsimp [aff_toFun]; rw [if_neg hz]
    rw [h_in, aff_toFun_stereo_chart_symm]
    have h_inv : ((l⁻¹ : ℝ) : ℂ) * (l : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hl), Complex.ofReal_one]
    have h_alg : - ((l⁻¹ : ℝ) : ℂ) * a + ((l⁻¹ : ℝ) : ℂ) * (a + (l : ℂ) * stereo_chart z) = stereo_chart z := by
      calc - ((l⁻¹ : ℝ) : ℂ) * a + ((l⁻¹ : ℝ) : ℂ) * (a + (l : ℂ) * stereo_chart z)
        _ = (- (((l⁻¹ : ℝ) : ℂ) * a) + ((l⁻¹ : ℝ) : ℂ) * a) + (((l⁻¹ : ℝ) : ℂ) * (l : ℂ)) * stereo_chart z := by ring
        _ = 0 + 1 * stereo_chart z := by rw [neg_add_cancel, h_inv]
        _ = stereo_chart z := by ring
    rw [h_alg]
    exact stereo_chart.left_inv h_src

theorem aff_toFun_right_inv (a : ℂ) (l : ℝ) (hl : 0 < l) (z : CP1) :
    aff_toFun a l (aff_toFun (- ((l⁻¹ : ℝ) : ℂ) * a) l⁻¹ z) = z := by
  have h_inv := aff_toFun_inv (- ((l⁻¹ : ℝ) : ℂ) * a) l⁻¹ (inv_pos.mpr hl) z
  have hl_inv : (((l⁻¹ : ℝ)⁻¹ : ℝ) : ℂ) = (l : ℂ) := by rw [inv_inv]
  have ha_inv : - (((l⁻¹ : ℝ)⁻¹ : ℝ) : ℂ) * (- ((l⁻¹ : ℝ) : ℂ) * a) = a := by
    rw [hl_inv]
    have h1 : (l : ℂ) * ((l⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt hl), Complex.ofReal_one]
    calc - (l : ℂ) * (- ((l⁻¹ : ℝ) : ℂ) * a)
      _ = ((l : ℂ) * ((l⁻¹ : ℝ) : ℂ)) * a := by ring
      _ = 1 * a := by rw [h1]
      _ = a := by ring
  have h_inv_inv : (l⁻¹ : ℝ)⁻¹ = l := inv_inv l
  rw [ha_inv, h_inv_inv] at h_inv
  exact h_inv

theorem aff_toFun_south_pole (a : ℂ) (l : ℝ) :
    aff_toFun a l south_pole = stereo_chart.symm a := by
  dsimp [aff_toFun]
  have h_ne : south_pole ≠ north_pole := south_pole_ne_north_pole
  rw [if_neg h_ne, stereo_chart_south_pole, mul_zero, add_zero]

theorem aff_toFun_south_pole_ne (a : ℂ) (ha : a ≠ 0) :
    aff_toFun a 1 south_pole ≠ south_pole := by
  rw [aff_toFun_south_pole]
  intro h
  have h_chart := congr_arg stereo_chart h
  have h_a_src : a ∈ stereo_chart.target := by simp [stereo_chart]
  rw [stereo_chart.right_inv h_a_src, stereo_chart_south_pole] at h_chart
  exact ha h_chart

theorem aff_toFun_is_moebius (a : ℂ) (l : ℝ) (hl : 0 < l) (z : CP1) :
    cp1ToOnePoint (aff_toFun a l z) = (MoebiusMatrix.affine_scaling a l hl).eval (cp1ToOnePoint z) := by
  by_cases hz : z = north_pole
  · subst hz
    rw [aff_toFun_north_pole]
    dsimp [cp1ToOnePoint]
    rw [if_pos rfl]
    exact (MoebiusMatrix.eval_affine_scaling_infty a l hl).symm
  · dsimp [cp1ToOnePoint]
    have h_ne : aff_toFun a l z ≠ north_pole := by
      intro h_np
      have h_inv := aff_toFun_inv a l hl z
      rw [h_np, aff_toFun_north_pole] at h_inv
      exact hz h_inv.symm
    rw [if_neg hz, if_neg h_ne]
    have h_src : z ∈ stereo_chart.source := by
      rw [stereo_chart_source]; exact hz
    have h_in : aff_toFun a l z = stereo_chart.symm (a + (l : ℂ) * stereo_chart z) := by
      dsimp [aff_toFun]; rw [if_neg hz]
    rw [h_in]
    have hw : stereo_chart (stereo_chart.symm (a + (l : ℂ) * stereo_chart z)) = a + (l : ℂ) * stereo_chart z :=
      stereo_chart.right_inv (show a + (l : ℂ) * stereo_chart z ∈ stereo_chart.target by simp [stereo_chart])
    rw [hw]
    exact (MoebiusMatrix.eval_affine_scaling a l hl (stereo_chart z)).symm

theorem aff_toFun_eq_aff_fun (a : ℂ) (l : ℝ) (hl : 0 < l) (z : CP1) :
    (aff_toFun a l z).1 = aff_fun a l z.1 := by
  by_cases hz : z = north_pole
  · subst hz
    rw [aff_toFun_north_pole]
    exact (aff_fun_north_pole a l hl).symm
  · have h_src : z ∈ stereo_chart.source := by
      rw [stereo_chart_source]; exact hz
    have h_z_symm : z = stereo_chart.symm (stereo_chart z) :=
      (stereo_chart.left_inv h_src).symm
    nth_rw 2 [h_z_symm]
    rw [aff_fun_stereo_chart_symm a l hl (stereo_chart z)]
    dsimp [aff_toFun]; rw [if_neg hz]

theorem continuous_aff_toFun (a : ℂ) (l : ℝ) (hl : 0 < l) :
    Continuous (aff_toFun a l) := by
  have h_eq : (fun (z : CP1) => (aff_toFun a l z).1) = (fun (z : CP1) => aff_fun a l z.1) := by
    funext z; exact aff_toFun_eq_aff_fun a l hl z
  rw [continuous_induced_rng]
  change Continuous (fun z => (aff_toFun a l z).1)
  rw [h_eq]
  exact continuous_aff_fun_on_cp1 a l hl

/-- The authentic stereographic affine scaling homeomorphism $w \mapsto a + \lambda w$. -/
noncomputable def aff_homeo (a : ℂ) (l : ℝ) (hl : 0 < l) : CP1 ≃ₜ CP1 where
  toFun := aff_toFun a l
  invFun := aff_toFun (- ((l⁻¹ : ℝ) : ℂ) * a) l⁻¹
  left_inv := aff_toFun_inv a l hl
  right_inv := aff_toFun_right_inv a l hl
  continuous_toFun := continuous_aff_toFun a l hl
  continuous_invFun := continuous_aff_toFun (- ((l⁻¹ : ℝ) : ℂ) * a) l⁻¹ (inv_pos.mpr hl)

theorem cp1_norm_sq (z : CP1) : (z.1 0)^2 + (z.1 1)^2 + (z.1 2)^2 = 1 := by
  have hz : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  rw [EuclideanSpace.norm_eq] at hz
  have h_pos : 0 ≤ ‖z.1 0‖ ^ 2 + ‖z.1 1‖ ^ 2 + ‖z.1 2‖ ^ 2 := by positivity
  have h_sq := congr_arg (fun x => x^2) hz
  simp only [Fin.sum_univ_three] at h_sq
  rw [Real.sq_sqrt h_pos] at h_sq
  have h_norm_sq (x : ℝ) : ‖x‖ ^ 2 = x ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
  rw [h_norm_sq, h_norm_sq, h_norm_sq] at h_sq
  norm_num at h_sq
  exact h_sq

theorem cp1_D_aff_ne_zero (a : ℂ) (l : ℝ) (hl : 0 < l) (z : CP1) : D_aff a l z.1 ≠ 0 :=
  D_aff_ne_zero a l hl z.1 (cp1_norm_sq z)

theorem aff_toFun_is_smooth (a : ℂ) (l : ℝ) (hl : 0 < l) :
    ContMDiff I_CP1 I_CP1 ∞ (aff_toFun a l) := by
  have h_comp : ContMDiff I_CP1 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (fun (z : CP1) => (aff_toFun a l z).1) := by
    have h_fun_eq : (fun (z : CP1) => (aff_toFun a l z).1) =
        (aff_fun a l ∘ ((↑) : CP1 → EuclideanSpace ℝ (Fin 3))) := by
      funext z; exact aff_toFun_eq_aff_fun a l hl z
    rw [h_fun_eq]
    intro z
    have hD := cp1_D_aff_ne_zero a l hl z
    have hg := contDiffAt_aff_fun a l z.1 hD
    have hf := (contMDiff_coe_sphere (m := ∞) (n := 2)).contMDiffAt (x := z)
    exact hg.comp_contMDiffAt hf
  have h_mem (z : CP1) : (aff_toFun a l z).1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    (aff_toFun a l z).2
  exact ContMDiff.codRestrict_sphere (n := 2) h_comp h_mem

theorem aff_homeo_is_smooth (a : ℂ) (l : ℝ) (hl : 0 < l) :
    ContMDiff I_CP1 I_CP1 ∞ (aff_homeo a l hl) :=
  aff_toFun_is_smooth a l hl

theorem aff_homeo_symm_is_smooth (a : ℂ) (l : ℝ) (hl : 0 < l) :
    ContMDiff I_CP1 I_CP1 ∞ (aff_homeo a l hl).symm :=
  aff_toFun_is_smooth (- ((l⁻¹ : ℝ) : ℂ) * a) l⁻¹ (inv_pos.mpr hl)

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
  /-- Compatibility between the geometric homeomorphism and projective matrix action. -/
  is_moebius : ∀ z : CP1, cp1ToOnePoint (toHomeo z) = matrix.eval (cp1ToOnePoint z)

instance : TopologicalSpace MoebiusFrame := ⊥

instance : DiscreteTopology MoebiusFrame := ⟨rfl⟩

namespace MoebiusFrame

/-- Identity Möbius frame. -/
def id : MoebiusFrame where
  matrix := MoebiusMatrix.id
  toHomeo := Homeomorph.refl CP1
  is_smooth := contMDiff_id
  is_smooth_symm := contMDiff_id
  is_moebius z := by
    change cp1ToOnePoint z = MoebiusMatrix.id.eval (cp1ToOnePoint z)
    exact (MoebiusMatrix.eval_id (cp1ToOnePoint z)).symm

/-- Composition of Möbius frames: $\phi_1 \circ \phi_2$. -/
def comp (ϕ₁ ϕ₂ : MoebiusFrame) : MoebiusFrame where
  matrix := MoebiusMatrix.comp ϕ₁.matrix ϕ₂.matrix
  toHomeo := ϕ₂.toHomeo.trans ϕ₁.toHomeo
  is_smooth := ϕ₁.is_smooth.comp ϕ₂.is_smooth
  is_smooth_symm := ϕ₂.is_smooth_symm.comp ϕ₁.is_smooth_symm
  is_moebius z := by
    change cp1ToOnePoint (ϕ₁.toHomeo (ϕ₂.toHomeo z)) = (MoebiusMatrix.comp ϕ₁.matrix ϕ₂.matrix).eval (cp1ToOnePoint z)
    rw [ϕ₁.is_moebius (ϕ₂.toHomeo z), ϕ₂.is_moebius z, eval_comp]

/-- Inverse Möbius frame: $\phi^{-1}$. -/
def inv (ϕ : MoebiusFrame) : MoebiusFrame where
  matrix := MoebiusMatrix.inv ϕ.matrix
  toHomeo := ϕ.toHomeo.symm
  is_smooth := ϕ.is_smooth_symm
  is_smooth_symm := ϕ.is_smooth
  is_moebius z := by
    have h := ϕ.is_moebius (ϕ.toHomeo.symm z)
    have h_apply : ϕ.toHomeo (ϕ.toHomeo.symm z) = z := ϕ.toHomeo.apply_symm_apply z
    rw [h_apply] at h
    have h_inv := congr_arg (MoebiusMatrix.inv ϕ.matrix).eval h.symm
    rw [eval_inv_eval] at h_inv
    exact h_inv

end MoebiusFrame

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

/-- Groupoid inverse law on homeomorphisms (alias): ϕ⁻¹ ∘ ϕ = id. -/
theorem moebius_frame_inv_comp (ϕ : MoebiusFrame) :
    (MoebiusFrame.comp (MoebiusFrame.inv ϕ) ϕ).toHomeo = MoebiusFrame.id.toHomeo :=
  moebius_frame_inv_comp_toHomeo ϕ

/-- Groupoid inverse law on homeomorphisms (alias): ϕ ∘ ϕ⁻¹ = id. -/
theorem moebius_frame_comp_inv (ϕ : MoebiusFrame) :
    (MoebiusFrame.comp ϕ (MoebiusFrame.inv ϕ)).toHomeo = MoebiusFrame.id.toHomeo :=
  moebius_frame_comp_inv_toHomeo ϕ

namespace MoebiusFrame

theorem comp_id (ϕ : MoebiusFrame) : comp ϕ id = ϕ := moebius_frame_comp_id ϕ
theorem id_comp (ϕ : MoebiusFrame) : comp id ϕ = ϕ := moebius_frame_id_comp ϕ
theorem comp_assoc (ϕ₁ ϕ₂ ϕ₃ : MoebiusFrame) : comp (comp ϕ₁ ϕ₂) ϕ₃ = comp ϕ₁ (comp ϕ₂ ϕ₃) := moebius_frame_comp_assoc ϕ₁ ϕ₂ ϕ₃
theorem inv_comp_toHomeo (ϕ : MoebiusFrame) : (comp (inv ϕ) ϕ).toHomeo = id.toHomeo := moebius_frame_inv_comp_toHomeo ϕ
theorem comp_inv_toHomeo (ϕ : MoebiusFrame) : (comp ϕ (inv ϕ)).toHomeo = id.toHomeo := moebius_frame_comp_inv_toHomeo ϕ
theorem inv_comp (ϕ : MoebiusFrame) : (comp (inv ϕ) ϕ).toHomeo = id.toHomeo := moebius_frame_inv_comp_toHomeo ϕ
theorem comp_inv (ϕ : MoebiusFrame) : (comp ϕ (inv ϕ)).toHomeo = id.toHomeo := moebius_frame_comp_inv_toHomeo ϕ
theorem inv_comp_matrix (ϕ : MoebiusFrame) : PglEquiv (comp (inv ϕ) ϕ).matrix MoebiusMatrix.id := moebius_frame_inv_comp_matrix ϕ
theorem comp_inv_matrix (ϕ : MoebiusFrame) : PglEquiv (comp ϕ (inv ϕ)).matrix MoebiusMatrix.id := moebius_frame_comp_inv_matrix ϕ

end MoebiusFrame

/-- Standard affine scaling $z \mapsto a + \lambda z$ on $\mathbb{C} \subset \mathbb{CP}^1$ for center $a \in \mathbb{C}$
and scaling parameter $\lambda > 0$, implemented via authentic stereographic affine homeomorphism `aff_homeo`. -/
noncomputable def affine_scaling (a : ℂ) (scale : ℝ) (hscale : 0 < scale) : MoebiusFrame where
  matrix := MoebiusMatrix.affine_scaling a scale hscale
  toHomeo := aff_homeo a scale hscale
  is_smooth := aff_homeo_is_smooth a scale hscale
  is_smooth_symm := aff_homeo_symm_is_smooth a scale hscale
  is_moebius := aff_toFun_is_moebius a scale hscale

theorem affine_scaling_north_pole (a : ℂ) (scale : ℝ) (hscale : 0 < scale) :
    (affine_scaling a scale hscale).toHomeo north_pole = north_pole := by
  change aff_toFun a scale north_pole = north_pole
  exact aff_toFun_north_pole a scale

theorem affine_scaling_stereo_chart_symm (a : ℂ) (scale : ℝ) (hscale : 0 < scale) (w : ℂ) :
    (affine_scaling a scale hscale).toHomeo (stereo_chart.symm w) = stereo_chart.symm (a + (scale : ℂ) * w) := by
  change aff_toFun a scale (stereo_chart.symm w) = stereo_chart.symm (a + (scale : ℂ) * w)
  exact aff_toFun_stereo_chart_symm a scale w

theorem affine_scaling_south_pole (a : ℂ) (scale : ℝ) (hscale : 0 < scale) :
    (affine_scaling a scale hscale).toHomeo south_pole = stereo_chart.symm a := by
  change aff_toFun a scale south_pole = stereo_chart.symm a
  exact aff_toFun_south_pole a scale

theorem affine_scaling_south_pole_ne (a : ℂ) (ha : a ≠ 0) :
    (affine_scaling a 1 one_pos).toHomeo south_pole ≠ south_pole := by
  change aff_toFun a 1 south_pole ≠ south_pole
  exact aff_toFun_south_pole_ne a ha

theorem affine_scaling_matrix (a : ℂ) (scale : ℝ) (hscale : 0 < scale) :
    (affine_scaling a scale hscale).matrix = MoebiusMatrix.affine_scaling a scale hscale :=
  rfl

end GromovCompactness
