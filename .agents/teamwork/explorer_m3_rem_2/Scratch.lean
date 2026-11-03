import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

structure MoebiusMat where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

def MoebiusMat.mul (M N : MoebiusMat) : MoebiusMat where
  a := M.a * N.a + M.b * N.c
  b := M.a * N.b + M.b * N.d
  c := M.c * N.a + M.d * N.c
  d := M.c * N.b + M.d * N.d
  det_ne_zero := by
    have h_det : (M.a * N.a + M.b * N.c) * (M.c * N.b + M.d * N.d) -
                 (M.a * N.b + M.b * N.d) * (M.c * N.a + M.d * N.c) =
                 (M.a * M.d - M.b * M.c) * (N.a * N.d - N.b * N.c) := by ring
    rw [h_det]
    exact mul_ne_zero M.det_ne_zero N.det_ne_zero

def MoebiusMat.adj (M : MoebiusMat) : MoebiusMat where
  a := M.d
  b := -M.b
  c := -M.c
  d := M.a
  det_ne_zero := by
    have h_det : M.d * M.a - (-M.b) * (-M.c) = M.a * M.d - M.b * M.c := by ring
    rw [h_det]
    exact M.det_ne_zero

def cross_ratio_mat (z₁ z₂ z₃ : ℂ)
    (h12 : z₁ ≠ z₂) (h23 : z₂ ≠ z₃) (h13 : z₁ ≠ z₃) : MoebiusMat where
  a := z₂ - z₃
  b := -z₁ * (z₂ - z₃)
  c := z₂ - z₁
  d := -z₃ * (z₂ - z₁)
  det_ne_zero := by
    have h_det : (z₂ - z₃) * (-z₃ * (z₂ - z₁)) - (-z₁ * (z₂ - z₃)) * (z₂ - z₁) =
      (z₂ - z₃) * (z₂ - z₁) * (z₁ - z₃) := by ring
    rw [h_det]
    have hz23 : z₂ - z₃ ≠ 0 := sub_ne_zero.mpr h23
    have hz21 : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
    have hz13 : z₁ - z₃ ≠ 0 := sub_ne_zero.mpr h13
    exact mul_ne_zero (mul_ne_zero hz23 hz21) hz13

/-- Action of MoebiusMat on homogeneous coordinate (x, y). -/
def MoebiusMat.act (M : MoebiusMat) (p : ℂ × ℂ) : ℂ × ℂ :=
  (M.a * p.1 + M.b * p.2, M.c * p.1 + M.d * p.2)

/-- Equivalence of homogeneous coordinates (proportionality). -/
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
      intro h
      exact hq (Prod.ext hq1 h)
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

lemma act_comp (M N : MoebiusMat) (p : ℂ × ℂ) :
    (M.mul N).act p = M.act (N.act p) := by
  dsimp [MoebiusMat.mul, MoebiusMat.act]
  ext <;> ring

lemma act_adj_cancel (M : MoebiusMat) (p : ℂ × ℂ) :
    ProjEquiv (M.adj.act (M.act p)) p := by
  dsimp [MoebiusMat.adj, MoebiusMat.act, ProjEquiv]
  have h_det : (M.d * (M.a * p.1 + M.b * p.2) + -M.b * (M.c * p.1 + M.d * p.2)) =
               (M.a * M.d - M.b * M.c) * p.1 := by ring
  have h_den : (-M.c * (M.a * p.1 + M.b * p.2) + M.a * (M.c * p.1 + M.d * p.2)) =
               (M.a * M.d - M.b * M.c) * p.2 := by ring
  rw [h_det, h_den]
  ring

/-- The three-point mapping matrix sending z₁, z₂, z₃ to w₁, w₂, w₃. -/
def three_point_mat (z₁ z₂ z₃ w₁ w₂ w₃ : ℂ)
    (hz12 : z₁ ≠ z₂) (hz23 : z₂ ≠ z₃) (hz13 : z₁ ≠ z₃)
    (hw12 : w₁ ≠ w₂) (hw23 : w₂ ≠ w₃) (hw13 : w₁ ≠ w₃) : MoebiusMat :=
  (cross_ratio_mat w₁ w₂ w₃ hw12 hw23 hw13).adj.mul
  (cross_ratio_mat z₁ z₂ z₃ hz12 hz23 hz13)
theorem three_point_mat_eval_1 (z₁ z₂ z₃ w₁ w₂ w₃ : ℂ)
    (hz12 : z₁ ≠ z₂) (hz23 : z₂ ≠ z₃) (hz13 : z₁ ≠ z₃)
    (hw12 : w₁ ≠ w₂) (hw23 : w₂ ≠ w₃) (hw13 : w₁ ≠ w₃) :
    let M := three_point_mat z₁ z₂ z₃ w₁ w₂ w₃ hz12 hz23 hz13 hw12 hw23 hw13
    ProjEquiv (M.act (z₁, 1)) (w₁, 1) := by
  dsimp [three_point_mat, MoebiusMat.mul, MoebiusMat.adj, cross_ratio_mat, MoebiusMat.act, ProjEquiv]
  ring

theorem three_point_mat_eval_2 (z₁ z₂ z₃ w₁ w₂ w₃ : ℂ)
    (hz12 : z₁ ≠ z₂) (hz23 : z₂ ≠ z₃) (hz13 : z₁ ≠ z₃)
    (hw12 : w₁ ≠ w₂) (hw23 : w₂ ≠ w₃) (hw13 : w₁ ≠ w₃) :
    let M := three_point_mat z₁ z₂ z₃ w₁ w₂ w₃ hz12 hz23 hz13 hw12 hw23 hw13
    ProjEquiv (M.act (z₂, 1)) (w₂, 1) := by
  dsimp [three_point_mat, MoebiusMat.mul, MoebiusMat.adj, cross_ratio_mat, MoebiusMat.act, ProjEquiv]
  ring

theorem three_point_mat_eval_3 (z₁ z₂ z₃ w₁ w₂ w₃ : ℂ)
    (hz12 : z₁ ≠ z₂) (hz23 : z₂ ≠ z₃) (hz13 : z₁ ≠ z₃)
    (hw12 : w₁ ≠ w₂) (hw23 : w₂ ≠ w₃) (hw13 : w₁ ≠ w₃) :
    let M := three_point_mat z₁ z₂ z₃ w₁ w₂ w₃ hz12 hz23 hz13 hw12 hw23 hw13
    ProjEquiv (M.act (z₃, 1)) (w₃, 1) := by
  dsimp [three_point_mat, MoebiusMat.mul, MoebiusMat.adj, cross_ratio_mat, MoebiusMat.act, ProjEquiv]
  ring
lemma moebius_fix_three_standard (M : MoebiusMat)
    (h0 : ProjEquiv (M.act (0, 1)) (0, 1))
    (h1 : ProjEquiv (M.act (1, 1)) (1, 1))
    (hinf : ProjEquiv (M.act (1, 0)) (1, 0))
    (p : ℂ × ℂ) :
    ProjEquiv (M.act p) p := by
  dsimp [MoebiusMat.act, ProjEquiv] at *
  -- h0 : (M.a * 0 + M.b * 1) * 1 = (M.c * 0 + M.d * 1) * 0 => M.b = 0
  have hb : M.b = 0 := by
    linear_combination h0
  -- hinf : (M.a * 1 + M.b * 0) * 0 = (M.c * 1 + M.d * 0) * 1 => M.c = 0
  have hc : M.c = 0 := by
    linear_combination -hinf
  have had : M.a = M.d := by
    linear_combination h1 - hb + hc
  linear_combination p.2^2 * hb - p.1^2 * hc + (p.1 * p.2) * had
/-- Canonical frame matrix sending the standard frame [1:0], [0:1], [1:1]
to three pairwise distinct projective points v₁, v₂, v₃ in ℂ² (homogeneous coordinates). -/
def frame_mat (v₁ v₂ v₃ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h23 : ¬ ProjEquiv v₂ v₃) (h13 : ¬ ProjEquiv v₁ v₃) : MoebiusMat where
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
      intro h
      have : ProjEquiv v₂ v₃ := by
        dsimp [ProjEquiv]
        linear_combination -h
      exact h23 this
    have hC2 : v₁.1 * v₃.2 - v₁.2 * v₃.1 ≠ 0 := by
      intro h
      have : ProjEquiv v₁ v₃ := by
        dsimp [ProjEquiv]
        linear_combination h
      exact h13 this
    have hΔ : v₁.1 * v₂.2 - v₁.2 * v₂.1 ≠ 0 := by
      intro h
      have : ProjEquiv v₁ v₂ := by
        dsimp [ProjEquiv]
        linear_combination h
      exact h12 this
    exact mul_ne_zero (mul_ne_zero hC1 hC2) hΔ

theorem frame_mat_eval_1 (v₁ v₂ v₃ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h23 : ¬ ProjEquiv v₂ v₃) (h13 : ¬ ProjEquiv v₁ v₃) :
    let M := frame_mat v₁ v₂ v₃ h12 h23 h13
    ProjEquiv (M.act (1, 0)) v₁ := by
  dsimp [frame_mat, MoebiusMat.act, ProjEquiv]
  ring

theorem frame_mat_eval_2 (v₁ v₂ v₃ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h23 : ¬ ProjEquiv v₂ v₃) (h13 : ¬ ProjEquiv v₁ v₃) :
    let M := frame_mat v₁ v₂ v₃ h12 h23 h13
    ProjEquiv (M.act (0, 1)) v₂ := by
  dsimp [frame_mat, MoebiusMat.act, ProjEquiv]
  ring

theorem frame_mat_eval_3 (v₁ v₂ v₃ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h23 : ¬ ProjEquiv v₂ v₃) (h13 : ¬ ProjEquiv v₁ v₃) :
    let M := frame_mat v₁ v₂ v₃ h12 h23 h13
    ProjEquiv (M.act (1, 1)) v₃ := by
  dsimp [frame_mat, MoebiusMat.act, ProjEquiv]
  ring
/-- Full 3-point transitivity matrix for any two triples of distinct projective points in ℂ². -/
def general_three_point_mat (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃) : MoebiusMat :=
  (frame_mat w₁ w₂ w₃ hw12 hw23 hw13).mul
  (frame_mat v₁ v₂ v₃ hv12 hv23 hv13).adj

theorem general_three_point_eval_1 (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃) :
    let M := general_three_point_mat v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13
    ProjEquiv (M.act v₁) w₁ := by
  dsimp [general_three_point_mat, frame_mat, MoebiusMat.mul, MoebiusMat.adj, MoebiusMat.act, ProjEquiv]
  ring

theorem general_three_point_eval_2 (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃) :
    let M := general_three_point_mat v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13
    ProjEquiv (M.act v₂) w₂ := by
  dsimp [general_three_point_mat, frame_mat, MoebiusMat.mul, MoebiusMat.adj, MoebiusMat.act, ProjEquiv]
  ring

theorem general_three_point_eval_3 (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
    (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
    (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃) :
    let M := general_three_point_mat v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13
    ProjEquiv (M.act v₃) w₃ := by
  dsimp [general_three_point_mat, frame_mat, MoebiusMat.mul, MoebiusMat.adj, MoebiusMat.act, ProjEquiv]
  ring
/-- Equivalence of Moebius matrices in PGL(2, ℂ): they act identically on all projective points. -/
def PglEquiv (M N : MoebiusMat) : Prop :=
  ∀ p : ℂ × ℂ, ProjEquiv (M.act p) (N.act p)

lemma PglEquiv.refl (M : MoebiusMat) : PglEquiv M M :=
  fun p => ProjEquiv.refl (M.act p)

lemma PglEquiv.symm {M N : MoebiusMat} (h : PglEquiv M N) : PglEquiv N M :=
  fun p => ProjEquiv.symm (h p)
open Metric

/-- Rotation matrix around the x₂-axis (polar axis) by angle θ on ℝ³. -/
noncomputable def rot_z_map (θ : ℝ) : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearMap.pi fun i =>
    match i with
    | 0 => (Real.cos θ) • ContinuousLinearMap.proj 0 - (Real.sin θ) • ContinuousLinearMap.proj 1
    | 1 => (Real.sin θ) • ContinuousLinearMap.proj 0 + (Real.cos θ) • ContinuousLinearMap.proj 1
    | 2 => ContinuousLinearMap.proj 2

/-- Inversion map on ℝ³ (180° rotation around x₀ axis: (x₀, x₁, x₂) ↦ (x₀, -x₁, -x₂)).
This corresponds precisely to stereographic inversion z ↦ 1/z. -/
noncomputable def inversion_map : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearMap.pi fun i =>
    match i with
    | 0 => ContinuousLinearMap.proj 0
    | 1 => -ContinuousLinearMap.proj 1
    | 2 => -ContinuousLinearMap.proj 2
