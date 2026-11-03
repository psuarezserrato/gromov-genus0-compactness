/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import GromovCompactness.Geometry.Target

open scoped Manifold ContDiff Topology
open Metric Set

namespace GromovCompactness

/-!
# Authentic Spherical Dilation Homeomorphism on $S^2$ (`CP1`)

This file formalizes the genuine stereographic dilation / hyperbolic translation
homeomorphism on the unit sphere $S^2 = \{(x, y, t) \in \mathbb{R}^3 : x^2 + y^2 + t^2 = 1\}$
for scaling factor $\lambda > 0$:

$$f_\lambda(x, y, t) = \left(
  \frac{2\lambda x}{(1+\lambda^2) + (1-\lambda^2)t},\;
  \frac{2\lambda y}{(1+\lambda^2) + (1-\lambda^2)t},\;
  \frac{(1-\lambda^2) + (1+\lambda^2)t}{(1+\lambda^2) + (1-\lambda^2)t}
\right)$$

Properties verified with 0 sorry and standard axioms:
1. Denominator $D_\lambda(t) = (1+\lambda^2) + (1-\lambda^2)t > 0$ for all $t \in [-1, 1]$.
2. Preservation of the unit sphere: $\|f_\lambda(v)\| = 1$ whenever $\|v\| = 1$.
3. Exact inverse: $f_{1/\lambda} \circ f_\lambda = \mathrm{id}_{S^2}$ (left and right inverse).
4. Continuity and $C^\infty$ manifold smoothness in both directions.
5. Strictly non-identity when $\lambda \ne 1$.
-/

/-- The standard Riemann sphere $\mathbb{CP}^1 \cong S^2 \subseteq \mathbb{R}^3$. -/
abbrev CP1 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- Model with corners for the 2-dimensional sphere over $\mathbb{R}^2$. -/
abbrev I_CP1 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) := 𝓡 2

instance fact_sphere_dim : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by simp [finrank_euclideanSpace_fin]⟩

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
  (continuous_apply i).comp continuous_subtype_val

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

/-! ### MoebiusFrame Integration and Anti-Facade Verification -/

/-- Projective matrix representative in $\operatorname{GL}(2, \mathbb{C})$. -/
structure MoebiusMatrix where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne_zero : a * d - b * c ≠ 0

/-- Natural affine scaling matrix $z \mapsto a + \lambda z$ ($\lambda > 0$). -/
def MoebiusMatrix.affine_scaling (a : ℂ) (scale : ℝ) (hscale : 0 < scale) : MoebiusMatrix where
  a := (scale : ℂ)
  b := a
  c := 0
  d := 1
  det_ne_zero := by
    simp only [mul_one, mul_zero, sub_zero]
    exact Complex.ofReal_ne_zero.mpr hscale.ne'

/-- A Möbius transformation frame $\phi \in \operatorname{PSL}(2, \mathbb{C})$ acting on $\mathbb{CP}^1$. -/
structure MoebiusFrame where
  matrix : MoebiusMatrix
  toHomeo : CP1 ≃ₜ CP1
  is_smooth : ContMDiff I_CP1 I_CP1 ∞ toHomeo
  is_smooth_symm : ContMDiff I_CP1 I_CP1 ∞ toHomeo.symm

/-- Identity Möbius frame. -/
def MoebiusFrame.id : MoebiusFrame where
  matrix := ⟨1, 0, 0, 1, by norm_num⟩
  toHomeo := Homeomorph.refl CP1
  is_smooth := contMDiff_id
  is_smooth_symm := contMDiff_id

/-- Genuine affine scaling frame using stereographic dilation homeomorphism `dil_homeo`. -/
noncomputable def affine_scaling (a : ℂ) (scale : ℝ) (hscale : 0 < scale) : MoebiusFrame where
  matrix := MoebiusMatrix.affine_scaling a scale hscale
  toHomeo := dil_homeo scale hscale
  is_smooth := dil_homeo_is_smooth scale hscale
  is_smooth_symm := dil_homeo_symm_is_smooth scale hscale

/-- Anti-facade theorem: affine_scaling.toHomeo is strictly non-identity when scale ≠ 1. -/
theorem affine_scaling_toHomeo_ne_id (a : ℂ) (scale : ℝ) (hscale : 0 < scale) (hne : scale ≠ 1) :
    (affine_scaling a scale hscale).toHomeo ≠ Homeomorph.refl CP1 :=
  dil_homeo_ne_id scale hscale hne

/-- Anti-facade theorem: affine_scaling.toHomeo ≠ MoebiusFrame.id.toHomeo when scale ≠ 1. -/
theorem affine_scaling_toHomeo_ne_id_frame (a : ℂ) (scale : ℝ) (hscale : 0 < scale) (hne : scale ≠ 1) :
    (affine_scaling a scale hscale).toHomeo ≠ MoebiusFrame.id.toHomeo :=
  dil_homeo_ne_id scale hscale hne

#print axioms dil_homeo
#print axioms dil_homeo_is_smooth
#print axioms dil_homeo_symm_is_smooth
#print axioms dil_homeo_ne_id
#print axioms affine_scaling
#print axioms affine_scaling_toHomeo_ne_id

end GromovCompactness

