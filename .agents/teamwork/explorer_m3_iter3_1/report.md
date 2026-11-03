# Technical Investigation Report: Genuine Non-Identity Spherical Homeomorphism for `affine_scaling`

**Author**: `explorer_m3_iter3_1`  
**Working Directory**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_iter3_1/`  
**Date**: 2026-11-03  
**Status**: COMPLETE (Zero `sorry`, 100% Type-Checked in Lean 4)  

---

## 1. Executive Summary

In Milestone 3 remediation, the forensic integrity auditor (`teamwork_auditor_m3_rem_1`) and reviewer (`teamwork_reviewer_m3_rem_2`) identified an integrity violation under Prohibited Pattern #2 (Facade Implementation) in `Sphere.lean`:
```lean
noncomputable def affine_scaling (a : ℂ) (scale : ℝ) (hscale : 0 < scale) : MoebiusFrame where
  matrix := MoebiusMatrix.affine_scaling a scale hscale
  toHomeo := Homeomorph.refl CP1
  is_smooth := contMDiff_id
  is_smooth_symm := contMDiff_id
```
Because `toHomeo` was hardcoded to `Homeomorph.refl CP1`, the theorem `(affine_scaling a scale hscale).toHomeo = MoebiusFrame.id.toHomeo` was provable by `rfl`. In Gromov compactness bubbling-off analysis, composition $u \circ \phi.\mathrm{toHomeo}$ was identically $u \circ \mathrm{id} = u$, completely disabling domain dilation on the sphere $S^2$.

This investigation has designed, verified, and machine-checked in Lean 4 a genuine, smooth, non-identity spherical homeomorphism `dil_homeo (scale : ℝ) (hscale : 0 < scale) : CP1 ≃ₜ CP1` that:
1. Replaces `Homeomorph.refl CP1` in `affine_scaling.toHomeo`.
2. Genuinely acts on $S^2$ as hyperbolic translation along the $z$-axis (the conformal dilation conjugate to $z \mapsto \lambda z$ under stereographic projection).
3. Is strictly non-identity for all $\lambda \ne 1$ (proved by theorem `dil_homeo_ne_id`).
4. Is proved $C^\infty$ smooth in both directions using standard Mathlib manifold tools (`ContMDiff.codRestrict_sphere`).
5. Compiles cleanly with **zero `sorry`** and depends strictly on standard foundational axioms `[propext, Classical.choice, Quot.sound]`.

The complete working formulation is type-checked and available in `Scratch.lean`.

---

## 2. Mathematical Analysis of the Stereographic Dilation $f_\lambda$

### 2.1 The Coordinate Formula
Let $S^2 = \{(x, y, t) \in \mathbb{R}^3 : x^2 + y^2 + t^2 = 1\}$. For any scaling factor $\lambda > 0$, the spherical dilation map $f_\lambda : S^2 \to S^2$ is defined by:
$$f_\lambda(x, y, t) = \left(
  \frac{2\lambda x}{(1+\lambda^2) + (1-\lambda^2)t},\;
  \frac{2\lambda y}{(1+\lambda^2) + (1-\lambda^2)t},\;
  \frac{(1-\lambda^2) + (1+\lambda^2)t}{(1+\lambda^2) + (1-\lambda^2)t}
\right)$$

### 2.2 Strict Positivity of the Denominator $D_\lambda(t)$
The denominator is:
$$D_\lambda(t) = (1+\lambda^2) + (1-\lambda^2)t$$
Rewriting as an affine combination of the endpoints $t \in [-1, 1]$:
$$D_\lambda(t) = (1 - t)\lambda^2 + (1 + t)$$
For any $t \in [-1, 1]$:
- If $t = -1$: $D_\lambda(-1) = 2\lambda^2 > 0$ (since $\lambda > 0$).
- If $t = 1$: $D_\lambda(1) = 2 > 0$.
- If $-1 < t \le 1$: $1 - t \ge 0$ and $1 + t > 0$, so $(1 - t)\lambda^2 + (1 + t) > 0$.

Thus, $D_\lambda(t) \ge \min(2, 2\lambda^2) > 0$ strictly for all $t \in [-1, 1]$. In particular, $D_\lambda(z_2) \ne 0$ for all $z \in S^2$.

### 2.3 Preservation of the Unit Sphere ($\|f_\lambda(x, y, t)\|^2 = 1$)
Let $(x', y', t') = f_\lambda(x, y, t)$. We calculate the sum of squares of the numerators:
$$N = (2\lambda x)^2 + (2\lambda y)^2 + \big((1-\lambda^2) + (1+\lambda^2)t\big)^2$$
Since $x^2 + y^2 + t^2 = 1$, we substitute $x^2 + y^2 = 1 - t^2$:
$$N = 4\lambda^2(1 - t^2) + (1 - \lambda^2)^2 + 2(1 - \lambda^4)t + (1 + \lambda^2)^2 t^2$$
Expanding and collecting powers of $t$:
- $t^0$ term: $4\lambda^2 + (1 - 2\lambda^2 + \lambda^4) = 1 + 2\lambda^2 + \lambda^4 = (1 + \lambda^2)^2$.
- $t^1$ term: $2(1 - \lambda^4)t = 2(1 + \lambda^2)(1 - \lambda^2)t$.
- $t^2$ term: $-4\lambda^2 + (1 + 2\lambda^2 + \lambda^4) = 1 - 2\lambda^2 + \lambda^4 = (1 - \lambda^2)^2$.

Hence:
$$N = (1 + \lambda^2)^2 + 2(1 + \lambda^2)(1 - \lambda^2)t + (1 - \lambda^2)^2 t^2 = \big((1 + \lambda^2) + (1 - \lambda^2)t\big)^2 = D_\lambda(t)^2$$
Since $D_\lambda(t) > 0$, dividing by $D_\lambda(t)^2$ gives:
$$(x')^2 + (y')^2 + (t')^2 = \frac{D_\lambda(t)^2}{D_\lambda(t)^2} = 1$$
This is an exact algebraic identity.

### 2.4 Exact Inverse Property ($f_{1/\lambda} \circ f_\lambda = \mathrm{id}$)
Let $(x', y', t') = f_\lambda(x, y, t)$. When we apply $f_{1/\lambda}$ to $(x', y', t')$, the denominator is $D_{1/\lambda}(t')$.
A crucial algebraic discovery:
$$D_\lambda(t) \cdot D_{1/\lambda}(t') = D_\lambda(t) \cdot \left((1 + \lambda^{-2}) + (1 - \lambda^{-2}) \frac{(1-\lambda^2) + (1+\lambda^2)t}{D_\lambda(t)}\right)$$
$$= (1 + \lambda^{-2}) D_\lambda(t) + (1 - \lambda^{-2})\big((1-\lambda^2) + (1+\lambda^2)t\big)$$
$$= (1 + \lambda^{-2})(1 + \lambda^2) + (1 - \lambda^{-2})(1 - \lambda^2) + \big[(1 + \lambda^{-2})(1 - \lambda^2) + (1 - \lambda^{-2})(1 + \lambda^2)\big]t$$
Evaluating the coefficients:
- Constant term: $(1 + \lambda^2 + \lambda^{-2} + 1) + (1 - \lambda^2 - \lambda^{-2} + 1) = 4$.
- Coefficient of $t$: $(1 - \lambda^2 + \lambda^{-2} - 1) + (1 + \lambda^2 - \lambda^{-2} - 1) = 0$.

Therefore, **identically for all $t$ and all $\lambda \ne 0$**:
$$D_\lambda(t) \cdot D_{1/\lambda}(t') = 4$$
Evaluating the coordinates of $f_{1/\lambda}(x', y', t')$:
- Coordinate 0:
  $$\frac{2\lambda^{-1} x'}{D_{1/\lambda}(t')} = \frac{2\lambda^{-1} \frac{2\lambda x}{D_\lambda(t)}}{D_{1/\lambda}(t')} = \frac{4 x}{D_\lambda(t) D_{1/\lambda}(t')} = \frac{4 x}{4} = x$$
- Coordinate 1:
  $$\frac{2\lambda^{-1} y'}{D_{1/\lambda}(t')} = \frac{4 y}{4} = y$$
- Coordinate 2:
  The numerator multiplied by $D_\lambda(t)$ is $(1 - \lambda^{-2}) D_\lambda(t) + (1 + \lambda^{-2})\big((1-\lambda^2) + (1+\lambda^2)t\big) = 4t$.
  Dividing by $4$ yields $t$.

Thus $f_{1/\lambda}(f_\lambda(v)) = v$ unconditionally for all $v \in \mathbb{R}^3$ with $D_\lambda(v_2) \ne 0$.

### 2.5 Strict Non-Identity When $\lambda \ne 1$
Evaluate $f_\lambda$ at the equatorial point $P = (1, 0, 0) \in S^2$ (where $t = 0$):
$$f_\lambda(1, 0, 0) = \left(\frac{2\lambda}{1+\lambda^2},\; 0,\; \frac{1-\lambda^2}{1+\lambda^2}\right)$$
If $f_\lambda(1, 0, 0) = (1, 0, 0)$, then the third coordinate must be zero:
$$\frac{1-\lambda^2}{1+\lambda^2} = 0 \implies 1 - \lambda^2 = 0 \implies \lambda = 1 \quad (\text{since } \lambda > 0)$$
Thus, for any $\lambda \ne 1$, $f_\lambda(1, 0, 0) \ne (1, 0, 0)$, so $f_\lambda \ne \mathrm{id}_{S^2}$.

---

## 3. Lean 4 Formalization Architecture

The complete formalization is implemented in `Scratch.lean`. Below is the architectural walkthrough:

### 3.1 Foundational Lemmas
1. `D_val_pos (l : ℝ) (hl : 0 < l) (t : ℝ) (ht1 : -1 ≤ t) (ht2 : t ≤ 1) : 0 < D_val l t`
   - Proved via `ring` decomposition into $(1-t)l^2 + (1+t)$ and case analysis on $t = -1$.
2. `cp1_coord_two_bounds (z : CP1) : -1 ≤ z.1 2 ∧ z.1 2 ≤ 1`
   - Derived from `‖z.1‖ = 1` using `EuclideanSpace.norm_eq` and `sq_le_one_iff_abs_le_one`.
3. `cp1_D_val_pos` and `cp1_D_val_ne_zero`
   - Unconditional positivity of denominator on `CP1`.

### 3.2 Mapping and Inverses
1. `dil_fun (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3)`
   - Computes $f_\lambda(v)$.
2. `dil_denom_mul (l : ℝ) (hl : l ≠ 0) (t : ℝ) (hD : D_val l t ≠ 0) : D_val l t * D_val l⁻¹ (...) = 4`
   - Proved in 5 lines via `field_simp; ring`.
3. `dil_fun_inv_apply (l : ℝ) (hl : l ≠ 0) (v : EuclideanSpace ℝ (Fin 3)) (hD : D_val l (v 2) ≠ 0) : dil_fun l⁻¹ (dil_fun l v) = v`
   - Proved for each coordinate via `div_div_div_comm` and cancellation with 4.

### 3.3 Sphere Preservation and Homeomorphism
1. `dil_fun_norm_sq` and `dil_fun_norm`
   - Proves `‖dil_fun l v‖ = 1` for all $v \in S^2$ via `linear_combination 4 * l^2 * hv`.
2. `continuous_dil_fun_on_cp1 (l : ℝ) (hl : 0 < l) : Continuous (fun z : CP1 => dil_fun l z.1)`
   - Proved coordinate-wise using `Continuous.div` and `continuous_cp1_coord`.
3. `dil_homeo (l : ℝ) (hl : 0 < l) : CP1 ≃ₜ CP1`
   - Constructed as a `Homeomorph` with `toFun`, `invFun`, `left_inv`, `right_inv`, `continuous_toFun`, `continuous_invFun` all verified.
4. `dil_homeo_ne_id (l : ℝ) (hl : 0 < l) (hne : l ≠ 1) : dil_homeo l hl ≠ Homeomorph.refl CP1`
   - Proved by evaluation at `!₂[1, 0, 0]`.

### 3.4 Smooth Manifold Extension (`ContMDiff`)
Smoothness on manifolds is typically the hardest hurdle. We established it cleanly:
1. `contDiffAt_euclidean_coord (i : Fin 3) (v : EuclideanSpace ℝ (Fin 3)) : ContDiffAt ℝ ∞ (fun x => x i) v`
   - Directly from `(EuclideanSpace.proj i).contDiff.contDiffAt`.
2. `contDiffAt_dil_fun (l : ℝ) (v : EuclideanSpace ℝ (Fin 3)) (hD : D_val l (v 2) ≠ 0) : ContDiffAt ℝ ∞ (dil_fun l) v`
   - Proved via `EuclideanSpace.equiv (Fin 3) ℝ`, `contDiffAt_pi`, and `ContDiffAt.div`.
3. `dil_homeo_is_smooth (l : ℝ) (hl : 0 < l) : ContMDiff I_CP1 I_CP1 ∞ (dil_homeo l hl)`
   - Connects local smoothness on the ambient space to the manifold:
     - For any $z \in \mathrm{CP1}$, $hg = \mathrm{contDiffAt\_dil\_fun}$ and $hf = \mathrm{contMDiff\_coe\_sphere.contMDiffAt}$.
     - `hg.comp_contMDiffAt hf` establishes ambient smoothness of `dil_fun l ∘ coe`.
     - `ContMDiff.codRestrict_sphere (n := 2)` restricts the codomain to `CP1`.
4. `dil_homeo_symm_is_smooth (l : ℝ) (hl : 0 < l) : ContMDiff I_CP1 I_CP1 ∞ (dil_homeo l hl).symm`
   - Immediate by evaluating `dil_homeo_is_smooth l⁻¹ (inv_pos.mpr hl)`.

### 3.5 MoebiusFrame Integration
```lean
noncomputable def affine_scaling (a : ℂ) (scale : ℝ) (hscale : 0 < scale) : MoebiusFrame where
  matrix := MoebiusMatrix.affine_scaling a scale hscale
  toHomeo := dil_homeo scale hscale
  is_smooth := dil_homeo_is_smooth scale hscale
  is_smooth_symm := dil_homeo_symm_is_smooth scale hscale

theorem affine_scaling_toHomeo_ne_id (a : ℂ) (scale : ℝ) (hscale : 0 < scale) (hne : scale ≠ 1) :
    (affine_scaling a scale hscale).toHomeo ≠ Homeomorph.refl CP1 :=
  dil_homeo_ne_id scale hscale hne
```

---

## 4. Verification and Evidence

### 4.1 Lake Compilation
```bash
$ lake env lean .agents/teamwork/explorer_m3_iter3_1/Scratch.lean
# Exit code: 0 (clean compilation, zero warnings, zero errors)
```

### 4.2 Static Checks
```bash
$ grep -nE "(sorry|admit|axiom )" .agents/teamwork/explorer_m3_iter3_1/Scratch.lean
# Result: 0 matches in code (only occurrence is line 30 comment "0 sorry")
```

### 4.3 Axiom Forensics (`#print axioms`)
All declarations depend exclusively on standard foundational axioms:
```
'GromovCompactness.dil_homeo' depends on axioms: [propext, Classical.choice, Quot.sound]
'GromovCompactness.dil_homeo_is_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'GromovCompactness.dil_homeo_symm_is_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'GromovCompactness.dil_homeo_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'GromovCompactness.affine_scaling' depends on axioms: [propext, Classical.choice, Quot.sound]
'GromovCompactness.affine_scaling_toHomeo_ne_id' depends on axioms: [propext, Classical.choice, Quot.sound]
```

---

## 5. Instructions for Implementation Worker

To resolve the forensic audit violation in `GromovCompactness/Geometry/Sphere.lean`:
1. Add the import:
   ```lean
   import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
   ```
2. Insert lines 43–354 from `Scratch.lean` into `Sphere.lean` right before the `MoebiusFrame` structure definition.
3. In `noncomputable def affine_scaling (a : ℂ) (scale : ℝ) (hscale : 0 < scale) : MoebiusFrame`:
   Replace:
   ```lean
     toHomeo := Homeomorph.refl CP1
     is_smooth := contMDiff_id
     is_smooth_symm := contMDiff_id
   ```
   With:
   ```lean
     toHomeo := dil_homeo scale hscale
     is_smooth := dil_homeo_is_smooth scale hscale
     is_smooth_symm := dil_homeo_symm_is_smooth scale hscale
   ```
4. Add the anti-facade lemma:
   ```lean
   theorem affine_scaling_toHomeo_ne_id (a : ℂ) (scale : ℝ) (hscale : 0 < scale) (hne : scale ≠ 1) :
       (affine_scaling a scale hscale).toHomeo ≠ Homeomorph.refl CP1 :=
     dil_homeo_ne_id scale hscale hne
   ```
5. Run `lake build GromovCompactness.Geometry.Sphere` to confirm zero errors.
