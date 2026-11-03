# Technical Investigation Report: `MoebiusFrame` Structure, Conformal Generators, and Groupoid Laws in `Sphere.lean`

**Author**: `explorer_m3_iter3_2` (teamwork_explorer)  
**Working Directory**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_iter3_2/`  
**Reference Codebase**: `GromovCompactness/Geometry/Sphere.lean` (F02), `Analysis/Energy.lean` (F03), `Topology/SmoothLocal.lean` (F04)  
**Verification Harness**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_iter3_2/VerifyMoebiusFrame.lean`  
**Date**: 2026-11-03  

---

## 1. Executive Summary

This investigation analyzes the architecture, integrity status, and downstream integration requirements of `MoebiusFrame` in `GromovCompactness/Geometry/Sphere.lean`. Our findings are summarized as follows:

1. **Forensic Confirmation of Auditor Finding 1 & Reviewer 2 Finding 1**:
   In `Sphere.lean` lines 742–746, `affine_scaling` contains a persistent facade implementation under Prohibited Pattern #2. While its `matrix` field is correctly populated with `MoebiusMatrix.affine_scaling a scale hscale`, its geometric spherical homeomorphism field `toHomeo` is hardcoded as `Homeomorph.refl CP1`. As a consequence, `(affine_scaling a scale hscale).toHomeo` is definitionally identical to `MoebiusFrame.id.toHomeo` (provable by `rfl`). This discards the center $a \in \mathbb{C}$ and scaling parameter $\lambda > 0$, causing reparametrizations $u \circ \phi.\mathrm{toHomeo}$ to evaluate to $u \circ \mathrm{id} = u$, which fatally disables domain zooming in Hofer rescaling and bubble extraction.
2. **Authenticity of `inversion` and `rotation`**:
   In contrast to `affine_scaling`, `inversion` and `rotation θ` are mathematically genuine and authentic:
   - `inversion.toHomeo := inv_homeo` implements the $\mathrm{SO}(3)$ reflection/rotation $(x, y, t) \mapsto (x, -y, -t)$, which rigorously interchanges north and south poles ($1/0 = \infty$, $1/\infty = 0$) and corresponds to $z \mapsto 1/z$ under stereographic projection. It is proved smooth via `ContMDiff.codRestrict_sphere` and non-identity (`inv_homeo_ne_id`).
   - `rotation θ .toHomeo := rot_homeo θ` implements the genuine $\mathrm{SO}(3)$ rotation around the $z$-axis by angle $\theta$, preserving the sphere and fixing both poles, matching $z \mapsto e^{i\theta} z$. It is proved smooth via `ContMDiff.codRestrict_sphere`.
3. **Architectural Root Cause**:
   The `MoebiusFrame` structure lacks a semantic compatibility invariant between `matrix` and `toHomeo`. Because `toHomeo` was unconstrained by `matrix`, the typechecker accepted pairing a non-trivial projective matrix with a dummy identity homeomorphism.
4. **Authentic Spherical Action of Affine Scaling**:
   We have derived the closed-form rational algebraic transformation on $S^2 \subset \mathbb{R}^3$ for the general affine scaling $z \mapsto a + s z$ ($s > 0, a = a_1 + i a_2 \in \mathbb{C}$):
   $$x' = \frac{2(a_1(1-t) + s x)}{D},\quad y' = \frac{2(a_2(1-t) + s y)}{D},\quad t' = \frac{D - 2(1-t)}{D}$$
   where $D(x, y, t) = |a|^2(1-t) + 2s(a_1 x + a_2 y) + s^2(1+t) + (1-t) > 0$.
   In `VerifyMoebiusFrame.lean`, we proved with zero `sorry` that $(x')^2 + (y')^2 + (t')^2 = 1$ identically on the unit sphere via `linear_combination 4 * s^2 * h_sq`.
5. **Machine-Checked Groupoid Identity Theorems (Reviewer 2 Finding 3)**:
   We formulated and machine-checked all 5 groupoid laws for `MoebiusFrame` with zero `sorry` in Lean 4:
   - `moebius_frame_comp_id : MoebiusFrame.comp ϕ MoebiusFrame.id = ϕ`
   - `moebius_frame_id_comp : MoebiusFrame.comp MoebiusFrame.id ϕ = ϕ`
   - `moebius_frame_comp_assoc : MoebiusFrame.comp (MoebiusFrame.comp ϕ₁ ϕ₂) ϕ₃ = MoebiusFrame.comp ϕ₁ (MoebiusFrame.comp ϕ₂ ϕ₃)`
   - `moebius_frame_inv_comp_toHomeo : (MoebiusFrame.comp (MoebiusFrame.inv ϕ) ϕ).toHomeo = MoebiusFrame.id.toHomeo`
   - `moebius_frame_comp_inv_toHomeo : (MoebiusFrame.comp ϕ (MoebiusFrame.inv ϕ)).toHomeo = MoebiusFrame.id.toHomeo`
   - `moebius_frame_inv_comp_matrix : PglEquiv (MoebiusFrame.comp (MoebiusFrame.inv ϕ) ϕ).matrix MoebiusMatrix.id`
   - `moebius_frame_comp_inv_matrix : PglEquiv (MoebiusFrame.comp ϕ (MoebiusFrame.inv ϕ)).matrix MoebiusMatrix.id`
   along with extensionality principles `MoebiusMatrix.ext` and `MoebiusFrame.ext`.
6. **Downstream Integration Assessment**:
   Downstream modules (`Analysis/Energy.lean` and `Topology/SmoothLocal.lean`) interact with `MoebiusFrame` strictly through `ϕ.toHomeo : CP1 ≃ₜ CP1` and the induced topology. They do not depend on internal matrix fields, but require groupoid rewrite lemmas to perform inverse cancellations during conformal energy change of variables and chain-rule limit calculations.

---

## 2. Review of Prior Findings

### 2.1 Auditor Finding 1 (Forensic Audit Report)
- **Observation**: Lines 742–746 of `Sphere.lean`:
  ```lean
  noncomputable def affine_scaling (a : ℂ) (scale : ℝ) (hscale : 0 < scale) : MoebiusFrame where
    matrix := MoebiusMatrix.affine_scaling a scale hscale
    toHomeo := Homeomorph.refl CP1
    is_smooth := contMDiff_id
    is_smooth_symm := contMDiff_id
  ```
- **Analysis**: The geometric spherical action is completely severed from the algebraic matrix. The parameters $a$ and `scale` are discarded.
- **Empirical Check**:
  ```lean
  theorem affine_scaling_is_id_toHomeo (a : ℂ) (scale : ℝ) (hscale : 0 < scale) :
      (affine_scaling a scale hscale).toHomeo = MoebiusFrame.id.toHomeo := rfl
  ```
  holds definitionally.
- **Impact**: In Gromov bubbling analysis, zooming into a singularity $z_0$ requires reparametrization $u \circ \phi_n$ with $\phi_n = \operatorname{affine\_scaling}(z_n, \lambda_n)$ where $\lambda_n \to 0$. Because $\phi_n.\mathrm{toHomeo} = \mathrm{id}$, $u \circ \phi_n = u$, collapsing the renormalization scheme.

### 2.2 Reviewer 2 Finding 1 (Critical Facade in `affine_scaling`)
- Corroborates Auditor Finding 1.
- Identifies that while `inversion` and `rotation` were upgraded to genuine $\mathrm{SO}(3)$ homeomorphisms in Iteration 2, `affine_scaling` was left as `Homeomorph.refl CP1`.
- Notes that tests like `challenge_affine_scaling_fixes_all` in `tests/ChallengeGeometry.lean` still pass definitionally on the codebase.

### 2.3 Reviewer 2 Finding 3 (Missing Groupoid Rewrite Lemmas)
- Lines 677–700 define `MoebiusFrame.id`, `MoebiusFrame.comp`, and `MoebiusFrame.inv`, but no rewrite lemmas (`comp_assoc`, `comp_id`, `id_comp`, `comp_inv`, `inv_comp`) were provided.
- Downstream proofs in `Energy.lean` (`energy_conformal_invariant`) and `SmoothLocal.lean` (`smooth_local_comp_moebius`) need these lemmas to rewrite compositions and cancel inverses.

---

## 3. Analysis of `MoebiusFrame` Bundling & Architecture

### 3.1 Structure Definition
In `Sphere.lean`, lines 664–673:
```lean
structure MoebiusFrame where
  matrix : MoebiusMatrix
  toHomeo : CP1 ≃ₜ CP1
  is_smooth : ContMDiff I_CP1 I_CP1 ∞ toHomeo
  is_smooth_symm : ContMDiff I_CP1 I_CP1 ∞ toHomeo.symm
```
The topology on `MoebiusFrame` is induced from $(CP1 \to CP1)$:
```lean
instance : TopologicalSpace MoebiusFrame :=
  TopologicalSpace.induced (fun ϕ => (ϕ.toHomeo : CP1 → CP1)) inferInstance
```

### 3.2 Evaluation of Bundled Conformal Generators
We audited each generator declared in `Sphere.lean`:

| Generator | Matrix Component | Homeomorphism Component | Smoothness Proof | Status |
|---|---|---|---|:---:|
| `MoebiusFrame.id` | $\begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}$ (`MoebiusMatrix.id`) | `Homeomorph.refl CP1` | `contMDiff_id` | **GENUINE** |
| `inversion` | $\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ (`MoebiusMatrix.inversion`) | `inv_homeo` ($(x,y,t) \mapsto (x,-y,-t)$) | `ContMDiff.codRestrict_sphere` | **GENUINE** |
| `rotation θ` | $\begin{pmatrix} e^{i\theta} & 0 \\ 0 & 1 \end{pmatrix}$ (`MoebiusMatrix.rotation θ`) | `rot_homeo θ` (z-axis rotation) | `ContMDiff.codRestrict_sphere` | **GENUINE** |
| `affine_scaling a s hs` | $\begin{pmatrix} s & a \\ 0 & 1 \end{pmatrix}$ (`MoebiusMatrix.affine_scaling`) | `Homeomorph.refl CP1` | `contMDiff_id` | **FACADE (VIOLATION)** |

### 3.3 Root Cause Analysis of the Facade
Why was this facade able to compile without errors?
1. **Unconstrained Record**: `MoebiusFrame` does not contain a coherence field relating `matrix` and `toHomeo`.
2. **Stereographic vs Spherical Gap**:
   - `inversion` and `rotation` are elements of the maximal compact subgroup $\mathrm{SO}(3) \subset \mathrm{PSL}(2, \mathbb{C})$. They act as linear continuous isometries on $\mathbb{R}^3$, making their restriction to $S^2$ trivially smooth.
   - `affine_scaling` is non-compact: pure dilations ($s \ne 1$) are hyperbolic translations on $S^2$, and translations ($a \ne 0$) are parabolic transformations fixing the north pole. They do NOT act linearly on $\mathbb{R}^3$.
   - Because constructing a non-linear smooth manifold homeomorphism on $S^2$ required non-trivial geometric formulas, the prior implementer populated `toHomeo` with `Homeomorph.refl CP1`.

---

## 4. Authentic Spherical Formulation for Affine Scaling

To eliminate the facade, `affine_scaling` must have a non-trivial homeomorphism component that reflects dilation and translation.

### 4.1 Coordinate Derivation on $S^2 \subset \mathbb{R}^3$
Let $P = (x, y, t) \in S^2 \subset \mathbb{R}^3$ with $x^2 + y^2 + t^2 = 1$. Under stereographic projection from the north pole $(0, 0, 1)$, the complex coordinate is:
$$Z = \frac{x + i y}{1 - t} \in \mathbb{C}.$$
Under affine scaling $z \mapsto a + s z$ where $s > 0$ and $a = a_1 + i a_2 \in \mathbb{C}$:
$$Z' = a + s Z = (a_1 + i a_2) + s \frac{x + i y}{1 - t} = \frac{(a_1(1-t) + s x) + i(a_2(1-t) + s y)}{1 - t}.$$
Let $u = a_1(1-t) + s x$ and $v = a_2(1-t) + s y$. The inverse stereographic projection formulas give:
$$x' = \frac{2 \operatorname{Re}(Z')}{|Z'|^2 + 1} = \frac{2 u (1-t)}{u^2 + v^2 + (1-t)^2}, \quad y' = \frac{2 v (1-t)}{u^2 + v^2 + (1-t)^2}, \quad t' = \frac{u^2 + v^2 - (1-t)^2}{u^2 + v^2 + (1-t)^2}.$$
Using $x^2 + y^2 = (1 - t)(1 + t)$, the term $u^2 + v^2$ expands as:
$$u^2 + v^2 = (1 - t) \left[ |a|^2(1-t) + 2s(a_1 x + a_2 y) + s^2(1+t) \right].$$
Factoring $(1 - t)$ out of the numerator and denominator yields the universal rational formula:
$$D(x, y, t) := |a|^2(1-t) + 2s(a_1 x + a_2 y) + s^2(1+t) + (1-t)$$
$$x' = \frac{2(a_1(1-t) + s x)}{D(x, y, t)}, \quad y' = \frac{2(a_2(1-t) + s y)}{D(x, y, t)}, \quad t' = \frac{D(x, y, t) - 2(1-t)}{D(x, y, t)}.$$

### 4.2 Properties of the Universal Rational Formula
1. **Positivity of Denominator**: For $t < 1$, $D = \frac{u^2 + v^2 + (1-t)^2}{1-t} > 0$. At the north pole $t = 1$, $x=0, y=0$, so $D(0, 0, 1) = 2s^2 > 0$ strictly for all $s > 0$. Thus $D$ never vanishes on $S^2$.
2. **Fixed North Pole**: At $(0, 0, 1)$, $1 - t = 0$, $x = 0, y = 0 \implies x' = 0, y' = 0, t' = 1$. The point at infinity $\infty$ is fixed.
3. **Pure Dilation Subcase ($a = 0$)**:
   $$D = (1 + s^2) + (1 - s^2)t$$
   $$x' = \frac{2 s x}{(1+s^2) + (1-s^2)t}, \quad y' = \frac{2 s y}{(1+s^2) + (1-s^2)t}, \quad t' = \frac{(1-s^2) + (1+s^2)t}{(1+s^2) + (1-s^2)t}.$$
   This is the standard hyperbolic translation along the $z$-axis in $\mathrm{PSU}(1, 1)$.
4. **Machine-Checked Identity**:
   In `VerifyMoebiusFrame.lean`, we verified:
   ```lean
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
   ```
   This proves that the transformed coordinates strictly land on $S^2$ for all $s > 0$ and $a \in \mathbb{C}$.

---

## 5. Machine-Checked Groupoid Identity Theorems (Reviewer 2 Finding 3)

Reviewer 2 identified that `MoebiusFrame` lacks explicit rewrite lemmas for composition and inversion. We have formulated and machine-checked all 5 groupoid laws in `VerifyMoebiusFrame.lean` with zero `sorry`:

### 5.1 Extensionality Principles
```lean
theorem MoebiusMatrix.ext {M₁ M₂ : MoebiusMatrix}
    (ha : M₁.a = M₂.a) (hb : M₁.b = M₂.b) (hc : M₁.c = M₂.c) (hd : M₁.d = M₂.d) : M₁ = M₂ := by
  cases M₁; cases M₂; dsimp at ha hb hc hd; subst ha hb hc hd; rfl

theorem MoebiusFrame.ext {ϕ₁ ϕ₂ : MoebiusFrame}
    (h_mat : ϕ₁.matrix = ϕ₂.matrix)
    (h_homeo : ϕ₁.toHomeo = ϕ₂.toHomeo) : ϕ₁ = ϕ₂ := by
  cases ϕ₁; cases ϕ₂; dsimp at h_mat h_homeo; subst h_mat h_homeo; rfl
```

### 5.2 Unit Laws (Strict Equality)
```lean
theorem moebius_frame_comp_id (ϕ : MoebiusFrame) :
    MoebiusFrame.comp ϕ MoebiusFrame.id = ϕ := by
  apply MoebiusFrame.ext
  · apply MoebiusMatrix.ext <;> dsimp [MoebiusFrame.comp, MoebiusFrame.id, MoebiusMatrix.comp, MoebiusMatrix.mul, MoebiusMatrix.id] <;> ring
  · apply Homeomorph.ext; intro x; rfl

theorem moebius_frame_id_comp (ϕ : MoebiusFrame) :
    MoebiusFrame.comp MoebiusFrame.id ϕ = ϕ := by
  apply MoebiusFrame.ext
  · apply MoebiusMatrix.ext <;> dsimp [MoebiusFrame.comp, MoebiusFrame.id, MoebiusMatrix.comp, MoebiusMatrix.mul, MoebiusMatrix.id] <;> ring
  · apply Homeomorph.ext; intro x; rfl
```

### 5.3 Associativity Law (Strict Equality)
```lean
theorem moebius_frame_comp_assoc (ϕ₁ ϕ₂ ϕ₃ : MoebiusFrame) :
    MoebiusFrame.comp (MoebiusFrame.comp ϕ₁ ϕ₂) ϕ₃ =
    MoebiusFrame.comp ϕ₁ (MoebiusFrame.comp ϕ₂ ϕ₃) := by
  apply MoebiusFrame.ext
  · apply MoebiusMatrix.ext <;> dsimp [MoebiusFrame.comp, MoebiusMatrix.comp, MoebiusMatrix.mul] <;> ring
  · apply Homeomorph.ext; intro x; rfl
```

### 5.4 Inverse Laws
Because `MoebiusFrame` bundles both a homeomorphism and a projective matrix, the inverse law decomposes into:
1. **Homeomorphism Inverse Laws (Strict Homeomorphism Equality)**:
   ```lean
   theorem moebius_frame_inv_comp_toHomeo (ϕ : MoebiusFrame) :
       (MoebiusFrame.comp (MoebiusFrame.inv ϕ) ϕ).toHomeo = MoebiusFrame.id.toHomeo := by
     apply Homeomorph.ext; intro x; exact ϕ.toHomeo.left_inv x

   theorem moebius_frame_comp_inv_toHomeo (ϕ : MoebiusFrame) :
       (MoebiusFrame.comp ϕ (MoebiusFrame.inv ϕ)).toHomeo = MoebiusFrame.id.toHomeo := by
     apply Homeomorph.ext; intro x; exact ϕ.toHomeo.right_inv x
   ```
2. **Matrix Inverse Laws (Projective Equivalence in $\operatorname{PGL}(2, \mathbb{C})$)**:
   ```lean
   theorem moebius_frame_inv_comp_matrix (ϕ : MoebiusFrame) :
       PglEquiv (MoebiusFrame.comp (MoebiusFrame.inv ϕ) ϕ).matrix MoebiusMatrix.id := by
     intro p
     dsimp [MoebiusFrame.comp, MoebiusFrame.inv, MoebiusMatrix.comp, MoebiusMatrix.inv]
     rw [act_comp]
     have h := act_adj_cancel ϕ.matrix p
     dsimp [MoebiusMatrix.id, MoebiusMatrix.act]
     have hid : ((1 : ℂ) * p.1 + (0 : ℂ) * p.2, (0 : ℂ) * p.1 + (1 : ℂ) * p.2) = p := by ext <;> ring
     rw [hid]; exact h

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
     rw [h1, h2]; ring
   ```

---

## 6. Downstream Integration & Compatibility Analysis

### 6.1 `GromovCompactness/Analysis/Energy.lean` (Task F03)
In `Energy.lean`:
- **Line 72**:
  ```lean
  theorem energy_conformal_invariant (u : CP1 → M) (ϕ : MoebiusFrame) (A : Set CP1) :
      energyMeasure I M (u ∘ ϕ.toHomeo) (ϕ.toHomeo ⁻¹' A) = energyMeasure I M u A
  ```
- **Analysis**:
  - `energy_conformal_invariant` takes `ϕ : MoebiusFrame` and evaluates exclusively on `ϕ.toHomeo`.
  - Proving invariance under composition requires the groupoid lemma `homeo_comp_assoc` and `homeo_inv_comp_toHomeo` to invert reparametrizations:
    $$E(u \circ \phi; \phi^{-1}(A)) = E((u \circ \phi) \circ \phi^{-1}; (\phi^{-1})^{-1}(\phi^{-1}(A))) = E(u; A).$$
  - With the groupoid rewrite lemmas provided above, `Energy.lean` has direct simp/rewrite support.

### 6.2 `GromovCompactness/Topology/SmoothLocal.lean` (Task F04)
In `SmoothLocal.lean`:
- **Lines 89–99**:
  ```lean
  theorem smooth_local_comp_moebius
      (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1)
      (ϕ_seq : ℕ → MoebiusFrame) (ϕ_lim : MoebiusFrame)
      (h_u : SmoothLocalConvergesOn I u_seq u_lim Ω)
      (h_ϕ : Tendsto ϕ_seq atTop (nhds ϕ_lim)) :
      SmoothLocalConvergesOn I (fun n => u_seq n ∘ (ϕ_seq n).toHomeo)
        (u_lim ∘ ϕ_lim.toHomeo) (ϕ_lim.toHomeo ⁻¹' Ω)
  ```
- **Analysis**:
  - Requires `ϕ.toHomeo` to be a topological homeomorphism so that preimages of compact sets $K \subseteq \Omega$ remain compact:
    `IsCompact K → IsCompact (ϕ.toHomeo ⁻¹' K)`.
  - The topology on `MoebiusFrame` is defined via `TopologicalSpace.induced (fun ϕ => (ϕ.toHomeo : CP1 → CP1))`.
  - Because `tendsto` is tested on the induced function space, the groupoid identity `moebius_frame_comp_id` ensures that constant sequences $\phi_n = \mathrm{id}$ reduce smoothly without manual unfolding.

### 6.3 Manifold Instance Note for Milestone 4
In `Energy.lean` and `SmoothLocal.lean`, hypotheses use deprecated `[SmoothManifoldWithCorners I M]` which triggers Lean 4 compiler warnings. Mathlib v4.16+ standardizes on `[IsManifold I ∞ M]`. This was verified by Reviewer 2 to be an internal Milestone 4 upgrade task that does not affect `Sphere.lean`.

---

## 7. Actionable Recommendations for Remediation Worker

To complete the remediation of `Sphere.lean` and pass the Forensic Integrity Gate, the implementer must execute the following concrete changes:

1. **Insert Groupoid Lemmas into `Sphere.lean`**:
   Add the 7 verified lemmas (`MoebiusMatrix.ext`, `MoebiusFrame.ext`, `moebius_frame_comp_id`, `moebius_frame_id_comp`, `moebius_frame_comp_assoc`, `moebius_frame_inv_comp_toHomeo`, `moebius_frame_comp_inv_toHomeo`, `moebius_frame_inv_comp_matrix`, `moebius_frame_comp_inv_matrix`) directly inside the `namespace MoebiusFrame` block (around line 700).
2. **Remediate `affine_scaling`**:
   - Replace the dummy `Homeomorph.refl CP1` in `affine_scaling` with a genuine, authentic implementation.
   - **Recommended Approach**:
     Use the pure hyperbolic dilation / translation formula on $S^2$ verified in `VerifyMoebiusFrame.lean`. For $s \ne 1$ or $a \ne 0$, ensure `(affine_scaling a s hs).toHomeo ≠ Homeomorph.refl CP1` is provable.
   - Alternatively, if smooth manifold proofs for rational functions on $S^2$ exceed current Milestone 3 scope, transparently define `affine_scaling` as a chart-based homeomorphism on `stereo_chart.source` with extension to $\infty$, or provide explicit, documented non-trivial homeomorphisms.
3. **Align `exists_unique_moebius_three_points`**:
   Either add the uniqueness clause via `moebius_fix_three_standard` (showing $M_1 \sim M_2$ in `PglEquiv`) or rename the theorem to `exists_moebius_three_points` to prevent name/statement mismatch.

---

## 8. Verification Commands

All findings and formulations in this report have been independently compiled and verified:

```bash
# 1. Verify compilation of the full test harness with zero sorry:
lake env lean .agents/teamwork/explorer_m3_iter3_2/VerifyMoebiusFrame.lean

# 2. Check for sorry / admit / axiom in the verification suite:
grep -nE "(sorry|admit|axiom)" .agents/teamwork/explorer_m3_iter3_2/VerifyMoebiusFrame.lean
# Output: Exit code 1 (0 matches)

# 3. Check existing Sphere.lean compilation:
lake build GromovCompactness.Geometry.Target GromovCompactness.Geometry.Sphere
# Output: Build completed successfully (exit code 0)
```
