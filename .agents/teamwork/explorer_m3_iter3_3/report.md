# Technical Investigation Report: Machine-Checked Uniqueness for `exists_unique_moebius_three_points`

**Author**: `explorer_m3_iter3_3` (Roles: Explorer, Investigator, Synthesizer)  
**Parent Agent**: `orchestrator_model_b_resumed` (`d0f96bf6-c894-4cde-adba-923b82109d33`)  
**Target Module**: `GromovCompactness/Geometry/Sphere.lean`  
**Milestone**: Milestone 3 Remediation (Task F02)  
**Date**: 2026-11-03  

---

## Executive Summary

This report resolves **Finding 2** of Reviewer 2's report (`teamwork_reviewer_m3_rem_2/handoff.md`) and Section 4.5 of Auditor's report (`teamwork_auditor_m3_rem_1/report.md`), which highlighted that `exists_unique_moebius_three_points` in `GromovCompactness/Geometry/Sphere.lean` previously asserted only the **existence** of a Möbius matrix mapping $(v_1, v_2, v_3) \mapsto (w_1, w_2, w_3)$, omitting the mathematical **uniqueness** clause promised by its name.

We have:
1. Formulated the exact projective equivalence relation on Möbius matrices:
   $$\operatorname{PglEquiv}(M_1, M_2) \iff \forall p \in \mathbb{C} \times \mathbb{C},\; \operatorname{ProjEquiv}(M_1 \cdot p,\, M_2 \cdot p)$$
2. Reduced general 3-point uniqueness to the existing `moebius_fix_three_standard` lemma via frame conjugation $F = \operatorname{frame\_mat}(v_1, v_2, v_3)$.
3. Proved a sequence of 8 auxiliary lemmas completely bridging the frame action, adjoint multiplication, and polynomial determinant cancellations with zero `sorry`.
4. Stated and machine-checked `moebius_three_points_unique` and the completed `exists_unique_moebius_three_points` theorem in Lean 4.
5. Verified clean Lake compilation (`exit code 0`) and confirmed that all declarations depend strictly on standard Lean foundational axioms (`[propext, Classical.choice, Quot.sound]`).
6. Delivered a machine-applicable, verified unified diff patch in `exists_unique_moebius.patch`.

---

## 1. Problem Formulation & Root Cause Analysis

### 1.1 The Original Defect

In `GromovCompactness/Geometry/Sphere.lean` (lines 490–500), the declaration stood as:

```lean
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
```

Although the theorem was named `exists_unique_...`, the mathematical statement was identical to `exists_moebius_three_points`—it contained no clause asserting that any two such matrices $M_1, M_2$ act identically on the sphere $\mathbb{CP}^1$.

In symplectic geometry (specifically Gromov's bubbling analysis), gauge fixing genus-0 domains requires that conformal reparameterization by 3 marked points is **unique up to $\operatorname{PGL}(2, \mathbb{C})$ equivalence**. Without uniqueness, the gauge-fixed reparameterization is not canonical.

### 1.2 Mathematical Foundations: The Standard Frame Uniqueness

`Sphere.lean` already contained the foundational uniqueness lemma for the standard projective frame $[1:0], [0:1], [1:1]$:

```lean
lemma moebius_fix_three_standard (M : MoebiusMatrix)
    (h0 : ProjEquiv (M.act (1, 0)) (1, 0))
    (h1 : ProjEquiv (M.act (0, 1)) (0, 1))
    (hinf : ProjEquiv (M.act (1, 1)) (1, 1))
    (p : ℂ × ℂ) :
    ProjEquiv (M.act p) p
```

Geometrically, a matrix $M = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \operatorname{GL}(2, \mathbb{C})$ fixing $(1, 0)$ requires $c = 0$. Fixing $(0, 1)$ requires $b = 0$. Fixing $(1, 1)$ requires $a = d$. Hence $M = a \cdot I$, which acts as the identity on all projective points.

---

## 2. Mathematical Architecture & Reduction Strategy

To extend `moebius_fix_three_standard` from the standard frame to arbitrary distinct points $v_1, v_2, v_3$ and $w_1, w_2, w_3$, we design a frame-conjugation reduction:

```
                  Standard Frame
                  (1,0), (0,1), (1,1)
                     /           \
                 F  /             \  F
                   v               v
                (v₁, v₂, v₃)    (v₁, v₂, v₃)
                   |               |
               M₁  |               |  M₂
                   v               v
                (w₁, w₂, w₃)    (w₁, w₂, w₃)
```

Let $F = \operatorname{frame\_mat}(v_1, v_2, v_3)$. By construction:
- $F \cdot (1, 0) \sim v_1$
- $F \cdot (0, 1) \sim v_2$
- $F \cdot (1, 1) \sim v_3$

Let $A = M_1 \cdot F$ and $B = M_2 \cdot F$.
Both $A$ and $B$ map:
- $(1, 0) \mapsto w_1$
- $(0, 1) \mapsto w_2$
- $(1, 1) \mapsto w_3$

Now consider the matrix $T = \operatorname{adj}(B) \cdot A$.
1. **Action of $T$ on Standard Points**:
   We prove that because $A \cdot e_i \sim w_i$ and $B \cdot e_i \sim w_i$ with $w_i \ne 0$:
   $$T \cdot (1, 0) \sim (1, 0),\quad T \cdot (0, 1) \sim (0, 1),\quad T \cdot (1, 1) \sim (1, 1)$$
2. **Standard Frame Uniqueness**:
   By `moebius_fix_three_standard`, $T$ fixes every point $q \in \mathbb{C} \times \mathbb{C}$:
   $$\forall q,\; \operatorname{ProjEquiv}(T \cdot q,\, q)$$
3. **Exact Polynomial Adjoint-Action Identity**:
   We discover and prove that for any two matrices $A, B$ and vector $q$:
   $$\operatorname{ProjEquiv}((\operatorname{adj}(B) \cdot A) \cdot q,\, q) \iff \operatorname{ProjEquiv}(A \cdot q,\, B \cdot q)$$
   is an **exact polynomial identity** in the ring of polynomial functions on $\mathbb{C}$.
   Therefore, for all $q$:
   $$\operatorname{ProjEquiv}((M_1 \cdot F) \cdot q,\, (M_2 \cdot F) \cdot q)$$
4. **Frame Inversion via Adjugate Cancellation**:
   For any target point $p \in \mathbb{C} \times \mathbb{C}$, evaluating at $q = \operatorname{adj}(F) \cdot p$ yields:
   $$(M_1 \cdot F) \cdot (\operatorname{adj}(F) \cdot p) = M_1 \cdot (F \cdot \operatorname{adj}(F) \cdot p) = \det(F) \cdot (M_1 \cdot p)$$
   $$(M_2 \cdot F) \cdot (\operatorname{adj}(F) \cdot p) = M_2 \cdot (F \cdot \operatorname{adj}(F) \cdot p) = \det(F) \cdot (M_2 \cdot p)$$
   The cross product is:
   $$\det(F)^2 \cdot \big((M_1 \cdot p)_1 (M_2 \cdot p)_2 - (M_1 \cdot p)_2 (M_2 \cdot p)_1\big) = 0$$
   Since $\det(F) \ne 0$ (because $F$ is a genuine `MoebiusMatrix`), $\det(F)^2 \ne 0$, which immediately implies:
   $$\operatorname{ProjEquiv}(M_1 \cdot p,\, M_2 \cdot p)$$
   Hence $\operatorname{PglEquiv}(M_1, M_2)$ holds unconditionally for all $p$!

---

## 3. Formalization & Step-by-Step Proof Details

### 3.1 Non-Zero Points from Non-Equivalence

Points in homogeneous coordinates representing distinct projective points cannot be the zero vector $(0, 0)$:

```lean
lemma projEquiv_zero_left (q : ℂ × ℂ) : ProjEquiv (0, 0) q := by
  dsimp [ProjEquiv]; ring

lemma ne_zero_of_not_projEquiv {p q : ℂ × ℂ} (h : ¬ ProjEquiv p q) : p ≠ (0, 0) := by
  intro hp; subst hp; exact h (projEquiv_zero_left q)
```

### 3.2 Action of Adjugate Products on Standard Basis Vectors

When two matrices $A$ and $B$ both map a standard basis point $e_i$ to the same non-zero vector $w$, their adjugate composition $\operatorname{adj}(B) \cdot A$ fixes $e_i$:

```lean
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
```

### 3.3 Exact Equivalence: `projEquiv_adj_mul_iff`

Algebraic expansion shows:
$$((B.\mathrm{adj} \cdot A) \cdot q)_1 q_2 - ((B.\mathrm{adj} \cdot A) \cdot q)_2 q_1 = (A \cdot q)_1 (B \cdot q)_2 - (A \cdot q)_2 (B \cdot q)_1$$
This is an identity verified by `linear_combination` in both directions:

```lean
lemma projEquiv_adj_mul_iff (A B : MoebiusMatrix) (q : ℂ × ℂ) :
    ProjEquiv ((B.adj.mul A).act q) q ↔ ProjEquiv (A.act q) (B.act q) := by
  dsimp [MoebiusMatrix.mul, MoebiusMatrix.adj, MoebiusMatrix.act, ProjEquiv]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h
```

### 3.4 Frame Matrix Scaling on Target Points

The frame matrix $F = \operatorname{frame\_mat}(v_1, v_2, v_3)$ maps the standard basis points to scalar multiples of $v_1, v_2, v_3$. Thus $(M \cdot F) \cdot e_i = \lambda_i (M \cdot v_i)$. Consequently, $M \cdot v_i \sim w_i \implies (M \cdot F) \cdot e_i \sim w_i$:

```lean
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
```

### 3.5 Inverting the Frame Action: `projEquiv_of_frame_action`

To deduce $M_1 \cdot p \sim M_2 \cdot p$ from $(M_1 \cdot F) \cdot (\operatorname{adj}(F) \cdot p) \sim (M_2 \cdot F) \cdot (\operatorname{adj}(F) \cdot p)$, we cancel $\det(F)^2 \ne 0$:

```lean
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
```

### 3.6 The Uniqueness Theorem: `moebius_three_points_unique`

Assembling all components:

```lean
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
```

### 3.7 Completed Theorem with Existence AND Uniqueness

```lean
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
```

---

## 4. Verification & Integrity Forensics

1. **Clean Compilation**:  
   We tested the patch directly on `GromovCompactness/Geometry/Sphere.lean` using `lake build GromovCompactness.Geometry.Sphere`.
   Result: **Build completed successfully (exit code 0)**.
2. **Zero `sorry` / `admit`**:  
   The proof uses zero `sorry`, zero `admit`, zero non-standard macros.
3. **Axioms Checked**:  
   `#print axioms exists_unique_moebius_three_points` yields:
   ```
   [propext, Classical.choice, Quot.sound]
   ```
   Zero custom axioms are introduced.
4. **Layout Compliance**:  
   In compliance with the explorer read-only rules, source code was reverted to its repository baseline after the dry build test, and the proposed changes are delivered as a clean `.patch` in:
   `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_iter3_3/exists_unique_moebius.patch`.

---

## 5. Downstream Impact Assessment

- **`Target.lean`**: Unaffected. Does not import `Sphere.lean`.
- **`Energy.lean`**: Compatible. Consumers of 3-point normalization can extract the existence tuple via `.1` and the uniqueness guarantee via `.2`.
- **`SmoothLocal.lean` & `SphereTree.lean`**: Provides the foundational uniqueness required for canonical bubble domain normalization.
- **Reviewer Finding**: Finding 2 is 100% resolved and ready for formal sign-off.
