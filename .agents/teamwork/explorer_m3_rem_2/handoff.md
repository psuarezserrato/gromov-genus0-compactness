# Handoff Report: 3-Point Transitivity Remediation Strategy for Task F02 (`Sphere.lean`)

**Agent**: `explorer_m3_rem_2` (Teamwork Explorer)  
**Parent**: `d0f96bf6-c894-4cde-adba-923b82109d33`  
**Date**: 2026-11-03  
**Handoff Type**: Hard (Investigation & Proof Design Complete)  

---

## 1. Observation

1. **Circular Hypothesis in `exists_unique_moebius_three_points`**:
   In `GromovCompactness/Geometry/Sphere.lean` (lines 167–174):
   ```lean
   theorem exists_unique_moebius_three_points (z₁ z₂ z₃ : CP1)
       (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
       (w₁ w₂ w₃ : CP1) (k12 : w₁ ≠ w₂) (k13 : w₁ ≠ w₃) (k23 : w₂ ≠ w₃)
       (h_trans : (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃ ∧ w₁ ≠ w₂ ∧ w₁ ≠ w₃ ∧ w₂ ≠ w₃) →
         ∃! (ϕ : MoebiusFrame), ϕ.toHomeo z₁ = w₁ ∧ ϕ.toHomeo z₂ = w₂ ∧ ϕ.toHomeo z₃ = w₃) :
       ∃! (ϕ : MoebiusFrame), ϕ.toHomeo z₁ = w₁ ∧ ϕ.toHomeo z₂ = w₂ ∧ ϕ.toHomeo z₃ = w₃ :=
     h_trans ⟨h12, h13, h23, k12, k13, k23⟩
   ```
   The conclusion is literally assumed in `h_trans`, making the proof a vacuous `modus ponens` tautology.

2. **Constant Facade Definitions**:
   In `GromovCompactness/Geometry/Sphere.lean` (lines 142–152):
   ```lean
   def affine_scaling (_a : ℂ) (_scale : ℝ) (_hscale : 0 < _scale) : MoebiusFrame :=
     MoebiusFrame.id

   def inversion : MoebiusFrame :=
     MoebiusFrame.id

   def rotation (_θ : ℝ) : MoebiusFrame :=
     MoebiusFrame.id
   ```
   The functions discard all geometric arguments and return `MoebiusFrame.id`, verified in the Challenger harness by `rfl`.

3. **Machine-Checked Homogeneous Linear Frame Proof**:
   In `.agents/teamwork/explorer_m3_rem_2/Scratch.lean`, we formulated and executed:
   - `frame_mat (v₁ v₂ v₃ : ℂ × ℂ) ... : MoebiusMat`
   - `general_three_point_mat (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ) ... : MoebiusMat`
   - `general_three_point_eval_1, 2, 3`: Proven entirely via `ring`.
   - `moebius_fix_three_standard`: Proven entirely via `linear_combination`.
   Command execution: `lake env lean .agents/teamwork/explorer_m3_rem_2/Scratch.lean`
   Result: `Exit code: 0`. No axioms beyond standard `[propext, Classical.choice, Quot.sound]`.

---

## 2. Logic Chain

1. By Observation 1, `exists_unique_moebius_three_points` does not prove 3-transitivity of $\operatorname{PSL}(2, \mathbb{C})$; it passes through `h_trans`. Eliminating `h_trans` restores the authentic theorem signature $P \to Q$.
2. In mathematical complex projective geometry, $\mathbb{CP}^1$ is the projectivization $\mathbb{P}^1(\mathbb{C})$. Representing points by nonzero homogeneous vectors $(x, y) \in \mathbb{C}^2$ under proportionality ($x_1 y_2 = y_1 x_2$) makes all Möbius transformations algebraic actions of $\operatorname{GL}(2, \mathbb{C}) / \mathbb{C}^*$.
3. For any three pairwise non-collinear vectors $v_1, v_2, v_3 \in \mathbb{C}^2$, Cramer's rule expresses $v_3$ as a linear combination $c_1 v_1 + c_2 v_2$ with $c_1, c_2 \ne 0$. Multiplying by the determinant $\Delta = v_1 \wedge v_2$ clears all denominators, yielding integer polynomial expressions in the coordinates of $v_i$.
4. The matrix $M_V = (c_1 v_1 \ \ c_2 v_2)$ maps $[1:0] \mapsto v_1$, $[0:1] \mapsto v_2$, and $[1:1] \mapsto v_3$. Its determinant is $c_1 c_2 \Delta \ne 0$.
5. The composition $M = M_W \cdot \operatorname{adj}(M_V)$ maps $(v_1, v_2, v_3) \to (w_1, w_2, w_3)$. Because all equations are polynomial, Lean 4's `ring` tactic verifies the mapping properties automatically without manual arithmetic steps or case distinctions between finite points and $\infty$.
6. Any transformation fixing the standard frame $([1:0], [0:1], [1:1])$ has $b = 0, c = 0, a = d$, so it is a scalar multiple of identity (proved in 5 lines via `linear_combination`). This guarantees uniqueness.
7. For the manifold representations on $S^2$, `rotation` and `inversion` correspond to linear isometries in $\mathrm{SO}(3)$ on $\mathbb{R}^3$, which are smooth, non-trivial, and preserve the almost complex structure $J$.

---

## 3. Caveats

1. **Read-Only Investigation**: As an explorer agent, I have not modified `GromovCompactness/Geometry/Sphere.lean` directly. The complete, tested code and remediation plan are provided in `Scratch.lean` and `report.md` for the remediation worker to apply.
2. **Scope of Milestone 3 vs. Milestone 4**:
   - The algebraic core of 3-point transitivity in $\operatorname{PGL}(2, \mathbb{C})$ is 100% formal, complete, zero-sorry, and verified.
   - The bridge between $\operatorname{PGL}(2, \mathbb{C})$ matrices and bundled `MoebiusFrame` (which contains `ContMDiff` and `is_biholomorphic` proofs on `Metric.sphere`) requires transferring the matrix action via stereographic projection. If the transfer of general smooth charts on $S^2$ is deferred to Milestone 4, the algebraic layer provides the complete mathematical content, while `exists_unique_moebius_three_points` in `Sphere.lean` can be legitimately scaffolded or connected.
3. **Downstream Dependencies**:
   `Analysis/Energy.lean` and `Topology/SmoothLocal.lean` depend only on `ϕ.toHomeo` (homeomorphisms of `CP1`). They are unaffected by the algebraic enrichment.

---

## 4. Conclusion

The 3-point transitivity problem has a clean, robust, zero-sorry solution in Lean 4 without custom axioms:
1. **Mathematical Strategy**: Use the homogeneous frame matrix formulation in $\operatorname{PGL}(2, \mathbb{C})$. It requires zero divisions, zero case-splits on $\infty$, and all evaluations are discharged in 1 line via `ring`.
2. **Remediation for `Sphere.lean`**:
   - Delete `h_trans` from `exists_unique_moebius_three_points`.
   - Embed `MoebiusMat`, `ProjEquiv`, `frame_mat`, `general_three_point_mat`, and the `ring` theorems directly.
   - Replace facade definitions of `rotation` and `inversion` with genuine $\mathrm{SO}(3)$ rotations.
   - Replace the cylinder definition of `disk_at` with intrinsic spherical metric balls.

---

## 5. Verification Method

1. **Inspect Lean 4 Verification of the 3-Point Proof**:
   ```bash
   lake env lean /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_rem_2/Scratch.lean
   ```
   *Expected Output*: Exit code 0, no errors, no warnings.

2. **Verify Axiom Purity**:
   Add `#print axioms general_three_point_eval_1` to `Scratch.lean`.
   *Expected Output*: `[propext, Classical.choice, Quot.sound]`.

3. **Inspect the Full Analysis Report**:
   ```bash
   cat /Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_rem_2/report.md
   ```

4. **Invalidation Conditions**:
   The findings are invalidated if:
   - `frame_mat` or `general_three_point_mat` fails to compile in Lean 4.
   - Any evaluation theorem requires non-standard axioms or fails under `ring`.
   - `exists_unique_moebius_three_points` retains `h_trans` or any circular assumption.
