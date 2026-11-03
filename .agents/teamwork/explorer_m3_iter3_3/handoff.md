# Handoff Report: Machine-Checked Uniqueness for `exists_unique_moebius_three_points` (Task F02)

**Author**: `explorer_m3_iter3_3` (teamwork_explorer)  
**Recipient / Parent Agent**: `orchestrator_model_b_resumed` (`d0f96bf6-c894-4cde-adba-923b82109d33`)  
**Task**: Formulate and machine-check the uniqueness clause in `exists_unique_moebius_three_points` in `GromovCompactness/Geometry/Sphere.lean` using `moebius_fix_three_standard`.  
**Artifacts Produced**:
- Report: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_iter3_3/report.md`
- Patch: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_iter3_3/exists_unique_moebius.patch`
- Handoff: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_iter3_3/handoff.md`  
**Handoff Type**: Hard (Task Complete)  

---

## 1. Observation

1. **Reviewer 2 Defect Observation**:  
   In `GromovCompactness/Geometry/Sphere.lean` lines 490–500, `exists_unique_moebius_three_points` was defined as:
   ```lean
   theorem exists_unique_moebius_three_points (v₁ v₂ v₃ w₁ w₂ w₃ : ℂ × ℂ)
       (hv12 : ¬ ProjEquiv v₁ v₂) (hv23 : ¬ ProjEquiv v₂ v₃) (hv13 : ¬ ProjEquiv v₁ v₃)
       (hw12 : ¬ ProjEquiv w₁ w₂) (hw23 : ¬ ProjEquiv w₂ w₃) (hw13 : ¬ ProjEquiv w₁ w₃) :
       ∃ (M : MoebiusMatrix),
         ProjEquiv (M.act v₁) w₁ ∧
         ProjEquiv (M.act v₂) w₂ ∧
         ProjEquiv (M.act v₃) w₃ :=
     exists_moebius_three_points v₁ v₂ v₃ w₁ w₂ w₃ hv12 hv23 hv13 hw12 hw23 hw13
   ```
   Direct observation: this statement lacks any uniqueness clause (`∃!`), despite the declaration name.
2. **Available Standard Uniqueness Lemma**:  
   In `Sphere.lean` lines 390–401, `moebius_fix_three_standard` was proved with zero `sorry`:
   ```lean
   lemma moebius_fix_three_standard (M : MoebiusMatrix)
       (h0 : ProjEquiv (M.act (1, 0)) (1, 0))
       (h1 : ProjEquiv (M.act (0, 1)) (0, 1))
       (hinf : ProjEquiv (M.act (1, 1)) (1, 1))
       (p : ℂ × ℂ) :
       ProjEquiv (M.act p) p
   ```
3. **PGL Equivalence Definition**:  
   In `Sphere.lean` line 502, `PglEquiv` is defined as:
   ```lean
   def PglEquiv (M N : MoebiusMatrix) : Prop :=
     ∀ p : ℂ × ℂ, ProjEquiv (M.act p) (N.act p)
   ```
4. **Lake Build & Toolchain State**:  
   Lean 4 toolchain `leanprover/lean4:v4.17.0` with Lake.
   `lake build GromovCompactness.Geometry.Sphere` builds in ~4 seconds.

---

## 2. Logic Chain

1. **Identification of Gauge Invariant**: In $\operatorname{PGL}(2, \mathbb{C})$, matrices $M_1, M_2$ act identically on projective space $\mathbb{CP}^1$ if and only if for all $p \in \mathbb{C} \times \mathbb{C}$, $\operatorname{ProjEquiv}(M_1 \cdot p,\, M_2 \cdot p)$ (i.e. $\operatorname{PglEquiv}(M_1, M_2)$).
2. **Frame Reduction Strategy**: Given distinct triple $(v_1, v_2, v_3)$, the frame matrix $F = \operatorname{frame\_mat}(v_1, v_2, v_3)$ maps $[1:0] \mapsto v_1$, $[0:1] \mapsto v_2$, and $[1:1] \mapsto v_3$ up to non-zero complex scalar multiples.
3. **Composed Matrix Action on Standard Points**:
   Let $A = M_1 \cdot F$ and $B = M_2 \cdot F$.
   Since $M_1 \cdot v_i \sim w_i$ and $M_2 \cdot v_i \sim w_i$, lemmas `act_mul_frame_w1`, `w2`, `w3` establish that $A \cdot e_i \sim w_i$ and $B \cdot e_i \sim w_i$.
4. **Adjugate Action on Standard Frame**:
   Let $T = \operatorname{adj}(B) \cdot A$. Lemmas `adj_mul_act_standard_1`, `2`, `3` prove that $T \cdot (1, 0) \sim (1, 0)$, $T \cdot (0, 1) \sim (0, 1)$, and $T \cdot (1, 1) \sim (1, 1)$.
5. **Standard Frame Uniqueness Application**:
   Applying `moebius_fix_three_standard T`, we deduce that for all $q \in \mathbb{C} \times \mathbb{C}$, $\operatorname{ProjEquiv}(T \cdot q,\, q)$.
6. **Equivalence Lemma**:
   `projEquiv_adj_mul_iff` establishes the polynomial identity:
   $$\operatorname{ProjEquiv}((\operatorname{adj}(B) \cdot A) \cdot q,\, q) \iff \operatorname{ProjEquiv}(A \cdot q,\, B \cdot q)$$
   Hence, for all $q$, $\operatorname{ProjEquiv}((M_1 \cdot F) \cdot q,\, (M_2 \cdot F) \cdot q)$.
7. **Cancelling the Frame Action**:
   For any $p \in \mathbb{C} \times \mathbb{C}$, setting $q = \operatorname{adj}(F) \cdot p$ yields:
   $$(M_i \cdot F) \cdot (\operatorname{adj}(F) \cdot p) = \det(F) \cdot (M_i \cdot p)$$
   Lemma `projEquiv_of_frame_action` cancels the non-zero scalar factor $\det(F)^2 \ne 0$, proving:
   $$\operatorname{ProjEquiv}(M_1 \cdot p,\, M_2 \cdot p)$$
8. **Theorem Assembly**:
   Step 7 establishes `moebius_three_points_unique`. Combining this with `exists_moebius_three_points` yields `exists_unique_moebius_three_points` asserting both existence and uniqueness up to `PglEquiv` with zero `sorry`.

---

## 3. Caveats

1. **Equivalence Modulo Center**: Uniqueness in $\operatorname{GL}(2, \mathbb{C})$ is only up to non-zero scalar multiplication $\mathbb{C}^\times \cdot I$, which is precisely captured by `PglEquiv`. Strict matrix equality $M_1 = M_2$ is mathematically false in $\operatorname{PGL}(2, \mathbb{C})$ (e.g. $M$ and $2M$ define the same transformation), so uniqueness is correctly and necessarily formulated modulo `PglEquiv`.
2. **Consumer Field Access**: Consumers expecting `h.1` for existence now have `h.1.1` (or can use `exists_moebius_three_points` directly).
3. **No Caveats on Verification**: Zero `sorry`, clean build, standard axioms verified.

---

## 4. Conclusion

The uniqueness clause for `exists_unique_moebius_three_points` is fully formulated, machine-checked, and verified in Lean 4 without `sorry`. Finding 2 from Reviewer 2 is completely resolved.

The complete patch is ready for integration by the Milestone 3 remediation worker at:
`/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m3_iter3_3/exists_unique_moebius.patch`.

---

## 5. Verification Method

The parent orchestrator and reviewers can independently verify the patch with the following terminal commands:

```bash
# 1. Apply patch to verify build
cd /Users/pablosuarez/Desktop/SympTopAutoForm
patch -p1 < .agents/teamwork/explorer_m3_iter3_3/exists_unique_moebius.patch

# 2. Compile Sphere.lean with Lake
lake build GromovCompactness.Geometry.Sphere
# Expected: Build completed successfully (exit code 0)

# 3. Verify zero sorry or admit in the file
grep -nE "(sorry|admit)" GromovCompactness/Geometry/Sphere.lean
# Expected: Exit code 1 (0 matches)

# 4. Check foundational axioms
lake env lean --stdin << 'EOF'
import GromovCompactness.Geometry.Sphere
open GromovCompactness

#print axioms exists_unique_moebius_three_points
EOF
# Expected: depends on axioms: [propext, Classical.choice, Quot.sound]

# 5. Cleanly restore working copy (if maintaining git hygiene before commit)
git checkout GromovCompactness/Geometry/Sphere.lean
```
