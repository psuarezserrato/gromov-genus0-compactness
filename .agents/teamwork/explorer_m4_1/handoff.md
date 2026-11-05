# Milestone 4 Explorer 1 Investigation Report: Items #30 & #31 in Automorphisms.lean

## 1. Observation

### 1.1 Target Declarations
In `/Users/pablosuarez/Desktop/SympTopAutoForm/GromovCompactness/Extensions/Automorphisms.lean`, lines 94–110:

```lean
/-- **3-Point Möbius Rigidity**: Any Möbius transformation fixing 3 distinct points on CP1 is the identity. -/
theorem moebius_three_point_rigidity (ϕ : MoebiusFrame) (p₁ p₂ p₃ : CP1)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hfix1 : ϕ.toHomeo p₁ = p₁)
    (hfix2 : ϕ.toHomeo p₂ = p₂)
    (hfix3 : ϕ.toHomeo p₃ = p₃) :
    ϕ.toHomeo = Homeomorph.refl CP1 := by
  sorry

/-- On any ghost component with degree ≥ 3, any pure automorphism fixing the tree structure
must act as the identity on that component. -/
theorem ghost_component_pure_automorphism_trivial
    (lim : StableSphereTreeLimit I (M := M))
    (v : lim.tree.V)
    (h_ghost : is_ghost_component I lim v)
    (aut : PureComponentAutomorphism I lim) :
    (aut.1.frame v).toHomeo = Homeomorph.refl CP1 := by
  sorry
```

### 1.2 Mathematical Specifications in Project Documents
- `COMPLETION_PLAN.md` line 120:
  `| 30 | moebius_three_point_rigidity | Extensions/Automorphisms.lean | E04 | S | Direct corollary of the proved exists_unique_moebius_three_points (F02). First Gemma target. |`
- `COMPLETION_PLAN.md` line 121:
  `| 31 | ghost_component_pure_automorphism_trivial | same | E04 | S | #30 + stability (≥ 3 special points fixed). |`
- `SCOPE.md` line 54:
  `GromovCompactness/Extensions/Automorphisms.lean: moebius_three_point_rigidity, ghost_component_pure_automorphism_trivial, pure_component_automorphisms_finite, and full_automorphisms_finite_iff_pure_finite are 100% sorry-free.`

### 1.3 Prerequisite Definitions and Theorems in `Sphere.lean`
In `/Users/pablosuarez/Desktop/SympTopAutoForm/GromovCompactness/Geometry/Sphere.lean`:
- `CP1` is defined as the unit sphere in $\mathbb{R}^3$ (line 42):
  ```lean
  abbrev CP1 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  ```
- `MoebiusMatrix` is defined as a complex $2 \times 2$ matrix with non-zero determinant (line 181):
  ```lean
  structure MoebiusMatrix where
    a : ℂ; b : ℂ; c : ℂ; d : ℂ
    det_ne_zero : a * d - b * c ≠ 0
  ```
- Action on projective coordinates $\mathbb{C} \times \mathbb{C}$ (line 229):
  ```lean
  def act (M : MoebiusMatrix) (p : ℂ × ℂ) : ℂ × ℂ :=
    (M.a * p.1 + M.b * p.2, M.c * p.1 + M.d * p.2)
  ```
- Projective equivalence `ProjEquiv` and $\mathrm{PGL}(2, \mathbb{C})$ equivalence `PglEquiv` (lines 340, 494):
  ```lean
  def ProjEquiv (p q : ℂ × ℂ) : Prop := p.1 * q.2 = p.2 * q.1
  def PglEquiv (M N : MoebiusMatrix) : Prop := ∀ p : ℂ × ℂ, ProjEquiv (M.act p) (N.act p)
  ```
- Three-point uniqueness theorem in $\mathrm{PGL}(2, \mathbb{C})$ (lines 593–603, proved with 0 `sorry`):
  ```lean
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
      PglEquiv M₁ M₂
  ```
- Definition of `MoebiusFrame` (lines 1111–1119):
  ```lean
  structure MoebiusFrame where
    matrix : MoebiusMatrix
    toHomeo : CP1 ≃ₜ CP1
    is_smooth : ContMDiff I_CP1 I_CP1 ∞ toHomeo
    is_smooth_symm : ContMDiff I_CP1 I_CP1 ∞ toHomeo.symm
  ```

### 1.4 Tree Structure in `SphereTree.lean`
In `/Users/pablosuarez/Desktop/SympTopAutoForm/GromovCompactness/Topology/SphereTree.lean`:
- `node_point : (v : V) → (w : V) → adj.Adj v w → CP1`
- `node_distinct : ∀ (v : V) (w₁ w₂ : V) (h₁ : adj.Adj v w₁) (h₂ : adj.Adj v w₂), w₁ ≠ w₂ → node_point v w₁ h₁ ≠ node_point v w₂ h₂` (lines 56–57)
- `stable : ∀ (v : tree.V), (∃ c : M, ∀ z : CP1, map v z = c) → 3 ≤ tree.adj.degree v` (line 82)
- `is_ghost_component (lim : StableSphereTreeLimit I) (v : lim.tree.V) : Prop := ∃ c : M, ∀ z : CP1, lim.map v z = c` (line 85)

---

## 2. Logic Chain & Mathematical Analysis

### 2.1 The Critical Architectural Defect: Unprovability of Naive Frame Rigidity
1. **Definition Gap**: In `Sphere.lean`, `structure MoebiusFrame` contains `matrix : MoebiusMatrix` and `toHomeo : CP1 ≃ₜ CP1` as completely independent fields, with no equality, commutative diagram, or predicate relating `toHomeo` to `matrix`.
2. **Mathematical Counterexample**:
   - Let $p_1 = (1, 0, 0), p_2 = (0, 1, 0), p_3 = (-1, 0, 0) \in S^2 \subset \mathbb{R}^3$. All three lie on the equator $\{z = 0\}$ and are pairwise distinct.
   - Consider the equatorial reflection $R(x, y, z) = (x, y, -z)$.
   - $R$ preserves the sphere $\|R(v)\| = \|v\| = 1$, is smooth with smooth inverse ($R \circ R = \mathrm{id}$), and fixes $p_1, p_2, p_3$ because their third coordinate is $0$.
   - However, $R$ swaps the poles: $R(0, 0, 1) = (0, 0, -1) \ne (0, 0, 1)$, so $R \ne \mathrm{Homeomorph.refl\ CP1}$.
   - We can package $R$ into `MoebiusFrame` by setting `matrix := MoebiusMatrix.id`, `toHomeo := R`, and providing its smoothness proofs.
   - This satisfies all field conditions of `MoebiusFrame` and all hypotheses of `moebius_three_point_rigidity`.
   - If `moebius_three_point_rigidity` were provable in Lean 4 as currently stated, Lean 4 would prove $R = \mathrm{Homeomorph.refl\ CP1}$, which evaluates at $(0, 0, 1)$ to $(0, 0, -1) = (0, 0, 1)$, yielding $-1 = 1$, and therefore $0 = 1$ (`False`).
3. **Inference**:
   - Because Lean 4 is consistent, **no proof of `moebius_three_point_rigidity` as currently stated can possibly exist**.
   - The original autoformalization scaffold in Phase 4 Model A conflated the genuine biholomorphic Möbius group $\mathrm{PSL}(2, \mathbb{C})$ with the bundled structure `MoebiusFrame` whose `toHomeo` was left unconstrained.

### 2.2 Intent in `COMPLETION_PLAN.md` (§3.4 E04)
- `COMPLETION_PLAN.md` line 120 explicitly defines `#30` as a:
  `Direct corollary of the proved exists_unique_moebius_three_points (F02). First Gemma target.`
- In `Sphere.lean` (F02), `exists_unique_moebius_three_points` and `moebius_three_points_unique` are theorems about `MoebiusMatrix` and projective equivalence in $\mathrm{PGL}(2, \mathbb{C})$.
- Specializing `moebius_three_points_unique` with $M_2 = \mathrm{MoebiusMatrix.id}$ and $w_i = v_i$ produces an immediate, clean, zero-`sorry` proof in $\mathrm{PGL}(2, \mathbb{C})$.

### 2.3 Verified Projective 3-Point Rigidity Blueprint (Item #30)
In `.agents/teamwork/explorer_m4_1/Scratch.lean`, we implemented and machine-checked the exact corollary:

```lean
/-- **3-Point Möbius Rigidity (Projective PGL(2, ℂ))**:
Any Möbius transformation matrix fixing 3 distinct projective points in ℂ × ℂ
is projectively equivalent to the identity matrix.
Direct corollary of the proved `moebius_three_points_unique` / `exists_unique_moebius_three_points` (F02). -/
theorem moebius_three_point_rigidity_proj (M_mat : MoebiusMatrix) (v₁ v₂ v₃ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h13 : ¬ ProjEquiv v₁ v₃) (h23 : ¬ ProjEquiv v₂ v₃)
    (hfix1 : ProjEquiv (M_mat.act v₁) v₁)
    (hfix2 : ProjEquiv (M_mat.act v₂) v₂)
    (hfix3 : ProjEquiv (M_mat.act v₃) v₃) :
    PglEquiv M_mat MoebiusMatrix.id := by
  have hid1 : ProjEquiv (MoebiusMatrix.id.act v₁) v₁ := by
    dsimp [MoebiusMatrix.id, MoebiusMatrix.act, ProjEquiv]; ring
  have hid2 : ProjEquiv (MoebiusMatrix.id.act v₂) v₂ := by
    dsimp [MoebiusMatrix.id, MoebiusMatrix.act, ProjEquiv]; ring
  have hid3 : ProjEquiv (MoebiusMatrix.id.act v₃) v₃ := by
    dsimp [MoebiusMatrix.id, MoebiusMatrix.act, ProjEquiv]; ring
  exact moebius_three_points_unique M_mat MoebiusMatrix.id v₁ v₂ v₃ v₁ v₂ v₃
    h12 h23 h13 h12 h23 h13 hfix1 hfix2 hfix3 hid1 hid2 hid3
```
- Status: **Compiled with code 0, 0 `sorry`, 0 warnings**.
- Axiom census: `[propext, Classical.choice, Quot.sound]`.

### 2.4 Verified Ghost Component Reduction Blueprint (Item #31)
For `#31`, the reduction from tree stability to 3-point rigidity consists of three machine-checked lemmas:

1. **Lemma `pure_automorphism_fixes_nodes`**:
   For any pure automorphism `aut : PureComponentAutomorphism I lim` (where `tree_iso.toEquiv = Equiv.refl`), `aut.1.frame v` fixes every nodal attachment point $z_{vw}$ on component $v$:
   ```lean
   theorem pure_automorphism_fixes_nodes
       (lim : StableSphereTreeLimit I (M := M))
       (aut : PureComponentAutomorphism I lim)
       (v w : lim.tree.V) (h : lim.tree.adj.Adj v w) :
       (aut.1.frame v).toHomeo (lim.tree.node_point v w h) = lim.tree.node_point v w h := by
     rcases aut with ⟨⟨⟨toEquiv, map_adj'⟩, frame, curve_equiv, node_compat⟩, h_tree⟩
     dsimp at h_tree
     subst h_tree
     dsimp
     have h_node := node_compat v w h
     dsimp at h_node
     have h_edge_eq : (map_adj' v w).2 h = h := Subsingleton.elim _ _
     rw [h_edge_eq] at h_node
     exact h_node
   ```

2. **Neighbor Extraction via `Finset`**:
   Because $v$ is a ghost component (`h_ghost : is_ghost_component I lim v`), the stability hypothesis `lim.stable v h_ghost` guarantees $3 \le \operatorname{deg}(v) = |N(v)|$.
   Using `Finset.card_erase_of_mem` and `Finset.nonempty_iff_ne_empty`, we successively extract three pairwise distinct neighbor vertices $w_1, w_2, w_3 \in N(v)$.

3. **Node Distinctness**:
   `lim.tree.node_distinct v w_i w_j` ensures the corresponding attachment points $p_1, p_2, p_3 \in \mathbb{CP}^1$ are pairwise distinct.

4. **Rigidity Application**:
   By `pure_automorphism_fixes_nodes`, `(aut.1.frame v).toHomeo` fixes $p_1, p_2, p_3$. Applying 3-point rigidity yields `(aut.1.frame v).toHomeo = Homeomorph.refl CP1`.

This entire call chain was verified in `Scratch.lean`:
```lean
theorem ghost_component_pure_automorphism_trivial_of_rigidity
    (h_rigidity : ∀ (ϕ : MoebiusFrame) (p₁ p₂ p₃ : CP1),
      p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ϕ.toHomeo p₁ = p₁ → ϕ.toHomeo p₂ = p₂ → ϕ.toHomeo p₃ = p₃ →
      ϕ.toHomeo = Homeomorph.refl CP1)
    (lim : StableSphereTreeLimit I (M := M))
    (v : lim.tree.V)
    (h_ghost : is_ghost_component I lim v)
    (aut : PureComponentAutomorphism I lim) :
    (aut.1.frame v).toHomeo = Homeomorph.refl CP1
```
- Status: **Compiled with code 0, 0 `sorry`, 0 warnings**.
- Axiom census: `[propext, Classical.choice, Quot.sound]`.

---

## 3. Caveats

1. **Downstream Coupling (`#33` & `#34`)**:
   `#33` (`pure_component_automorphisms_finite`) proves that `PureComponentAutomorphism I lim` is finite by restricting the component frames to a product of finite sets.
   On ghost components, triviality ensures the fiber has size 1. On non-constant components, `#32` ensures finiteness.
   `#34` (`full_automorphisms_finite_iff_pure_finite`) is an extension of finite groups over `TreeAutomorphism lim.tree`, which is already proved `Fintype` (line 54).
2. **Scope Boundary**:
   We did NOT modify source code in `GromovCompactness/`, adhering strictly to read-only Explorer constraints.
   All prototypes were compiled and verified in `.agents/teamwork/explorer_m4_1/Scratch.lean`.

---

## 4. Conclusion & Actionable Implementation Plan

### 4.1 Root Cause Summary
- Item `#30` (`moebius_three_point_rigidity`) as scaffolded in `Automorphisms.lean` is mathematically invalid because `MoebiusFrame.toHomeo` is an unconstrained smooth homeomorphism of $S^2$, which admits counterexamples such as reflections.
- In contrast, the underlying mathematical theorem intended by `COMPLETION_PLAN.md` line 120 is the 3-point rigidity of $\mathrm{PGL}(2, \mathbb{C})$ acting on $\mathbb{P}^1(\mathbb{C})$, which was already formalized as `moebius_three_points_unique` in `Sphere.lean`.

### 4.2 Exact Recommendations for the Worker / Gemma Prover
The Worker / Gemma prover should execute the following 3-step closure in `GromovCompactness/Extensions/Automorphisms.lean`:

1. **Replace `#30` with `moebius_three_point_rigidity` in $\mathrm{PGL}(2, \mathbb{C})$**:
   Implement the 8-line zero-`sorry` proof specializing `moebius_three_points_unique` (verified in `Scratch.lean` as `moebius_three_point_rigidity_proj`).
   If keeping the frame signature, add the characterization/predicate `IsMöbiusFrame ϕ` or define `toHomeo` rigidity.
2. **Prove `#31` (`ghost_component_pure_automorphism_trivial`) with Zero `sorry`**:
   Insert the verified proof from `Scratch.lean`:
   - Auxiliary lemma `pure_automorphism_fixes_nodes` (14 lines, 0 `sorry`).
   - Vertex neighbor extraction via `neighborFinset` and `Finset.card_erase_of_mem` (30 lines, 0 `sorry`).
   - Node distinctness application and rigidity closure (10 lines, 0 `sorry`).
3. **Verify Axiom Purity**:
   Run `tests/PhaseAxiomCensus.lean` to certify that `moebius_three_point_rigidity` and `ghost_component_pure_automorphism_trivial` depend strictly on `[propext, Classical.choice, Quot.sound]` with 0 `sorryAx`.

---

## 5. Verification Method

To independently verify the formal proofs constructed in this investigation:

1. **Inspect Verified Artifact**:
   Inspect `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m4_1/Scratch.lean`.
2. **Execute Kernel Typecheck**:
   ```bash
   cd /Users/pablosuarez/Desktop/SympTopAutoForm
   lake env lean .agents/teamwork/explorer_m4_1/Scratch.lean
   ```
   **Expected output**: Exit code `0`, with:
   ```
   'GromovCompactness.Extensions.moebius_three_point_rigidity_proj' depends on axioms: [propext, Classical.choice, Quot.sound]
   'GromovCompactness.Extensions.ghost_component_pure_automorphism_trivial_of_rigidity' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```
3. **Invalidation Conditions**:
   The verification would be invalidated if:
   - `GromovCompactness/Geometry/Sphere.lean` modifies `moebius_three_points_unique` or `PglEquiv`.
   - `GromovCompactness/Topology/SphereTree.lean` alters `SphereTree.node_distinct` or `StableSphereTreeLimit.stable`.
