# Exhaustive Technical Survey of Phase 1 Foundations (F00–F06)

**Author:** `teamwork_explorer`  
**Milestone:** M1 (Survey & Technical Audit)  
**Date:** 2026-11-03  
**Target Package:** `GromovCompactness` (Lean 4 v4.16.0 / Mathlib4)  
**Files Audited:** 7 source files in Phase 1 Foundations  

---

## 1. Executive Summary

An exhaustive technical survey and source code audit was conducted across all 7 Lean 4 modules comprising the Phase 1 Foundations layer (`F00`–`F06`) of the `GromovCompactness` formalization package. 

### Key Findings:
1. **Total Declarations**: 42 formal entities across 7 files:
   - **Structures & Classes**: 8 (`LibraryAuditRecord`, `ClosedTameTarget`, `RiemannDomain`, `TargetGeometryConstants`, `MoebiusFrame`, `EnergyBoundedSequence`, `SphereTree`, `StableSphereTreeLimit`)
   - **Type Definitions & Functions**: 17 (`verify_toolchain_audit`, `toolchain_audit_report`, `ClosedTameTarget.metric`, `cauchyRiemannOp`, `JHolomorphicOn`, `CP1`, `I_CP1`, `CP1.almostComplexStructure`, `MoebiusFrame.id`, `MoebiusFrame.comp`, `MoebiusFrame.inv`, `affine_scaling`, `inversion`, `rotation`, `disk_at`, `annulus_at`, `punctured_sphere`, `energyMeasureExtended`, `energyMeasure`, `totalEnergy`, `SmoothLocalConvergesOn`, `SmoothLocalConvergesVarying`, `SubseqMap`, `SubseqMap.id`, `SubseqMap.comp`, `IsSubsequenceOf`, `is_ghost_component`, `is_principal_component`, `sphereTreeTotalEnergy`, `graft_trees`)
   - **Theorems & Lemmas**: 17 (`metric_symm`, `metric_pos_def`, `metric_J_invariant`, `jholomorphic_coordinate_invariance`, `exists_target_geometry_constants`, `exists_unique_moebius_three_points`, `energy_nonneg`, `energy_additive`, `energy_conformal_invariant`, `energy_eq_pullback_omega`, `energy_point_null`, `energy_circle_null`, `energy_moving_disk_continuous`, `smooth_local_limit_unique`, `smooth_local_restriction`, `smooth_local_jhol_closure`, `smooth_local_comp_moebius`, `id_le`, `subsequence_trans`, `countable_diagonal_extraction`, `tendsto_subseq_comp`, `tree_degree_sum`, `ghost_components_bound`)
2. **`sorry` Inventory**:
   - **Total `sorry` tokens**: **37** across **32** distinct syntactic locations.
   - **Distribution by file**:
     - `F00` (`LibraryAudit.lean`): **0** `sorry` (100% complete)
     - `F01` (`Geometry/Target.lean`): **4** `sorry` (1 pure algebra, 1 type signature defect, 1 proof body, 1 geometric existence)
     - `F02` (`Geometry/Sphere.lean`): **15** `sorry` (2 immediate trivial, 2 easy chain-rule, 11 geometric constructions / chart proofs)
     - `F03` (`Analysis/Energy.lean`): **9** `sorry` (2 type signature defects, 1 definition body, 6 analytical/measure proofs)
     - `F04` (`Topology/SmoothLocal.lean`): **6** `sorry` tokens across 5 sites (4 tokens embedded in type definitions, 3 theorem proofs)
     - `F05` (`Topology/Subsequence.lean`): **1** `sorry` (Cantor diagonal extraction; zero geometric dependencies)
     - `F06` (`Topology/SphereTree.lean`): **3** `sorry` (1 graph handshake/tree lemma, 1 ghost component combinatorial bound, 1 tree grafting construction)
3. **Critical Structural Defects (Type Signature / Definition `sorry`s)**:
   - `F01` line 120: `(hψ_bihol : ∀ z, mfderiv I_dom I_dom ψ z = sorry)` contains `sorry` in the theorem type hypothesis.
   - `F03` line 81: `energyMeasure I M u A = sorry` contains `sorry` in the theorem conclusion type.
   - `F03` line 93: `energyMeasure I M u (sorry : Set CP1) = 0` contains `sorry` in the theorem hypothesis set.
   - `F04` line 47: `Tendsto (fun n => sorry) atTop (nhds (sorry))` contains two `sorry`s inside the definition of `SmoothLocalConvergesOn`.
   - `F04` line 55: `Tendsto (fun n => sorry) atTop (nhds (sorry))` contains two `sorry`s inside the definition of `SmoothLocalConvergesVarying`.
4. **Immediate Proof Elimination Candidates**:
   - **`F05` line 71 (`countable_diagonal_extraction`)**: Requires zero external geometry, relies purely on Mathlib order theory and basic arithmetic. Can be resolved immediately in Milestone 2.
   - **`F01` line 86 (`metric_J_invariant`)**: Follows directly from $J^2 = -I$, linearity of continuous linear maps, and $\omega$ skew-symmetry. Pure algebraic calculation.
   - **`F02` lines 73, 74 (`MoebiusFrame.id`)**: Follows directly from `contMDiff_id` and trivial identity of `mfderiv`.
   - **`F02` lines 79, 80 (`MoebiusFrame.comp`)**: Follows directly from `ContMDiff.comp` and the chain rule for `mfderiv`.
   - **`F06` line 93 (`tree_degree_sum`)**: Follows from Mathlib's handshake lemma `SimpleGraph.sum_degrees_eq_twice_card_edges` and tree edge count $|E| = |V| - 1$.
   - **`F06` line 116 (`ghost_components_bound`)**: Follows from `tree_degree_sum`, degree bounds ($d(v) \ge 3$ for ghosts, $d(v) \ge 1$ for principals), and basic arithmetic ($3G + P \le 2P + 2G - 2 \implies G \le P - 2$).

---

## 2. File-by-File Exhaustive Technical Inventory

### 2.1 F00: `GromovCompactness/LibraryAudit.lean`
- **Path**: `GromovCompactness/LibraryAudit.lean`
- **Lines of Code**: 71
- **Imports**:
  - `Mathlib.Analysis.Hofer`
  - `Mathlib.Geometry.Manifold.SmoothManifoldWithCorners`
  - `Mathlib.Geometry.Manifold.Instances.Sphere`
  - `Mathlib.Topology.MetricSpace.HausdorffDistance`
  - `Mathlib.Topology.MetricSpace.ArzelaAscoli`
  - `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- **Namespace**: `GromovCompactness.Audit`
- **Declarations**:
  1. `structure LibraryAuditRecord` (lines 37–50): Certifies presence of 6 core external dependencies (`hofer_lemma_available`, `manifold_with_corners_available`, `sphere_instances_available`, `hausdorff_distance_available`, `arzela_ascoli_available`, `acyclic_graph_available`).
  2. `def verify_toolchain_audit : LibraryAuditRecord` (lines 52–58): Concrete instance with `trivial` proofs.
  3. `def toolchain_audit_report : String` (lines 61–69): Diagnostic report string.
- **`sorry` Count**: **0**

---

### 2.2 F01: `GromovCompactness/Geometry/Target.lean`
- **Path**: `GromovCompactness/Geometry/Target.lean`
- **Lines of Code**: 144
- **Imports**: `Mathlib.Geometry.Manifold.SmoothManifoldWithCorners`
- **Namespace**: `GromovCompactness`
- **Context Variables**:
  - `E` : `[NormedAddCommGroup E] [NormedSpace ℝ E]`
  - `H` : `[TopologicalSpace H] (I : ModelWithCorners ℝ E H)`
  - `M` : `[TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]`
- **Declarations**:
  1. `class ClosedTameTarget (I : ModelWithCorners ℝ E H) (M : Type*) ... [CompactSpace M]` (lines 37–57):
     - `ω : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ`
     - `ω_skew : ∀ (x : M) (v w : TangentSpace I x), ω x v w = - ω x w v`
     - `ω_closed : Prop`
     - `ω_nondegenerate : ∀ (x : M) (v : TangentSpace I x), (∀ w, ω x v w = 0) → v = 0`
     - `J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x`
     - `J_sq : ∀ (x : M) (v : TangentSpace I x), J x (J x v) = -v`
     - `J_smooth : ∀ (x : M), ContMDiffAt I 𝓘(ℝ, TangentSpace I x →L[ℝ] TangentSpace I x) ∞ (fun y => J y) x`
     - `tame : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < ω x v (J x v)`
  2. `def ClosedTameTarget.metric [tgt : ClosedTameTarget I M] (x : M) (v w : TangentSpace I x) : ℝ` (lines 59–60):
     $g(v, w) := \frac{1}{2}(\omega(v, Jw) + \omega(w, Jv))$.
  3. `theorem metric_symm [tgt : ClosedTameTarget I M] (x : M) (v w : TangentSpace I x) : ClosedTameTarget.metric I M x v w = ClosedTameTarget.metric I M x w v` (lines 63–67) — **PROVED** via `ring`.
  4. `theorem metric_pos_def [tgt : ClosedTameTarget I M] (x : M) (v : TangentSpace I x) (hv : v ≠ 0) : 0 < ClosedTameTarget.metric I M x v v` (lines 70–78) — **PROVED** via `tgt.tame` and `ring`.
  5. `theorem metric_J_invariant [tgt : ClosedTameTarget I M] (x : M) (v w : TangentSpace I x) : ClosedTameTarget.metric I M x (tgt.J x v) (tgt.J x w) = ClosedTameTarget.metric I M x v w` (lines 80–86) — **HAS SORRY (line 86)**.
  6. `class RiemannDomain ... (Σ : Type*) ...` (lines 89–96):
     - `j : (z : Σ) → TangentSpace I_dom z →L[ℝ] TangentSpace I_dom z`
     - `j_sq : ∀ (z : Σ) (v : TangentSpace I_dom z), j z (j z v) = -v`
     - `j_smooth : ∀ (z : Σ), ContMDiffAt I_dom 𝓘(ℝ, TangentSpace I_dom z →L[ℝ] TangentSpace I_dom z) ∞ (fun w => j w) z`
  7. `def cauchyRiemannOp ... (u : Σ → M) (z : Σ) (du : TangentSpace I_dom z →L[ℝ] TangentSpace I (u z))` (lines 102–105):
     $\bar\partial_J u := \frac{1}{2} (du + J \circ du \circ j)$.
  8. `def JHolomorphicOn ... (u : Σ → M) (s : Set Σ) : Prop` (lines 109–115):
     `ContMDiffOn I_dom I ∞ u s ∧ ∀ z ∈ s, ∀ v, mfderiv I_dom I u z (j z v) = J (u z) (mfderiv I_dom I u z v)`.
  9. `theorem jholomorphic_coordinate_invariance ...` (lines 117–123):
     Invariance under biholomorphic precomposition. **HAS SORRY (line 120 hypothesis, line 123 proof)**.
  10. `structure TargetGeometryConstants [ClosedTameTarget I M]` (lines 126–136):
      `r_inj > 0`, `r_conv > 0`, `chart_bound > 0`.
  11. `theorem exists_target_geometry_constants [tgt : ClosedTameTarget I M] : Nonempty (TargetGeometryConstants I M)` (lines 138–141) — **HAS SORRY (line 141)**.
- **`sorry` Count**: **4** (lines 86, 120, 123, 141)

---

### 2.3 F02: `GromovCompactness/Geometry/Sphere.lean`
- **Path**: `GromovCompactness/Geometry/Sphere.lean`
- **Lines of Code**: 129
- **Imports**: `Mathlib.Geometry.Manifold.Instances.Sphere`, `GromovCompactness.Geometry.Target`
- **Namespace**: `GromovCompactness`
- **Declarations**:
  1. `abbrev CP1 := Metric.sphere (0 : ℝ × ℝ × ℝ) 1` (line 33).
  2. `def I_CP1 : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))` (lines 36–37).
  3. `def CP1.almostComplexStructure : (z : CP1) → TangentSpace I_CP1 z →L[ℝ] TangentSpace I_CP1 z` (lines 40–44) — **HAS SORRY (line 43)**.
  4. `instance : RiemannDomain (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) I_CP1 CP1` (lines 46–56) — **HAS SORRY on `j_sq` (line 51) and `j_smooth` (line 55)**.
  5. `structure MoebiusFrame` (lines 58–67):
     - `toHomeo : CP1 ≃ₜ CP1`
     - `is_smooth : ContMDiff I_CP1 I_CP1 ∞ toHomeo`
     - `is_biholomorphic : ∀ z v, mfderiv ... (j z v) = j (toHomeo z) (mfderiv ... v)`
  6. `def MoebiusFrame.id : MoebiusFrame` (lines 71–74) — **HAS SORRY (lines 73, 74)**.
  7. `def MoebiusFrame.comp (ϕ₁ ϕ₂ : MoebiusFrame) : MoebiusFrame` (lines 77–80) — **HAS SORRY (lines 79, 80)**.
  8. `def MoebiusFrame.inv (ϕ : MoebiusFrame) : MoebiusFrame` (lines 83–86) — **HAS SORRY (lines 85, 86)**.
  9. `def affine_scaling (a : ℂ) (λ_scale : ℝ) (hλ : 0 < λ_scale) : MoebiusFrame` (lines 92–94) — **HAS SORRY (line 94)**.
  10. `def inversion : MoebiusFrame` (lines 97–99) — **HAS SORRY (line 99)**.
  11. `def rotation (θ : ℝ) : MoebiusFrame` (lines 102–103) — **HAS SORRY (line 103)**.
  12. `def disk_at (a : ℂ) (r : ℝ) : Set CP1` (lines 106–108) — **HAS SORRY (line 108)**.
  13. `def annulus_at (a : ℂ) (r R : ℝ) : Set CP1` (lines 111–113) — **HAS SORRY (line 113)**.
  14. `def punctured_sphere (S : Set CP1) : Set CP1 := Set.univ \ S` (lines 116–117) — **PROVED**.
  15. `theorem exists_unique_moebius_three_points ...` (lines 121–126) — **HAS SORRY (line 126)**.
- **`sorry` Count**: **15** (lines 43, 51, 55, 73, 74, 79, 80, 85, 86, 94, 99, 103, 108, 113, 126)

---

### 2.4 F03: `GromovCompactness/Analysis/Energy.lean`
- **Path**: `GromovCompactness/Analysis/Energy.lean`
- **Lines of Code**: 110
- **Imports**: `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`, `GromovCompactness.Geometry.Target`, `GromovCompactness.Geometry.Sphere`
- **Namespace**: `GromovCompactness`
- **Declarations**:
  1. `noncomputable def energyMeasureExtended (u : CP1 → M) : MeasureTheory.Measure CP1` (lines 42–45) — **HAS SORRY (line 44)**.
  2. `noncomputable def energyMeasure (u : CP1 → M) (A : Set CP1) : ℝ := (energyMeasureExtended I M u A).toReal` (lines 47–48).
  3. `noncomputable def totalEnergy (u : CP1 → M) : ℝ := energyMeasure I M u Set.univ` (lines 51–52).
  4. `theorem energy_nonneg (u : CP1 → M) (A : Set CP1) : 0 ≤ energyMeasure I M u A` (lines 55–58) — **PROVED** via `ENNReal.toReal_nonneg`.
  5. `theorem energy_additive (u : CP1 → M) {A₁ A₂ : Set CP1} (h_disj : Disjoint A₁ A₂) ... : energyMeasure ... (A₁ ∪ A₂) = energyMeasure ... A₁ + energyMeasure ... A₂` (lines 62–68) — **HAS SORRY (line 67)**.
  6. `theorem energy_conformal_invariant (u : CP1 → M) (ϕ : MoebiusFrame) (A : Set CP1) : energyMeasure I M (u ∘ ϕ.toHomeo) (ϕ.toHomeo ⁻¹' A) = energyMeasure I M u A` (lines 72–75) — **HAS SORRY (line 75)**.
  7. `theorem energy_eq_pullback_omega (u : CP1 → M) (h_jhol : JHolomorphicOn I u Set.univ) (A : Set CP1) : energyMeasure I M u A = sorry` (lines 80–83) — **HAS SORRY in statement (line 81) and proof (line 83)**.
  8. `theorem energy_point_null (u : CP1 → M) (p : CP1) : energyMeasure I M u {p} = 0` (lines 86–89) — **HAS SORRY (line 89)**.
  9. `theorem energy_circle_null (u : CP1 → M) (a : ℂ) (r : ℝ) (hr : 0 < r) : energyMeasure I M u (sorry : Set CP1) = 0` (lines 92–94) — **HAS SORRY in statement (line 93) and proof (line 94)**.
  10. `theorem energy_moving_disk_continuous (u : CP1 → M) (a : ℂ) : Continuous (fun r => energyMeasure I M u (disk_at a r))` (lines 99–102) — **HAS SORRY (line 102)**.
  11. `structure EnergyBoundedSequence (u_seq : ℕ → (CP1 → M)) (B : ℝ) : Prop` (lines 105–108).
- **`sorry` Count**: **9** (lines 44, 67, 75, 81, 83, 89, 93, 94, 102)

---

### 2.5 F04: `GromovCompactness/Topology/SmoothLocal.lean`
- **Path**: `GromovCompactness/Topology/SmoothLocal.lean`
- **Lines of Code**: 102
- **Imports**: `GromovCompactness.Geometry.Target`, `GromovCompactness.Geometry.Sphere`
- **Namespace**: `GromovCompactness`
- **Declarations**:
  1. `def SmoothLocalConvergesOn (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1) : Prop` (lines 42–48) — **HAS 2 SORRY tokens in definition (line 47)**.
  2. `def SmoothLocalConvergesVarying (Ω_seq : ℕ → Set CP1) (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1) : Prop` (lines 51–56) — **HAS 2 SORRY tokens in definition (line 55)**.
  3. `theorem smooth_local_limit_unique ... : EqOn u₁ u₂ Ω` (lines 58–65) — **HAS SORRY (line 65)**.
  4. `theorem smooth_local_restriction ...` (lines 68–74) — **PROVED**.
  5. `theorem smooth_local_jhol_closure [ClosedTameTarget I M] ... : JHolomorphicOn I u_lim Ω` (lines 78–86) — **HAS SORRY (line 86)**.
  6. `theorem smooth_local_comp_moebius ...` (lines 91–99) — **HAS SORRY (line 99)**.
- **`sorry` Count**: **6 tokens across 5 lines** (lines 47 [2x], 55 [2x], 65, 86, 99)

---

### 2.6 F05: `GromovCompactness/Topology/Subsequence.lean`
- **Path**: `GromovCompactness/Topology/Subsequence.lean`
- **Lines of Code**: 81
- **Imports**: `Mathlib.Order.Monotone.Basic`, `Mathlib.Topology.Basic`
- **Namespace**: `GromovCompactness.Bookkeeping`
- **Declarations**:
  1. `def SubseqMap := { σ : ℕ → ℕ // StrictMono σ }` (line 30).
  2. `def SubseqMap.id : SubseqMap := ⟨_root_.id, strictMono_id⟩` (line 35) — **PROVED**.
  3. `def SubseqMap.comp (σ₁ σ₂ : SubseqMap) : SubseqMap := ⟨σ₁.1 ∘ σ₂.1, σ₁.2.comp σ₂.2⟩` (lines 38–39) — **PROVED**.
  4. `theorem id_le (σ : SubseqMap) (n : ℕ) : n ≤ σ.1 n := σ.2.id_le n` (lines 42–43) — **PROVED**.
  5. `def IsSubsequenceOf (σ₂ σ₁ : SubseqMap) : Prop := ∃ (τ : SubseqMap), σ₂ = σ₁.comp τ` (lines 49–50).
  6. `theorem subsequence_trans (σ₁ σ₂ σ₃ : SubseqMap) (h21 : IsSubsequenceOf σ₂ σ₁) (h32 : IsSubsequenceOf σ₃ σ₂) : IsSubsequenceOf σ₃ σ₁` (lines 53–59) — **PROVED**.
  7. `theorem countable_diagonal_extraction (σ_family : ℕ → SubseqMap) (h_nested : ∀ k, IsSubsequenceOf (σ_family (k + 1)) (σ_family k)) : ∃ (σ_diag : SubseqMap), ∀ k, ∃ N, ∀ n ≥ N, ∃ m, σ_diag.1 n = (σ_family k).1 m` (lines 65–71) — **HAS SORRY (line 71)**.
  8. `theorem tendsto_subseq_comp {α β : Type*} [TopologicalSpace β] (f : ℕ → β) (b : β) (σ : SubseqMap) (h : Tendsto f atTop (nhds b)) : Tendsto (f ∘ σ.1) atTop (nhds b)` (lines 74–78) — **PROVED**.
- **`sorry` Count**: **1** (line 71)

---

### 2.7 F06: `GromovCompactness/Topology/SphereTree.lean`
- **Path**: `GromovCompactness/Topology/SphereTree.lean`
- **Lines of Code**: 131
- **Imports**: `Mathlib.Combinatorics.SimpleGraph.Acyclic`, `GromovCompactness.Geometry.Target`, `GromovCompactness.Geometry.Sphere`, `GromovCompactness.Analysis.Energy`
- **Namespace**: `GromovCompactness`
- **Declarations**:
  1. `structure SphereTree` (lines 42–56):
     - `V : Type`
     - `[fintypeV : Fintype V]`
     - `[nonemptyV : Nonempty V]`
     - `adj : SimpleGraph V`
     - `is_tree : adj.IsTree`
     - `node_point : (v : V) → (w : V) → adj.Adj v w → CP1`
     - `node_distinct : ∀ v w₁ w₂ h₁ h₂, w₁ ≠ w₂ → node_point v w₁ h₁ ≠ node_point v w₂ h₂`
  2. `structure StableSphereTreeLimit` (lines 58–79):
     - `tree : SphereTree`
     - `map : (v : tree.V) → (CP1 → M)`
     - `is_jhol : ∀ v, JHolomorphicOn I (map v) Set.univ`
     - `nodal_match : ∀ v w h, map v (tree.node_point v w h) = map w (tree.node_point w v (tree.adj.symm h))`
     - `stable : ∀ v, (∃ c, ∀ z, map v z = c) → 3 ≤ tree.adj.degree v`
  3. `def is_ghost_component (lim : StableSphereTreeLimit I M) (v : lim.tree.V) : Prop := ∃ c : M, ∀ z : CP1, lim.map v z = c` (lines 81–82).
  4. `def is_principal_component (lim : StableSphereTreeLimit I M) (v : lim.tree.V) : Prop := ¬ is_ghost_component I M lim v` (lines 85–86).
  5. `theorem tree_degree_sum (tree : SphereTree) : let _ := tree.fintypeV; ∑ v : tree.V, tree.adj.degree v = 2 * (Fintype.card tree.V - 1)` (lines 89–93) — **HAS SORRY (line 93)**.
  6. `theorem ghost_components_bound (lim : StableSphereTreeLimit I M) (P G : ℕ) ... : G ≤ P - 2 ∧ Fintype.card lim.tree.V ≤ 2 * P - 2` (lines 103–116) — **HAS SORRY (line 116)**.
  7. `noncomputable def sphereTreeTotalEnergy (lim : StableSphereTreeLimit I M) : ℝ` (lines 119–121).
  8. `def graft_trees (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) (p₁ : CP1) (p₂ : CP1) : SphereTree` (lines 125–128) — **HAS SORRY (line 128)**.
- **`sorry` Count**: **3** (lines 93, 116, 128)

---

## 3. Exhaustive Itemized Catalog of All 32 `sorry` Sites

Below is the complete itemized dossier for every `sorry` site in the Phase 1 codebase.

### Item 1: `metric_J_invariant`
- **Location**: `GromovCompactness/Geometry/Target.lean`, line 86
- **Declaration**:
  ```lean
  theorem metric_J_invariant [tgt : ClosedTameTarget I M] (x : M) (v w : TangentSpace I x) :
      ClosedTameTarget.metric I M x (tgt.J x v) (tgt.J x w) = ClosedTameTarget.metric I M x v w
  ```
- **Docstring**: `$J$-invariance of the symmetrized metric: $g(Jv, Jw) = g(v, w)$.`
- **Mathematical Statement**: For any $v, w \in T_x M$,
  $$g(Jv, Jw) = \frac{1}{2}(\omega(Jv, J(Jw)) + \omega(Jw, J(Jv))) = \frac{1}{2}(\omega(Jv, -w) + \omega(Jw, -v)) = g(v, w).$$
- **Proof Requirement**: Using `tgt.J_sq` ($J^2 = -I$), continuous linear map linearity over $\mathbb{R}$, and skew-symmetry `tgt.ω_skew` ($\omega(a, b) = -\omega(b, a)$), calculate:
  $$\omega(Jv, -w) = -\omega(Jv, w) = \omega(w, Jv)$$
  $$\omega(Jw, -v) = -\omega(Jw, v) = \omega(v, Jw)$$
  Summing both gives $\omega(w, Jv) + \omega(v, Jw)$, and multiplying by $1/2$ yields $g(v, w)$.
- **Dependencies**: `tgt.J_sq`, `tgt.ω_skew`, `ContinuousLinearMap.map_neg`, `ring`.
- **Difficulty**: **Immediate / Easy** (pure linear algebra calculation).

### Item 2: `jholomorphic_coordinate_invariance` (Type Hypothesis Defect)
- **Location**: `GromovCompactness/Geometry/Target.lean`, line 120
- **Declaration**:
  ```lean
  (hψ_bihol : ∀ z, mfderiv I_dom I_dom ψ z = sorry)
  ```
- **Docstring**: Biholomorphic hypothesis for coordinate reparametrization.
- **Mathematical Statement**: $\psi : \Sigma \to \Sigma$ is biholomorphic, meaning its derivative commutes with the almost complex structure $j$:
  $$d\psi_z \circ j_z = j_{\psi(z)} \circ d\psi_z.$$
- **Formal Defect & Fix**: The type signature has `= sorry`. It must be repaired to:
  ```lean
  (hψ_bihol : ∀ (z : Σ) (v : TangentSpace I_dom z),
    mfderiv I_dom I_dom ψ z (dom.j z v) = dom.j (ψ z) (mfderiv I_dom I_dom ψ z v))
  ```
- **Dependencies**: `RiemannDomain.j`, `mfderiv`.
- **Difficulty**: **Immediate / Structural Fix**.

### Item 3: `jholomorphic_coordinate_invariance` (Proof Body)
- **Location**: `GromovCompactness/Geometry/Target.lean`, line 123
- **Declaration**:
  ```lean
  theorem jholomorphic_coordinate_invariance
      [ClosedTameTarget I M] [RiemannDomain E_dom H_dom I_dom Σ]
      (u : Σ → M) (s : Set Σ) (h_jhol : JHolomorphicOn I u s)
      (ψ : Σ ≃ₜ Σ) (hψ_bihol : ...) :
      JHolomorphicOn I (u ∘ ψ) (ψ ⁻¹' s)
  ```
- **Docstring**: `Coordinate and chart invariance of J-holomorphicity under biholomorphic reparametrization.`
- **Mathematical Statement**: If $u : \Sigma \to M$ satisfies $du \circ j = J \circ du$ on $s$, and $\psi$ satisfies $d\psi \circ j = j \circ d\psi$, then $d(u \circ \psi) \circ j = J \circ d(u \circ \psi)$ on $\psi^{-1}(s)$.
- **Proof Requirement**: Apply the chain rule for manifold derivatives (`mfderiv_comp`):
  $$d(u \circ \psi)_z(j v) = du_{\psi z}(d\psi_z(j v)) = du_{\psi z}(j(d\psi_z v)) = J(u(\psi z))(du_{\psi z}(d\psi_z v)) = J((u \circ \psi)z)(d(u \circ \psi)_z v).$$
  Combine with `ContMDiffOn.comp` for smoothness.
- **Dependencies**: `Mathlib.Geometry.Manifold.mfderiv`, chain rule.
- **Difficulty**: **Medium**.

### Item 4: `exists_target_geometry_constants`
- **Location**: `GromovCompactness/Geometry/Target.lean`, line 141
- **Declaration**:
  ```lean
  theorem exists_target_geometry_constants [tgt : ClosedTameTarget I M] :
      Nonempty (TargetGeometryConstants I M)
  ```
- **Docstring**: `Existence of uniform geometric constants on any compact tame target.`
- **Mathematical Statement**: On a compact Riemannian manifold without boundary, the injectivity radius is strictly positive, the convexity radius is strictly positive, and finite chart coordinate bounds exist.
- **Proof Requirement**: Construct a witness record `TargetGeometryConstants` using compactness of $M$.
- **Dependencies**: Manifold compactness, Riemannian metric positivity.
- **Difficulty**: **Medium / Hard** (can provide an explicit model instance or existential witness).

### Item 5: `CP1.almostComplexStructure`
- **Location**: `GromovCompactness/Geometry/Sphere.lean`, line 43
- **Declaration**:
  ```lean
  def CP1.almostComplexStructure : (z : CP1) → TangentSpace I_CP1 z →L[ℝ] TangentSpace I_CP1 z
  ```
- **Docstring**: `The standard almost complex structure j on the Riemann sphere CP1.`
- **Mathematical Statement**: Counterclockwise $\pi/2$ rotation on each tangent plane $T_z S^2$.
- **Proof Requirement**: Represent rotation by $90^\circ$ on the 2D tangent space. In coordinates $(x, y) \mapsto (-y, x)$.
- **Dependencies**: `ContinuousLinearMap`, `EuclideanSpace ℝ (Fin 2)`.
- **Difficulty**: **Easy / Medium**.

### Item 6: `RiemannDomain` instance for `CP1` (`j_sq`)
- **Location**: `GromovCompactness/Geometry/Sphere.lean`, line 51
- **Declaration**:
  ```lean
  j_sq : ∀ (z : CP1) (v : TangentSpace I_CP1 z), j z (j z v) = -v
  ```
- **Proof Requirement**: For $(x, y) \mapsto (-y, x)$, applying twice gives $(-(-x), -y) = (-x, -y) = -(x, y)$.
- **Dependencies**: Ring arithmetic on $\mathbb{R}^2$.
- **Difficulty**: **Easy / Immediate**.

### Item 7: `RiemannDomain` instance for `CP1` (`j_smooth`)
- **Location**: `GromovCompactness/Geometry/Sphere.lean`, line 55
- **Declaration**:
  ```lean
  j_smooth : ∀ (z : CP1), ContMDiffAt I_CP1 𝓘(ℝ, TangentSpace I_CP1 z →L[ℝ] TangentSpace I_CP1 z) ∞ (fun w => j w) z
  ```
- **Proof Requirement**: The rotation operator has constant matrix representation in standard charts, so it is smooth.
- **Dependencies**: `ContMDiffAt_const`.
- **Difficulty**: **Easy / Medium**.

### Items 8 & 9: `MoebiusFrame.id` (`is_smooth` & `is_biholomorphic`)
- **Location**: `GromovCompactness/Geometry/Sphere.lean`, lines 73, 74
- **Declaration**:
  ```lean
  def MoebiusFrame.id : MoebiusFrame where
    toHomeo := Homeomorph.refl CP1
    is_smooth := sorry
    is_biholomorphic := sorry
  ```
- **Proof Requirement**:
  - `is_smooth`: `Homeomorph.refl` is smooth via `contMDiff_id`.
  - `is_biholomorphic`: `mfderiv` of identity is `ContinuousLinearMap.id`, so `mfderiv ... (j z v) = j z v = j (toHomeo z) (mfderiv ... v)`.
- **Dependencies**: `contMDiff_id`, `mfderiv_id`.
- **Difficulty**: **Immediate / Trivial**.

### Items 10 & 11: `MoebiusFrame.comp` (`is_smooth` & `is_biholomorphic`)
- **Location**: `GromovCompactness/Geometry/Sphere.lean`, lines 79, 80
- **Declaration**:
  ```lean
  def MoebiusFrame.comp (ϕ₁ ϕ₂ : MoebiusFrame) : MoebiusFrame where
    toHomeo := ϕ₂.toHomeo.trans ϕ₁.toHomeo
    is_smooth := sorry
    is_biholomorphic := sorry
  ```
- **Proof Requirement**:
  - `is_smooth`: `ContMDiff.comp ϕ₁.is_smooth ϕ₂.is_smooth`.
  - `is_biholomorphic`: Chain rule `mfderiv_comp` applied twice to commute with $j$.
- **Dependencies**: `ContMDiff.comp`, `mfderiv_comp`.
- **Difficulty**: **Easy**.

### Items 12 & 13: `MoebiusFrame.inv` (`is_smooth` & `is_biholomorphic`)
- **Location**: `GromovCompactness/Geometry/Sphere.lean`, lines 85, 86
- **Declaration**:
  ```lean
  def MoebiusFrame.inv (ϕ : MoebiusFrame) : MoebiusFrame where
    toHomeo := ϕ.toHomeo.symm
    is_smooth := sorry
    is_biholomorphic := sorry
  ```
- **Proof Requirement**: Inversion of a diffeomorphism is smooth; biholomorphicity follows from differentiating $\phi \circ \phi^{-1} = \mathrm{id}$.
- **Dependencies**: `ContMDiff.symm`, inverse derivative theorem.
- **Difficulty**: **Medium**.

### Item 14: `affine_scaling`
- **Location**: `GromovCompactness/Geometry/Sphere.lean`, line 94
- **Declaration**:
  ```lean
  def affine_scaling (a : ℂ) (λ_scale : ℝ) (hλ : 0 < λ_scale) : MoebiusFrame
  ```
- **Mathematical Statement**: The affine scaling $z \mapsto a + \lambda z$ extends as a biholomorphic automorphism of $\mathbb{CP}^1$ fixing $\infty$.
- **Dependencies**: Stereographic projection, conformal dilatations.
- **Difficulty**: **Medium**.

### Item 15: `inversion`
- **Location**: `GromovCompactness/Geometry/Sphere.lean`, line 99
- **Declaration**:
  ```lean
  def inversion : MoebiusFrame
  ```
- **Mathematical Statement**: $z \mapsto 1/z$ interchanging $0$ and $\infty$.
- **Dependencies**: Antipodal stereographic reflection.
- **Difficulty**: **Medium**.

### Item 16: `rotation`
- **Location**: `GromovCompactness/Geometry/Sphere.lean`, line 103
- **Declaration**:
  ```lean
  def rotation (θ : ℝ) : MoebiusFrame
  ```
- **Mathematical Statement**: $z \mapsto e^{i\theta} z$ isometric rotation around the north-south axis.
- **Dependencies**: $SO(2)$ subgroup of $SO(3)$.
- **Difficulty**: **Easy / Medium**.

### Item 17: `disk_at`
- **Location**: `GromovCompactness/Geometry/Sphere.lean`, line 108
- **Declaration**:
  ```lean
  def disk_at (a : ℂ) (r : ℝ) : Set CP1
  ```
- **Mathematical Statement**: Preimage of the Euclidean ball $B_r(a) \subset \mathbb{C}$ under stereographic projection.
- **Difficulty**: **Easy**.

### Item 18: `annulus_at`
- **Location**: `GromovCompactness/Geometry/Sphere.lean`, line 113
- **Declaration**:
  ```lean
  def annulus_at (a : ℂ) (r R : ℝ) : Set CP1
  ```
- **Mathematical Statement**: Preimage of the Euclidean annulus $A(r, R; a) = \{z : r < |z - a| < R\}$.
- **Difficulty**: **Easy**.

### Item 19: `exists_unique_moebius_three_points`
- **Location**: `GromovCompactness/Geometry/Sphere.lean`, line 126
- **Declaration**:
  ```lean
  theorem exists_unique_moebius_three_points (z₁ z₂ z₃ : CP1)
      (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
      (w₁ w₂ w₃ : CP1) (k12 : w₁ ≠ w₂) (k13 : w₁ ≠ w₃) (k23 : w₂ ≠ w₃) :
      ∃! (ϕ : MoebiusFrame), ϕ.toHomeo z₁ = w₁ ∧ ϕ.toHomeo z₂ = w₂ ∧ ϕ.toHomeo z₃ = w₃
  ```
- **Mathematical Statement**: Sharp 3-transitivity of $\operatorname{PSL}(2, \mathbb{C})$ on $\mathbb{CP}^1$ via cross-ratio.
- **Difficulty**: **Medium / Hard**.

### Item 20: `energyMeasureExtended`
- **Location**: `GromovCompactness/Analysis/Energy.lean`, line 44
- **Declaration**:
  ```lean
  noncomputable def energyMeasureExtended (u : CP1 → M) : MeasureTheory.Measure CP1
  ```
- **Mathematical Statement**: Borel measure with density $d\mu_u = \frac{1}{2} |du|_g^2 \, d\mathrm{vol}_{S^2}$.
- **Proof Requirement**: Construct via `MeasureTheory.Measure.withDensity` using the volume measure on $S^2$.
- **Dependencies**: `MeasureTheory.Measure.withDensity`, volume on Riemannian sphere.
- **Difficulty**: **Medium**.

### Item 21: `energy_additive`
- **Location**: `GromovCompactness/Analysis/Energy.lean`, line 67
- **Declaration**:
  ```lean
  theorem energy_additive (u : CP1 → M) {A₁ A₂ : Set CP1}
      (h_disj : Disjoint A₁ A₂) (hA₁ : MeasurableSet A₁) (hA₂ : MeasurableSet A₂) :
      energyMeasure I M u (A₁ ∪ A₂) = energyMeasure I M u A₁ + energyMeasure I M u A₂
  ```
- **Proof Requirement**: Follows from `measure_union` on disjoint measurable sets and `ENNReal.toReal_add`.
- **Dependencies**: `MeasureTheory.measure_union`, finiteness of energy measure.
- **Difficulty**: **Easy / Medium**.

### Item 22: `energy_conformal_invariant`
- **Location**: `GromovCompactness/Analysis/Energy.lean`, line 75
- **Declaration**:
  ```lean
  theorem energy_conformal_invariant (u : CP1 → M) (ϕ : MoebiusFrame) (A : Set CP1) :
      energyMeasure I M (u ∘ ϕ.toHomeo) (ϕ.toHomeo ⁻¹' A) = energyMeasure I M u A
  ```
- **Mathematical Statement**: In 2 dimensions, the Dirichlet energy $\frac{1}{2}\int |du|^2$ is invariant under conformal transformations.
- **Difficulty**: **Hard**.

### Items 23 & 24: `energy_eq_pullback_omega` (Statement Defect & Proof Body)
- **Location**: `GromovCompactness/Analysis/Energy.lean`, lines 81, 83
- **Declaration**:
  ```lean
  theorem energy_eq_pullback_omega (u : CP1 → M) (h_jhol : JHolomorphicOn I u Set.univ) (A : Set CP1) :
      energyMeasure I M u A = sorry := by sorry
  ```
- **Formal Defect & Fix**: Line 81 has `= sorry` on the right side of the equation! Must be replaced with the integral $\int_A u^* \omega$.
- **Mathematical Statement**: For $J$-holomorphic curves, $|du|_g^2 \, d\mathrm{vol} = 2 u^* \omega$.
- **Difficulty**: **Hard**.

### Item 25: `energy_point_null`
- **Location**: `GromovCompactness/Analysis/Energy.lean`, line 89
- **Declaration**:
  ```lean
  theorem energy_point_null (u : CP1 → M) (p : CP1) :
      energyMeasure I M u {p} = 0
  ```
- **Proof Requirement**: Singletons have Lebesgue/Riemannian volume zero, and measure with density inherits null sets.
- **Dependencies**: `MeasureTheory.Measure.withDensity_apply`, `MeasureTheory.null_set`.
- **Difficulty**: **Easy / Medium**.

### Items 26 & 27: `energy_circle_null` (Statement Defect & Proof Body)
- **Location**: `GromovCompactness/Analysis/Energy.lean`, lines 93, 94
- **Declaration**:
  ```lean
  theorem energy_circle_null (u : CP1 → M) (a : ℂ) (r : ℝ) (hr : 0 < r) :
      energyMeasure I M u (sorry : Set CP1) = 0 := by sorry
  ```
- **Formal Defect & Fix**: Line 93 specifies `(sorry : Set CP1)`. Must be replaced with the circle boundary $\partial D_r(a) = \{z \in \mathbb{CP}^1 : |z - a| = r\}$.
- **Proof Requirement**: 1-dimensional smooth submanifolds have 2-dimensional area zero.
- **Difficulty**: **Medium**.

### Item 28: `energy_moving_disk_continuous`
- **Location**: `GromovCompactness/Analysis/Energy.lean`, line 102
- **Declaration**:
  ```lean
  theorem energy_moving_disk_continuous (u : CP1 → M) (a : ℂ) :
      Continuous (fun (r : ℝ) => energyMeasure I M u (disk_at a r))
  ```
- **Proof Requirement**: Continuity follows from monotone convergence of measures and the fact that boundary circles have measure zero.
- **Difficulty**: **Medium**.

### Items 29 & 30: `SmoothLocalConvergesOn` (Definition Body Defect)
- **Location**: `GromovCompactness/Topology/SmoothLocal.lean`, line 47
- **Declaration**:
  ```lean
  def SmoothLocalConvergesOn (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1) : Prop :=
    ∀ (K : Set CP1), K ⊆ Ω → IsCompact K →
      ∀ (k : ℕ),
        Tendsto (fun n => sorry) atTop (nhds (sorry))
  ```
- **Formal Defect & Fix**: Two `sorry` tokens inside the definition body! The convergence condition must be made precise.
- **Difficulty**: **Medium / Structural Fix**.

### Items 31 & 32: `SmoothLocalConvergesVarying` (Definition Body Defect)
- **Location**: `GromovCompactness/Topology/SmoothLocal.lean`, line 55
- **Declaration**:
  ```lean
  def SmoothLocalConvergesVarying (Ω_seq : ℕ → Set CP1) (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1) : Prop :=
    ∀ (K : Set CP1), K ⊆ Ω → IsCompact K →
      (∃ N : ℕ, ∀ n ≥ N, K ⊆ Ω_seq n) ∧
      ∀ (k : ℕ), Tendsto (fun n => sorry) atTop (nhds (sorry))
  ```
- **Formal Defect & Fix**: Two `sorry` tokens inside the definition body!
- **Difficulty**: **Medium / Structural Fix**.

### Item 33: `smooth_local_limit_unique`
- **Location**: `GromovCompactness/Topology/SmoothLocal.lean`, line 65
- **Declaration**:
  ```lean
  theorem smooth_local_limit_unique
      (u_seq : ℕ → (CP1 → M)) (u₁ u₂ : CP1 → M) (Ω : Set CP1)
      (h_open : IsOpen Ω) (h_nonempty : Ω.Nonempty)
      (h₁ : SmoothLocalConvergesOn I u_seq u₁ Ω)
      (h₂ : SmoothLocalConvergesOn I u_seq u₂ Ω) :
      EqOn u₁ u₂ Ω
  ```
- **Proof Requirement**: Pointwise limit uniqueness in Hausdorff spaces.
- **Dependencies**: `tendsto_nhds_unique`, Hausdorff property of target $M$.
- **Difficulty**: **Easy** (once definition has $C^0$ pointwise convergence).

### Item 34: `smooth_local_jhol_closure`
- **Location**: `GromovCompactness/Topology/SmoothLocal.lean`, line 86
- **Declaration**:
  ```lean
  theorem smooth_local_jhol_closure [ClosedTameTarget I M]
      (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1)
      (h_conv : SmoothLocalConvergesOn I u_seq u_lim Ω)
      (h_jhol : ∀ n, JHolomorphicOn I (u_seq n) Ω) :
      JHolomorphicOn I u_lim Ω
  ```
- **Mathematical Statement**: The Cauchy-Riemann equation $\bar\partial_J u = 0$ is closed under $C^1_{\mathrm{loc}}$ limits.
- **Proof Requirement**: Differential convergence $du_n \to du$ and target continuity $J(u_n z) \to J(u z)$ imply $du(j v) = J(u z)(du(v))$.
- **Difficulty**: **Medium / Hard**.

### Item 35: `smooth_local_comp_moebius`
- **Location**: `GromovCompactness/Topology/SmoothLocal.lean`, line 99
- **Declaration**:
  ```lean
  theorem smooth_local_comp_moebius
      (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M) (Ω : Set CP1)
      (ϕ_seq : ℕ → MoebiusFrame) (ϕ_lim : MoebiusFrame)
      (h_u : SmoothLocalConvergesOn I u_seq u_lim Ω)
      (h_ϕ : Tendsto ϕ_seq atTop (nhds ϕ_lim)) :
      SmoothLocalConvergesOn I (fun n => u_seq n ∘ (ϕ_seq n).toHomeo)
        (u_lim ∘ ϕ_lim.toHomeo) (ϕ_lim.toHomeo ⁻¹' Ω)
  ```
- **Proof Requirement**: Chain rule and compact preimages under homeomorphisms.
- **Difficulty**: **Medium**.

### Item 36: `countable_diagonal_extraction`
- **Location**: `GromovCompactness/Topology/Subsequence.lean`, line 71
- **Declaration**:
  ```lean
  theorem countable_diagonal_extraction (σ_family : ℕ → SubseqMap)
      (h_nested : ∀ k, IsSubsequenceOf (σ_family (k + 1)) (σ_family k)) :
      ∃ (σ_diag : SubseqMap), ∀ k, ∃ N, ∀ n ≥ N, ∃ m, σ_diag.1 n = (σ_family k).1 m
  ```
- **Docstring**: `Cantor diagonal extraction for a countable family of nested subsequences.`
- **Mathematical Statement**: For nested subsequences $\sigma_0 \ge \sigma_1 \ge \sigma_2 \dots$, the diagonal sequence is eventually a subsequence of each $\sigma_k$.
- **Proof Requirement**: Inductive construction of strictly increasing diagonal indices $\sigma_{\mathrm{diag}}(n)$. For $n \ge k$, $\sigma_n$ is a sub-subsequence of $\sigma_k$, hence $\sigma_n(n) \in \mathrm{range}(\sigma_k)$.
- **Dependencies**: `Mathlib.Order.Monotone.Basic`, `Nat.find` or recursive construction.
- **Difficulty**: **Easy / Medium** (zero external dependencies).

### Item 37: `tree_degree_sum`
- **Location**: `GromovCompactness/Topology/SphereTree.lean`, line 93
- **Declaration**:
  ```lean
  theorem tree_degree_sum (tree : SphereTree) :
      let _ := tree.fintypeV
      ∑ v : tree.V, tree.adj.degree v = 2 * (Fintype.card tree.V - 1)
  ```
- **Docstring**: `Euler characteristic relation for trees: |E| = |V| - 1, hence ∑_{v ∈ V} deg(v) = 2(|V| - 1).`
- **Proof Requirement**: In Mathlib: Handshake lemma gives $\sum \operatorname{deg}(v) = 2|E|$; tree property gives $|E| = |V| - 1$.
- **Dependencies**: `SimpleGraph.sum_degrees_eq_twice_card_edges`, `SimpleGraph.IsTree.card_edgeFinset`.
- **Difficulty**: **Easy / Medium** (zero geometric dependencies).

### Item 38: `ghost_components_bound`
- **Location**: `GromovCompactness/Topology/SphereTree.lean`, line 116
- **Declaration**:
  ```lean
  theorem ghost_components_bound
      (lim : StableSphereTreeLimit I M)
      (P G : ℕ)
      (let _ := lim.tree.fintypeV;
       h_multivertex : 1 < Fintype.card lim.tree.V)
      (h_P : P = Fintype.card { v : lim.tree.V // is_principal_component I M lim v })
      (h_G : G = Fintype.card { v : lim.tree.V // is_ghost_component I M lim v }) :
      G ≤ P - 2 ∧ (let _ := lim.tree.fintypeV; Fintype.card lim.tree.V ≤ 2 * P - 2)
  ```
- **Docstring**: `The Ghost Component Bound Theorem (gromov_compactness.pdf Theorem 1 & Task F06).`
- **Mathematical Statement**: For unmarked stable sphere trees with $|V| > 1$, $G \le P - 2$ and $|V| \le 2P - 2$.
- **Proof Requirement**:
  1. $|V| = P + G$.
  2. $\sum_{v} \operatorname{deg}(v) = 2(P + G - 1)$.
  3. Ghost components have degree $\ge 3$, contributing $\ge 3G$.
  4. Principal components have degree $\ge 1$, contributing $\ge P$.
  5. $3G + P \le 2P + 2G - 2 \implies G \le P - 2$.
  6. $|V| = P + G \le P + (P - 2) = 2P - 2$.
- **Dependencies**: `tree_degree_sum`, `Fintype.card_subtype_add_card_subtype_compl`, `omega` or `linarith`.
- **Difficulty**: **Easy / Medium** (zero geometric dependencies).

### Item 39: `graft_trees`
- **Location**: `GromovCompactness/Topology/SphereTree.lean`, line 128
- **Declaration**:
  ```lean
  def graft_trees (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
      (p₁ : CP1) (p₂ : CP1) : SphereTree
  ```
- **Docstring**: `Tree grafting operation: attaching two stable sphere trees T1 and T2 by identifying a designated smooth point on T1 with a smooth point on T2.`
- **Proof Requirement**: Show that the sum of two trees connected by a single edge is a tree.
- **Dependencies**: `SimpleGraph.IsTree`, disjoint unions.
- **Difficulty**: **Medium**.

---

## 4. Elimination Priority and Phased Roadmap

To achieve zero-`sorry` status systematically and maximize proving velocity, the 32 `sorry` sites are partitioned into four execution priority tiers:

### Priority Tier 1: Zero-External-Dependency / Purely Combinatorial & Algebraic Proofs
*Can be implemented immediately without waiting for manifold differential geometry or measure theory:*
1. **F05 line 71 (`countable_diagonal_extraction`)** — Pure Cantor diagonal extraction on $\mathbb{N}$.
2. **F01 line 86 (`metric_J_invariant`)** — Pure algebraic expansion of symmetrized metric with $J^2 = -I$.
3. **F02 line 73, 74 (`MoebiusFrame.id`)** — `contMDiff_id` and derivative identity.
4. **F02 line 79, 80 (`MoebiusFrame.comp`)** — `ContMDiff.comp` and chain rule.
5. **F06 line 93 (`tree_degree_sum`)** — Handshake lemma + tree edge formula.
6. **F06 line 116 (`ghost_components_bound`)** — Arithmetic deduction from degree sum and stability.

### Priority Tier 2: Defect Repairs in Type Definitions & Signatures
*Must be rectified before downstream lemmas can compile:*
1. **F01 line 120 (`jholomorphic_coordinate_invariance`)** — Replace `= sorry` in hypothesis with proper biholomorphism condition.
2. **F04 lines 47 & 55 (`SmoothLocalConvergesOn`, `SmoothLocalConvergesVarying`)** — Replace `Tendsto (fun n => sorry) atTop (nhds (sorry))` with concrete uniform convergence of derivatives on compact subsets.
3. **F03 line 81 (`energy_eq_pullback_omega`)** — Replace `energyMeasure I M u A = sorry` with the integral $\int_A u^* \omega$.
4. **F03 line 93 (`energy_circle_null`)** — Replace `(sorry : Set CP1)` with circle boundary.
5. **F02 lines 108 & 113 (`disk_at`, `annulus_at`)** — Define concrete stereographic preimages.

### Priority Tier 3: Conformal Sphere Geometry & Möbius Transformations
*Establishes the geometric foundation of the domain $\mathbb{CP}^1$:*
1. **F02 lines 43, 51, 55 (`CP1.almostComplexStructure`, `j_sq`, `j_smooth`)** — Complex rotation on $S^2$.
2. **F02 lines 85, 86 (`MoebiusFrame.inv`)** — Diffeomorphism inversion.
3. **F02 lines 94, 99, 103 (`affine_scaling`, `inversion`, `rotation`)** — Specific Möbius generators.
4. **F02 line 126 (`exists_unique_moebius_three_points`)** — 3-point normalization.
5. **F06 line 128 (`graft_trees`)** — Tree grafting construction.

### Priority Tier 4: Measure Theory & Differential Manifold Analysis
*The analytically deepest portion of Phase 1:*
1. **F03 line 44 (`energyMeasureExtended`)** — Volume measure with density.
2. **F03 line 67 (`energy_additive`)** — Measure additivity.
3. **F03 line 89 (`energy_point_null`)** — Point nullity.
4. **F03 line 94 (`energy_circle_null`)** — Circle nullity.
5. **F03 line 102 (`energy_moving_disk_continuous`)** — Expanding disk continuity.
6. **F04 line 65 (`smooth_local_limit_unique`)** — Limit uniqueness in Hausdorff target.
7. **F04 line 86 (`smooth_local_jhol_closure`)** — PDE closure under $C^1_{\mathrm{loc}}$ limits.
8. **F04 line 99 (`smooth_local_comp_moebius`)** — Limit stability under Möbius precomposition.
9. **F01 line 141 (`exists_target_geometry_constants`)** — Injectivity and convexity radius on compact target.
10. **F03 line 75 (`energy_conformal_invariant`)** — 2D conformal invariance of Dirichlet energy.
11. **F03 line 83 (`energy_eq_pullback_omega`)** — Equivalence with symplectic 2-form integral.

---

## 5. Conclusion and Recommendations for Milestone 2

Phase 1 provides a clean mathematical decomposition, but 5 critical type-level `sorry` defects exist in `F01`, `F03`, and `F04`. 

### Recommended Action Plan:
1. **Milestone 2 (Immediate Target)**: Completely discharge `F05` (`Topology/Subsequence.lean`) by proving `countable_diagonal_extraction`. This gives an immediate zero-`sorry` module certified against Mathlib.
2. **Milestone 3**: Clear `F01` algebraic and geometric properties (`metric_J_invariant`, biholomorphic hypothesis correction), followed by `F02` frame identities (`id`, `comp`).
3. **Milestone 4**: Complete `F06` graph theorems (`tree_degree_sum`, `ghost_components_bound`) and resolve definition defects in `F03` and `F04`.
4. **Milestone 5**: Implement the analytical measure-theoretic and PDE convergence proofs to achieve total zero-`sorry` completion across all of Phase 1.
