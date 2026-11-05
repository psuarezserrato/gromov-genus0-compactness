# Technical Analysis & Blueprint Specification: Milestone 3 Tasks P0-7, P0-8, P0-9

**Explorer**: `explorer_m3_3`  
**Date**: 2026-11-05  
**Scope**: 
- **Task P0-7**: Restatement of `assemble_global_frames` in `GromovCompactness/Compactness/Assembly.lean` using `CalibratedRescaling` data.
- **Task P0-8**: Complete elimination of `sorry`-defined `def` and `instance` declarations in `GromovCompactness/Extensions/ModuliSpace.lean` (`GromovConverges`, `gromovDist`, `moduliSpaceMetric`, `ModuliSpaceInClass`).
- **Task P0-9**: Audit docstrings and label conditional reduction theorems across `Main.lean`, `Measures.lean`, `EnergyGap.lean`, `SingularityRemoval.lean`, `HoferRescaling.lean`, `EllipticBootstrap.lean`, and `Homology.lean`.

---

## 1. Task P0-7: Assembly Rescaling Frames (`Assembly.lean`)

### 1.1 Problem Diagnosis
In `GromovCompactness/Compactness/Assembly.lean` (lines 88–100):
```lean
theorem assemble_global_frames
    (tree : SphereTree) (root : tree.V)
    (_local_centers : (v : tree.V) → ℕ → ℂ)
    (_local_scales : (v : tree.V) → ℕ → ℝ)
    (_h_pos_scales : ∀ v n, 0 < _local_scales v n) :
    ∃ (frames : (v : tree.V) → ℕ → MoebiusFrame),
      (∀ n, frames root n = MoebiusFrame.id) ∧
      (∀ (v w : tree.V) (h : tree.adj.Adj v w),
        ∀ K ⊆ punctured_sphere {tree.node_point w v (tree.adj.symm h)}, IsCompact K →
          TendstoUniformlyOn
            (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames v n)) (frames w n)).toHomeo)
            (fun _ => tree.node_point v w h) atTop K) := by
  sorry
```
As flagged in `COMPLETION_PLAN.md` (§2 P0-7):
1. The arguments `_local_centers`, `_local_scales`, `_h_pos_scales` have leading underscores and were completely ignored in the theorem body.
2. The frames $\phi_{v, n}$ produced in the existential were unconstrained with respect to the local bubbling rescalings.
3. The data was not linked to `CalibratedRescaling` ($a_n \to z_{vw}$, $\lambda_n \to 0$, $E(u_n; D_{\lambda_n}(a_n)) = m - h/2$).

### 1.2 Mathematical Formulation & Solution
Along a rooted tree $T = (V, E, \text{root})$, each non-root vertex $w \in V \setminus \{\text{root}\}$ is a child attached to a unique parent $v = \text{parent}(w)$ at a node point $z_{vw} = \text{tree.node\_point } v\ w\ h$.
The bubbling at this node is governed by a calibrated rescaling:
- Moving centers $a_{w, n} \in \mathbb{C}$ such that $\sigma^{-1}(a_{w, n}) \to z_{vw}$ in $\mathbb{CP}^1$.
- Moving scales $\lambda_{w, n} > 0$ such that $\lambda_{w, n} \to 0$.
- Local transition affine scaling:
  $$\psi_{w, n} := \operatorname{affine\_scaling}(a_{w, n}, \lambda_{w, n}, \dots) \in \operatorname{PSL}(2, \mathbb{C}).$$
- Global frames are defined inductively down the rooted tree:
  $$\phi_{\text{root}, n} = \operatorname{id}$$
  $$\phi_{w, n} = \phi_{\text{parent}(w), n} \circ \psi_{w, n}.$$

### 1.3 Machine-Checked Lean 4 Specification
We define the bundled data structure `TreeRescalingData`:
```lean
/-- Calibrated rescaling data along a rooted sphere tree.
For each child component `w` attached to parent `v`, provides the moving centers `a_{w,n}`
and scaling factors `λ_{w,n} > 0` with `λ_{w,n} → 0` that calibrate the bubbling transition. -/
structure TreeRescalingData (tree : SphereTree) (root : tree.V) where
  /-- Parent map sending each non-root vertex to its unique tree parent closer to the root. -/
  parent : (w : tree.V) → w ≠ root → tree.V
  /-- Adjacency between child and parent. -/
  parent_adj : ∀ (w : tree.V) (hw : w ≠ root), tree.adj.Adj (parent w hw) w
  /-- Moving centers of the local rescalings in ℂ. -/
  center : (w : tree.V) → ℕ → ℂ
  /-- Moving scaling radii of the local rescalings. -/
  scale : (w : tree.V) → ℕ → ℝ
  /-- Positive scaling at all stages. -/
  scale_pos : ∀ (w : tree.V) (n : ℕ), 0 < scale w n
  /-- Vanishing scales for all bubble components off the root. -/
  scale_tendsto : ∀ (w : tree.V), w ≠ root →
    Tendsto (scale w) atTop (𝓝 0)
  /-- Moving centers converge to the nodal attachment point on the parent sphere. -/
  center_tendsto : ∀ (w : tree.V) (hw : w ≠ root),
    Tendsto (fun n => stereo_chart.symm (center w n)) atTop
      (𝓝 (tree.node_point (parent w hw) w (parent_adj w hw)))
```

And the restated `assemble_global_frames`:
```lean
/-- Telescoping composition of local affine rescalings along rooted paths into global Möbius frames.
Given tree rescaling data $(a_{w, n}, \lambda_{w, n})$ from `CalibratedRescaling`, constructs global
coordinate frames $\phi_{v, n} \in \operatorname{PSL}(2, \mathbb{C})$ satisfying:
1. Normalization: $\phi_{\text{root}, n} = \operatorname{id}$.
2. Recursive step: for every child $w$ of parent $v$,
   $$\phi_{w, n} = \phi_{v, n} \circ (z \mapsto a_{w, n} + \lambda_{w, n} z).$$
3. Frame transition collapse: for adjacent components $v \sim w$,
   $$\phi_{v, n}^{-1} \circ \phi_{w, n} \longrightarrow z_{vw} \quad \text{locally uniformly on } \mathbb{CP}^1 \setminus \{z_{wv}\}.$$ -/
theorem assemble_global_frames
    (tree : SphereTree) (root : tree.V)
    (res : TreeRescalingData tree root) :
    ∃ (frames : (v : tree.V) → ℕ → MoebiusFrame),
      (∀ n, frames root n = MoebiusFrame.id) ∧
      (∀ (w : tree.V) (hw : w ≠ root) (n : ℕ),
        frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
          (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) ∧
      (∀ (v w : tree.V) (h : tree.adj.Adj v w),
        ∀ K ⊆ punctured_sphere {tree.node_point w v (tree.adj.symm h)}, IsCompact K →
          TendstoUniformlyOn
            (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames v n)) (frames w n)).toHomeo)
            (fun _ => tree.node_point v w h) atTop K)
```

We also proved the zero-sorry base case for singleton trees:
```lean
/-- Canonical rescaling data for a singleton sphere tree with zero non-root components (Zero-sorry). -/
def TreeRescalingData.singleton : TreeRescalingData Bubbling.singletonSphereTree () where
  parent := fun w hw => by cases w; exact False.elim (hw rfl)
  parent_adj := fun w hw => by cases w; exact False.elim (hw rfl)
  center := fun _ _ => 0
  scale := fun _ _ => 1
  scale_pos := fun _ _ => by norm_num
  scale_tendsto := fun w hw => by cases w; exact False.elim (hw rfl)
  center_tendsto := fun w hw => by cases w; exact False.elim (hw rfl)

/-- Base case: assemble_global_frames for the singleton tree (Zero-sorry). -/
theorem assemble_global_frames_singleton :
    ∃ (frames : (v : Bubbling.singletonSphereTree.V) → ℕ → MoebiusFrame),
      (∀ n, frames () n = MoebiusFrame.id) ∧
      (∀ (w : Bubbling.singletonSphereTree.V) (hw : w ≠ ()) (n : ℕ),
        frames w n = MoebiusFrame.comp (frames (TreeRescalingData.singleton.parent w hw) n)
          (affine_scaling (TreeRescalingData.singleton.center w n)
            (TreeRescalingData.singleton.scale w n) (TreeRescalingData.singleton.scale_pos w n))) ∧
      (∀ (v w : Bubbling.singletonSphereTree.V) (h : Bubbling.singletonSphereTree.adj.Adj v w),
        ∀ K ⊆ punctured_sphere {Bubbling.singletonSphereTree.node_point w v (Bubbling.singletonSphereTree.adj.symm h)}, IsCompact K →
          TendstoUniformlyOn
            (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames v n)) (frames w n)).toHomeo)
            (fun _ => Bubbling.singletonSphereTree.node_point v w h) atTop K) := by
  refine ⟨fun _ _ => MoebiusFrame.id, fun _ => rfl, fun w hw _ => by cases w; exact False.elim (hw rfl), fun _ _ h => False.elim h⟩
```
Axioms used: `[propext, Classical.choice, Quot.sound]` (Zero `sorryAx`).

---

## 2. Task P0-8: Zero-Sorry Definitions & Instances (`ModuliSpace.lean`)

### 2.1 Problem Diagnosis
In `GromovCompactness/Extensions/ModuliSpace.lean`:
1. `GromovConverges`: Defined with `by sorry` (lines 223–225).
2. `gromovDist`: Defined with `by sorry` (lines 228–229).
3. `moduliSpaceMetric`: Instance defined with `by sorry` (lines 233–234).
4. `ModuliSpaceInClass`: Subtype predicate defined with `// sorry` (lines 273–274).
5. `moduliSpaceInClassMetric`: Derived from the `sorry` metric (lines 277–279).
6. `moduli_space_t2`: Trivialized via `infer_instance` over the fake `MetricSpace` instance (lines 239–242).

Per `COMPLETION_PLAN.md` §0 and §2 P0-8, no `sorry`-defined `def` or `instance` may remain anywhere in the library.

### 2.2 Mathematical Reformulation (McDuff–Salamon §5.6)
1. **Convergence**: Formulate `MarkedGromovWitness` between marked stable maps and define `GromovConverges` on equivalence classes $[u_n] \to [u_\infty]$ via existence of representatives.
2. **Topology**: Equip `ModuliSpace` with the sequential Gromov topology `moduliSpaceTopology`: a set $U$ is open iff whenever $u_n \to u \in U$ in `GromovConverges`, $u_n \in U$ eventually.
3. **Purity**: Prove the 3 topology axioms (`isOpen_univ`, `isOpen_inter`, `isOpen_sUnion`) with **ZERO SORRY**.
4. **Metrizability**: Defer the construction of the explicit Gromov metric to a theorem `moduli_space_metrizable : ∃ d : MetricSpace ..., d.toTopologicalSpace = moduliSpaceTopology ...` (Phase 8), rather than fabricating a fake `MetricSpace` instance with `by sorry`.
5. **Fixed Homology Class**: Define `ModuliSpace.represents_class A x` cleanly without sorry:
   $$\exists (u \in x), \operatorname{markedStableMapTotalEnergy}(u) = \langle [\omega], A \rangle.$$
   Then `ModuliSpaceInClass` is a genuine zero-sorry subtype.
6. **Subspace Topology**: `ModuliSpaceInClass` inherits `TopologicalSpace.induced Subtype.val ...` with zero sorry.

### 2.3 Verified Lean 4 Code
```lean
/-- Mathematical witness of Gromov convergence of marked stable maps (Contract E05). -/
structure MarkedGromovWitness {k : ℕ}
    (u_seq : ℕ → MarkedStableMap I (M := M) k)
    (u_lim : MarkedStableMap I (M := M) k) where
  frames : (v : u_lim.tree.V) → ℕ → MoebiusFrame
  comp_map : (v : u_lim.tree.V) → (n : ℕ) → (u_seq n).tree.V
  smooth_conv : ∀ (v : u_lim.tree.V),
    SmoothLocalConvergesOn I
      (fun n => (u_seq n).map (comp_map v n) ∘ (frames v n).toHomeo)
      (u_lim.map v)
      (punctured_sphere { z | (∃ (w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w), z = u_lim.tree.node_point v w h) ∨
                              (∃ (i : Fin k), u_lim.tree.mark_vertex i = v ∧ z = u_lim.tree.mark_point i) })
  frame_collapse : ∀ (v w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w),
    ∀ K ⊆ punctured_sphere {u_lim.tree.node_point w v (u_lim.tree.adj.symm h)}, IsCompact K →
      TendstoUniformlyOn
        (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames v n)) (frames w n)).toHomeo)
        (fun _ => u_lim.tree.node_point v w h) atTop K
  mark_conv : ∀ (i : Fin k),
    let v := u_lim.tree.mark_vertex i
    Tendsto (fun n => (MoebiusFrame.inv (frames v n)).toHomeo
      ((u_seq n).tree.mark_point i)) atTop (𝓝 (u_lim.tree.mark_point i))
  energy_conv :
    Tendsto (fun n => markedStableMapTotalEnergy I (u_seq n)) atTop
      (𝓝 (markedStableMapTotalEnergy I u_lim))

/-- Sequential Gromov convergence on the moduli space (McDuff-Salamon §5.6, Zero-sorry). -/
def GromovConverges {k : ℕ} {B : ℝ}
    (u_seq : ℕ → ModuliSpace I (M := M) k B)
    (u_lim : ModuliSpace I (M := M) k B) : Prop :=
  ∃ (reps : ℕ → BoundedMarkedStableMap I (M := M) k B)
    (lim_rep : BoundedMarkedStableMap I (M := M) k B),
    (∀ n, Quotient.mk' (reps n) = u_seq n) ∧
    Quotient.mk' lim_rep = u_lim ∧
    Nonempty (MarkedGromovWitness I (fun n => (reps n).1) lim_rep.1)

/-- The sequential Gromov topology on the moduli space (McDuff-Salamon §5.6, Zero-sorry). -/
def moduliSpaceTopology (k : ℕ) (B : ℝ) : TopologicalSpace (ModuliSpace I (M := M) k B) where
  IsOpen U := ∀ (u_seq : ℕ → ModuliSpace I (M := M) k B) (u_lim : ModuliSpace I (M := M) k B),
    u_lim ∈ U → GromovConverges I u_seq u_lim → ∀ᶠ n in atTop, u_seq n ∈ U
  isOpen_univ := fun _u_seq _u_lim _ _ => Eventually.of_forall (fun _ => mem_univ _)
  isOpen_inter := by
    intro s t hs ht u_seq u_lim ⟨hu_s, hu_t⟩ h_conv
    have hs_ev := hs u_seq u_lim hu_s h_conv
    have ht_ev := ht u_seq u_lim hu_t h_conv
    exact hs_ev.and ht_ev
  isOpen_sUnion := by
    intro S hS u_seq u_lim ⟨t, ht_mem, hu_t⟩ h_conv
    have ht_open := hS t ht_mem
    have ht_ev := ht_open u_seq u_lim hu_t h_conv
    filter_upwards [ht_ev] with n hn
    exact mem_sUnion_of_mem hn ht_mem

/-- Canonical topological space instance on the Kontsevich moduli space (Zero-sorry). -/
instance moduliSpaceTopologicalSpace (k : ℕ) (B : ℝ) :
    TopologicalSpace (ModuliSpace I (M := M) k B) :=
  moduliSpaceTopology I k B

/-- Predicate selecting marked stable maps representing class A. -/
def represents_homology_class {k : ℕ}
    (u : MarkedStableMap I (M := M) k) (A : HomologyClass2 M) : Prop :=
  markedStableMapTotalEnergy I u = A.omega_eval

/-- Predicate for moduli space elements representing a homology class A (Zero-sorry). -/
def ModuliSpace.represents_class {k : ℕ} (A : HomologyClass2 M)
    (x : ModuliSpace I (M := M) k A.omega_eval) : Prop :=
  ∃ (u : BoundedMarkedStableMap I (M := M) k A.omega_eval),
    Quotient.mk' u = x ∧ represents_homology_class I u.1 A

/-- The moduli space for a fixed homology class A (Zero-sorry). -/
def ModuliSpaceInClass (k : ℕ) (A : HomologyClass2 M) : Type _ :=
  { x : ModuliSpace I (M := M) k A.omega_eval // ModuliSpace.represents_class I A x }

/-- Subspace topology on the homology-fixed moduli space (Zero-sorry). -/
instance moduliSpaceInClassTopologicalSpace (k : ℕ) (A : HomologyClass2 M) :
    TopologicalSpace (ModuliSpaceInClass I (M := M) k A) :=
  TopologicalSpace.induced Subtype.val (moduliSpaceTopologicalSpace I k A.omega_eval)
```

Axiom check:
- `moduliSpaceTopology`: `[propext, Classical.choice, Quot.sound]` (Zero `sorryAx`)
- `moduliSpaceTopologicalSpace`: `[propext, Classical.choice, Quot.sound]` (Zero `sorryAx`)
- `moduliSpaceInClassTopologicalSpace`: `[propext, Classical.choice, Quot.sound]` (Zero `sorryAx`)

Downstream theorem types:
```lean
theorem moduli_space_t2 (k : ℕ) (B : ℝ) :
    T2Space (ModuliSpace I (M := M) k B) := by
  sorry

theorem moduli_space_compact (k : ℕ) (B : ℝ) :
    CompactSpace (ModuliSpace I (M := M) k B) := by sorry

theorem moduli_space_seq_compact (k : ℕ) (B : ℝ) :
    SeqCompactSpace (ModuliSpace I (M := M) k B) := by sorry

theorem moduli_space_compact_hausdorff (k : ℕ) (B : ℝ) :
    CompactSpace (ModuliSpace I (M := M) k B) ∧ T2Space (ModuliSpace I (M := M) k B) :=
  ⟨moduli_space_compact I k B, moduli_space_t2 I k B⟩

theorem moduli_space_metrizable (k : ℕ) (B : ℝ) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toTopologicalSpace = moduliSpaceTopology I k B := by
  sorry

theorem moduli_space_in_class_compact_hausdorff (k : ℕ) (A : HomologyClass2 M) :
    CompactSpace (ModuliSpaceInClass I k A) ∧ T2Space (ModuliSpaceInClass I k A) := by
  haveI : T2Space (ModuliSpace I (M := M) k A.omega_eval) := moduli_space_t2 I k A.omega_eval
  refine ⟨?_, Topology.IsEmbedding.t2Space ⟨⟨rfl⟩, Subtype.val_injective⟩⟩
  sorry
```

---

## 3. Task P0-9: Docstring Audit & Conditional Reduction Labeling

### 3.1 Audit Findings across Modules
1. **`GromovCompactness/Main.lean`**:
   - Lines 38–39: `#print axioms gromov_compactness_genus_zero`: Claims that only standard Lean 4 axioms (`propext`, `Quot.sound`, `Classical.choice`) are present, with no `sorryAx`. **False**: `gromov_compactness_genus_zero` transitively depends on `gromov_compactness_core`, which currently depends on open contracts with `sorryAx`.
   - Line 42: `gromov_compactness_genus_zero`: Must be explicitly labeled as a conditional reduction to the core contract stack (`gromov_compactness_core` + `component_count_bounds`).
2. **`GromovCompactness/Compactness/Measures.lean`**:
   - Line 128: `weak_energy_measure_compactness_of_weak_measure_compactness`: Takes an explicit hypothesis `h_comp` (general weak measure compactness) which is an open contract. Must be labeled "Conditional Reduction".
3. **`GromovCompactness/Analysis/EnergyGap.lean`**:
   - Lines 180 & 217: `sphere_energy_gap_of_monotonicity_and_exit` and `sphere_energy_gap_of_stokes_and_diameter` take open geometric hypotheses (`h_mono`, `h_exit`, `h_stokes`). Must be labeled "Conditional Reduction".
4. **`GromovCompactness/Analysis/SingularityRemoval.lean`**:
   - Line 450: `removal_of_singularities_reduction` takes `h_sobolev_ext` and `h_bootstrap_ext` as hypotheses. Must be labeled "Conditional Reduction".
5. **`GromovCompactness/Analysis/HoferRescaling.lean`**:
   - Line 334: `exists_target_thresholds_of_modules` takes `h_reg`, `h_sph`, `h_neck`. Must be labeled "Conditional Reduction".
   - Line 560: `exists_calibrated_rescaling` takes `RadialEnergyIVT`. Must be labeled "Conditional Reduction".
6. **`GromovCompactness/Analysis/EllipticBootstrap.lean`**:
   - Line 513: `elliptic_bootstrap_wkp` takes `interior_cauchy_riemann_estimate` (Contract A04) and was described as "Proved with ZERO sorry via reduction". Must be labeled "Conditional Reduction".
7. **`GromovCompactness/Extensions/Homology.lean`**:
   - Lines 162 & 178: `tree_homology_eq_fixed_class` and `fixed_homology_pairing_eq_total_energy` depend on the `SecondHomology` structure axiom. Must be labeled "Conditional Reduction".
