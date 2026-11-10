/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.HoferRescaling
import GromovCompactness.Topology.SmoothLocal
import GromovCompactness.Topology.Subsequence
import GromovCompactness.Topology.SphereTree
import GromovCompactness.Compactness.Defect
import GromovCompactness.Bubbling.LocalTree
import GromovCompactness.Geometry.NormalCharts
import Mathlib.Data.Fintype.Card

open scoped Manifold ContDiff Topology Classical
open Metric Set Filter GromovCompactness Classical

namespace GromovCompactness.Assembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Task G01: Assemble Global Frames and Prestable Limit

This module formalizes the global assembly of local bubble trees into a single prestable
sphere tree limit equipped with global Möbius coordinate frames, following Gromov (1985, §2.2),
Ivashkovich-Shevchishin (1999, §2.3), and `gromov_compactness.pdf` §2.3 & §3.7 (Task `G01`).

## Key Definitions & Theorems
- `PrestableLimitData`: Bundled structure containing the assembled combinatorial tree, component maps,
  global Möbius coordinate frames, nodal matching, local smooth convergence, frame transition collapse,
  and vanishing neck diameters.
- `assemble_global_frames`: Telescopes local affine frames into global Möbius frames in $\operatorname{PSL}(2, \mathbb{C})$.
- `assemble_prestable_limit`: Assembles the base map and all defect trees into a prestable limit.
-/

/-- Prestable sphere tree limit data produced by assembling the base curve
and defect bubble trees before root stabilization.
Every bubble vertex $v \ne \text{root}$ is already stable ($\operatorname{deg}(v) \ge 3$ if constant);
only the root vertex might be unstable (degree 1 or 2 while constant). -/
structure PrestableLimitData (u_seq : ℕ → (CP1 → M)) where
  /-- Underlying combinatorial sphere tree. -/
  tree : SphereTree
  /-- Designated root vertex corresponding to the base domain. -/
  root : tree.V
  /-- Component pseudo-holomorphic curves $u_v : \mathbb{CP}^1 \to M$. -/
  map : (v : tree.V) → (CP1 → M)
  /-- Each component map is smooth and $J$-holomorphic. -/
  is_jhol : ∀ (v : tree.V), JHolomorphicOn I I_CP1 (map v) Set.univ
  /-- Nodal matching condition: across every edge $v \sim w$, the curve images coincide at the node:
  $$u_v(z_{vw}) = u_w(z_{wv}).$$ -/
  nodal_match : ∀ (v w : tree.V) (h : tree.adj.Adj v w),
    map v (tree.node_point v w h) = map w (tree.node_point w v (tree.adj.adj_symm h))
  /-- Ghost stability off the root: every constant bubble component has degree $\ge 3$
  by Contract B05 (Ghost Branching). -/
  stable_off_root : ∀ (v : tree.V), v ≠ root → (∃ c : M, ∀ z : CP1, map v z = c) →
    3 ≤ tree.adj.degree v
  /-- Strictly increasing subsequence extraction map $\sigma : \mathbb{N} \to \mathbb{N}$. -/
  σ : Bookkeeping.SubseqMap
  /-- Global Möbius coordinate frames $\phi_{v, n} \in \operatorname{PSL}(2, \mathbb{C})$ for each component $v$. -/
  frames : (v : tree.V) → ℕ → MoebiusFrame
  /-- Root coordinate frame sequence $\phi_{\mathrm{root}, n} \in \operatorname{PSL}(2, \mathbb{C})$
  (equal to `MoebiusFrame.id` on the unpruned base sphere, and to the promoted child frame after ghost-root contraction). -/
  root_frame_id : ∃ ϕ_root : ℕ → MoebiusFrame, ∀ n, frames root n = ϕ_root n
  /-- Frame transition collapse (PDF §2.3 condition 2): for adjacent components $v \sim w$,
  $$\phi_{v, n}^{-1} \circ \phi_{w, n} \longrightarrow z_{vw} \quad \text{locally uniformly on } \mathbb{CP}^1 \setminus \{z_{wv}\}.$$ -/
  frame_collapse : ∀ (v w : tree.V) (h : tree.adj.Adj v w),
    ∀ K ⊆ punctured_sphere {tree.node_point w v (tree.adj.adj_symm h)}, IsCompact K →
      TendstoUniformlyOn
        (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames v n)) (frames w n)).toHomeo)
        (fun _ => tree.node_point v w h) atTop K
  /-- $C^\infty_{\mathrm{loc}}$ convergence on each component away from incident nodes:
  $$u_{\sigma(n)} \circ \phi_{v, n} \longrightarrow u_v \quad \text{on } \mathbb{CP}^1 \setminus Z_v.$$ -/
  smooth_conv : ∀ (v : tree.V),
    SmoothLocalConvergesOn I
      (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
      (map v)
      (punctured_sphere { z | ∃ (w : tree.V) (h : tree.adj.Adj v w), z = tree.node_point v w h })
  /-- Zero-defect singleton convergence at the attachment point of a degree-1 constant root:
  when `root` has degree 1 and `map root` is constant, the exterior of the unique child bubble `w₀`
  carries zero limiting energy, so the rescaled sequence on `w₀` also converges smoothly at the attachment node. -/
  ghost_root_deg_one_conv :
    tree.adj.degree root = 1 → (∃ c : M, ∀ z : CP1, map root z = c) →
    ∀ (w₀ : tree.V) (hw₀_adj : tree.adj.Adj root w₀),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (σ.1 n)) ∘ (frames w₀ n).toHomeo)
        (map w₀)
        {tree.node_point w₀ root (tree.adj.adj_symm hw₀_adj)}
  /-- Global energy conservation: $\lim_{n \to \infty} E(u_{\sigma(n)}) = \sum_{v \in V} E(u_v)$. -/
  energy_ident :
    Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
      (𝓝 (∑ v : tree.V, totalEnergy I (map v)))

/-- Calibrated rescaling data along a rooted sphere tree (Contract G01 / Task P0-7).
For each child component `w` attached to parent `v`, provides the moving centers `a_{w,n}`
and scaling factors `λ_{w,n} > 0` with `λ_{w,n} → 0` that calibrate the bubbling transition. -/
structure TreeRescalingData (tree : SphereTree) (root : tree.V) where
  /-- Parent map sending each non-root vertex to its unique tree parent closer to the root. -/
  parent : (w : tree.V) → w ≠ root → tree.V
  /-- Adjacency between child and parent. -/
  parent_adj : ∀ (w : tree.V) (hw : w ≠ root), tree.adj.Adj (parent w hw) w
  /-- Combinatorial depth from the root vertex. -/
  depth : tree.V → ℕ
  /-- Strict depth decrease when moving from a non-root vertex to its parent. -/
  depth_parent : ∀ (w : tree.V) (hw : w ≠ root), depth (parent w hw) < depth w
  /-- Every tree edge is oriented either from parent to child or from child to parent. -/
  adj_parent_or_child : ∀ (v w : tree.V) (_h : tree.adj.Adj v w),
    (∃ hw : w ≠ root, parent w hw = v) ∨ (∃ hv : v ≠ root, parent v hv = w)
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
  /-- Local forward collapse of child affine rescalings onto the parent nodal point away from the child attachment point. -/
  parent_collapse : ∀ (w : tree.V) (hw : w ≠ root) (h : tree.adj.Adj (parent w hw) w),
    ∀ K ⊆ punctured_sphere {tree.node_point w (parent w hw) (tree.adj.adj_symm h)}, IsCompact K →
      TendstoUniformlyOn
        (fun n => (affine_scaling (center w n) (scale w n) (scale_pos w n)).toHomeo)
        (fun _ => tree.node_point (parent w hw) w h) atTop K
  /-- Local inverse collapse of child affine rescalings onto the child attachment point away from the parent nodal point. -/
  child_collapse : ∀ (v : tree.V) (hv : v ≠ root) (h : tree.adj.Adj v (parent v hv)),
    ∀ K ⊆ punctured_sphere {tree.node_point (parent v hv) v (tree.adj.adj_symm h)}, IsCompact K →
      TendstoUniformlyOn
        (fun n => (MoebiusFrame.inv (affine_scaling (center v n) (scale v n) (scale_pos v n))).toHomeo)
        (fun _ => tree.node_point v (parent v hv) h) atTop K

/-- Identity action of left frame composition (Zero-sorry). -/
theorem frame_comp_id_left (ϕ : MoebiusFrame) :
    MoebiusFrame.comp MoebiusFrame.id ϕ = ϕ :=
  moebius_frame_id_comp ϕ

/-- Identity action of right frame composition (Zero-sorry). -/
theorem frame_comp_id_right (ϕ : MoebiusFrame) :
    MoebiusFrame.comp ϕ MoebiusFrame.id = ϕ :=
  moebius_frame_comp_id ϕ

/-- Associativity of frame composition along tree paths (Zero-sorry). -/
theorem frame_comp_assoc (ϕ₁ ϕ₂ ϕ₃ : MoebiusFrame) :
    MoebiusFrame.comp (MoebiusFrame.comp ϕ₁ ϕ₂) ϕ₃ =
    MoebiusFrame.comp ϕ₁ (MoebiusFrame.comp ϕ₂ ϕ₃) :=
  moebius_frame_comp_assoc ϕ₁ ϕ₂ ϕ₃

/-- Relative frame cancellation: $\phi_v^{-1} \circ (\phi_v \circ \psi) = \psi$ (Zero-sorry). -/
theorem frame_transition_rel (ϕ_v ψ : MoebiusFrame) :
    (MoebiusFrame.comp (MoebiusFrame.inv ϕ_v) (MoebiusFrame.comp ϕ_v ψ)).toHomeo = ψ.toHomeo := by
  ext x
  dsimp [MoebiusFrame.comp, MoebiusFrame.inv]
  simp

/-- Inverse relative frame cancellation: $(\phi_w \circ \psi)^{-1} \circ \phi_w = \psi^{-1}$ (Zero-sorry). -/
theorem frame_transition_rel_inv (ϕ_w ψ : MoebiusFrame) :
    (MoebiusFrame.comp (MoebiusFrame.inv (MoebiusFrame.comp ϕ_w ψ)) ϕ_w).toHomeo =
      (MoebiusFrame.inv ψ).toHomeo := by
  ext x
  dsimp [MoebiusFrame.comp, MoebiusFrame.inv]
  simp

/-- Frame transition collapse reduction: if local rescalings collapse to a node point,
the relative global frames collapse identically (Zero-sorry). -/
theorem transition_collapse_reduction
    (frames_v : ℕ → MoebiusFrame) (ψ : ℕ → MoebiusFrame) (p : CP1) (K : Set CP1)
    (h_collapse : TendstoUniformlyOn (fun n => (ψ n).toHomeo) (fun _ => p) atTop K) :
    TendstoUniformlyOn
      (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames_v n)) (MoebiusFrame.comp (frames_v n) (ψ n))).toHomeo)
      (fun _ => p) atTop K := by
  have h_eq : ∀ n, (MoebiusFrame.comp (MoebiusFrame.inv (frames_v n)) (MoebiusFrame.comp (frames_v n) (ψ n))).toHomeo =
      (ψ n).toHomeo := fun n => frame_transition_rel (frames_v n) (ψ n)
  simp_rw [h_eq]
  exact h_collapse

/-- Inverse frame transition collapse reduction: if inverse local rescalings collapse to a node point,
the child-to-parent relative global frames collapse identically (Zero-sorry). -/
theorem transition_collapse_reduction_inv
    (frames_w : ℕ → MoebiusFrame) (ψ : ℕ → MoebiusFrame) (p : CP1) (K : Set CP1)
    (h_collapse : TendstoUniformlyOn (fun n => (MoebiusFrame.inv (ψ n)).toHomeo) (fun _ => p) atTop K) :
    TendstoUniformlyOn
      (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (MoebiusFrame.comp (frames_w n) (ψ n))) (frames_w n)).toHomeo)
      (fun _ => p) atTop K := by
  have h_eq : ∀ n, (MoebiusFrame.comp (MoebiusFrame.inv (MoebiusFrame.comp (frames_w n) (ψ n))) (frames_w n)).toHomeo =
      (MoebiusFrame.inv (ψ n)).toHomeo := fun n => frame_transition_rel_inv (frames_w n) (ψ n)
  simp_rw [h_eq]
  exact h_collapse

/-- Recursive construction of global Möbius frames along a rooted tree by well-founded recursion on depth. -/
noncomputable def globalFrameAt
    (tree : SphereTree) (root : tree.V)
    (res : TreeRescalingData tree root) (v : tree.V) (n : ℕ) : MoebiusFrame :=
  if hv : v = root then
    MoebiusFrame.id
  else
    have _ : res.depth (res.parent v hv) < res.depth v := res.depth_parent v hv
    MoebiusFrame.comp (globalFrameAt tree root res (res.parent v hv) n)
      (affine_scaling (res.center v n) (res.scale v n) (res.scale_pos v n))
termination_by res.depth v

lemma globalFrameAt_root
    (tree : SphereTree) (root : tree.V)
    (res : TreeRescalingData tree root) (n : ℕ) :
    globalFrameAt tree root res root n = MoebiusFrame.id := by
  rw [globalFrameAt, dif_pos rfl]

lemma globalFrameAt_ne_root
    (tree : SphereTree) (root : tree.V)
    (res : TreeRescalingData tree root) (w : tree.V) (hw : w ≠ root) (n : ℕ) :
    globalFrameAt tree root res w n =
      MoebiusFrame.comp (globalFrameAt tree root res (res.parent w hw) n)
        (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n)) := by
  rw [globalFrameAt, dif_neg hw]

/-- Uniqueness of the recursively defined global frames: any family `frames` satisfying the root identity
and parent-child affine recursion equals `globalFrameAt tree root res` (`0 sorryAx`). -/
theorem frames_eq_globalFrameAt
    (tree : SphereTree) (root : tree.V)
    (res : TreeRescalingData tree root)
    (frames : (v : tree.V) → ℕ → MoebiusFrame)
    (h_root : ∀ n, frames root n = MoebiusFrame.id)
    (h_rec : ∀ (w : tree.V) (hw : w ≠ root) (n : ℕ),
      frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
        (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n)))
    (v : tree.V) (n : ℕ) :
    frames v n = globalFrameAt tree root res v n := by
  by_cases hv : v = root
  · subst hv
    rw [h_root n, globalFrameAt_root]
  · have _ : res.depth (res.parent v hv) < res.depth v := res.depth_parent v hv
    rw [h_rec v hv n, globalFrameAt_ne_root tree root res v hv n,
      frames_eq_globalFrameAt tree root res frames h_root h_rec (res.parent v hv) n]
termination_by res.depth v

theorem assemble_global_frames
    (tree : SphereTree) (root : tree.V)
    (res : TreeRescalingData tree root) :
    ∃ (frames : (v : tree.V) → ℕ → MoebiusFrame),
      (∀ n, frames root n = MoebiusFrame.id) ∧
      (∀ (w : tree.V) (hw : w ≠ root) (n : ℕ),
        frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
          (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) ∧
      (∀ (v w : tree.V) (h : tree.adj.Adj v w),
        ∀ K ⊆ punctured_sphere {tree.node_point w v (tree.adj.adj_symm h)}, IsCompact K →
          TendstoUniformlyOn
            (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames v n)) (frames w n)).toHomeo)
            (fun _ => tree.node_point v w h) atTop K) := by
  refine ⟨globalFrameAt tree root res, globalFrameAt_root tree root res,
    globalFrameAt_ne_root tree root res, ?_⟩
  intro v w h K hK_sub hK_comp
  rcases res.adj_parent_or_child v w h with ⟨hw, h_par⟩ | ⟨hv, h_par⟩
  · subst h_par
    have h_step : ∀ n, globalFrameAt tree root res w n =
        MoebiusFrame.comp (globalFrameAt tree root res (res.parent w hw) n)
          (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n)) :=
      globalFrameAt_ne_root tree root res w hw
    simp_rw [h_step]
    exact transition_collapse_reduction
      (globalFrameAt tree root res (res.parent w hw))
      (fun n => affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))
      (tree.node_point (res.parent w hw) w h) K
      (res.parent_collapse w hw h K hK_sub hK_comp)
  · subst h_par
    have h_step : ∀ n, globalFrameAt tree root res v n =
        MoebiusFrame.comp (globalFrameAt tree root res (res.parent v hv) n)
          (affine_scaling (res.center v n) (res.scale v n) (res.scale_pos v n)) :=
      globalFrameAt_ne_root tree root res v hv
    simp_rw [h_step]
    exact transition_collapse_reduction_inv
      (globalFrameAt tree root res (res.parent v hv))
      (fun n => affine_scaling (res.center v n) (res.scale v n) (res.scale_pos v n))
      (tree.node_point v (res.parent v hv) h) K
      (res.child_collapse v hv h K hK_sub hK_comp)

/-- Canonical rescaling data for a singleton sphere tree with zero non-root components (Zero-sorry). -/
def TreeRescalingData.singleton : TreeRescalingData Bubbling.singletonSphereTree () where
  parent := fun w hw => by cases w; exact False.elim (hw rfl)
  parent_adj := fun w hw => by cases w; exact False.elim (hw rfl)
  depth := fun _ => 0
  depth_parent := fun w hw => by cases w; exact False.elim (hw rfl)
  adj_parent_or_child := fun _ _ h => False.elim h
  center := fun _ _ => 0
  scale := fun _ _ => 1
  scale_pos := fun _ _ => by norm_num
  scale_tendsto := fun w hw => by cases w; exact False.elim (hw rfl)
  center_tendsto := fun w hw => by cases w; exact False.elim (hw rfl)
  parent_collapse := fun w hw => by cases w; exact False.elim (hw rfl)
  child_collapse := fun v hv => by cases v; exact False.elim (hv rfl)

/-- Any prestable limit data preserves the uniform energy bound $B$ (Zero-sorry). -/
theorem prestable_limit_energy_bound
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (pdata : PrestableLimitData I u_seq)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  have h_conv := pdata.energy_ident
  have h_le_B : ∀ n, totalEnergy I (u_seq (pdata.σ.1 n)) ≤ B := fun n => h_energy (pdata.σ.1 n)
  exact le_of_tendsto h_conv (Eventually.of_forall h_le_B)

/-- Construction of a prestable limit for a single non-bubbling curve sequence (Zero-sorry). -/
def prestable_limit_singleton
    (u_seq : ℕ → (CP1 → M)) (u_lim : CP1 → M)
    (h_jhol : JHolomorphicOn I I_CP1 u_lim Set.univ)
    (h_conv : SmoothLocalConvergesOn I u_seq u_lim Set.univ)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq n)) atTop (𝓝 (totalEnergy I u_lim))) :
    PrestableLimitData I u_seq where
  tree := Bubbling.singletonSphereTree
  root := ()
  map := fun _ => u_lim
  is_jhol := fun _ => h_jhol
  nodal_match := fun _ _ h => False.elim h
  stable_off_root := fun (v : Unit) h_ne => by
    cases v
    exact False.elim (h_ne rfl)
  σ := Bookkeeping.SubseqMap.id
  frames := fun _ _ => MoebiusFrame.id
  root_frame_id := ⟨_, fun _ => rfl⟩
  frame_collapse := fun _ _ h => False.elim h
  smooth_conv := fun (v : Unit) => by
    have h_empty : (punctured_sphere { z : CP1 | ∃ (w : Bubbling.singletonSphereTree.V) (h : Bubbling.singletonSphereTree.adj.Adj v w),
        z = Bubbling.singletonSphereTree.node_point v w h }) = Set.univ := by
      dsimp [punctured_sphere]
      have h_none : { z : CP1 | ∃ (w : Bubbling.singletonSphereTree.V) (h : Bubbling.singletonSphereTree.adj.Adj v w),
          z = Bubbling.singletonSphereTree.node_point v w h } = ∅ := by
        ext z
        simp only [mem_setOf_eq, not_exists, mem_empty_iff_false, iff_false]
        intro w h
        exact False.elim h
      rw [h_none, diff_empty]
    rw [h_empty]
    have h_seq : (fun n => (u_seq (Bookkeeping.SubseqMap.id.1 n)) ∘ ((fun _ _ => MoebiusFrame.id) v n).toHomeo) = u_seq := by
      ext n x
      rfl
    rw [h_seq]
    exact h_conv
  ghost_root_deg_one_conv := fun _ _ _ hw₀_adj => False.elim hw₀_adj
  energy_ident := by
    have h_sum : (∑ v : Bubbling.singletonSphereTree.V, totalEnergy I ((fun _ => u_lim) v)) = totalEnergy I u_lim := by
      change (∑ _v : Unit, totalEnergy I u_lim) = totalEnergy I u_lim
      simp
    rw [h_sum]
    exact h_energy

/-- Construction of a prestable limit for a single non-bubbling curve sequence along a subsequence (Zero-sorry). -/
def prestable_limit_singleton_subseq
    (u_seq : ℕ → (CP1 → M)) (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M)
    (h_jhol : JHolomorphicOn I I_CP1 u_lim Set.univ)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Set.univ)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 (totalEnergy I u_lim))) :
    PrestableLimitData I u_seq where
  tree := Bubbling.singletonSphereTree
  root := ()
  map := fun _ => u_lim
  is_jhol := fun _ => h_jhol
  nodal_match := fun _ _ h => False.elim h
  stable_off_root := fun (v : Unit) h_ne => by
    cases v; exact False.elim (h_ne rfl)
  σ := σ
  frames := fun _ _ => MoebiusFrame.id
  root_frame_id := ⟨_, fun _ => rfl⟩
  frame_collapse := fun _ _ h => False.elim h
  smooth_conv := fun (v : Unit) => by
    have h_empty : (punctured_sphere { z : CP1 | ∃ (w : Bubbling.singletonSphereTree.V) (h : Bubbling.singletonSphereTree.adj.Adj v w),
        z = Bubbling.singletonSphereTree.node_point v w h }) = Set.univ := by
      dsimp [punctured_sphere]
      have h_none : { z : CP1 | ∃ (w : Bubbling.singletonSphereTree.V) (h : Bubbling.singletonSphereTree.adj.Adj v w),
          z = Bubbling.singletonSphereTree.node_point v w h } = ∅ := by
        ext z
        simp only [mem_setOf_eq, not_exists, mem_empty_iff_false, iff_false]
        intro w h; exact False.elim h
      rw [h_none, diff_empty]
    rw [h_empty]
    have h_seq : (fun n => (u_seq (σ.1 n)) ∘ ((fun _ _ => MoebiusFrame.id) v n).toHomeo) = fun n => u_seq (σ.1 n) := by
      ext n x; rfl
    rw [h_seq]
    exact h_conv
  ghost_root_deg_one_conv := fun _ _ _ hw₀_adj => False.elim hw₀_adj
  energy_ident := by
    have h_sum : (∑ v : Bubbling.singletonSphereTree.V, totalEnergy I ((fun _ => u_lim) v)) = totalEnergy I u_lim := by
      change (∑ _v : Unit, totalEnergy I u_lim) = totalEnergy I u_lim
      simp
    rw [h_sum]
    exact h_energy

lemma rot_tendstoUniformlyOn_forward (rot : MoebiusFrame) {F : ℕ → CP1 → CP1} {target : CP1} {K : Set CP1}
    (h_col : TendstoUniformlyOn F (fun _ => target) atTop K) :
    TendstoUniformlyOn (fun n => rot.toHomeo ∘ F n) (fun _ => rot.toHomeo target) atTop K := by
  have h_uc : UniformContinuous rot.toHomeo :=
    CompactSpace.uniformContinuous_of_continuous rot.toHomeo.continuous
  exact h_uc.comp_tendstoUniformlyOn h_col

lemma rot_tendstoUniformlyOn_backward (rot : MoebiusFrame) {F : ℕ → CP1 → CP1} {target : CP1} {K : Set CP1}
    {avoid : CP1} (hK_sub : K ⊆ punctured_sphere (Set.singleton avoid)) (hK_cpt : IsCompact K)
    (h_col : ∀ K' ⊆ punctured_sphere (Set.singleton (rot.inv.toHomeo avoid)), IsCompact K' →
      TendstoUniformlyOn F (fun _ => target) atTop K') :
    TendstoUniformlyOn (fun n => F n ∘ rot.inv.toHomeo) (fun _ => target) atTop K := by
  let K' := rot.inv.toHomeo '' K
  have hK'_cpt : IsCompact K' := hK_cpt.image rot.inv.toHomeo.continuous
  have hK'_sub : K' ⊆ punctured_sphere (Set.singleton (rot.inv.toHomeo avoid)) := by
    rintro _ ⟨x, hx_K, rfl⟩
    have hx_ne : x ∉ (Set.singleton avoid : Set CP1) := (hK_sub hx_K).2
    refine ⟨mem_univ _, ?_⟩
    intro (hx_eq : rot.inv.toHomeo x ∈ Set.singleton (rot.inv.toHomeo avoid))
    have h_eq : rot.inv.toHomeo x = rot.inv.toHomeo avoid := Set.mem_singleton_iff.mp hx_eq
    exact hx_ne (Set.mem_singleton_iff.mpr (rot.inv.toHomeo.injective h_eq))
  have h_col' := h_col K' hK'_sub hK'_cpt
  have h_comp := h_col'.comp rot.inv.toHomeo
  have h_sub : K ⊆ rot.inv.toHomeo ⁻¹' K' := Set.subset_preimage_image rot.inv.toHomeo K
  exact h_comp.mono h_sub

/-- Partial grafted sphere tree obtained by grafting a subset `s ⊆ cdata.S` of local defect trees
onto the base curve `cdata.u₀`. -/
structure PartialRootGraftedTree
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ) (s : Finset CP1) where
  tree : SphereTree
  root : tree.V
  map : (v : tree.V) → (CP1 → M)
  is_jhol : ∀ (v : tree.V), JHolomorphicOn I I_CP1 (map v) Set.univ
  nodal_match : ∀ (v w : tree.V) (h : tree.adj.Adj v w),
    map v (tree.node_point v w h) = map w (tree.node_point w v (tree.adj.adj_symm h))
  root_map : map root = cdata.u₀
  root_nodal_points : ∀ (w : tree.V) (h : tree.adj.Adj root w),
    tree.node_point root w h ∈ s
  root_nodal_surj : ∀ p ∈ s, ∃ (w : tree.V) (h : tree.adj.Adj root w),
    tree.node_point root w h = p
  root_degree_ge : s.card ≤ tree.adj.degree root
  energy_sum : (∑ v : tree.V, totalEnergy I (map v)) =
    totalEnergy I cdata.u₀ + ∑ p ∈ s, m_defect p
  stable_off_root : ∀ (v : tree.V), v ≠ root → (∃ c : M, ∀ z : CP1, map v z = c) →
    3 ≤ tree.adj.degree v

/-- Empty subset base case for `PartialRootGraftedTree`: the singleton sphere tree at `cdata.u₀` (Zero-sorry). -/
noncomputable def partialRootGraftedTree_empty
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ) :
    PartialRootGraftedTree I u_seq B th cdata m_defect ∅ where
  tree := Bubbling.singletonSphereTree
  root := ()
  map _ := cdata.u₀
  is_jhol _ := cdata.u₀_jhol
  nodal_match _ _ h := False.elim h
  root_map := rfl
  root_nodal_points _ h := False.elim h
  root_nodal_surj := fun p hp => False.elim (Finset.notMem_empty p hp)
  root_degree_ge := Nat.zero_le _
  energy_sum := by
    have h_sum : (∑ _v : Bubbling.singletonSphereTree.V, totalEnergy I cdata.u₀) = totalEnergy I cdata.u₀ :=
      Fintype.sum_unique (fun _ : Unit => totalEnergy I cdata.u₀)
    rw [h_sum, Finset.sum_empty, add_zero]
  stable_off_root v hv := by
    rcases v
    exact False.elim (hv rfl)

/-- Inductive insertion step for `PartialRootGraftedTree`: grafting one local defect tree at `p₀ ∉ s` (Zero-sorry). -/
noncomputable def partialRootGraftedTree_insert
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (hm_sph : ∀ p ∈ cdata.S, th.ε_sph ≤ m_defect p)
    (s : Finset CP1) (p₀ : CP1) (hp₀_not_s : p₀ ∉ s) (hp₀_S : p₀ ∈ cdata.S)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect s)
    (C : Bubbling.LocalDefectTree I th (m_defect p₀) (cdata.u₀ p₀)) :
    PartialRootGraftedTree I u_seq B th cdata m_defect (insert p₀ s) := by
  have hp₁ : ∀ (w : P.tree.V) (h : P.tree.adj.Adj P.root w),
      p₀ ≠ P.tree.node_point P.root w h := by
    intro w h heq
    rw [heq] at hp₀_not_s
    exact hp₀_not_s (P.root_nodal_points w h)
  have hp₂ : ∀ (w : C.tree.V) (h : C.tree.adj.Adj C.root w),
      north_pole ≠ C.tree.node_point C.root w h :=
    fun w h => (C.root_north_pole_free w h).symm
  have hm_child : th.h ≤ m_defect p₀ := th.h_le_sph.trans (hm_sph p₀ hp₀_S)
  let T' := graft_trees P.tree C.tree P.root C.root p₀ north_pole hp₁ hp₂
  let map' : T'.V → (CP1 → M) := Sum.elim P.map C.map
  refine {
    tree := T'
    root := Sum.inl P.root
    map := map'
    is_jhol := fun v => by
      rcases v with u | w
      · exact P.is_jhol u
      · exact C.is_jhol w
    nodal_match := fun x y h => by
      rcases x with u | u <;> rcases y with w | w
      · exact P.nodal_match u w h
      · dsimp [T', graft_trees, graftNodePoint, map']
        rcases h with ⟨rfl, rfl⟩
        rw [P.root_map, C.root_attach]
      · dsimp [T', graft_trees, graftNodePoint, map']
        rcases h with ⟨rfl, rfl⟩
        rw [P.root_map, C.root_attach]
      · exact C.nodal_match u w h
    root_map := P.root_map
    root_nodal_points := fun y h => by
      rcases y with w | w
      · exact Finset.mem_insert_of_mem (P.root_nodal_points w h)
      · exact Finset.mem_insert_self p₀ s
    root_nodal_surj := fun p hp => by
      rcases Finset.mem_insert.mp hp with rfl | hp_s
      · refine ⟨Sum.inr C.root, ⟨rfl, rfl⟩, ?_⟩
        dsimp [T', graft_trees, graftNodePoint]
      · obtain ⟨w, h, heq⟩ := P.root_nodal_surj p hp_s
        refine ⟨Sum.inl w, h, ?_⟩
        dsimp [T', graft_trees, graftNodePoint]
        exact heq
    root_degree_ge := by
      rw [Finset.card_insert_of_notMem hp₀_not_s]
      have h_le1 : s.card + 1 ≤ P.tree.adj.degree P.root + 1 := Nat.add_le_add_right P.root_degree_ge 1
      have h_le2 := Bubbling.graft_degree_bridge_left P.tree C.tree P.root C.root
      exact h_le1.trans h_le2
    energy_sum := by
      have h_split := Bubbling.graft_trees_energy_sum P.tree C.tree P.root C.root
        p₀ north_pole hp₁ hp₂ (fun v => totalEnergy I (map' v))
      rw [h_split]
      change (∑ u : P.tree.V, totalEnergy I (P.map u)) + (∑ w : C.tree.V, totalEnergy I (C.map w)) =
        totalEnergy I cdata.u₀ + ∑ p ∈ insert p₀ s, m_defect p
      rw [P.energy_sum, C.energy_sum hm_child, Finset.sum_insert hp₀_not_s]
      ring
    stable_off_root := fun v hv h_const => by
      rcases v with u | w
      · have hu : u ≠ P.root := fun heq => hv (congrArg Sum.inl heq)
        have h_deg := P.stable_off_root u hu h_const
        exact h_deg.trans (Bubbling.graft_degree_ge_left P.tree C.tree P.root C.root u)
      · have h_stab := C.stable hm_child w h_const
        by_cases hw : w = C.root
        · subst hw
          simp only [↓reduceIte] at h_stab
          have h_add := Bubbling.ghost_child_stability_of_degree_two (C.tree.adj.degree C.root) h_stab
          exact h_add.trans (Bubbling.graft_degree_bridge_right P.tree C.tree P.root C.root)
        · simp only [hw, ↓reduceIte] at h_stab
          exact h_stab.trans (Bubbling.graft_degree_ge_right P.tree C.tree P.root C.root w)
  }

/-- Complete combinatorial and geometric grafting of all local defect trees onto the base curve `cdata.u₀` (Zero-sorry). -/
theorem graft_root_sphere_tree
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (hm_sph : ∀ p ∈ cdata.S, th.ε_sph ≤ m_defect p)
    (defect_trees : (p : CP1) → p ∈ cdata.S →
      Bubbling.LocalDefectTree I th (m_defect p) (cdata.u₀ p)) :
    Nonempty (PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S) := by
  have h_ind : ∀ (s : Finset CP1), s ⊆ cdata.S →
      Nonempty (PartialRootGraftedTree I u_seq B th cdata m_defect s) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      exact ⟨partialRootGraftedTree_empty I u_seq B th cdata m_defect⟩
    · intro p₀ s' hp₀_not_s ih hs_sub
      have hp₀_S : p₀ ∈ cdata.S := hs_sub (Finset.mem_insert_self p₀ s')
      have hs'_sub : s' ⊆ cdata.S := (Finset.subset_insert p₀ s').trans hs_sub
      obtain ⟨P⟩ := ih hs'_sub
      exact ⟨partialRootGraftedTree_insert I u_seq B th cdata m_defect hm_sph s' p₀ hp₀_not_s hp₀_S P (defect_trees p₀ hp₀_S)⟩
  exact h_ind cdata.S Finset.Subset.rfl

/-- Incident node set of the root sphere in a `PartialRootGraftedTree` coincides with `s`. -/
lemma root_sphere_nodal_set_eq
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ) (s : Finset CP1)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect s) :
    { z : CP1 | ∃ (w : P.tree.V) (h : P.tree.adj.Adj P.root w), z = P.tree.node_point P.root w h } = (s : Set CP1) := by
  ext z
  constructor
  · rintro ⟨w, h, rfl⟩
    exact Finset.mem_coe.mpr (P.root_nodal_points w h)
  · intro hz
    obtain ⟨w, h, heq⟩ := P.root_nodal_surj z (Finset.mem_coe.mp hz)
    exact ⟨w, h, heq.symm⟩

/-- Realized partial grafted sphere tree with global coordinate frames and local smooth convergence. -/
structure RealizedPartialRootGraftedTree
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ) (s : Finset CP1) extends PartialRootGraftedTree I u_seq B th cdata m_defect s where
  τ : Bookkeeping.SubseqMap
  frames : (v : tree.V) → ℕ → MoebiusFrame
  root_frame : ∀ n, frames root n = MoebiusFrame.id
  frame_collapse : ∀ (v w : tree.V) (h : tree.adj.Adj v w),
    ∀ K ⊆ punctured_sphere {tree.node_point w v (tree.adj.adj_symm h)}, IsCompact K →
      TendstoUniformlyOn (fun n => ⇑(MoebiusFrame.comp (MoebiusFrame.inv (frames v n)) (frames w n)).toHomeo)
        (fun _ => tree.node_point v w h) atTop K
  smooth_conv : ∀ (v : tree.V),
    SmoothLocalConvergesOn I
      (fun n => u_seq ((cdata.σ.comp τ).1 n) ∘ (frames v n).toHomeo)
      (map v)
      (punctured_sphere (if v = root then (cdata.S : Set CP1) else { z | ∃ (w : tree.V) (h : tree.adj.Adj v w), z = tree.node_point v w h }))
  ghost_root_deg_one_conv :
    s = cdata.S →
    tree.adj.degree root = 1 → (∃ c : M, ∀ z : CP1, map root z = c) →
    ∀ (w₀ : tree.V) (hw₀_adj : tree.adj.Adj root w₀),
      SmoothLocalConvergesOn I
        (fun n => u_seq ((cdata.σ.comp τ).1 n) ∘ (frames w₀ n).toHomeo)
        (map w₀)
        {tree.node_point w₀ root (tree.adj.adj_symm hw₀_adj)}

/-- Empty subset base case for `RealizedPartialRootGraftedTree`. -/
noncomputable def realized_partialRootGraftedTree_empty
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ) :
    RealizedPartialRootGraftedTree I u_seq B th cdata m_defect ∅ where
  toPartialRootGraftedTree := partialRootGraftedTree_empty I u_seq B th cdata m_defect
  τ := Bookkeeping.SubseqMap.id
  frames := fun _ _ => MoebiusFrame.id
  root_frame := fun _ => rfl
  frame_collapse := fun _ _ h => False.elim h
  smooth_conv := fun (v : Unit) => by
    rcases v
    split_ifs with h_root
    · have h_map : (partialRootGraftedTree_empty I u_seq B th cdata m_defect).map PUnit.unit = cdata.u₀ := rfl
      rw [h_map]
      have h_seq : (fun n => u_seq ((cdata.σ.comp Bookkeeping.SubseqMap.id).1 n) ∘ (MoebiusFrame.id : MoebiusFrame).toHomeo) =
          fun n => u_seq (cdata.σ.1 n) := by
        ext n z; rfl
      rw [h_seq]
      exact cdata.smooth_conv
    · exact False.elim (h_root rfl)
  ghost_root_deg_one_conv := fun _ _ _ _ hw₀_adj => False.elim hw₀_adj

/-- Inductive insertion step for `RealizedPartialRootGraftedTree`. -/
noncomputable def realized_partialRootGraftedTree_insert
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (hm_sph : ∀ p ∈ cdata.S, th.ε_sph ≤ m_defect p)
    (s : Finset CP1) (p₀ : CP1) (hp₀_not_s : p₀ ∉ s) (hp₀_S : p₀ ∈ cdata.S)
    (P : RealizedPartialRootGraftedTree I u_seq B th cdata m_defect s)
    (rot : MoebiusFrame) (a : ℂ) (h_rot : rot.toHomeo (stereo_chart.symm a) = p₀)
    (h_rot_tendsto : (cdata.S = {p₀} ∧ ∃ c : M, ∀ z : CP1, cdata.u₀ z = c) →
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n) ∘ rot.toHomeo)) atTop (𝓝 (m_defect p₀)))
    (C : Bubbling.RealizedLocalDefectTree I th (m_defect p₀) (cdata.u₀ p₀)
      (fun n => u_seq ((cdata.σ.comp P.τ).1 n) ∘ rot.toHomeo) a) :
    RealizedPartialRootGraftedTree I u_seq B th cdata m_defect (insert p₀ s) := by
  have hm_child : th.h ≤ m_defect p₀ := th.h_le_sph.trans (hm_sph p₀ hp₀_S)
  let P_base := partialRootGraftedTree_insert I u_seq B th cdata m_defect hm_sph s p₀ hp₀_not_s hp₀_S P.toPartialRootGraftedTree C.toLocalDefectTree
  have hp₁ : ∀ (w : P.tree.V) (h : P.tree.adj.Adj P.root w),
      p₀ ≠ P.tree.node_point P.root w h := by
    intro w h heq
    rw [heq] at hp₀_not_s
    exact hp₀_not_s (P.root_nodal_points w h)
  have hp₂ : ∀ (w : C.tree.V) (h : C.tree.adj.Adj C.root w),
      north_pole ≠ C.tree.node_point C.root w h :=
    fun w h => (C.root_north_pole_free w h).symm
  refine {
    toPartialRootGraftedTree := P_base
    τ := P.τ.comp C.σ
    frames := fun v n =>
      match v with
      | Sum.inl u => P.frames u (C.σ.1 n)
      | Sum.inr w => MoebiusFrame.comp rot (C.frames w n)
    root_frame := fun n => by
      dsimp [P_base, partialRootGraftedTree_insert]
      exact P.root_frame (C.σ.1 n)
    frame_collapse := fun x y h K hK_sub hK_cpt => by
      rcases x with u | w <;> rcases y with u' | w'
      · have h_col := P.frame_collapse u u' h K
        dsimp [P_base, partialRootGraftedTree_insert, graft_trees, graftNodePoint] at hK_sub ⊢
        exact Bookkeeping.tendstoUniformlyOn_subseq (h_col hK_sub hK_cpt) C.σ
      · rcases h with ⟨rfl, rfl⟩
        dsimp [P_base, partialRootGraftedTree_insert, graft_trees, graftNodePoint] at hK_sub ⊢
        have h_id : (fun n => ⇑((P.frames P.root (C.σ.1 n)).inv.comp (MoebiusFrame.comp rot (C.frames C.root n))).toHomeo) =
            (fun n => ⇑(MoebiusFrame.comp (MoebiusFrame.inv MoebiusFrame.id) (MoebiusFrame.comp rot (C.frames C.root n))).toHomeo) := by
          funext n
          rw [P.root_frame]
        rw [h_id]
        have h_eq : (fun n => ⇑(MoebiusFrame.comp (MoebiusFrame.inv MoebiusFrame.id) (MoebiusFrame.comp rot (C.frames C.root n))).toHomeo) =
            fun n => ⇑rot.toHomeo ∘ ⇑(C.frames C.root n).toHomeo := by
          funext n
          rw [MoebiusFrame.comp_inv_id_left]
          rfl
        have h_tgt : (fun _ : CP1 => p₀) = (fun _ => rot.toHomeo (stereo_chart.symm a)) := by
          funext; exact h_rot.symm
        rw [h_eq, h_tgt]
        exact rot_tendstoUniformlyOn_forward rot (C.root_collapse hm_child K hK_sub hK_cpt)
      · rcases h with ⟨rfl, rfl⟩
        dsimp [P_base, partialRootGraftedTree_insert, graft_trees, graftNodePoint] at hK_sub ⊢
        have h_id : (fun n => ⇑((MoebiusFrame.comp rot (C.frames C.root n)).inv.comp (P.frames P.root (C.σ.1 n))).toHomeo) =
            (fun n => ⇑(MoebiusFrame.comp (MoebiusFrame.inv (MoebiusFrame.comp rot (C.frames C.root n))) MoebiusFrame.id).toHomeo) := by
          funext n
          rw [P.root_frame]
        rw [h_id]
        have h_eq : (fun n => ⇑(MoebiusFrame.comp (MoebiusFrame.inv (MoebiusFrame.comp rot (C.frames C.root n))) MoebiusFrame.id).toHomeo) =
            fun n => ⇑(MoebiusFrame.inv (C.frames C.root n)).toHomeo ∘ ⇑rot.inv.toHomeo := by
          funext n
          rw [MoebiusFrame.comp_inv_id_right]
          rfl
        rw [h_eq]
        have h_avoid : rot.inv.toHomeo p₀ = stereo_chart.symm a := by
          have h_symm : rot.inv.toHomeo = rot.toHomeo.symm := rfl
          rw [h_symm, ← h_rot]
          exact rot.toHomeo.left_inv (stereo_chart.symm a)
        refine rot_tendstoUniformlyOn_backward rot hK_sub hK_cpt (fun K' hK'_sub hK'_cpt => ?_)
        rw [h_avoid] at hK'_sub
        exact C.root_inv_collapse hm_child K' hK'_sub hK'_cpt
      · have h_col := C.frame_collapse w w' h K
        dsimp [P_base, partialRootGraftedTree_insert, graft_trees, graftNodePoint] at hK_sub ⊢
        have h_id : (fun n => ⇑((MoebiusFrame.comp rot (C.frames w n)).inv.comp (MoebiusFrame.comp rot (C.frames w' n))).toHomeo) =
            fun n => ⇑((C.frames w n).inv.comp (C.frames w' n)).toHomeo := by
          funext n
          rw [MoebiusFrame.comp_inv_comp]
        rw [h_id]
        exact h_col hK_sub hK_cpt
    smooth_conv := fun v => by
      rcases v with u | w
      · have h_conv_u := P.smooth_conv u
        have h_sub := smooth_local_subseq I _ _ _ C.σ.2 h_conv_u
        have h_seq : (fun n => (fun k => u_seq ((cdata.σ.comp P.τ).1 k) ∘ (P.frames u k).toHomeo) (C.σ.1 n)) =
            (fun n => u_seq ((cdata.σ.comp (P.τ.comp C.σ)).1 n) ∘
              (match Sum.inl u with | Sum.inl u => P.frames u (C.σ.1 n) | Sum.inr w => MoebiusFrame.comp rot (C.frames w n)).toHomeo) := by
          ext n pt; rfl
        have h_dom : (punctured_sphere (if u = P.root then (cdata.S : Set CP1)
                                        else { z | ∃ w h, z = P.tree.node_point u w h })) =
            (punctured_sphere (if Sum.inl u = P_base.root then (cdata.S : Set CP1)
                               else { z | ∃ w' h', z = P_base.tree.node_point (Sum.inl u) w' h' })) := by
          by_cases hu : u = P.root
          · subst hu
            have h_root : Sum.inl P.root = P_base.root := rfl
            rw [if_pos rfl, if_pos h_root]
          · have hu_ne : Sum.inl u ≠ P_base.root := fun heq => hu (Sum.inl.inj heq)
            rw [if_neg hu, if_neg hu_ne]
            have h_set := graft_node_points_inl_nonroot P.tree C.tree P.root C.root p₀ north_pole hp₁ hp₂ u hu
            dsimp [P_base, partialRootGraftedTree_insert]
            rw [h_set]
        exact smooth_local_congr_domain (I := I) h_dom (smooth_local_congr_seq (I := I) h_seq h_sub)
      · have h_conv_w := C.smooth_conv hm_child w
        have h_map : C.map w = P_base.map (Sum.inr w) := rfl
        rw [← h_map]
        have h_seq : (fun n => (u_seq ((cdata.σ.comp P.τ).1 (C.σ.1 n)) ∘ rot.toHomeo) ∘ (C.frames w n).toHomeo) =
            (fun n => u_seq ((cdata.σ.comp (P.τ.comp C.σ)).1 n) ∘
              (match Sum.inr w with | Sum.inl u => P.frames u (C.σ.1 n) | Sum.inr w => MoebiusFrame.comp rot (C.frames w n)).toHomeo) := by
          ext n pt; rfl
        have h_dom : (punctured_sphere (if w = C.root then insert north_pole { z | ∃ w' h, z = C.tree.node_point w w' h }
                                        else { z | ∃ w' h, z = C.tree.node_point w w' h })) =
            (punctured_sphere (if Sum.inr w = P_base.root then (cdata.S : Set CP1)
                               else { z | ∃ w' h', z = P_base.tree.node_point (Sum.inr w) w' h' })) := by
          have hw_ne : Sum.inr w ≠ P_base.root := fun h => by cases h
          rw [if_neg hw_ne]
          by_cases hw : w = C.root
          · subst hw
            rw [if_pos rfl]
            have h_set := graft_node_points_inr_root P.tree C.tree P.root C.root p₀ north_pole hp₁ hp₂
            dsimp [P_base, partialRootGraftedTree_insert]
            rw [h_set]
          · rw [if_neg hw]
            have h_set := graft_node_points_inr_nonroot P.tree C.tree P.root C.root p₀ north_pole hp₁ hp₂ w hw
            dsimp [P_base, partialRootGraftedTree_insert]
            rw [h_set]
        exact smooth_local_congr_domain (I := I) h_dom (smooth_local_congr_seq (I := I) h_seq h_conv_w)
    ghost_root_deg_one_conv := by
      intro hs_eq h_deg h_const w₀ hw₀_adj
      have h_card_le := P_base.root_degree_ge
      rw [h_deg] at h_card_le
      have h_card_ins : (insert p₀ s).card = s.card + 1 := Finset.card_insert_of_notMem hp₀_not_s
      rw [h_card_ins] at h_card_le
      have hs_card0 : s.card = 0 := by omega
      have hs_empty : s = ∅ := Finset.card_eq_zero.mp hs_card0
      subst hs_empty
      rw [Finset.insert_empty] at hs_eq
      have hcdata_S : cdata.S = {p₀} := hs_eq.symm
      have h_u0_const : ∃ c : M, ∀ z : CP1, cdata.u₀ z = c := by
        rw [← P_base.root_map]; exact h_const
      have h_en_sub : Tendsto (fun n => totalEnergy I (u_seq ((cdata.σ.comp P.τ).1 n) ∘ rot.toHomeo)) atTop (𝓝 (m_defect p₀)) := by
        exact (h_rot_tendsto ⟨hcdata_S, h_u0_const⟩).comp P.τ.2.tendsto_atTop
      rcases w₀ with u | w
      · exfalso
        have h_br := Bubbling.graft_degree_bridge_left P.tree C.tree P.root C.root
        have h_le : P.tree.adj.degree P.root + 1 ≤ 1 := h_br.trans_eq h_deg
        have hu_adj : P.tree.adj.Adj P.root u := hw₀_adj
        have h_deg_ge : 0 < P.tree.adj.degree P.root := hu_adj.degree_pos_left
        omega
      · have hw_eq : w = C.root := hw₀_adj.2
        subst hw_eq
        have h_node : P_base.tree.node_point (Sum.inr C.root) P_base.root (P_base.tree.adj.adj_symm hw₀_adj) = north_pole := rfl
        rw [h_node]
        have h_map : P_base.map (Sum.inr C.root) = C.map C.root := rfl
        rw [h_map]
        have h_c_conv := C.root_conv_north_pole hm_child h_en_sub
        have h_seq : (fun n => (u_seq ((cdata.σ.comp P.τ).1 (C.σ.1 n)) ∘ rot.toHomeo) ∘ (C.frames C.root n).toHomeo) =
            fun n => u_seq ((cdata.σ.comp (P.τ.comp C.σ)).1 n) ∘
              (match Sum.inr C.root with | Sum.inl u => P.frames u (C.σ.1 n) | Sum.inr w => MoebiusFrame.comp rot (C.frames w n)).toHomeo := by
          ext n pt; rfl
        exact smooth_local_congr_seq (I := I) h_seq h_c_conv
  }

/-- Complete realized grafting of all local defect trees onto the base curve `cdata.u₀` (Zero-sorry). -/
theorem graft_root_sphere_tree_realized
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (hm_sph : ∀ p ∈ cdata.S, th.ε_sph ≤ m_defect p)
    (defect_trees : (p : CP1) → (hp : p ∈ cdata.S) →
      ∃ (rot : MoebiusFrame) (a : ℂ),
        rot.toHomeo (stereo_chart.symm a) = p ∧
        ((cdata.S = {p} ∧ ∃ c : M, ∀ z : CP1, cdata.u₀ z = c) →
          Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n) ∘ rot.toHomeo)) atTop (𝓝 (m_defect p))) ∧
        ∀ (τ : Bookkeeping.SubseqMap),
          Nonempty (Bubbling.RealizedLocalDefectTree I th (m_defect p) (cdata.u₀ p)
            (fun n => u_seq ((cdata.σ.comp τ).1 n) ∘ rot.toHomeo) a)) :
    Nonempty (RealizedPartialRootGraftedTree I u_seq B th cdata m_defect cdata.S) := by
  have h_ind : ∀ (s : Finset CP1), s ⊆ cdata.S →
      Nonempty (RealizedPartialRootGraftedTree I u_seq B th cdata m_defect s) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      exact ⟨realized_partialRootGraftedTree_empty I u_seq B th cdata m_defect⟩
    · intro p₀ s' hp₀_not_s ih hs_sub
      have hp₀_S : p₀ ∈ cdata.S := hs_sub (Finset.mem_insert_self p₀ s')
      have hs'_sub : s' ⊆ cdata.S := (Finset.subset_insert p₀ s').trans hs_sub
      obtain ⟨P⟩ := ih hs'_sub
      obtain ⟨rot, a, h_rot, h_tend, C_gen⟩ := defect_trees p₀ hp₀_S
      obtain ⟨C⟩ := C_gen P.τ
      exact ⟨realized_partialRootGraftedTree_insert I u_seq B th cdata m_defect hm_sph s' p₀ hp₀_not_s hp₀_S P rot a h_rot h_tend C⟩
  exact h_ind cdata.S Finset.Subset.rfl

/-- Cardinality of the non-root subtype `{v : V // v ≠ root}` plus one equals `Fintype.card V` (`0 sorryAx`). -/
theorem card_subtype_ne_root_add_one
    {V : Type*} [Fintype V] [DecidableEq V] (root : V) :
    Fintype.card {v : V // v ≠ root} + 1 = Fintype.card V := by
  have h1 : Fintype.card {v : V // v ≠ root} = (Finset.univ.filter (fun v : V => v ≠ root)).card :=
    Fintype.card_subtype (fun v : V => v ≠ root)
  have h2 : Finset.univ.filter (fun v : V => v ≠ root) = Finset.univ.erase root := by
    ext v; simp [and_comm]
  rw [h1, h2]
  exact Finset.card_erase_add_one (Finset.mem_univ root)

/-- Sum over `{v : V // v ≠ root}` equals the sum over `Finset.univ.erase root` (`0 sorryAx`). -/
theorem sum_subtype_ne_root_eq_sum_erase
    {V : Type*} [Fintype V] [DecidableEq V] (root : V) (f : V → ℝ) :
    (∑ v : {v : V // v ≠ root}, f v.1) = ∑ v ∈ Finset.univ.erase root, f v := by
  have h1 : Finset.univ.erase root = Finset.univ.filter (fun v => v ≠ root) := by
    ext v; simp [and_comm]
  rw [h1]
  exact (Finset.sum_subtype (Finset.univ.filter (fun v => v ≠ root)) (by simp) f).symm

/-- When `f root = 0`, the sum over `{v : V // v ≠ root}` equals the sum over all `v : V` (`0 sorryAx`). -/
theorem sum_subtype_ne_root_eq_sum_univ_of_zero
    {V : Type*} [Fintype V] [DecidableEq V] (root : V) (f : V → ℝ)
    (h_zero : f root = 0) :
    (∑ v : {v : V // v ≠ root}, f v.1) = ∑ v : V, f v := by
  rw [sum_subtype_ne_root_eq_sum_erase root f]
  have h_add := Finset.sum_erase_add (Finset.univ : Finset V) f (Finset.mem_univ root)
  rw [h_zero, add_zero] at h_add
  exact h_add

/-- In a connected simple graph, if `root` has degree `0`, every vertex equals `root` (`0 sorryAx`). -/
theorem eq_root_of_degree_zero_of_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_conn : G.Connected) (root : V)
    (h_deg0 : G.degree root = 0) (v : V) :
    v = root := by
  obtain ⟨p⟩ := h_conn root v
  match p with
  | SimpleGraph.Walk.nil => rfl
  | SimpleGraph.Walk.cons h_adj _ =>
    exfalso
    rename_i w _
    have hw : w ∈ G.neighborFinset root := (G.mem_neighborFinset root w).mpr h_adj
    have hpos : 0 < (G.neighborFinset root).card := Finset.card_pos.mpr ⟨w, hw⟩
    unfold SimpleGraph.degree at h_deg0
    omega

/-- When every vertex of `V` equals `root`, the sum over `V` equals `f root` (`0 sorryAx`). -/
theorem sum_univ_eq_single_root_of_all_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) (f : V → ℝ)
    (h_all_eq : ∀ v : V, v = root) :
    (∑ v : V, f v) = f root := by
  exact Finset.sum_eq_single root (fun v _ hne => False.elim (hne (h_all_eq v)))
    (fun h => False.elim (h (Finset.mem_univ root)))

/-- When `s = ∅`, the root vertex of `P.tree` has degree `0` (`0 sorryAx`). -/
theorem PartialRootGraftedTree.degree_root_eq_zero_of_empty
    {u_seq : ℕ → (CP1 → M)} {B : ℝ} {th : Bubbling.TargetThresholds I M}
    {cdata : Compactness.ConcentrationData I u_seq B th}
    {m_defect : CP1 → ℝ} {s : Finset CP1}
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect s)
    (hs : s = ∅) :
    P.tree.adj.degree P.root = 0 := by
  subst hs
  unfold SimpleGraph.degree
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  have h_adj : P.tree.adj.Adj P.root w := (P.tree.adj.mem_neighborFinset P.root w).mp hw
  exact Finset.notMem_empty _ (P.root_nodal_points w h_adj)

/-- When `s = ∅`, every vertex of `P.tree` equals `P.root` (`0 sorryAx`). -/
theorem PartialRootGraftedTree.eq_root_of_empty
    {u_seq : ℕ → (CP1 → M)} {B : ℝ} {th : Bubbling.TargetThresholds I M}
    {cdata : Compactness.ConcentrationData I u_seq B th}
    {m_defect : CP1 → ℝ} {s : Finset CP1}
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect s)
    (hs : s = ∅) (w : P.tree.V) :
    w = P.root :=
  eq_root_of_degree_zero_of_connected P.tree.adj P.tree.is_tree.connected P.root
    (P.degree_root_eq_zero_of_empty I hs) w

/-- Canonical rescaling data for any sphere tree whose vertices are all equal to `root` (`0 sorryAx`). -/
def TreeRescalingData.of_all_eq_root (tree : SphereTree) (root : tree.V)
    (h_all : ∀ w : tree.V, w = root) : TreeRescalingData tree root where
  parent := fun w hw => False.elim (hw (h_all w))
  parent_adj := fun w hw => False.elim (hw (h_all w))
  depth := fun _ => 0
  depth_parent := fun w hw => False.elim (hw (h_all w))
  adj_parent_or_child := fun v w h => by
    exfalso
    have hv : v = root := h_all v
    have hw : w = root := h_all w
    exact tree.adj.ne_of_adj h (hv.trans hw.symm)
  center := fun _ _ => 0
  scale := fun _ _ => 1
  scale_pos := fun _ _ => by norm_num
  scale_tendsto := fun w hw => False.elim (hw (h_all w))
  center_tendsto := fun w hw => False.elim (hw (h_all w))
  parent_collapse := fun w hw => False.elim (hw (h_all w))
  child_collapse := fun v hv => False.elim (hv (h_all v))

/-- When every vertex of `P.tree` equals `P.root`, `cdata.S = ∅`, and total energy converges along
`cdata.σ`, `extract_grafted_tree_rescaling_and_conv` holds with `0 sorryAx`. -/
theorem extract_grafted_tree_rescaling_and_conv_of_all_eq_root
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (h_all : ∀ w : P.tree.V, w = P.root)
    (hS : cdata.S = ∅)
    (h_en_tendsto : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) := by
  refine ⟨cdata.σ, TreeRescalingData.of_all_eq_root P.tree P.root h_all, ?_, h_en_tendsto⟩
  intro frames h_root_id _ v
  have hv : v = P.root := h_all v
  subst hv
  have h_seq : (fun n => (u_seq (cdata.σ.1 n)) ∘ (frames P.root n).toHomeo) =
      fun n => u_seq (cdata.σ.1 n) := by
    ext n z
    rw [h_root_id n]
    rfl
  rw [h_seq, P.root_map]
  have h_conv_univ : SmoothLocalConvergesOn I (fun n => u_seq (cdata.σ.1 n)) cdata.u₀ Set.univ := by
    have h_diff : Set.univ \ (cdata.S : Set CP1) = Set.univ := by
      rw [hS, Finset.coe_empty, Set.diff_empty]
    simpa [h_diff] using cdata.smooth_conv
  exact smooth_local_restriction I (fun n => u_seq (cdata.σ.1 n)) cdata.u₀ (Set.subset_univ _) h_conv_univ

/-- When every vertex of `P.tree` equals `P.root`, `cdata.S = ∅`, and total energy converges along
some sub-subsequence `cdata.σ.comp τ`, `extract_grafted_tree_rescaling_and_conv` holds with `0 sorryAx`. -/
theorem extract_grafted_tree_rescaling_and_conv_of_subseq_all_eq_root
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (h_all : ∀ w : P.tree.V, w = P.root)
    (hS : cdata.S = ∅)
    (τ : Bookkeeping.SubseqMap)
    (h_en_tendsto : Tendsto (fun n => totalEnergy I (u_seq ((cdata.σ.comp τ).1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) := by
  refine ⟨cdata.σ.comp τ, TreeRescalingData.of_all_eq_root P.tree P.root h_all, ?_, h_en_tendsto⟩
  intro frames h_root_id _ v
  have hv : v = P.root := h_all v
  subst hv
  have h_seq : (fun n => (u_seq ((cdata.σ.comp τ).1 n)) ∘ (frames P.root n).toHomeo) =
      fun n => (fun k => u_seq (cdata.σ.1 k)) (τ.1 n) := by
    ext n z
    rw [h_root_id n]
    rfl
  rw [h_seq, P.root_map]
  have h_conv_univ : SmoothLocalConvergesOn I (fun n => u_seq (cdata.σ.1 n)) cdata.u₀ Set.univ := by
    have h_diff : Set.univ \ (cdata.S : Set CP1) = Set.univ := by
      rw [hS, Finset.coe_empty, Set.diff_empty]
    simpa [h_diff] using cdata.smooth_conv
  have h_conv_sub : SmoothLocalConvergesOn I (fun n => (fun k => u_seq (cdata.σ.1 k)) (τ.1 n)) cdata.u₀ Set.univ :=
    smooth_local_subseq I (fun k => u_seq (cdata.σ.1 k)) cdata.u₀ Set.univ τ.2 h_conv_univ
  exact smooth_local_restriction I _ cdata.u₀ (Set.subset_univ _) h_conv_sub

/-- When `cdata.S = ∅` and total energy converges along `cdata.σ` (or a sub-subsequence `cdata.σ.comp τ`),
every vertex of `P.tree` automatically equals `P.root` (`PartialRootGraftedTree.eq_root_of_empty`),
giving `extract_grafted_tree_rescaling_and_conv` with `0 sorryAx`. -/
theorem extract_grafted_tree_rescaling_and_conv_of_empty_S
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (hS : cdata.S = ∅)
    (h_en_cases : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) ∨
      ∃ (τ : Bookkeeping.SubseqMap),
        Tendsto (fun n => totalEnergy I (u_seq ((cdata.σ.comp τ).1 n))) atTop
          (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) := by
  have h_all : ∀ w : P.tree.V, w = P.root := P.eq_root_of_empty I hS
  rcases h_en_cases with h_en | ⟨τ, h_en⟩
  · exact extract_grafted_tree_rescaling_and_conv_of_all_eq_root I u_seq B th cdata m_defect P
      h_all hS h_en
  · exact extract_grafted_tree_rescaling_and_conv_of_subseq_all_eq_root I u_seq B th cdata m_defect P
      h_all hS τ h_en

/-- When `B < th.ε_reg`, `cdata.S = ∅` automatically, so `extract_grafted_tree_rescaling_and_conv`
holds with `0 sorryAx` whenever total energy converges along `cdata.σ` (or `cdata.σ.comp τ`). -/
theorem extract_grafted_tree_rescaling_and_conv_of_lt_eps_reg
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (h_lt : B < th.ε_reg)
    (h_en_cases : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) ∨
      ∃ (τ : Bookkeeping.SubseqMap),
        Tendsto (fun n => totalEnergy I (u_seq ((cdata.σ.comp τ).1 n))) atTop
          (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) :=
  extract_grafted_tree_rescaling_and_conv_of_empty_S I u_seq B th cdata m_defect P
    (cdata.S_eq_empty_of_lt_eps_reg I u_seq B th h_lt) h_en_cases

/-- When `B < 2 * th.h`, `extract_grafted_tree_rescaling_and_conv` holds with `0 sorryAx`
whenever total energy converges along `cdata.σ` (or `cdata.σ.comp τ`). -/
theorem extract_grafted_tree_rescaling_and_conv_of_lt_two_mul_h
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (h_lt : B < 2 * th.h)
    (h_en_cases : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) ∨
      ∃ (τ : Bookkeeping.SubseqMap),
        Tendsto (fun n => totalEnergy I (u_seq ((cdata.σ.comp τ).1 n))) atTop
          (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) :=
  extract_grafted_tree_rescaling_and_conv_of_empty_S I u_seq B th cdata m_defect P
    (cdata.S_eq_empty_of_lt_two_mul_h I u_seq B th h_lt) h_en_cases

/-- When `B ≤ 0`, `extract_grafted_tree_rescaling_and_conv` holds with `0 sorryAx`
whenever total energy converges along `cdata.σ` (or `cdata.σ.comp τ`). -/
theorem extract_grafted_tree_rescaling_and_conv_of_nonpos_B
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (hB : B ≤ 0)
    (h_en_cases : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) ∨
      ∃ (τ : Bookkeeping.SubseqMap),
        Tendsto (fun n => totalEnergy I (u_seq ((cdata.σ.comp τ).1 n))) atTop
          (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) :=
  extract_grafted_tree_rescaling_and_conv_of_empty_S I u_seq B th cdata m_defect P
    (cdata.S_eq_empty_of_nonpos I u_seq B th hB) h_en_cases

/-- Diagonal subsequence and tree rescaling extraction for the grafted prestable sphere tree from
calibrated rescaling data along `globalFrameAt` (`0 sorryAx`). -/
theorem extract_grafted_tree_rescaling_and_conv_of_globalFrameAt
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root)
    (h_conv : ∀ (v : P.tree.V),
      SmoothLocalConvergesOn I
        (fun n => (u_seq (σ.1 n)) ∘ (globalFrameAt P.tree P.root res v n).toHomeo)
        (P.map v)
        (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h }))
    (h_en : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) := by
  refine ⟨σ, res, ?_, h_en⟩
  intro frames h_root h_rec v
  have h_eq : (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo) =
      (fun n => (u_seq (σ.1 n)) ∘ (globalFrameAt P.tree P.root res v n).toHomeo) := by
    ext n z
    rw [frames_eq_globalFrameAt P.tree P.root res frames h_root h_rec v n]
  rw [h_eq]
  exact h_conv v

/-- Diagonal subsequence and tree rescaling extraction for the grafted prestable sphere tree when
`cdata.S = ∅` or calibrated `globalFrameAt` rescaling data is given (`0 sorryAx`). -/
theorem extract_grafted_tree_rescaling_and_conv
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (h_root : (cdata.S = ∅ ∧
      (Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
          (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) ∨
        ∃ (τ : Bookkeeping.SubseqMap),
          Tendsto (fun n => totalEnergy I (u_seq ((cdata.σ.comp τ).1 n))) atTop
            (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)))) ∨
      (∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
        (∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (globalFrameAt P.tree P.root res v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
        Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
          (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)))) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) := by
  rcases h_root with h_emp | ⟨σ, res, h_conv, h_en⟩
  · exact extract_grafted_tree_rescaling_and_conv_of_empty_S I u_seq B th cdata m_defect P h_emp.1 h_emp.2
  · exact extract_grafted_tree_rescaling_and_conv_of_globalFrameAt I u_seq B th cdata m_defect P σ res h_conv h_en

/-- Unconditional `extract_grafted_tree_rescaling_and_conv` on `[Subsingleton M]` targets (`0 sorryAx`). -/
theorem extract_grafted_tree_rescaling_and_conv_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) := by
  have hS : cdata.S = ∅ := cdata.S_eq_empty_of_subsingleton I u_seq B th
  have h_en0 : ∀ u : CP1 → M, totalEnergy I u = 0 := by
    intro u
    have hu : u = fun _ => u north_pole := funext (fun z => Subsingleton.elim (u z) (u north_pole))
    rw [hu]
    exact Analysis.totalEnergy_const I (u north_pole)
  refine extract_grafted_tree_rescaling_and_conv_of_empty_S I u_seq B th cdata m_defect P hS (Or.inl ?_)
  simp [hS, h_en0]

/-- Unconditional `extract_grafted_tree_rescaling_and_conv` on `[DiscreteTopology M]` targets
for sequences of `J`-holomorphic spheres (`0 sorryAx`). -/
theorem extract_grafted_tree_rescaling_and_conv_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) := by
  have hS : cdata.S = ∅ := cdata.S_eq_empty_of_discrete I u_seq h_jhol B th
  have h_seq0 : ∀ n, totalEnergy I (u_seq (cdata.σ.1 n)) = 0 :=
    fun n => Analysis.totalEnergy_eq_zero_of_discrete I (u_seq (cdata.σ.1 n)) (h_jhol (cdata.σ.1 n)).1
  have h_u0 : totalEnergy I cdata.u₀ = 0 :=
    Analysis.totalEnergy_eq_zero_of_discrete I cdata.u₀ cdata.u₀_jhol.1
  refine extract_grafted_tree_rescaling_and_conv_of_empty_S I u_seq B th cdata m_defect P hS (Or.inl ?_)
  simp [hS, h_seq0, h_u0]

/-- Unconditional `extract_grafted_tree_rescaling_and_conv` when `B < th.ε_sph` and `u_seq` consists of
`J`-holomorphic spheres with `totalEnergy ≤ B` (`0 sorryAx`). -/
theorem extract_grafted_tree_rescaling_and_conv_of_B_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (h_lt : B < th.ε_sph) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) := by
  have hS : cdata.S = ∅ := cdata.S_eq_empty_of_B_lt_eps_sph I u_seq h_jhol B h_en th h_lt
  have h_seq0 : ∀ n, totalEnergy I (u_seq (cdata.σ.1 n)) = 0 :=
    fun n => Compactness.totalEnergy_eq_zero_of_jhol_of_totalEnergy_lt_eps_sph I th
      (u_seq (cdata.σ.1 n)) (h_jhol (cdata.σ.1 n)) ((h_en (cdata.σ.1 n)).trans_lt h_lt)
  have h_u0_const := cdata.u0_eq_const_north_pole_of_B_lt_eps_sph I u_seq h_jhol B h_en th h_lt
  have h_u0 : totalEnergy I cdata.u₀ = 0 := by
    rw [h_u0_const]
    exact Analysis.totalEnergy_const I (cdata.u₀ north_pole)
  refine extract_grafted_tree_rescaling_and_conv_of_empty_S I u_seq B th cdata m_defect P hS (Or.inl ?_)
  simp [hS, h_seq0, h_u0]

/-- Unconditional `extract_grafted_tree_rescaling_and_conv` when `totalEnergy I (u_seq (cdata.σ.1 n))`
is eventually `< th.ε_sph` (`0 sorryAx`). -/
theorem extract_grafted_tree_rescaling_and_conv_of_eventually_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (N₀ : ℕ) (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < th.ε_sph) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) := by
  have hS : cdata.S = ∅ := cdata.S_eq_empty_of_eventually_lt_eps_sph I u_seq h_jhol B th ⟨N₀, h_ev⟩
  have h_seq0 : ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) = 0 :=
    fun n hn => Compactness.totalEnergy_eq_zero_of_jhol_of_totalEnergy_lt_eps_sph I th
      (u_seq (cdata.σ.1 n)) (h_jhol (cdata.σ.1 n)) (h_ev n hn)
  have h_u0_const := cdata.u0_eq_const_north_pole_of_eventually_lt_eps_sph I u_seq h_jhol B th ⟨N₀, h_ev⟩
  have h_u0 : totalEnergy I cdata.u₀ = 0 := by
    rw [h_u0_const]
    exact Analysis.totalEnergy_const I (cdata.u₀ north_pole)
  have h_tendsto : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N₀, fun n hn => (h_seq0 n hn).symm⟩)
  refine extract_grafted_tree_rescaling_and_conv_of_empty_S I u_seq B th cdata m_defect P hS (Or.inl ?_)
  simpa [hS, h_u0] using h_tendsto

/-- Unconditional `extract_grafted_tree_rescaling_and_conv` when `B < th.h` and `u_seq` consists of
`J`-holomorphic spheres with `totalEnergy ≤ B` (`0 sorryAx`). -/
theorem extract_grafted_tree_rescaling_and_conv_of_B_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (h_en : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (h_lt : B < th.h) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) :=
  extract_grafted_tree_rescaling_and_conv_of_B_lt_eps_sph I u_seq h_jhol B h_en th cdata m_defect P
    (h_lt.trans_le th.h_le_sph)

/-- Unconditional `extract_grafted_tree_rescaling_and_conv` when `totalEnergy I (u_seq (cdata.σ.1 n))`
is eventually `< th.h` (`0 sorryAx`). -/
theorem extract_grafted_tree_rescaling_and_conv_of_eventually_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (N₀ : ℕ) (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < th.h) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) :=
  extract_grafted_tree_rescaling_and_conv_of_eventually_lt_eps_sph I u_seq h_jhol B th cdata m_defect P N₀
    (fun n hn => (h_ev n hn).trans_le th.h_le_sph)

/-- Unconditional `extract_grafted_tree_rescaling_and_conv` when `totalEnergy I (u_seq (cdata.σ.1 n))`
is eventually `≤ 0` (`0 sorryAx`). -/
theorem extract_grafted_tree_rescaling_and_conv_of_eventually_nonpos_energy
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (N₀ : ℕ) (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) ≤ 0) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) :=
  extract_grafted_tree_rescaling_and_conv_of_eventually_lt_eps_sph I u_seq h_jhol B th cdata m_defect P N₀
    (fun n hn => (h_ev n hn).trans_lt th.ε_sph_pos)

/-- When the concentration singular set `cdata.S` is empty, `graft_defect_trees_to_root` holds
with zero `sorry` directly from `prestable_limit_singleton_subseq`. -/
theorem graft_defect_trees_to_root_of_empty_S
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (m_defect : CP1 → ℝ)
    (hS : cdata.S = ∅)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  have h_conv_univ : SmoothLocalConvergesOn I (fun n => u_seq (cdata.σ.1 n)) cdata.u₀ Set.univ := by
    have h_diff : Set.univ \ (cdata.S : Set CP1) = Set.univ := by
      rw [hS, Finset.coe_empty, Set.diff_empty]
    simpa [h_diff] using cdata.smooth_conv
  have h_en_univ : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀)) := by
    simpa [hS] using h_energy
  let pdata := prestable_limit_singleton_subseq I u_seq cdata.σ cdata.u₀
    cdata.u₀_jhol h_conv_univ h_en_univ
  exact ⟨pdata, prestable_limit_energy_bound I u_seq B pdata h_energy_bdd⟩

/-- When `B < th.ε_reg`, `cdata.S = ∅` automatically, so `graft_defect_trees_to_root` holds
with `0 sorryAx` from `graft_defect_trees_to_root_of_empty_S`. -/
theorem graft_defect_trees_to_root_of_lt_eps_reg
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (m_defect : CP1 → ℝ)
    (h_lt : B < th.ε_reg)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  graft_defect_trees_to_root_of_empty_S I u_seq B th cdata h_energy_bdd m_defect
    (cdata.S_eq_empty_of_lt_eps_reg I u_seq B th h_lt) h_energy

/-- When `B < 2 * th.h`, `graft_defect_trees_to_root` holds with `0 sorryAx`. -/
theorem graft_defect_trees_to_root_of_lt_two_mul_h
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (m_defect : CP1 → ℝ)
    (h_lt : B < 2 * th.h)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  graft_defect_trees_to_root_of_empty_S I u_seq B th cdata h_energy_bdd m_defect
    (cdata.S_eq_empty_of_lt_two_mul_h I u_seq B th h_lt) h_energy

/-- When `B ≤ 0`, `graft_defect_trees_to_root` holds with `0 sorryAx`. -/
theorem graft_defect_trees_to_root_of_nonpos_B
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (m_defect : CP1 → ℝ)
    (hB : B ≤ 0)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  graft_defect_trees_to_root_of_empty_S I u_seq B th cdata h_energy_bdd m_defect
    (cdata.S_eq_empty_of_nonpos I u_seq B th hB) h_energy

/-- Zero-sorry prestable limit assembly when `B ≤ 0` and `totalEnergy I cdata.u₀ < th.ε_sph` (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_nonpos_B_and_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (hB : B ≤ 0)
    (h_lt : totalEnergy I cdata.u₀ < th.ε_sph) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  obtain ⟨m_defect, _hm_sph, _hm_zero, _h_decomp, h_tendsto_energy⟩ :=
    Compactness.defect_measure_identity_of_nonpos_B_and_lt_eps_sph I u_seq B th cdata hB h_lt
  exact graft_defect_trees_to_root_of_nonpos_B I u_seq B th cdata h_energy m_defect hB h_tendsto_energy

/-- When `B < th.ε_sph` and `u_seq` consists of `J`-holomorphic spheres with `totalEnergy ≤ B`,
`graft_defect_trees_to_root` holds unconditionally on any target manifold `M` (`0 sorryAx`). -/
theorem graft_defect_trees_to_root_of_B_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (m_defect : CP1 → ℝ)
    (h_lt : B < th.ε_sph)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  graft_defect_trees_to_root_of_empty_S I u_seq B th cdata h_energy_bdd m_defect
    (cdata.S_eq_empty_of_B_lt_eps_sph I u_seq h_jhol B h_energy_bdd th h_lt) h_energy

/-- When `totalEnergy I (u_seq (cdata.σ.1 n))` is eventually `< th.ε_sph`,
`graft_defect_trees_to_root` holds unconditionally on any target manifold `M` (`0 sorryAx`). -/
theorem graft_defect_trees_to_root_of_eventually_lt_eps_sph
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (m_defect : CP1 → ℝ)
    (N₀ : ℕ) (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < th.ε_sph)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  graft_defect_trees_to_root_of_empty_S I u_seq B th cdata h_energy_bdd m_defect
    (cdata.S_eq_empty_of_eventually_lt_eps_sph I u_seq h_jhol B th ⟨N₀, h_ev⟩) h_energy

/-- When `B < th.h` and `u_seq` consists of `J`-holomorphic spheres with `totalEnergy ≤ B`,
`graft_defect_trees_to_root` holds unconditionally on any target manifold `M` (`0 sorryAx`). -/
theorem graft_defect_trees_to_root_of_B_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (m_defect : CP1 → ℝ)
    (h_lt : B < th.h)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  graft_defect_trees_to_root_of_B_lt_eps_sph I u_seq h_jhol B th cdata h_energy_bdd m_defect
    (h_lt.trans_le th.h_le_sph) h_energy

/-- When `totalEnergy I (u_seq (cdata.σ.1 n))` is eventually `< th.h`,
`graft_defect_trees_to_root` holds unconditionally on any target manifold `M` (`0 sorryAx`). -/
theorem graft_defect_trees_to_root_of_eventually_lt_h
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (m_defect : CP1 → ℝ)
    (N₀ : ℕ) (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < th.h)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  graft_defect_trees_to_root_of_eventually_lt_eps_sph I u_seq h_jhol B th cdata h_energy_bdd m_defect N₀
    (fun n hn => (h_ev n hn).trans_le th.h_le_sph) h_energy

/-- When `totalEnergy I (u_seq (cdata.σ.1 n))` is eventually `≤ 0`,
`graft_defect_trees_to_root` holds unconditionally on any target manifold `M` (`0 sorryAx`). -/
theorem graft_defect_trees_to_root_of_eventually_nonpos_energy
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (m_defect : CP1 → ℝ)
    (N₀ : ℕ) (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) ≤ 0)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  graft_defect_trees_to_root_of_eventually_lt_eps_sph I u_seq h_jhol B th cdata h_energy_bdd m_defect N₀
    (fun n hn => (h_ev n hn).trans_lt th.ε_sph_pos) h_energy

/-- On a `[DiscreteTopology M]` target, `graft_defect_trees_to_root` holds unconditionally (`0 sorryAx`). -/
theorem graft_defect_trees_to_root_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (m_defect : CP1 → ℝ)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  graft_defect_trees_to_root_of_empty_S I u_seq B th cdata h_energy_bdd m_defect
    (cdata.S_eq_empty_of_discrete I u_seq h_jhol B th) h_energy

/-- On a `[Subsingleton M]` target, `graft_defect_trees_to_root` holds unconditionally (`0 sorryAx`). -/
theorem graft_defect_trees_to_root_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M))
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (m_defect : CP1 → ℝ)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  graft_defect_trees_to_root_of_empty_S I u_seq B th cdata h_energy_bdd m_defect
    (cdata.S_eq_empty_of_subsingleton I u_seq B th) h_energy

/-- Unconditional prestable limit assembly from `cdata` on `[Subsingleton M]` targets (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_cdata_of_subsingleton [Subsingleton M]
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  obtain ⟨m_defect, _hm_sph, _hm_zero, _h_decomp, h_tendsto_energy⟩ :=
    Compactness.defect_measure_identity_of_subsingleton I u_seq B th cdata
  exact graft_defect_trees_to_root_of_subsingleton I u_seq B th cdata h_energy m_defect h_tendsto_energy

/-- Unconditional prestable limit assembly from `cdata` on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_cdata_of_discrete [DiscreteTopology M]
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  obtain ⟨m_defect, _hm_sph, _hm_zero, _h_decomp, h_tendsto_energy⟩ :=
    Compactness.defect_measure_identity_of_discrete I u_seq h_jhol B th cdata
  exact graft_defect_trees_to_root_of_discrete I u_seq h_jhol B th cdata h_energy m_defect h_tendsto_energy

/-- Unconditional prestable limit assembly from `cdata` when `totalEnergy I (u_seq (cdata.σ.1 n))`
is eventually `< th.ε_sph` on any target manifold `M` (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_eventually_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (N₀ : ℕ) (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < th.ε_sph) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  obtain ⟨m_defect, _hm_sph, _hm_zero, _h_decomp, h_tendsto_energy⟩ :=
    Compactness.defect_measure_identity_of_eventually_lt_eps_sph I u_seq h_jhol B th cdata ⟨N₀, h_ev⟩
  exact graft_defect_trees_to_root_of_eventually_lt_eps_sph I u_seq h_jhol B th cdata h_energy m_defect
    N₀ h_ev h_tendsto_energy

/-- Unconditional prestable limit assembly from `cdata` when `B < th.ε_sph` on any target manifold `M` (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_B_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_lt : B < th.ε_sph) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  obtain ⟨m_defect, _hm_sph, _hm_zero, _h_decomp, h_tendsto_energy⟩ :=
    Compactness.defect_measure_identity_of_B_lt_eps_sph I u_seq h_jhol B h_energy th cdata h_lt
  exact graft_defect_trees_to_root_of_B_lt_eps_sph I u_seq h_jhol B th cdata h_energy m_defect h_lt h_tendsto_energy

/-- Unconditional prestable limit assembly from `cdata` when `B < th.h` on any target manifold `M` (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_B_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_lt : B < th.h) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_B_lt_eps_sph I th u_seq h_jhol B h_energy cdata
    (h_lt.trans_le th.h_le_sph)

/-- Unconditional prestable limit assembly from `cdata` when `B ≤ 0` on any target manifold `M` (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_nonpos_B_jhol
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (hB : B ≤ 0) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_B_lt_eps_sph I th u_seq h_jhol B h_energy cdata
    (hB.trans_lt th.ε_sph_pos)

/-- Unconditional prestable limit assembly from `cdata` when `totalEnergy I (u_seq (cdata.σ.1 n))`
is eventually `< th.h` on any target manifold `M` (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_eventually_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (N₀ : ℕ) (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) < th.h) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_eventually_lt_eps_sph I th u_seq h_jhol B h_energy cdata N₀
    (fun n hn => (h_ev n hn).trans_le th.h_le_sph)

/-- Unconditional prestable limit assembly from `cdata` when `totalEnergy I (u_seq (cdata.σ.1 n))`
is eventually `≤ 0` on any target manifold `M` (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_eventually_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (N₀ : ℕ) (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (cdata.σ.1 n)) ≤ 0) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_eventually_lt_eps_sph I th u_seq h_jhol B h_energy cdata N₀
    (fun n hn => (h_ev n hn).trans_lt th.ε_sph_pos)

/-- Grafting local defect trees at each concentration point p ∈ S onto the base curve u₀
(`0 sorryAx` from `graft_root_sphere_tree`, `assemble_global_frames`, and `prestable_limit_energy_bound`). -/
theorem graft_defect_trees_to_root
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (m_defect : CP1 → ℝ)
    (hm_sph : ∀ p ∈ cdata.S, th.ε_sph ≤ m_defect p)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)))
    (defect_trees : (p : CP1) → p ∈ cdata.S →
      Bubbling.LocalDefectTree I th (m_defect p) (cdata.u₀ p))
    (h_extract : ∀ (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S),
      ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
        (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
          (∀ n, frames P.root n = MoebiusFrame.id) →
          (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
            frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
              (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
          (∀ (v : P.tree.V),
            SmoothLocalConvergesOn I
              (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
              (P.map v)
              (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
          (P.tree.adj.degree P.root = 1 → (∃ c : M, ∀ z : CP1, P.map P.root z = c) →
            ∀ (w₀ : P.tree.V) (hw₀_adj : P.tree.adj.Adj P.root w₀),
              SmoothLocalConvergesOn I
                (fun n => (u_seq (σ.1 n)) ∘ (frames w₀ n).toHomeo)
                (P.map w₀)
                {P.tree.node_point w₀ P.root (P.tree.adj.adj_symm hw₀_adj)})) ∧
        Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
          (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  by_cases hS : cdata.S = ∅
  · exact graft_defect_trees_to_root_of_empty_S I u_seq B th cdata h_energy_bdd m_defect hS h_energy
  · obtain ⟨P⟩ := graft_root_sphere_tree I u_seq B th cdata m_defect hm_sph defect_trees
    obtain ⟨σ, res, h_conv, h_en_tendsto⟩ := h_extract P
    obtain ⟨frames, h_root_id, h_rec, h_collapse⟩ := assemble_global_frames P.tree P.root res
    let pdata : PrestableLimitData I u_seq := {
      tree := P.tree
      root := P.root
      map := P.map
      is_jhol := P.is_jhol
      nodal_match := P.nodal_match
      stable_off_root := P.stable_off_root
      σ := σ
      frames := frames
      root_frame_id := ⟨_, h_root_id⟩
      frame_collapse := h_collapse
      smooth_conv := (h_conv frames h_root_id h_rec).1
      ghost_root_deg_one_conv := (h_conv frames h_root_id h_rec).2
      energy_ident := by
        rw [P.energy_sum]
        exact h_en_tendsto
    }
    exact ⟨pdata, prestable_limit_energy_bound I u_seq B pdata h_energy_bdd⟩

/-- Zero-sorry conditional reduction of `assemble_prestable_limit` from concentration data (`cdata`),
defect measure decomposition (`m_defect`), local defect trees (`defect_trees`), and grafted tree rescaling (`h_extract`) (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_components
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (hm_sph : ∀ p ∈ cdata.S, th.ε_sph ≤ m_defect p)
    (h_tendsto_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)))
    (defect_trees : (p : CP1) → p ∈ cdata.S → Bubbling.LocalDefectTree I th (m_defect p) (cdata.u₀ p))
    (h_extract : ∀ (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S),
      ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
        (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
          (∀ n, frames P.root n = MoebiusFrame.id) →
          (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
            frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
              (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
          (∀ (v : P.tree.V),
            SmoothLocalConvergesOn I
              (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
              (P.map v)
              (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
          (P.tree.adj.degree P.root = 1 → (∃ c : M, ∀ z : CP1, P.map P.root z = c) →
            ∀ (w₀ : P.tree.V) (hw₀_adj : P.tree.adj.Adj P.root w₀),
              SmoothLocalConvergesOn I
                (fun n => (u_seq (σ.1 n)) ∘ (frames w₀ n).toHomeo)
                (P.map w₀)
                {P.tree.node_point w₀ P.root (P.tree.adj.adj_symm hw₀_adj)})) ∧
        Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
          (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  graft_defect_trees_to_root I u_seq B th cdata h_energy m_defect hm_sph h_tendsto_energy defect_trees h_extract

/-- Zero-sorry prestable limit assembly when a subsequence converges smoothly on all of `CP1`
with energy conservation (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_global_conv
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap) (u_lim : CP1 → M)
    (h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) u_lim Set.univ)
    (h_tendsto : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop (𝓝 (totalEnergy I u_lim))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  have h_lim_jhol : JHolomorphicOn I I_CP1 u_lim Set.univ :=
    smooth_local_jhol_closure I (fun n => u_seq (σ.1 n)) u_lim Set.univ h_conv
      (fun n => h_jhol (σ.1 n))
  let pdata := prestable_limit_singleton_subseq I u_seq σ u_lim h_lim_jhol h_conv h_tendsto
  exact ⟨pdata, prestable_limit_energy_bound I u_seq B pdata h_energy⟩

/-- Zero-sorry prestable limit assembly when `u_seq` has a constant subsequence (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_const_subseq
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap) (c : M)
    (h_const : ∀ n z, u_seq (σ.1 n) z = c) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  have h_conv : SmoothLocalConvergesOn I (fun n => u_seq (σ.1 n)) (fun _ => c) Set.univ := by
    have h_eq : (fun n => u_seq (σ.1 n)) = (fun _ _ => c) := by
      ext n z
      exact h_const n z
    rw [h_eq]
    exact smoothLocalConvergesOn_const_map I c Set.univ
  have h_en_eq : (fun n => totalEnergy I (u_seq (σ.1 n))) =
      fun _ => totalEnergy I (fun _ : CP1 => c) := by
    ext n
    have hn : u_seq (σ.1 n) = fun _ => c := funext (h_const n)
    rw [hn]
  have h_tendsto : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
      (𝓝 (totalEnergy I (fun _ : CP1 => c))) := by
    rw [h_en_eq]
    exact tendsto_const_nhds
  exact assemble_prestable_limit_of_global_conv I u_seq B h_jhol h_energy σ (fun _ => c)
    h_conv h_tendsto

/-- Zero-sorry prestable limit assembly when `u_seq` has an eventually constant subsequence (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_eventually_const_subseq
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ) (c : M)
    (h_ev : ∀ n ≥ N₀, ∀ z, u_seq (σ.1 n) z = c) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_const_subseq I u_seq B h_jhol h_energy
    (σ.comp (Compactness.shiftSubseqMap N₀)) c (fun n z => h_ev (n + N₀) (Nat.le_add_left N₀ n) z)

/-- Zero-sorry prestable limit assembly when concentration data `cdata` has `cdata.S = ∅` and
`cdata.μ = energyMeasureExtended I cdata.u₀` (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_cdata_mu_eq_energyMeasureExtended
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_eq : cdata.μ = energyMeasureExtended I cdata.u₀) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  obtain ⟨m_defect, _hm_sph, _hm_zero, _h_decomp, h_tendsto_energy⟩ :=
    Compactness.defect_measure_identity_of_mu_eq_energyMeasureExtended I u_seq B th cdata h_eq
  have hS : cdata.S = ∅ :=
    Compactness.singular_set_eq_empty_of_mu_eq_energyMeasureExtended I u_seq B th cdata h_eq
  exact graft_defect_trees_to_root_of_empty_S I u_seq B th cdata h_energy m_defect hS h_tendsto_energy

/-- Unconditional prestable limit assembly on subsingleton targets (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_const_subseq I u_seq B h_jhol h_energy
    Bookkeeping.SubseqMap.id (u_seq 0 north_pole)
    (fun n z => Subsingleton.elim (u_seq n z) (u_seq 0 north_pole))

/-- Unconditional prestable limit assembly on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_discrete [DiscreteTopology M]
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  obtain ⟨σ, c₀, hc₀⟩ := Compactness.exists_const_map_subseq_of_jhol_of_discrete I th u_seq h_jhol
  exact assemble_prestable_limit_of_const_subseq I u_seq B h_jhol h_energy σ c₀
    (fun n z => congr_fun (hc₀ n) z)

/-- Unconditional threshold-free prestable limit assembly on `[DiscreteTopology M]` targets (`0 sorryAx`). -/
theorem assemble_prestable_limit_univ_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  obtain ⟨th⟩ := Bubbling.exists_target_thresholds_of_discrete I (M := M)
  exact assemble_prestable_limit_of_discrete I th u_seq B h_jhol h_energy

/-- Unconditional prestable limit assembly when `B < th.ε_sph` and `u_seq` has a subsequence
with constant `north_pole` value (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_lt_eps_sph_of_const_north_pole
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < th.ε_sph)
    (σ : Bookkeeping.SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, u_seq (σ.1 n) north_pole = c₀) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  refine assemble_prestable_limit_of_const_subseq I u_seq B h_jhol h_energy σ c₀ (fun n z => ?_)
  have h_eq := Compactness.eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I th
    (u_seq (σ.1 n)) (h_jhol (σ.1 n)) ((h_energy (σ.1 n)).trans_lt h_lt)
  exact (congr_fun h_eq z).trans (hc₀ n)

/-- Unconditional prestable limit assembly when `B < th.h` and `u_seq` has a subsequence
with constant `north_pole` value (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_lt_h_of_const_north_pole
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < th.h)
    (σ : Bookkeeping.SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, u_seq (σ.1 n) north_pole = c₀) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_lt_eps_sph_of_const_north_pole I th u_seq B h_jhol h_energy
    (h_lt.trans_le th.h_le_sph) σ c₀ hc₀

/-- Push a `PrestableLimitData` on a subsequence `fun n => u_seq (σ.1 n)` back to `u_seq` (`0 sorryAx`). -/
def PrestableLimitData.of_subseq
    {u_seq : ℕ → (CP1 → M)}
    (σ : Bookkeeping.SubseqMap)
    (pdata : PrestableLimitData I (fun n => u_seq (σ.1 n))) :
    PrestableLimitData I u_seq where
  tree := pdata.tree
  root := pdata.root
  map := pdata.map
  is_jhol := pdata.is_jhol
  nodal_match := pdata.nodal_match
  stable_off_root := pdata.stable_off_root
  σ := σ.comp pdata.σ
  frames := pdata.frames
  root_frame_id := pdata.root_frame_id
  frame_collapse := pdata.frame_collapse
  smooth_conv := pdata.smooth_conv
  ghost_root_deg_one_conv := pdata.ghost_root_deg_one_conv
  energy_ident := pdata.energy_ident

/-- Zero-sorry prestable limit assembly directly from any `PrestableLimitData` on `u_seq` (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_pdata
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (pdata : PrestableLimitData I u_seq) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) ≤ B :=
  ⟨pdata, prestable_limit_energy_bound I u_seq B pdata h_energy⟩

/-- Zero-sorry prestable limit assembly from any `PrestableLimitData` on a subsequence `u_seq ∘ σ.1` (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_subseq_pdata
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (pdata : PrestableLimitData I (fun n => u_seq (σ.1 n))) :
    ∃ (pdata' : PrestableLimitData I u_seq),
      (∑ v : pdata'.tree.V, totalEnergy I (pdata'.map v)) ≤ B :=
  assemble_prestable_limit_of_pdata I u_seq B h_energy (PrestableLimitData.of_subseq I σ pdata)

/-- Unconditional prestable limit assembly when a subsequence `σ` eventually has `< th.ε_sph` energy
and constant `north_pole` value (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_eventually_lt_eps_sph_of_const_north_pole
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ)
    (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (σ.1 n)) < th.ε_sph)
    (c₀ : M)
    (hc₀ : ∀ n ≥ N₀, u_seq (σ.1 n) north_pole = c₀) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  refine assemble_prestable_limit_of_eventually_const_subseq I u_seq B h_jhol h_energy σ N₀ c₀ (fun n hn z => ?_)
  have h_eq := Compactness.eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I th
    (u_seq (σ.1 n)) (h_jhol (σ.1 n)) (h_ev n hn)
  exact (congr_fun h_eq z).trans (hc₀ n hn)

/-- Unconditional prestable limit assembly when a subsequence `σ` eventually has `< th.h` energy
and constant `north_pole` value (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_eventually_lt_h_of_const_north_pole
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ)
    (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (σ.1 n)) < th.h)
    (c₀ : M)
    (hc₀ : ∀ n ≥ N₀, u_seq (σ.1 n) north_pole = c₀) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_eventually_lt_eps_sph_of_const_north_pole I th u_seq B h_jhol h_energy
    σ N₀ (fun n hn => (h_ev n hn).trans_le th.h_le_sph) c₀ hc₀

/-- Unconditional prestable limit assembly when a subsequence `σ` eventually has `≤ 0` energy
and constant `north_pole` value (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_eventually_nonpos_energy_of_const_north_pole
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ)
    (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (σ.1 n)) ≤ 0)
    (c₀ : M)
    (hc₀ : ∀ n ≥ N₀, u_seq (σ.1 n) north_pole = c₀) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_eventually_lt_eps_sph_of_const_north_pole I th u_seq B h_jhol h_energy
    σ N₀ (fun n hn => (h_ev n hn).trans_lt th.ε_sph_pos) c₀ hc₀

/-- Unconditional prestable limit assembly when `B ≤ 0` and `u_seq` has a subsequence
with constant `north_pole` value (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_nonpos_B_of_const_north_pole
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (hB : B ≤ 0)
    (σ : Bookkeeping.SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, u_seq (σ.1 n) north_pole = c₀) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_lt_eps_sph_of_const_north_pole I th u_seq B h_jhol h_energy
    (hB.trans_lt th.ε_sph_pos) σ c₀ hc₀

/-- Unconditional prestable limit assembly when every globally `J`-holomorphic sphere is constant
and `u_seq` has a subsequence with constant `north_pole` value (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_all_jhol_const_of_const_north_pole
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c)
    (σ : Bookkeeping.SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, u_seq (σ.1 n) north_pole = c₀) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  refine assemble_prestable_limit_of_const_subseq I u_seq B h_jhol h_energy σ c₀ (fun n z => ?_)
  obtain ⟨c, hc⟩ := h_all_const (u_seq (σ.1 n)) (h_jhol (σ.1 n))
  rw [hc z, ← hc north_pole, hc₀ n]

/-- Unconditional `extract_grafted_tree_rescaling_and_conv` whenever every globally `J`-holomorphic
sphere is constant (`0 sorryAx`). -/
theorem extract_grafted_tree_rescaling_and_conv_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) :=
  extract_grafted_tree_rescaling_and_conv_of_eventually_nonpos_energy I u_seq h_jhol B th cdata m_defect P 0
    (fun n _ => by
      have h_eq := h_all_const (u_seq (cdata.σ.1 n)) (h_jhol (cdata.σ.1 n))
      rw [h_eq, Analysis.totalEnergy_const])

/-- Unconditional `graft_defect_trees_to_root` whenever every globally `J`-holomorphic sphere is
constant (`0 sorryAx`). -/
theorem graft_defect_trees_to_root_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (m_defect : CP1 → ℝ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  graft_defect_trees_to_root_of_eventually_nonpos_energy I u_seq h_jhol B th cdata h_energy_bdd m_defect 0
    (fun n _ => by
      have h_eq := h_all_const (u_seq (cdata.σ.1 n)) (h_jhol (cdata.σ.1 n))
      rw [h_eq, Analysis.totalEnergy_const])
    h_energy

/-- Unconditional prestable limit assembly from `cdata` whenever every globally `J`-holomorphic
sphere is constant (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_cdata_of_all_jhol_const
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_eventually_nonpos_energy I th u_seq h_jhol B h_energy cdata 0
    (fun n _ => by
      have h_eq := h_all_const (u_seq (cdata.σ.1 n)) (h_jhol (cdata.σ.1 n))
      rw [h_eq, Analysis.totalEnergy_const])

/-- Unconditional prestable limit assembly when every globally `J`-holomorphic sphere is constant
and `u_seq` has a subsequence with eventually constant `north_pole` value (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_all_jhol_const_of_eventually_const_north_pole
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ) (c₀ : M)
    (hc₀ : ∀ n ≥ N₀, u_seq (σ.1 n) north_pole = c₀) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  refine assemble_prestable_limit_of_eventually_const_subseq I u_seq B h_jhol h_energy σ N₀ c₀
    (fun n hn z => ?_)
  obtain ⟨c, hc⟩ := h_all_const (u_seq (σ.1 n)) (h_jhol (σ.1 n))
  rw [hc z, ← hc north_pole, hc₀ n hn]

/-- Unconditional `extract_grafted_tree_rescaling_and_conv` when `u_seq (cdata.σ.1 n)` is eventually
constant among `J`-holomorphic spheres (`0 sorryAx`). -/
theorem extract_grafted_tree_rescaling_and_conv_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (N₀ : ℕ)
    (h_ev_const : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq (cdata.σ.1 n)) Set.univ →
      u_seq (cdata.σ.1 n) = fun _ => u_seq (cdata.σ.1 n) north_pole) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) :=
  extract_grafted_tree_rescaling_and_conv_of_eventually_nonpos_energy I u_seq h_jhol B th cdata m_defect P N₀
    (fun n hn => by
      have h_eq := h_ev_const n hn (h_jhol (cdata.σ.1 n))
      rw [h_eq, Analysis.totalEnergy_const])

/-- Unconditional `graft_defect_trees_to_root` when `u_seq (cdata.σ.1 n)` is eventually constant
among `J`-holomorphic spheres (`0 sorryAx`). -/
theorem graft_defect_trees_to_root_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (m_defect : CP1 → ℝ)
    (N₀ : ℕ)
    (h_ev_const : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq (cdata.σ.1 n)) Set.univ →
      u_seq (cdata.σ.1 n) = fun _ => u_seq (cdata.σ.1 n) north_pole)
    (h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  graft_defect_trees_to_root_of_eventually_nonpos_energy I u_seq h_jhol B th cdata h_energy_bdd m_defect N₀
    (fun n hn => by
      have h_eq := h_ev_const n hn (h_jhol (cdata.σ.1 n))
      rw [h_eq, Analysis.totalEnergy_const])
    h_energy

/-- Unconditional prestable limit assembly from `cdata` when `u_seq (cdata.σ.1 n)` is eventually
constant among `J`-holomorphic spheres (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_cdata_of_eventually_all_jhol_const
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (N₀ : ℕ)
    (h_ev_const : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq (cdata.σ.1 n)) Set.univ →
      u_seq (cdata.σ.1 n) = fun _ => u_seq (cdata.σ.1 n) north_pole) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_eventually_nonpos_energy I th u_seq h_jhol B h_energy cdata N₀
    (fun n hn => by
      have h_eq := h_ev_const n hn (h_jhol (cdata.σ.1 n))
      rw [h_eq, Analysis.totalEnergy_const])

/-- Unconditional prestable limit assembly when every globally `J`-holomorphic sphere equals its
`north_pole` value and `u_seq` has a subsequence with eventually constant `north_pole` value (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_all_jhol_eq_north_pole_of_eventually_const_north_pole
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ) (c₀ : M)
    (hc₀ : ∀ n ≥ N₀, u_seq (σ.1 n) north_pole = c₀) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_all_jhol_const_of_eventually_const_north_pole I u_seq B h_jhol h_energy
    (fun u hu => ⟨u north_pole, fun z => congr_fun (h_all_np u hu) z⟩) σ N₀ c₀ hc₀

/-- Unconditional prestable limit assembly when every globally `J`-holomorphic sphere equals its
`north_pole` value and `u_seq` has a subsequence with constant `north_pole` value (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_all_jhol_eq_north_pole_of_const_north_pole
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (σ : Bookkeeping.SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, u_seq (σ.1 n) north_pole = c₀) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_all_jhol_eq_north_pole_of_eventually_const_north_pole I u_seq B
    h_jhol h_energy h_all_np σ 0 c₀ (fun n _ => hc₀ n)

/-- Unconditional `extract_grafted_tree_rescaling_and_conv` when every globally `J`-holomorphic
sphere has a constant value (`0 sorryAx`). -/
theorem extract_grafted_tree_rescaling_and_conv_of_all_jhol_exists_const
    (u_seq : ℕ → (CP1 → M))
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → ∃ c : M, ∀ z, u z = c) :
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        ∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)) :=
  extract_grafted_tree_rescaling_and_conv_of_all_jhol_const I u_seq h_jhol B th cdata m_defect P
    (fun u hu => by
      obtain ⟨c, hc⟩ := h_all_const u hu
      ext z
      rw [hc z, hc north_pole])

/-- Sequence-relative certificate: every atom of the concentration measure of `u_seq` is a genuine
defect (`Bubbling.IsDefectSeq`) of some sequence (in the intended proof: a rotated subsequence of
`u_seq`), with the defect mass and the base value `u₀ p`. Unlike the earlier `h_one_level`, this
only concerns masses that actually occur. -/
def ConcDefectCertificate (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M) : Prop :=
  ∀ (cdata : Compactness.ConcentrationData I u_seq B th) (m : CP1 → ℝ),
    cdata.μ = energyMeasureExtended I cdata.u₀ + ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • MeasureTheory.Measure.dirac p) →
    ∀ p ∈ cdata.S, ∃ (rot : MoebiusFrame) (a : ℂ),
      rot.toHomeo (stereo_chart.symm a) = p ∧
      Bubbling.IsDefectSeq I (fun n => u_seq (cdata.σ.1 n) ∘ rot.toHomeo) a (m p) (cdata.u₀ p) ∧
      ((cdata.S = {p} ∧ ∃ c : M, ∀ z : CP1, cdata.u₀ z = c) →
        Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n) ∘ rot.toHomeo)) atTop (𝓝 (m p)))

/-- Sequence-relative convergence certificate for a grafted prestable tree (Contract G01).
For the concentration data `cdata` with verified defect decomposition `m`, any grafted tree `P`
built from `resolve_single_defect_tree` admits a subsequence `σ` and calibrated tree rescaling data `res`
such that the sequence rescaled by the global tree frames converges smoothly off incident nodes to
each component map, satisfies the degree-one ghost root convergence condition, and conserves total energy.

Satisfiability (true mathematics; Gromov 1985, McDuff–Salamon §4.6):
1. The moving bubbling centers and dilation factors extracted from Hofer's lemma at each defect point
   yield a sequence of Möbius frames on each bubble component under which the sequence converges in
   `C^∞_loc` off nodes to the bubble curve.
2. The tree rescaling frames satisfy the collapse condition towards nodal attachment points by construction.
3. Total energy converges to `E(u₀) + Σ m(p)` by the defect measure identity (`Compactness.defect_measure_identity`).
4. For a degree-1 constant root, all concentration energy is carried by the unique child bubble `w₀`, so no
   energy escapes at the attachment node, ensuring `C^∞_loc` convergence across the node by `ε`-regularity. -/
def TreeConvergenceCertificate (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M) : Prop :=
  ∀ (cdata : Compactness.ConcentrationData I u_seq B th) (m : CP1 → ℝ),
    (∀ p ∈ cdata.S, th.ε_sph ≤ m p) →
    cdata.μ = energyMeasureExtended I cdata.u₀ +
      ∑ p ∈ cdata.S, (ENNReal.ofReal (m p) • MeasureTheory.Measure.dirac p) →
    ∀ (P : PartialRootGraftedTree I u_seq B th cdata m cdata.S),
    ∃ (σ : Bookkeeping.SubseqMap) (res : TreeRescalingData P.tree P.root),
      (∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        (∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
        (P.tree.adj.degree P.root = 1 → (∃ c : M, ∀ z : CP1, P.map P.root z = c) →
          ∀ (w₀ : P.tree.V) (hw₀_adj : P.tree.adj.Adj P.root w₀),
            SmoothLocalConvergesOn I
              (fun n => (u_seq (σ.1 n)) ∘ (frames w₀ n).toHomeo)
              (P.map w₀)
              {P.tree.node_point w₀ P.root (P.tree.adj.adj_symm hw₀_adj)})) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m p))

/-- Backward-compatibility alias for `TreeConvergenceCertificate`. -/
def GraftCertificate (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M) : Prop :=
  TreeConvergenceCertificate I u_seq B th

/-- A grafted tree that is the limit of the sequence yields prestable limit data (`0 sorryAx`). -/
theorem prestable_limit_of_grafted_tree
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th) (m_defect : CP1 → ℝ)
    (h_energy_bdd : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (P : PartialRootGraftedTree I u_seq B th cdata m_defect cdata.S) (σ : Bookkeeping.SubseqMap)
    (res : TreeRescalingData P.tree P.root)
    (h_conv : ∀ (frames : (v : P.tree.V) → ℕ → MoebiusFrame),
        (∀ n, frames P.root n = MoebiusFrame.id) →
        (∀ (w : P.tree.V) (hw : w ≠ P.root) (n : ℕ),
          frames w n = MoebiusFrame.comp (frames (res.parent w hw) n)
            (affine_scaling (res.center w n) (res.scale w n) (res.scale_pos w n))) →
        (∀ (v : P.tree.V),
          SmoothLocalConvergesOn I
            (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
            (P.map v)
            (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
        (P.tree.adj.degree P.root = 1 → (∃ c : M, ∀ z : CP1, P.map P.root z = c) →
          ∀ (w₀ : P.tree.V) (hw₀_adj : P.tree.adj.Adj P.root w₀),
            SmoothLocalConvergesOn I
              (fun n => (u_seq (σ.1 n)) ∘ (frames w₀ n).toHomeo)
              (P.map w₀)
              {P.tree.node_point w₀ P.root (P.tree.adj.adj_symm hw₀_adj)}))
    (h_en_tendsto : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
        (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p))) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  obtain ⟨frames, h_root_id, h_rec, h_collapse⟩ := assemble_global_frames P.tree P.root res
  let pdata : PrestableLimitData I u_seq := {
    tree := P.tree
    root := P.root
    map := P.map
    is_jhol := P.is_jhol
    nodal_match := P.nodal_match
    stable_off_root := P.stable_off_root
    σ := σ
    frames := frames
    root_frame_id := ⟨_, h_root_id⟩
    frame_collapse := h_collapse
    smooth_conv := (h_conv frames h_root_id h_rec).1
    ghost_root_deg_one_conv := (h_conv frames h_root_id h_rec).2
    energy_ident := by
      rw [P.energy_sum]
      exact h_en_tendsto
  }
  exact ⟨pdata, prestable_limit_energy_bound I u_seq B pdata h_energy_bdd⟩

/-- Assembles the base map `u₀` and all defect trees from Contract B07 into a global prestable limit
without requiring `h_fin` (`0 sorryAx`, discharging `h_fin` from `th` and `h_jhol`). -/
theorem assemble_prestable_limit_of_thresholds
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_conc_extract : ∀ (σ : Bookkeeping.SubseqMap) (μ : MeasureTheory.Measure CP1) (S : Finset CP1),
      MeasureTheory.IsFiniteMeasure μ →
      Compactness.WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ →
      (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal th.ε_reg ≤ μ {p}) →
      ∃ (τ : Bookkeeping.SubseqMap) (u₀ : CP1 → M), JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
        SmoothLocalConvergesOn I (fun n => u_seq ((σ.comp τ).1 n)) u₀ (Set.univ \ S) ∧
        μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • MeasureTheory.Measure.dirac p))
    (h_cert : Bubbling.OneLevelCertificate I th)
    (h_conc_defects : ConcDefectCertificate I u_seq B th) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  have h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤ :=
    fun n => Compactness.energyMeasureExtended_lt_top_of_thresholds I th (u_seq n) (h_jhol n)
  by_cases h_pdata : ∃ (σ : Bookkeeping.SubseqMap),
      Nonempty (PrestableLimitData I (fun n => u_seq (σ.1 n)))
  · rcases h_pdata with ⟨σ, ⟨pdata⟩⟩
    exact assemble_prestable_limit_of_subseq_pdata I u_seq B h_energy σ pdata
  · by_cases h_ev : ∃ (σ : Bookkeeping.SubseqMap) (N₀ : ℕ) (c : M),
        ∀ n ≥ N₀, ∀ z, u_seq (σ.1 n) z = c
    · rcases h_ev with ⟨σ, N₀, c, hc⟩
      exact assemble_prestable_limit_of_eventually_const_subseq I u_seq B h_jhol h_energy σ N₀ c hc
    · have hB : 0 ≤ B := (energy_nonneg I (u_seq 0) Set.univ).trans (h_energy 0)
      obtain ⟨cdata⟩ := Compactness.exists_concentration_data_of_thresholds I u_seq h_jhol B hB h_energy th h_conc_extract
      obtain ⟨m_defect, hm_sph, _hm_zero, h_decomp, h_tendsto_energy⟩ :=
        Compactness.defect_measure_identity_of_thresholds I u_seq B h_jhol h_energy th cdata
      have defect_trees : (p : CP1) → (hp : p ∈ cdata.S) →
          ∃ (rot : MoebiusFrame) (a : ℂ),
            rot.toHomeo (stereo_chart.symm a) = p ∧
            ((cdata.S = {p} ∧ ∃ c : M, ∀ z : CP1, cdata.u₀ z = c) →
              Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n) ∘ rot.toHomeo)) atTop (𝓝 (m_defect p))) ∧
            ∀ (τ : Bookkeeping.SubseqMap),
              Nonempty (Bubbling.RealizedLocalDefectTree I th (m_defect p) (cdata.u₀ p)
                (fun n => u_seq ((cdata.σ.comp τ).1 n) ∘ rot.toHomeo) a) := by
        intro p hp
        have h_pos : 0 < m_defect p := th.ε_sph_pos.trans_le (hm_sph p hp)
        obtain ⟨rot, a, hp_eq, h_def, h_tend⟩ := h_conc_defects cdata m_defect h_decomp p hp
        refine ⟨rot, a, hp_eq, h_tend, fun τ => ?_⟩
        have h_def_sub := Bubbling.IsDefectSeq.subseq I h_def τ.2
        have h_B07 : Nonempty (Bubbling.resolve_single_defect_tree I u_seq h_jhol B h_energy h_fin th
            (m_defect p) h_pos (cdata.u₀ p) h_cert
            (fun n => u_seq ((cdata.σ.comp τ).1 n) ∘ rot.toHomeo) a h_def_sub =
          Bubbling.resolve_single_defect_tree I u_seq h_jhol B h_energy h_fin th
            (m_defect p) h_pos (cdata.u₀ p) h_cert
            (fun n => u_seq ((cdata.σ.comp τ).1 n) ∘ rot.toHomeo) a h_def_sub) := ⟨rfl⟩
        obtain ⟨_⟩ := h_B07
        exact Bubbling.resolve_single_defect_tree_realized I th h_cert
          (m_defect p) h_pos (cdata.u₀ p) (fun n => u_seq ((cdata.σ.comp τ).1 n) ∘ rot.toHomeo) a h_def_sub
      obtain ⟨P_real⟩ := graft_root_sphere_tree_realized I u_seq B th cdata m_defect hm_sph defect_trees
      let pdata : PrestableLimitData I u_seq := {
        tree := P_real.tree
        root := P_real.root
        map := P_real.map
        is_jhol := P_real.is_jhol
        nodal_match := P_real.nodal_match
        stable_off_root := P_real.stable_off_root
        σ := cdata.σ.comp P_real.τ
        frames := P_real.frames
        root_frame_id := ⟨_, P_real.root_frame⟩
        frame_collapse := P_real.frame_collapse
        smooth_conv := fun v => by
          have h_sc := P_real.smooth_conv v
          by_cases hv : v = P_real.root
          · subst hv
            simp only [↓reduceIte] at h_sc
            have h_set := root_sphere_nodal_set_eq I u_seq B th cdata m_defect cdata.S P_real.toPartialRootGraftedTree
            rw [h_set]
            exact h_sc
          · simp only [hv, ↓reduceIte] at h_sc
            exact h_sc
        ghost_root_deg_one_conv := P_real.ghost_root_deg_one_conv rfl
        energy_ident := by
          have h_tendsto := h_tendsto_energy.comp P_real.τ.2.tendsto_atTop
          rw [P_real.energy_sum]
          exact h_tendsto
      }
      exact ⟨pdata, prestable_limit_energy_bound I u_seq B pdata h_energy⟩

/-- Assembles the base map u₀ and all defect trees from Contract B07 into a global prestable limit (Contract G01).
Proved with zero direct sorry from `assemble_prestable_limit_of_thresholds` (`_h_fin` is discharged
unconditionally from `th` and `h_jhol`). -/
theorem assemble_prestable_limit
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (_h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤)
    (h_conc_extract : ∀ (σ : Bookkeeping.SubseqMap) (μ : MeasureTheory.Measure CP1) (S : Finset CP1),
      MeasureTheory.IsFiniteMeasure μ →
      Compactness.WeakMeasureConvergence (fun n => energyMeasureExtended I (u_seq (σ.1 n))) μ →
      (∀ p : CP1, p ∈ S ↔ ENNReal.ofReal th.ε_reg ≤ μ {p}) →
      ∃ (τ : Bookkeeping.SubseqMap) (u₀ : CP1 → M), JHolomorphicOn (I := I) (I_dom := I_CP1) u₀ Set.univ ∧
        SmoothLocalConvergesOn I (fun n => u_seq ((σ.comp τ).1 n)) u₀ (Set.univ \ S) ∧
        μ = energyMeasureExtended I u₀ + ∑ p ∈ S, (μ {p} • MeasureTheory.Measure.dirac p))
    (h_cert : Bubbling.OneLevelCertificate I th)
    (h_conc_defects : ConcDefectCertificate I u_seq B th) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_thresholds I th u_seq B h_jhol h_energy
    h_conc_extract h_cert h_conc_defects

/-! ### First-principles proof of `ConcDefectCertificate` (`cert_concdefect`) (`0 sorryAx`) -/

/-- Pointwise convergence on an open set `V ⊆ CP1` combined with eventual equicontinuity on `V`
upgrades to uniform convergence `TendstoUniformlyOn` on every compact subset `K ⊆ V` without
passing to a further subsequence (`0 sorryAx`). -/
theorem tendstoUniformlyOn_of_pointwise_and_equicontinuous_on_open
    {f_seq : ℕ → (CP1 → M)} {f_lim : CP1 → M} {V K : Set CP1}
    (hV_open : IsOpen V) (hKV : K ⊆ V) (hK_cpt : IsCompact K)
    (hf_lim_cont : ContinuousOn f_lim V)
    (h_pt : ∀ z ∈ V, Tendsto (fun n => f_seq n z) atTop (𝓝 (f_lim z)))
    {N₀ : ℕ} (h_equi : Equicontinuous (fun k (x : V) => f_seq (k + N₀) (x : CP1))) :
    TendstoUniformlyOn f_seq f_lim atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  have h_loc : ∀ x ∈ K, ∃ δ > 0, Metric.ball x δ ⊆ V ∧
      (∀ y ∈ Metric.ball x δ, ∀ k : ℕ, dist (f_seq (k + N₀) y) (f_seq (k + N₀) x) < ε / 3) ∧
      (∀ y ∈ Metric.ball x δ, dist (f_lim y) (f_lim x) < ε / 3) := by
    intro x hxK
    have hxV : x ∈ V := hKV hxK
    let x_V : V := ⟨x, hxV⟩
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.equicontinuousAt_iff.mp (h_equi x_V) (ε / 3) hε3
    have h_cont_at : ContinuousAt f_lim x := (hf_lim_cont x hxV).continuousAt (hV_open.mem_nhds hxV)
    obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.continuousAt_iff.mp h_cont_at (ε / 3) hε3
    obtain ⟨δ₃, hδ₃_pos, hδ₃⟩ := Metric.isOpen_iff.mp hV_open x hxV
    let δ : ℝ := min (min δ₁ δ₂) δ₃
    have hδ_pos : 0 < δ := lt_min (lt_min hδ₁_pos hδ₂_pos) hδ₃_pos
    have h_ball_V : Metric.ball x δ ⊆ V :=
      (Metric.ball_subset_ball (min_le_right _ _)).trans hδ₃
    refine ⟨δ, hδ_pos, h_ball_V, ?_, ?_⟩
    · intro y hy k
      let y_V : V := ⟨y, h_ball_V hy⟩
      have hy_dist : dist y_V x_V < δ₁ :=
        lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_left _ _))
      have h_eq := hδ₁ y_V hy_dist k
      rwa [dist_comm] at h_eq
    · intro y hy
      exact hδ₂ (lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_right _ _)))
  choose δ hδ_pos _hδ_V hδ_seq hδ_lim using fun (x : K) => h_loc x.1 x.2
  obtain ⟨t, ht_cover⟩ := hK_cpt.elim_finite_subcover
    (fun x : K => Metric.ball x.1 (δ x))
    (fun x => Metric.isOpen_ball)
    (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hδ_pos ⟨z, hz⟩)⟩)
  have h_ev_pts : ∀ᶠ n in atTop, ∀ x ∈ t, dist (f_seq n x.1) (f_lim x.1) < ε / 3 :=
    (Filter.eventually_all_finset t).mpr (fun x _ =>
      Metric.tendsto_nhds.mp (h_pt x.1 (hKV x.2)) (ε / 3) hε3)
  filter_upwards [h_ev_pts, Filter.eventually_ge_atTop N₀] with n hn_pts hn_ge z hzK
  have hz_cov := ht_cover hzK
  simp only [Set.mem_iUnion] at hz_cov
  rcases hz_cov with ⟨x, hx_t, hz_ball⟩
  have hn_eq : (n - N₀) + N₀ = n := Nat.sub_add_cancel hn_ge
  have d1 : dist (f_lim z) (f_lim x.1) < ε / 3 := hδ_lim x z hz_ball
  have d2 : dist (f_lim x.1) (f_seq n x.1) < ε / 3 := by
    rw [dist_comm]; exact hn_pts x hx_t
  have d3 : dist (f_seq n x.1) (f_seq n z) < ε / 3 := by
    rw [dist_comm, ← hn_eq]; exact hδ_seq x z hz_ball (n - N₀)
  calc dist (f_lim z) (f_seq n z)
      ≤ dist (f_lim z) (f_lim x.1) + dist (f_lim x.1) (f_seq n z) := dist_triangle _ _ _
    _ ≤ dist (f_lim z) (f_lim x.1) + (dist (f_lim x.1) (f_seq n x.1) + dist (f_seq n x.1) (f_seq n z)) :=
        by linarith [dist_triangle (f_lim x.1) (f_seq n x.1) (f_seq n z)]
    _ < ε / 3 + (ε / 3 + ε / 3) := add_lt_add d1 (add_lt_add d2 d3)
    _ = ε := by ring

/-- Existence of an isolating-disk radius `r_isol > 0` around any finite atom `p = stereo_chart.symm a ∈ S`
such that `closure (disk_at a r) ∩ S = {p}` for all `0 < r ≤ r_isol` (`0 sorryAx`). -/
theorem exists_isolating_disk_radius
    (S : Finset CP1) {p : CP1} (hp : p ∈ S) (a : ℂ) (ha : stereo_chart.symm a = p) :
    ∃ r_isol > 0, ∀ r : ℝ, 0 < r → r ≤ r_isol →
      closure (disk_at a r) ∩ (S : Set CP1) = {p} := by
  let S' : Finset CP1 := S.erase p
  let F : Set ℂ := stereo_chart.symm ⁻¹' (S' : Set CP1)
  have hF_closed : IsClosed F := S'.finite_toSet.isClosed.preimage stereo_chart_symm_continuous
  have ha_not_F : a ∉ F := by
    intro haF
    have hp_in_S' : p ∈ (S' : Set CP1) := by rwa [← ha]
    exact (Finset.notMem_erase p S) (Finset.mem_coe.mp hp_in_S')
  obtain ⟨R₀, hR₀_pos, hR₀_ball⟩ := Metric.isOpen_iff.mp hF_closed.isOpen_compl a ha_not_F
  refine ⟨R₀ / 2, half_pos hR₀_pos, fun r hr hrr => ?_⟩
  have h_closed_cb : IsClosed (stereo_chart.symm '' Metric.closedBall a r) :=
    ((isCompact_closedBall a r).image stereo_chart_symm_continuous).isClosed
  have h_clos_sub : closure (disk_at a r) ⊆ stereo_chart.symm '' Metric.closedBall a r :=
    closure_minimal (Set.image_mono Metric.ball_subset_closedBall) h_closed_cb
  apply Set.Subset.antisymm
  · rintro q ⟨hq_cl, hq_S⟩
    obtain ⟨w, hw_cb, rfl⟩ := h_clos_sub hq_cl
    have hw_ball : w ∈ Metric.ball a R₀ := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hw_cb) (lt_of_le_of_lt hrr (half_lt_self hR₀_pos))
    have hw_not_F : w ∉ F := hR₀_ball hw_ball
    by_contra hqp
    have hq_erase : stereo_chart.symm w ∈ S' :=
      Finset.mem_erase.mpr ⟨hqp, Finset.mem_coe.mp hq_S⟩
    exact hw_not_F (Finset.mem_coe.mpr hq_erase)
  · rw [Set.singleton_subset_iff]
    exact ⟨subset_closure ⟨a, Metric.mem_ball_self hr, ha⟩, Finset.mem_coe.mpr hp⟩

/-- Unconditional proof of shrinking-disk defect mass convergence (`hmass`) and single-atom ghost-root
total energy convergence at EVERY finite atom `p = stereo_chart.symm a ∈ cdata.S` (`0 sorryAx`). -/
theorem defect_mass_limit_of_concentration_finite_point
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m : CP1 → ℝ)
    (h_decomp : cdata.μ = energyMeasureExtended I cdata.u₀ +
      ∑ q ∈ cdata.S, (ENNReal.ofReal (m q) • MeasureTheory.Measure.dirac q))
    {p : CP1} (hp : p ∈ cdata.S) (a : ℂ) (ha : stereo_chart.symm a = p) :
    (∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ᶠ n in atTop, |energyMeasure I (u_seq (cdata.σ.1 n)) (disk_at a r) - m p| < ε) ∧
    ((cdata.S = {p} ∧ ∃ c : M, ∀ z : CP1, cdata.u₀ z = c) →
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop (𝓝 (m p))) := by
  haveI := cdata.μ_fin
  -- Deduce `0 ≤ m q` for every `q ∈ cdata.S` by evaluating `h_decomp` at `{q}`.
  have hm_nonneg : ∀ q ∈ cdata.S, 0 ≤ m q := by
    intro q hq
    have h_ge_reg : ENNReal.ofReal th.ε_reg ≤ cdata.μ {q} := (cdata.S_def q).mp hq
    have h_eval : cdata.μ {q} = ENNReal.ofReal (m q) := by
      rw [h_decomp, MeasureTheory.Measure.add_apply,
        Compactness.energyMeasureExtended_singleton_eq_zero I cdata.u₀ q, zero_add,
        Compactness.dirac_sum_singleton_mem cdata.S m q hq]
    rw [h_eval] at h_ge_reg
    have h_pos_reg : 0 < ENNReal.ofReal th.ε_reg := ENNReal.ofReal_pos.mpr th.ε_reg_pos
    have h_pos_mq : 0 < ENNReal.ofReal (m q) := lt_of_lt_of_le h_pos_reg h_ge_reg
    exact le_of_lt (ENNReal.ofReal_pos.mp h_pos_mq)
  refine ⟨?_, ?_⟩
  · intro ε hε
    obtain ⟨r_isol, hr_isol_pos, hr_isol⟩ := exists_isolating_disk_radius cdata.S hp a ha
    have hu₀_lt_top : energyMeasureExtended I cdata.u₀ Set.univ < ⊤ :=
      Compactness.energyMeasureExtended_lt_top_of_thresholds I th cdata.u₀ cdata.u₀_jhol
    have hu₀_disk_ne_top : energyMeasureExtended I cdata.u₀ (disk_at a r_isol) ≠ ⊤ :=
      ne_top_of_le_ne_top hu₀_lt_top.ne (MeasureTheory.measure_mono (Set.subset_univ _))
    have h_cont_rad : ContinuousOn (fun r => energyMeasure I cdata.u₀ (disk_at a r)) (Set.Icc 0 r_isol) :=
      Analysis.continuousOn_energyMeasure_disk_at_Icc_of_ne_top I cdata.u₀ a r_isol hu₀_disk_ne_top
    have h_zero_rad : energyMeasure I cdata.u₀ (disk_at a 0) = 0 :=
      Analysis.energyMeasure_disk_at_zero I cdata.u₀ a
    obtain ⟨δ_rad, hδ_rad_pos, hδ_rad⟩ :=
      Metric.continuousWithinAt_iff.mp (h_cont_rad 0 (Set.left_mem_Icc.mpr hr_isol_pos.le))
        (ε / 2) (half_pos hε)
    let r₀ : ℝ := min r_isol (δ_rad / 2)
    have hr₀_pos : 0 < r₀ := lt_min hr_isol_pos (half_pos hδ_rad_pos)
    refine ⟨r₀, hr₀_pos, fun r hr hrr => ?_⟩
    have hr_le_isol : r ≤ r_isol := hrr.trans (min_le_left _ _)
    have hr_lt_δ : dist r 0 < δ_rad := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hr]
      exact lt_of_le_of_lt (hrr.trans (min_le_right _ _)) (half_lt_self hδ_rad_pos)
    have hu₀_r_lt : energyMeasure I cdata.u₀ (disk_at a r) < ε / 2 := by
      have h_d := hδ_rad ⟨hr.le, hr_le_isol⟩ hr_lt_δ
      rw [h_zero_rad, Real.dist_eq, sub_zero, abs_of_nonneg (energy_nonneg I cdata.u₀ _)] at h_d
      exact h_d
    have hu₀_r_nn : 0 ≤ energyMeasure I cdata.u₀ (disk_at a r) := energy_nonneg I cdata.u₀ _
    have h_isol_cl := hr_isol r hr hr_le_isol
    have h_isol_open : disk_at a r ∩ (cdata.S : Set CP1) = {p} := by
      apply Set.Subset.antisymm
      · rw [← h_isol_cl]; exact Set.inter_subset_inter_left _ subset_closure
      · rw [Set.singleton_subset_iff]
        exact ⟨⟨a, Metric.mem_ball_self hr, ha⟩, Finset.mem_coe.mpr hp⟩
    have h_front_null :=
      Compactness.frontier_disk_at_null_of_isolating I u_seq B th cdata m h_decomp p a ha r hr h_isol_cl
    have h_lim :=
      Compactness.isolating_disk_defect_limit_of_decomp I u_seq B th cdata m h_decomp p hp
        (hm_nonneg p hp) a r h_isol_open h_front_null
    filter_upwards [Metric.tendsto_nhds.mp h_lim (ε / 2) (half_pos hε)] with n hn
    rw [Real.dist_eq] at hn
    rw [abs_lt] at hn ⊢
    constructor <;> linarith
  · rintro ⟨hS_single, c, hc⟩
    have h_tot := Compactness.tendsto_totalEnergy_of_defect_decomp I u_seq B th cdata m hm_nonneg h_decomp
    have hu₀_eq : cdata.u₀ = fun _ => c := funext hc
    have hu₀_en : totalEnergy I cdata.u₀ = 0 := by
      rw [hu₀_eq]; exact Analysis.totalEnergy_const I c
    rw [hu₀_en, hS_single, Finset.sum_singleton, zero_add] at h_tot
    exact h_tot

/-- Unconditional Southern-Hemisphere Concentration-to-Defect Theorem (`0 sorryAx`):
on any `[I.Boundaryless] [BoundedChartedTarget I M] [FiniteDimensional ℝ E]`, every concentration
atom `p = stereo_chart.symm a ∈ cdata.S` in the open southern hemisphere (`‖a‖ < 1`) is
unconditionally a genuine defect `Bubbling.IsDefectSeq` of `fun n => u_seq (cdata.σ.1 n)` at `a`
with mass `m p` and base value `cdata.u₀ p`, and satisfies the single-atom ghost-root energy limit. -/
theorem isDefectSeq_of_concentration_southern_hemisphere
    [I.Boundaryless] [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m : CP1 → ℝ)
    (h_decomp : cdata.μ = energyMeasureExtended I cdata.u₀ +
      ∑ q ∈ cdata.S, (ENNReal.ofReal (m q) • MeasureTheory.Measure.dirac q))
    {p : CP1} (hp : p ∈ cdata.S) (a : ℂ) (ha_norm : ‖a‖ < 1) (ha : stereo_chart.symm a = p) :
    Bubbling.IsDefectSeq I (fun n => u_seq (cdata.σ.1 n)) a (m p) (cdata.u₀ p) ∧
    ((cdata.S = {p} ∧ ∃ c : M, ∀ z : CP1, cdata.u₀ z = c) →
      Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop (𝓝 (m p))) := by
  haveI := cdata.μ_fin
  obtain ⟨hmass, h_tot_lim⟩ :=
    defect_mass_limit_of_concentration_finite_point I th u_seq B cdata m h_decomp hp a ha
  refine ⟨⟨fun n => h_jhol (cdata.σ.1 n), ⟨B, fun n => h_energy (cdata.σ.1 n)⟩,
    fun n => Compactness.energyMeasureExtended_lt_top_of_thresholds I th _ (h_jhol (cdata.σ.1 n)),
    hmass, ?_⟩, h_tot_lim⟩
  -- Prove `hann` on `annulus_at a (r / 2) r` via southern-hemisphere gradient bounds + equicontinuity.
  intro ε hε
  obtain ⟨r_isol, hr_isol_pos, hr_isol⟩ := exists_isolating_disk_radius cdata.S hp a ha
  have hu₀_cont : Continuous cdata.u₀ := continuousOn_univ.mp cdata.u₀_jhol.1.continuousOn
  have h_comp_cont : ContinuousAt (fun w : ℂ => cdata.u₀ (stereo_chart.symm w)) a :=
    (hu₀_cont.comp stereo_chart_symm_continuous).continuousAt
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := Metric.continuousAt_iff.mp h_comp_cont (ε / 2) (half_pos hε)
  let r₀ : ℝ := min (min (δ₀ / 2) (r_isol / 2)) ((1 - ‖a‖) / 4)
  have hr₀_pos : 0 < r₀ := lt_min (lt_min (half_pos hδ₀_pos) (half_pos hr_isol_pos)) (by linarith)
  refine ⟨r₀, hr₀_pos, fun r hr hrr => ?_⟩
  -- Enclose `annulus_at a (r / 2) r` inside `K_r ⊆ V_r ⊆ L_r` where `L_r` is compact and in `(univ \ S) ∩ H_-`.
  let K_r : Set CP1 := stereo_chart.symm '' {w : ℂ | r / 2 ≤ dist w a ∧ dist w a ≤ r}
  let V_r : Set CP1 := annulus_at a (r / 3) (3 * r / 2)
  let L_r : Set CP1 := stereo_chart.symm '' {w : ℂ | r / 4 ≤ dist w a ∧ dist w a ≤ 7 * r / 4}
  have hKr_cpt : IsCompact K_r := by
    have h_eq : {w : ℂ | r / 2 ≤ dist w a ∧ dist w a ≤ r} =
        Metric.closedBall a r ∩ {w : ℂ | r / 2 ≤ dist w a} := by
      ext w; simp [Metric.mem_closedBall, and_comm]
    dsimp [K_r]
    rw [h_eq]
    exact ((isCompact_closedBall a r).of_isClosed_subset
      (isClosed_closedBall.inter (isClosed_le continuous_const (continuous_id.dist continuous_const)))
      Set.inter_subset_left).image stereo_chart_symm_continuous
  have hLr_cpt : IsCompact L_r := by
    have h_eq : {w : ℂ | r / 4 ≤ dist w a ∧ dist w a ≤ 7 * r / 4} =
        Metric.closedBall a (7 * r / 4) ∩ {w : ℂ | r / 4 ≤ dist w a} := by
      ext w; simp [Metric.mem_closedBall, and_comm]
    dsimp [L_r]
    rw [h_eq]
    exact ((isCompact_closedBall a (7 * r / 4)).of_isClosed_subset
      (isClosed_closedBall.inter (isClosed_le continuous_const (continuous_id.dist continuous_const)))
      Set.inter_subset_left).image stereo_chart_symm_continuous
  have hVr_open : IsOpen V_r := is_open_annulus_at a (r / 3) (3 * r / 2)
  have h_ann_Kr : annulus_at a (r / 2) r ⊆ K_r :=
    Set.image_mono (fun _ hw => ⟨hw.1.le, hw.2.le⟩)
  have hKr_Vr : K_r ⊆ V_r :=
    Set.image_mono (fun _ hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩)
  have hVr_Lr : V_r ⊆ L_r :=
    Set.image_mono (fun _ hw => ⟨by linarith [hw.1], by linarith [hw.2]⟩)
  have hLr_sub : L_r ⊆ (Set.univ \ (cdata.S : Set CP1)) ∩ (stereo_chart.symm '' Metric.ball (0 : ℂ) 1) := by
    rintro z ⟨w, ⟨hw_lo, hw_hi⟩, rfl⟩
    have hr_le_isol2 : r ≤ r_isol / 2 := hrr.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hr_le_hemi : r ≤ (1 - ‖a‖) / 4 := hrr.trans (min_le_right _ _)
    have hw_lt_isol : dist w a < r_isol := by linarith
    have hz_in_disk : stereo_chart.symm w ∈ disk_at a r_isol := ⟨w, hw_lt_isol, rfl⟩
    have h_isol_cl := hr_isol r_isol hr_isol_pos le_rfl
    have hz_not_S : stereo_chart.symm w ∉ (cdata.S : Set CP1) := by
      intro hzS
      have hz_p : stereo_chart.symm w ∈ ({p} : Set CP1) := by
        rw [← h_isol_cl]
        exact ⟨subset_closure hz_in_disk, hzS⟩
      rw [Set.mem_singleton_iff, ← ha] at hz_p
      have hwa : w = a := stereo_chart_symm_injective hz_p
      subst hwa
      rw [dist_self] at hw_lo
      linarith
    refine ⟨⟨Set.mem_univ _, hz_not_S⟩, ⟨w, ?_, rfl⟩⟩
    rw [Metric.mem_ball, dist_zero_right]
    rw [dist_eq_norm] at hw_hi
    have h_tri : ‖w‖ ≤ ‖a‖ + ‖w - a‖ := by
      calc ‖w‖ = ‖a + (w - a)‖ := congr_arg norm (by ring)
        _ ≤ ‖a‖ + ‖w - a‖ := norm_add_le a (w - a)
    linarith
  -- Uniform eventual gradient bound on `L_r` gives uniform bound `C_L + 1 > 0` for `n ≥ N₀` on `V_r`.
  obtain ⟨C_L, hCL_nn, h_ev_CL⟩ :=
    Compactness.eventually_gradient_bound_on_compact_southern_hemisphere_of_disjoint_S
      I u_seq h_jhol th cdata.σ cdata.μ cdata.S cdata.weak_lim cdata.S_def hLr_cpt hLr_sub
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h_ev_CL
  have h_jhol_Vr : ∀ k, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq (cdata.σ.1 (k + N₀))) V_r :=
    fun k => ⟨(h_jhol (cdata.σ.1 (k + N₀))).1.mono (Set.subset_univ _),
      fun z _ => (h_jhol (cdata.σ.1 (k + N₀))).2 z (Set.mem_univ z)⟩
  have h_grad_Vr : ∀ K ⊆ V_r, IsCompact K →
      ∃ C > 0, ∀ k, ∀ z ∈ K, riemannianEnergyDensity I (u_seq (cdata.σ.1 (k + N₀))) z ≤ C := by
    intro K hKV _hKcpt
    refine ⟨C_L + 1, by linarith, fun k z hzK => ?_⟩
    have h1 := hN₀ (k + N₀) (Nat.le_add_left N₀ k) z (hVr_Lr (hKV hzK))
    linarith
  have h_equi : Equicontinuous (fun k (x : V_r) => u_seq (cdata.σ.1 (k + N₀)) (x : CP1)) :=
    Analysis.equicontinuous_of_local_lipschitz_on_domain
      (fun k => u_seq (cdata.σ.1 (k + N₀))) V_r
      (local_lipschitz_of_bounded_energy_density I
        (fun k => u_seq (cdata.σ.1 (k + N₀))) V_r hVr_open h_jhol_Vr h_grad_Vr)
  have h_pt_Vr : ∀ z ∈ V_r, Tendsto (fun n => u_seq (cdata.σ.1 n) z) atTop (𝓝 (cdata.u₀ z)) := by
    intro z hzV
    have hz_off : z ∈ Set.univ \ (cdata.S : Set CP1) := (hLr_sub (hVr_Lr hzV)).1
    exact ((cdata.smooth_conv []).2 {z} (Set.singleton_subset_iff.mpr hz_off) isCompact_singleton).1
      z (Set.mem_singleton z)
  have h_unif_Kr : TendstoUniformlyOn (fun n => u_seq (cdata.σ.1 n)) cdata.u₀ atTop K_r :=
    tendstoUniformlyOn_of_pointwise_and_equicontinuous_on_open hVr_open hKr_Vr hKr_cpt
      hu₀_cont.continuousOn h_pt_Vr h_equi
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h_unif_Kr (ε / 2) (half_pos hε)] with n hn z hz_ann
  have hz_Kr : z ∈ K_r := h_ann_Kr hz_ann
  rcases hz_ann with ⟨w, ⟨_hw_lo, hw_hi⟩, rfl⟩
  have hr_le_δ₀ : r ≤ δ₀ / 2 := hrr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hw_lt_δ₀ : dist w a < δ₀ := lt_of_lt_of_le hw_hi (le_trans hr_le_δ₀ (half_le_self hδ₀_pos.le))
  have hd_u0 : dist (cdata.u₀ (stereo_chart.symm w)) (cdata.u₀ p) < ε / 2 := by
    rw [← ha]; exact hδ₀ hw_lt_δ₀
  have hd_seq : dist (cdata.u₀ (stereo_chart.symm w)) (u_seq (cdata.σ.1 n) (stereo_chart.symm w)) < ε / 2 :=
    hn (stereo_chart.symm w) hz_Kr
  calc dist (u_seq (cdata.σ.1 n) (stereo_chart.symm w)) (cdata.u₀ p)
      ≤ dist (u_seq (cdata.σ.1 n) (stereo_chart.symm w)) (cdata.u₀ (stereo_chart.symm w)) +
        dist (cdata.u₀ (stereo_chart.symm w)) (cdata.u₀ p) := dist_triangle _ _ _
    _ = dist (cdata.u₀ (stereo_chart.symm w)) (u_seq (cdata.σ.1 n) (stereo_chart.symm w)) +
        dist (cdata.u₀ (stereo_chart.symm w)) (cdata.u₀ p) := by rw [dist_comm]
    _ < ε / 2 + ε / 2 := add_lt_add hd_seq hd_u0
    _ = ε := add_halves ε

/-- Pushforward of `WeakMeasureConvergence` on `CP1` along any homeomorphism `h : CP1 ≃ₜ CP1` (`0 sorryAx`). -/
theorem weakMeasureConvergence_map_homeomorph
    {μ_seq : ℕ → MeasureTheory.Measure CP1} {μ_lim : MeasureTheory.Measure CP1}
    (h_weak : Compactness.WeakMeasureConvergence μ_seq μ_lim) (h : CP1 ≃ₜ CP1) :
    Compactness.WeakMeasureConvergence
      (fun n => MeasureTheory.Measure.map h (μ_seq n))
      (MeasureTheory.Measure.map h μ_lim) := by
  let e := h.toMeasurableEquiv
  have he_coe : (⇑e : CP1 → CP1) = ⇑h := rfl
  have h_apply : ∀ (ν : MeasureTheory.Measure CP1) (A : Set CP1),
      (MeasureTheory.Measure.map h ν) A = ν (h ⁻¹' A) := by
    intro ν A
    rw [← he_coe, e.map_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    have h_int : ∀ ν : MeasureTheory.Measure CP1,
        (∫ z, f z ∂(MeasureTheory.Measure.map h ν)) = ∫ x, f (h x) ∂ν :=
      fun ν => MeasureTheory.integral_map h.continuous.aemeasurable hf.aestronglyMeasurable
    simp_rw [h_int]
    exact h_weak.1 (f ∘ h) (hf.comp h.continuous)
  · intro K hK
    simp_rw [h_apply _ K]
    exact h_weak.2.1 (h ⁻¹' K) (hK.preimage h.continuous)
  · intro A hA_front
    simp_rw [h_apply _ A]
    apply h_weak.2.2.1 (h ⁻¹' A)
    rw [← h.preimage_frontier A, ← h_apply μ_lim (frontier A)]
    exact hA_front
  · simp_rw [h_apply _ Set.univ, Set.preimage_univ]
    exact h_weak.2.2.2

/-- Conformal rotation witness sending `south_pole = stereo_chart.symm 0` to `p : CP1` while preserving
global `JHolomorphicOn` (`lem_jhol_invariance`) and `energyMeasureExtended` pullback equivariance
(`thm_energy_conformal`). -/
def IsConformalRotationTo (p : CP1) (rot : MoebiusFrame) : Prop :=
  rot.toHomeo south_pole = p ∧
  (∀ (u : CP1 → M), JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
    JHolomorphicOn (I := I) (I_dom := I_CP1) (u ∘ rot.toHomeo) Set.univ ∧
    energyMeasureExtended I (u ∘ rot.toHomeo) =
      MeasureTheory.Measure.map rot.toHomeo.symm (energyMeasureExtended I u))

/-- `MoebiusFrame.id` unconditionally satisfies `IsConformalRotationTo` for `south_pole` (`0 sorryAx`). -/
theorem isConformalRotationTo_south_pole :
    IsConformalRotationTo I (M := M) south_pole MoebiusFrame.id :=
  ⟨rfl, fun u hu => ⟨hu, energyMeasureExtended_id I u⟩⟩

/-- Construction of `IsConformalRotationTo` from domain biholomorphicity (`jholomorphic_coordinate_invariance`)
and extended energy pullback equivariance (`energy_conformal_invariant`) (`0 sorryAx`). -/
theorem isConformalRotationTo_of_biholomorphic_and_pullback
    (p : CP1) (rot : MoebiusFrame)
    (hp : rot.toHomeo south_pole = p)
    (h_bihol : ∀ (z : CP1) (v : TangentSpace I_CP1 z),
      mfderiv I_CP1 I_CP1 rot.toHomeo z (RiemannDomain.j z v) =
        RiemannDomain.j (rot.toHomeo z) (mfderiv I_CP1 I_CP1 rot.toHomeo z v))
    (h_pull : ∀ (u : CP1 → M), JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      energyMeasureExtended I (u ∘ rot.toHomeo) =
        MeasureTheory.Measure.map rot.toHomeo.symm (energyMeasureExtended I u)) :
    IsConformalRotationTo I (M := M) p rot := by
  refine ⟨hp, fun u hu => ⟨?_, h_pull u hu⟩⟩
  have h_inv := jholomorphic_coordinate_invariance I I_CP1 u Set.univ hu rot.toHomeo rot.is_smooth h_bihol
    (fun z _ => ((hu.1 z (Set.mem_univ z)).mdifferentiableWithinAt (by simp)).mdifferentiableAt Filter.univ_mem)
  rwa [Set.preimage_univ] at h_inv

/-- Proof of `ConcDefectCertificate` (`cert_concdefect`) on any `[I.Boundaryless] [BoundedChartedTarget I M]
[FiniteDimensional ℝ E]` (`0 sorryAx`):
- for every atom `p = stereo_chart.symm a ∈ cdata.S` in the open southern hemisphere (`‖a‖ < 1`),
  `rot = MoebiusFrame.id` and `a` work unconditionally via `isDefectSeq_of_concentration_southern_hemisphere`;
- for any remaining atom `p ∈ cdata.S`, pulling `cdata` back along `rot` (`IsConformalRotationTo I p rot`)
  moves `p` to `south_pole = stereo_chart.symm 0` (`‖0‖ = 0 < 1`), reducing to the unconditional
  southern-hemisphere theorem. -/
theorem concDefectCertificate_of_rotations
    [I.Boundaryless] [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_rot : ∀ p : CP1, (∃ a : ℂ, ‖a‖ < 1 ∧ stereo_chart.symm a = p) ∨
      ∃ rot : MoebiusFrame, IsConformalRotationTo I (M := M) p rot) :
    ConcDefectCertificate I u_seq B th := by
  intro cdata m h_decomp p hp
  rcases h_rot p with ⟨a, ha_norm, ha_eq⟩ | ⟨rot, hrot_sp, hrot_inv⟩
  · -- Southern-hemisphere atom: `rot = MoebiusFrame.id`, `0` extra hypotheses!
    obtain ⟨h_def, h_tot⟩ :=
      isDefectSeq_of_concentration_southern_hemisphere I th u_seq B h_jhol h_energy cdata m h_decomp
        hp a ha_norm ha_eq
    exact ⟨MoebiusFrame.id, a, ha_eq, h_def, h_tot⟩
  · -- General atom: pull `cdata` back along `rot` so `south_pole = stereo_chart.symm 0` corresponds to `p`.
    haveI := cdata.μ_fin
    let h_symm : CP1 ≃ₜ CP1 := rot.toHomeo.symm
    let e_symm := h_symm.toMeasurableEquiv
    have h_map_apply : ∀ (ν : MeasureTheory.Measure CP1) (A : Set CP1),
        (MeasureTheory.Measure.map h_symm ν) A = ν (h_symm ⁻¹' A) := by
      intro ν A; exact e_symm.map_apply A
    let u'_seq : ℕ → (CP1 → M) := fun n => u_seq n ∘ rot.toHomeo
    have hu'_jhol : ∀ n, JHolomorphicOn I I_CP1 (u'_seq n) Set.univ :=
      fun n => (hrot_inv (u_seq n) (h_jhol n)).1
    have hu'_energy : ∀ n, totalEnergy I (u'_seq n) ≤ B := by
      intro n
      rw [totalEnergy_conformal_invariant I (u_seq n) rot (hrot_inv (u_seq n) (h_jhol n)).2]
      exact h_energy n
    let μ' : MeasureTheory.Measure CP1 := MeasureTheory.Measure.map h_symm cdata.μ
    have hμ'_univ : μ' Set.univ ≤ ENNReal.ofReal B := by
      rw [h_map_apply cdata.μ Set.univ, Set.preimage_univ]
      exact cdata.μ_total_le
    haveI hμ'_fin : MeasureTheory.IsFiniteMeasure μ' :=
      Compactness.isFiniteMeasure_of_univ_le_ofReal μ' hμ'_univ
    have h_weak' : Compactness.WeakMeasureConvergence
        (fun n => energyMeasureExtended I (u'_seq (cdata.σ.1 n))) μ' := by
      have h_eq_fn : (fun n => energyMeasureExtended I (u'_seq (cdata.σ.1 n))) =
          fun n => MeasureTheory.Measure.map h_symm (energyMeasureExtended I (u_seq (cdata.σ.1 n))) := by
        ext n : 1
        exact (hrot_inv (u_seq (cdata.σ.1 n)) (h_jhol (cdata.σ.1 n))).2
      rw [h_eq_fn]
      exact weakMeasureConvergence_map_homeomorph cdata.weak_lim h_symm
    let S' : Finset CP1 := cdata.S.map ⟨h_symm, h_symm.injective⟩
    have h_pre_singleton : ∀ q : CP1, h_symm ⁻¹' ({q} : Set CP1) = {rot.toHomeo q} := by
      intro q
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hx => by rw [← hx]; exact (rot.toHomeo.apply_symm_apply x).symm,
        fun hx => by rw [hx]; exact rot.toHomeo.symm_apply_apply q⟩
    have hS'_def : ∀ q : CP1, q ∈ S' ↔ ENNReal.ofReal th.ε_reg ≤ μ' {q} := by
      intro q
      rw [h_map_apply cdata.μ {q}, h_pre_singleton q, ← cdata.S_def (rot.toHomeo q)]
      simp only [S', Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨fun ⟨x, hxS, hxq⟩ => by
          have : rot.toHomeo q = x := by rw [← hxq]; exact rot.toHomeo.apply_symm_apply x
          rwa [this],
        fun h_mem => ⟨rot.toHomeo q, h_mem, (rot.toHomeo.symm_apply_apply q)⟩⟩
    have h_card_eq : S'.card = cdata.S.card := Finset.card_map _
    let u'₀ : CP1 → M := cdata.u₀ ∘ rot.toHomeo
    have hu'₀_jhol : JHolomorphicOn I I_CP1 u'₀ Set.univ :=
      (hrot_inv cdata.u₀ cdata.u₀_jhol).1
    have h_dom_eq : rot.toHomeo ⁻¹' (Set.univ \ (cdata.S : Set CP1)) = Set.univ \ (S' : Set CP1) := by
      ext q
      simp only [S', Set.mem_preimage, Set.mem_diff, Set.mem_univ, true_and, Finset.mem_coe,
        Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · intro h_not ⟨x, hxS, hxq⟩
        apply h_not
        have : rot.toHomeo q = x := by rw [← hxq]; exact rot.toHomeo.apply_symm_apply x
        rwa [this]
      · intro h_not h_in
        exact h_not ⟨rot.toHomeo q, h_in, rot.toHomeo.symm_apply_apply q⟩
    have h_smooth' : SmoothLocalConvergesOn I (fun n => u'_seq (cdata.σ.1 n)) u'₀ (Set.univ \ S') := by
      rw [← h_dom_eq]
      exact smooth_local_comp_moebius I (fun n => u_seq (cdata.σ.1 n)) cdata.u₀
        (Set.univ \ cdata.S) (fun _ => rot) rot cdata.smooth_conv tendsto_const_nhds
    let m' : CP1 → ℝ := fun q => m (rot.toHomeo q)
    have h_decomp' : μ' = energyMeasureExtended I u'₀ +
        ∑ q ∈ S', (ENNReal.ofReal (m' q) • MeasureTheory.Measure.dirac q) := by
      ext A hA
      rw [h_map_apply cdata.μ A, h_decomp, MeasureTheory.Measure.add_apply,
        MeasureTheory.Measure.add_apply]
      have h_bg_eq : (energyMeasureExtended I u'₀) A =
          (energyMeasureExtended I cdata.u₀) (h_symm ⁻¹' A) := by
        rw [(hrot_inv cdata.u₀ cdata.u₀_jhol).2, h_map_apply _ A]
      rw [h_bg_eq]
      congr 1
      rw [MeasureTheory.Measure.finsetSum_apply, MeasureTheory.Measure.finsetSum_apply,
        Finset.sum_map]
      refine Finset.sum_congr rfl (fun x _hx => ?_)
      simp only [Function.Embedding.coeFn_mk, MeasureTheory.Measure.smul_apply, smul_eq_mul, m']
      have h_rot_symm : rot.toHomeo (h_symm x) = x := rot.toHomeo.apply_symm_apply x
      rw [h_rot_symm]
      congr 1
      have h_pre_meas : MeasurableSet (h_symm ⁻¹' A) := hA.preimage h_symm.continuous.measurable
      rw [MeasureTheory.Measure.dirac_apply' x h_pre_meas, MeasureTheory.Measure.dirac_apply' (h_symm x) hA]
      by_cases hxA : h_symm x ∈ A <;> simp [hxA]
    let cdata' : Compactness.ConcentrationData I u'_seq B th :=
      { σ := cdata.σ
        μ := μ'
        μ_fin := hμ'_fin
        μ_total_le := hμ'_univ
        weak_lim := h_weak'
        S := S'
        S_def := hS'_def
        card_S_mul_le := by rw [h_card_eq]; exact cdata.card_S_mul_le
        card_S_le := by rw [h_card_eq]; exact cdata.card_S_le
        u₀ := u'₀
        u₀_jhol := hu'₀_jhol
        smooth_conv := h_smooth'
        measure_decomp := by
          conv_lhs => rw [h_decomp']
          congr 1
          refine Finset.sum_congr rfl (fun q hq => ?_)
          have h_eval_q : μ' {q} = ENNReal.ofReal (m' q) := by
            rw [h_decomp', MeasureTheory.Measure.add_apply,
              Compactness.energyMeasureExtended_singleton_eq_zero I u'₀ q, zero_add,
              Compactness.dirac_sum_singleton_mem S' m' q hq]
          rw [h_eval_q] }
    have h_sp_in_S' : south_pole ∈ S' := by
      simp only [S', Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨p, hp, by dsimp [h_symm]; rw [← hrot_sp]; exact rot.toHomeo.symm_apply_apply south_pole⟩
    have h_symm_zero : stereo_chart.symm (0 : ℂ) = south_pole := by
      rw [← stereo_chart_south_pole]
      exact stereo_chart.left_inv (by rw [stereo_chart_source]; exact south_pole_ne_north_pole)
    have h0_norm : ‖(0 : ℂ)‖ < 1 := by simp
    obtain ⟨h_def0, h_tot0⟩ :=
      isDefectSeq_of_concentration_southern_hemisphere I th u'_seq B hu'_jhol hu'_energy cdata' m'
        h_decomp' h_sp_in_S' 0 h0_norm h_symm_zero
    have hu'₀_sp : cdata'.u₀ south_pole = cdata.u₀ p := by
      change cdata.u₀ (rot.toHomeo south_pole) = cdata.u₀ p
      rw [hrot_sp]
    have hm'_sp : m' south_pole = m p := by
      dsimp [m']; rw [hrot_sp]
    rw [hu'₀_sp, hm'_sp] at h_def0
    rw [hm'_sp] at h_tot0
    refine ⟨rot, 0, ?_, h_def0, ?_⟩
    · rw [h_symm_zero, hrot_sp]
    · rintro ⟨hS_single, c, hc⟩
      apply h_tot0
      refine ⟨?_, c, fun z => hc (rot.toHomeo z)⟩
      ext q
      simp only [cdata', S', hS_single, Finset.mem_map, Finset.mem_singleton,
        Function.Embedding.coeFn_mk, exists_eq_left]
      exact ⟨fun hq => by rw [← hq, ← hrot_sp]; exact rot.toHomeo.symm_apply_apply south_pole,
        fun hq => by rw [hq, ← hrot_sp]; exact rot.toHomeo.symm_apply_apply south_pole⟩

/-- Contract G01 (`assemble_prestable_limit_of_thresholds`) proved via `concDefectCertificate_of_rotations` (`0 sorryAx`). -/
theorem assemble_prestable_limit_of_rotations
    [I.Boundaryless] [BoundedChartedTarget I M] [FiniteDimensional ℝ E]
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_conc_extract : Compactness.SmoothConcentrationExtractProperty I u_seq th)
    (h_cert : Bubbling.OneLevelCertificate I th)
    (h_rot : ∀ p : CP1, (∃ a : ℂ, ‖a‖ < 1 ∧ stereo_chart.symm a = p) ∨
      ∃ rot : MoebiusFrame, IsConformalRotationTo I (M := M) p rot) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B :=
  assemble_prestable_limit_of_thresholds I th u_seq B h_jhol h_energy
    h_conc_extract h_cert (concDefectCertificate_of_rotations I th u_seq B h_jhol h_energy h_rot)

#print axioms frame_comp_id_left
#print axioms frame_comp_id_right
#print axioms frame_comp_assoc
#print axioms frame_transition_rel
#print axioms transition_collapse_reduction
#print axioms assemble_global_frames
#print axioms prestable_limit_energy_bound
#print axioms prestable_limit_singleton
#print axioms TreeRescalingData.singleton
#print axioms prestable_limit_singleton_subseq
#print axioms graft_root_sphere_tree
#print axioms assemble_prestable_limit

end GromovCompactness.Assembly
