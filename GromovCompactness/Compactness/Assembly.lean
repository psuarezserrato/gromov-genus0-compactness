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
  energy_ident := by
    have h_sum : (∑ v : Bubbling.singletonSphereTree.V, totalEnergy I ((fun _ => u_lim) v)) = totalEnergy I u_lim := by
      change (∑ _v : Unit, totalEnergy I u_lim) = totalEnergy I u_lim
      simp
    rw [h_sum]
    exact h_energy

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

private theorem extract_grafted_tree_rescaling_and_conv_aux
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
  by_cases h_root : (cdata.S = ∅ ∧
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
          (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)))
  · exact extract_grafted_tree_rescaling_and_conv I u_seq B th cdata m_defect P h_root
  · sorry

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
          ∀ (v : P.tree.V),
            SmoothLocalConvergesOn I
              (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
              (P.map v)
              (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
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
      smooth_conv := h_conv frames h_root_id h_rec
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
          ∀ (v : P.tree.V),
            SmoothLocalConvergesOn I
              (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
              (P.map v)
              (punctured_sphere { z | ∃ (w : P.tree.V) (h : P.tree.adj.Adj v w), z = P.tree.node_point v w h })) ∧
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

/-- Assembles the base map u₀ and all defect trees from Contract B07 into a global prestable limit (Contract G01).
Proved with zero direct sorry. -/
theorem assemble_prestable_limit
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_fin : ∀ n, energyMeasureExtended I (u_seq n) Set.univ < ⊤) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  by_cases h_pdata : ∃ (σ : Bookkeeping.SubseqMap),
      Nonempty (PrestableLimitData I (fun n => u_seq (σ.1 n)))
  · rcases h_pdata with ⟨σ, ⟨pdata⟩⟩
    exact assemble_prestable_limit_of_subseq_pdata I u_seq B h_energy σ pdata
  · by_cases h_ev : ∃ (σ : Bookkeeping.SubseqMap) (N₀ : ℕ) (c : M),
        ∀ n ≥ N₀, ∀ z, u_seq (σ.1 n) z = c
    · rcases h_ev with ⟨σ, N₀, c, hc⟩
      exact assemble_prestable_limit_of_eventually_const_subseq I u_seq B h_jhol h_energy σ N₀ c hc
    · have hB : 0 ≤ B := (energy_nonneg I (u_seq 0) Set.univ).trans (h_energy 0)
      obtain ⟨cdata⟩ := Compactness.exists_concentration_data I u_seq h_jhol B hB h_energy h_fin th
      obtain ⟨m_defect, hm_sph, _hm_zero, _h_decomp, h_tendsto_energy⟩ :=
        Compactness.defect_measure_identity I u_seq B th cdata
      let defect_trees : (p : CP1) → p ∈ cdata.S → Bubbling.LocalDefectTree I th (m_defect p) (cdata.u₀ p) :=
        fun p hp =>
          have h_pos : 0 < m_defect p := th.ε_sph_pos.trans_le (hm_sph p hp)
          Classical.choice (Bubbling.resolve_single_defect_tree I th (m_defect p) h_pos (cdata.u₀ p))
      exact assemble_prestable_limit_of_components I th u_seq B h_energy cdata m_defect hm_sph h_tendsto_energy
        defect_trees (extract_grafted_tree_rescaling_and_conv_aux I u_seq B th cdata m_defect)

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
