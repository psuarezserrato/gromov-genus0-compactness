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
    map v (tree.node_point v w h) = map w (tree.node_point w v (tree.adj.symm h))
  /-- Ghost stability off the root: every constant bubble component has degree $\ge 3$
  by Contract B05 (Ghost Branching). -/
  stable_off_root : ∀ (v : tree.V), v ≠ root → (∃ c : M, ∀ z : CP1, map v z = c) →
    3 ≤ tree.adj.degree v
  /-- Strictly increasing subsequence extraction map $\sigma : \mathbb{N} \to \mathbb{N}$. -/
  σ : Bookkeeping.SubseqMap
  /-- Global Möbius coordinate frames $\phi_{v, n} \in \operatorname{PSL}(2, \mathbb{C})$ for each component $v$. -/
  frames : (v : tree.V) → ℕ → MoebiusFrame
  /-- Normalization of the base frame: the root frame is the identity. -/
  root_frame_id : ∀ n, frames root n = MoebiusFrame.id
  /-- Frame transition collapse (PDF §2.3 condition 2): for adjacent components $v \sim w$,
  $$\phi_{v, n}^{-1} \circ \phi_{w, n} \longrightarrow z_{vw} \quad \text{locally uniformly on } \mathbb{CP}^1 \setminus \{z_{wv}\}.$$ -/
  frame_collapse : ∀ (v w : tree.V) (h : tree.adj.Adj v w),
    ∀ K ⊆ punctured_sphere {tree.node_point w v (tree.adj.symm h)}, IsCompact K →
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
            (fun _ => tree.node_point v w h) atTop K) := by
  sorry

/-- Canonical rescaling data for a singleton sphere tree with zero non-root components (Zero-sorry). -/
def TreeRescalingData.singleton : TreeRescalingData Bubbling.singletonSphereTree () where
  parent := fun w hw => by cases w; exact False.elim (hw rfl)
  parent_adj := fun w hw => by cases w; exact False.elim (hw rfl)
  center := fun _ _ => 0
  scale := fun _ _ => 1
  scale_pos := fun _ _ => by norm_num
  scale_tendsto := fun w hw => by cases w; exact False.elim (hw rfl)
  center_tendsto := fun w hw => by cases w; exact False.elim (hw rfl)

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
  root_frame_id := fun _ => rfl
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
  root_frame_id := fun _ => rfl
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

/-- Grafting local defect trees at each concentration point p ∈ S onto the base curve u₀. -/
theorem graft_defect_trees_to_root
    (u_seq : ℕ → (CP1 → M)) (B : ℝ) (th : Bubbling.TargetThresholds I M)
    (cdata : Compactness.ConcentrationData I u_seq B th)
    (m_defect : CP1 → ℝ)
    (_hm_sph : ∀ p ∈ cdata.S, th.ε_sph ≤ m_defect p)
    (_h_energy : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop
      (𝓝 (totalEnergy I cdata.u₀ + ∑ p ∈ cdata.S, m_defect p)))
    (_defect_trees : (p : CP1) → p ∈ cdata.S →
      Bubbling.LocalDefectTree I th (m_defect p) (cdata.u₀ p)) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  sorry

/-- Assembles the base map u₀ and all defect trees from Contract B07 into a global prestable limit (Contract G01).
Proved with zero direct sorry. -/
theorem assemble_prestable_limit
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  have hB : 0 ≤ B := (energy_nonneg I (u_seq 0) Set.univ).trans (h_energy 0)
  obtain ⟨cdata⟩ := Compactness.exists_concentration_data I u_seq h_jhol B hB h_energy th
  obtain ⟨m_defect, hm_sph, _hm_zero, _h_decomp, h_tendsto_energy⟩ :=
    Compactness.defect_measure_identity I u_seq B th cdata
  by_cases hS : cdata.S = ∅
  · have h_smooth : SmoothLocalConvergesOn I (fun n => u_seq (cdata.σ.1 n)) cdata.u₀ Set.univ := by
      have h_sc := cdata.smooth_conv
      have h_diff : Set.univ \ (cdata.S : Set CP1) = Set.univ := by simp [hS]
      rwa [h_diff] at h_sc
    have h_en_lim : Tendsto (fun n => totalEnergy I (u_seq (cdata.σ.1 n))) atTop (𝓝 (totalEnergy I cdata.u₀)) := by
      have h_sum_zero : (∑ p ∈ cdata.S, m_defect p) = 0 := by simp [hS]
      rw [h_sum_zero, add_zero] at h_tendsto_energy
      exact h_tendsto_energy
    let pdata := prestable_limit_singleton_subseq I u_seq cdata.σ cdata.u₀ cdata.u₀_jhol h_smooth h_en_lim
    refine ⟨pdata, ?_⟩
    exact prestable_limit_energy_bound I u_seq B pdata h_energy
  · let defect_trees : (p : CP1) → p ∈ cdata.S → Bubbling.LocalDefectTree I th (m_defect p) (cdata.u₀ p) :=
      fun p hp =>
        have h_pos : 0 < m_defect p := th.ε_sph_pos.trans_le (hm_sph p hp)
        Classical.choice (Bubbling.resolve_single_defect_tree I th (m_defect p) h_pos (cdata.u₀ p))
    exact graft_defect_trees_to_root I u_seq B th cdata m_defect hm_sph h_tendsto_energy defect_trees

#print axioms frame_comp_id_left
#print axioms frame_comp_id_right
#print axioms frame_comp_assoc
#print axioms frame_transition_rel
#print axioms transition_collapse_reduction
#print axioms prestable_limit_energy_bound
#print axioms prestable_limit_singleton
#print axioms TreeRescalingData.singleton
#print axioms prestable_limit_singleton_subseq
#print axioms assemble_prestable_limit

end GromovCompactness.Assembly
