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

/-- Telescoping composition of local affine rescalings along rooted paths into global Möbius frames. -/
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

/-- Assembles the base map $u_0$ and all defect trees from Contract B07 into a global prestable limit. -/
theorem assemble_prestable_limit
    (_th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (_h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (_h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (pdata : PrestableLimitData I u_seq),
      (∑ v : pdata.tree.V, totalEnergy I (pdata.map v)) ≤ B := by
  sorry

end GromovCompactness.Assembly
