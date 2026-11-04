/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.EnergyGap
import GromovCompactness.Analysis.HoferRescaling
import GromovCompactness.Topology.SmoothLocal
import GromovCompactness.Topology.Subsequence
import GromovCompactness.Topology.SphereTree
import GromovCompactness.Compactness.Assembly
import GromovCompactness.Compactness.Stabilize

open scoped Manifold ContDiff Topology Classical
open Metric Set Filter GromovCompactness GromovCompactness.Assembly Classical

namespace GromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Task G03: Core Genus 0 Compactness Theorem

This module formalizes the core Genus 0 Gromov Compactness Theorem and the `CompactnessWitness`
structure, following Gromov (1985, Theorem 1.2), Ivashkovich-Shevchishin (1999, Theorem 1),
and `gromov_compactness.pdf` §2.3 & Theorem 1 (Task `G03`).

## Key Definitions & Theorems
- `CompactnessWitness`: The full mathematical witness certificate for Gromov convergence of a sequence
  of $J$-holomorphic spheres to a stable sphere tree limit.
- `gromov_compactness_core`: Core compactness theorem for sequences of non-constant curves.
- `gromov_subsequence_alternative`: Sequential compactness alternative for arbitrary sphere sequences
  (either constant subsequence or stable tree limit).
-/

/-- A mathematical witness of Gromov convergence of a sequence $u_n : \mathbb{CP}^1 \to M$
to a stable sphere tree limit curve $(T, \{u_v\}, \{z_{vw}\})$ (`gromov_compactness.pdf` §2.3). -/
structure CompactnessWitness
    (u_seq : ℕ → (CP1 → M)) (u_lim : StableSphereTreeLimit I (M := M)) where
  /-- Strictly increasing subsequence extraction map $\sigma : \mathbb{N} \to \mathbb{N}$. -/
  σ : Bookkeeping.SubseqMap
  /-- Global Möbius coordinate frames $\phi_{v, n} \in \operatorname{PSL}(2, \mathbb{C})$ for each component $v$. -/
  frames : (v : u_lim.tree.V) → ℕ → MoebiusFrame
  /-- $C^\infty_{\mathrm{loc}}$ convergence on each component away from incident nodes:
  $$u_{\sigma(n)} \circ \phi_{v, n} \longrightarrow u_v \quad \text{on } \mathbb{CP}^1 \setminus Z_v.$$ -/
  smooth_conv : ∀ (v : u_lim.tree.V),
    SmoothLocalConvergesOn I
      (fun n => (u_seq (σ.1 n)) ∘ (frames v n).toHomeo)
      (u_lim.map v)
      (punctured_sphere { z | ∃ (w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w), z = u_lim.tree.node_point v w h })
  /-- Frame transition collapse (PDF §2.3 condition 2): for adjacent components $v \sim w$,
  $$\phi_{v, n}^{-1} \circ \phi_{w, n} \longrightarrow z_{vw} \quad \text{locally uniformly on } \mathbb{CP}^1 \setminus \{z_{wv}\}.$$ -/
  frame_collapse : ∀ (v w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w),
    ∀ K ⊆ punctured_sphere {u_lim.tree.node_point w v (u_lim.tree.adj.symm h)}, IsCompact K →
      TendstoUniformlyOn
        (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames v n)) (frames w n)).toHomeo)
        (fun _ => u_lim.tree.node_point v w h) atTop K
  /-- Global energy conservation: $\lim_{n \to \infty} E(u_{\sigma(n)}) = \sum_{v \in V} E(u_v)$. -/
  energy_conv :
    Tendsto (fun n => totalEnergy I (u_seq (σ.1 n))) atTop
      (𝓝 (∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v)))

/-- **Core Genus 0 Gromov Compactness Theorem (Theorem 1 Core & Contract G03)**.
Let $u_n : \mathbb{CP}^1 \to M$ be a sequence of non-constant $J$-holomorphic spheres with
uniformly bounded energy $E(u_n) \le B < \infty$. Then there exists a subsequence converging
to a stable sphere tree limit in the compactness witness sense. -/
theorem gromov_compactness_core
    (_th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (_h_nonconst : ∀ n, ¬ ∃ c : M, ∀ z, u_seq n z = c)
    (_h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (_h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    ∃ (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I u_seq u_lim) := by
  sorry

/-- Sequential compactness alternative for arbitrary sphere sequences (PDF §2.3 & Theorem 1 note):
Either there exists an infinite constant subsequence converging in the compact manifold $M$,
or an infinite non-constant subsequence converging to a stable sphere tree limit. -/
theorem gromov_subsequence_alternative
    (_th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M)) (B : ℝ)
    (_h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n) Set.univ)
    (_h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B) :
    (∃ (σ : Bookkeeping.SubseqMap) (c : M),
      Tendsto (fun n => u_seq (σ.1 n)) atTop (𝓝 (fun _ => c))) ∨
    (∃ (σ : Bookkeeping.SubseqMap) (u_lim : StableSphereTreeLimit I (M := M)),
      Nonempty (CompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim)) := by
  sorry

end GromovCompactness
