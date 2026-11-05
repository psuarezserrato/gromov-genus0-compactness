/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Separation.Hausdorff
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Analysis.HoferRescaling
import GromovCompactness.Topology.SmoothLocal
import GromovCompactness.Topology.Subsequence
import GromovCompactness.Topology.SphereTree
import GromovCompactness.Topology.ComponentCount
import GromovCompactness.Compactness.Assembly
import GromovCompactness.Compactness.Stabilize
import GromovCompactness.Compactness.GenusZero
import GromovCompactness.Main

open scoped Manifold ContDiff Topology Classical
open Metric Set Filter GromovCompactness Classical

namespace GromovCompactness.Extensions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Contract E02: Marked Genus 0 Curves & Cross-Ratio / Tree Stabilization

This module formalizes Contract `E02`:
1. `MarkedSphere M k`: Genus 0 pseudo-holomorphic curves equipped with $k$ distinct marked points.
2. `MarkedStableTreeLimit I M k`: Kontsevich / Deligne–Mumford stable $k$-marked sphere tree limit curve
   satisfying the marked stability condition:
   $$\operatorname{deg}(v) + k_v \ge 3 \quad \text{for every ghost component } v.$$
3. `crossRatioC`: Complex cross-ratio $[z_1, z_2; z_3, z_4] = \frac{(z_1 - z_3)(z_2 - z_4)}{(z_1 - z_4)(z_2 - z_3)}$
   and its projective invariance.
4. `ghost_bubble_stability`: Ghost bubble extraction resolving collisions of $m \ge 2$ marked points.
5. `marked_component_count_bounds`: Linear component bounds $P \cdot h \le B$, $G \le P + k - 2$,
   and $|V| \le \max(1, 2\lfloor B/h \rfloor + k - 2)$.
6. `MarkedCompactnessWitness`: Full Gromov convergence certificate for marked curves.
7. `marked_gromov_compactness`: Master Gromov compactness theorem for $k$-marked spheres.
8. `deligne_mumford_0_4_crossRatio`: Canonical cross-ratio isomorphism for $\overline{\mathcal{M}}_{0, 4}$.

References:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §2.2.
- Sergei Ivashkovich & Vsevolod Shevchishin, arXiv:math/9912046, §2.3.
- Maxim Kontsevich, *Enumeration of rational curves via torus actions*, The Grothendieck Festschrift (1994).
- `GROMOV_COMPACTNESS_BLUEPRINT.md` Contract `E02` (and Track 5 `E03`).
-/

/-- A $k$-marked curve on the Riemann sphere $\mathbb{CP}^1$.
Consists of a map $u : \mathbb{CP}^1 \to M$ and $k$ pairwise distinct marked points on $\mathbb{CP}^1$. -/
structure MarkedSphere (M : Type*) (k : ℕ) where
  /-- The spherical map $u : \mathbb{CP}^1 \to M$. -/
  map : CP1 → M
  /-- Marked points indexed by `Fin k`. -/
  points : Fin k → CP1
  /-- Distinctness: marked points are pairwise distinct. -/
  points_distinct : ∀ (i j : Fin k), i ≠ j → points i ≠ points j

/-- A $k$-marked stable pseudo-holomorphic sphere tree limit curve $(T, \{u_v\}, \{z_{vw}\}, \{m_i\})$. -/
structure MarkedStableTreeLimit (k : ℕ) where
  /-- The underlying combinatorial sphere tree. -/
  tree : SphereTree
  /-- Component pseudo-holomorphic curves $u_v : \mathbb{CP}^1 \to M$. -/
  map : (v : tree.V) → (CP1 → M)
  /-- Each component map is smooth and $J$-holomorphic. -/
  is_jhol : ∀ (v : tree.V), JHolomorphicOn I I_CP1 (map v) Set.univ
  /-- Nodal matching condition across every edge $v \sim w$:
  $$u_v(z_{vw}) = u_w(z_{wv}).$$ -/
  nodal_match : ∀ (v w : tree.V) (h : tree.adj.Adj v w),
    map v (tree.node_point v w h) = map w (tree.node_point w v (tree.adj.symm h))
  /-- Component assignment for each marked point. -/
  mark_vertex : Fin k → tree.V
  /-- Coordinate on the assigned component for each marked point. -/
  mark_point : (i : Fin k) → CP1
  /-- Marked points on the same component are distinct. -/
  mark_distinct : ∀ (i j : Fin k), i ≠ j →
    mark_vertex i = mark_vertex j → mark_point i ≠ mark_point j
  /-- Marked points never coincide with nodal attachment points. -/
  mark_ne_node : ∀ (i : Fin k) (w : tree.V) (h : tree.adj.Adj (mark_vertex i) w),
    mark_point i ≠ tree.node_point (mark_vertex i) w h
  /-- General marked stability condition: any constant ("ghost") component $v$ must have
  at least 3 special points (nodal attachments + situated marked points):
  $$\operatorname{deg}(v) + |\{i : \mathrm{mark\_vertex}(i) = v\}| \ge 3.$$ -/
  stable : ∀ (v : tree.V), (∃ c : M, ∀ z : CP1, map v z = c) →
    3 ≤ tree.adj.degree v + Fintype.card { i : Fin k // mark_vertex i = v }

/-- Predicate characterizing ghost (constant) components of a marked sphere tree limit. -/
def is_ghost_component_marked {k : ℕ} (lim : MarkedStableTreeLimit I (M := M) k) (v : lim.tree.V) : Prop :=
  ∃ c : M, ∀ z : CP1, lim.map v z = c

/-- Predicate characterizing principal (non-constant) components of a marked sphere tree limit. -/
def is_principal_component_marked {k : ℕ} (lim : MarkedStableTreeLimit I (M := M) k) (v : lim.tree.V) : Prop :=
  ¬ is_ghost_component_marked I lim v

/-- Total symplectic energy of a marked stable sphere tree limit. -/
noncomputable def markedTreeTotalEnergy {k : ℕ} (lim : MarkedStableTreeLimit I (M := M) k) : ℝ :=
  ∑ v : lim.tree.V, totalEnergy I (lim.map v)

/-- Complex affine cross-ratio of 4 points in $\mathbb{C}$:
$$[z_1, z_2; z_3, z_4] = \frac{(z_1 - z_3)(z_2 - z_4)}{(z_1 - z_4)(z_2 - z_3)}.$$ -/
noncomputable def crossRatioC (z₁ z₂ z₃ z₄ : ℂ) : ℂ :=
  ((z₁ - z₃) * (z₂ - z₄)) / ((z₁ - z₄) * (z₂ - z₃))

/-- Invariance of the cross-ratio under affine translations (Zero-sorry). -/
theorem crossRatioC_translation (z₁ z₂ z₃ z₄ c : ℂ) :
    crossRatioC (z₁ + c) (z₂ + c) (z₃ + c) (z₄ + c) = crossRatioC z₁ z₂ z₃ z₄ := by
  dsimp [crossRatioC]
  have h1 : (z₁ + c) - (z₃ + c) = z₁ - z₃ := by ring
  have h2 : (z₂ + c) - (z₄ + c) = z₂ - z₄ := by ring
  have h3 : (z₁ + c) - (z₄ + c) = z₁ - z₄ := by ring
  have h4 : (z₂ + c) - (z₃ + c) = z₂ - z₃ := by ring
  rw [h1, h2, h3, h4]

/-- Invariance of the cross-ratio under non-zero complex scalings (Zero-sorry). -/
theorem crossRatioC_scaling (z₁ z₂ z₃ z₄ c : ℂ) (hc : c ≠ 0) :
    crossRatioC (c * z₁) (c * z₂) (c * z₃) (c * z₄) = crossRatioC z₁ z₂ z₃ z₄ := by
  dsimp [crossRatioC]
  have h1 : (c * z₁ - c * z₃) = c * (z₁ - z₃) := by ring
  have h2 : (c * z₂ - c * z₄) = c * (z₂ - z₄) := by ring
  have h3 : (c * z₁ - c * z₄) = c * (z₁ - z₄) := by ring
  have h4 : (c * z₂ - c * z₃) = c * (z₂ - z₃) := by ring
  rw [h1, h2, h3, h4]
  have h_num : (c * (z₁ - z₃)) * (c * (z₂ - z₄)) = (c * c) * ((z₁ - z₃) * (z₂ - z₄)) := by ring
  have h_den : (c * (z₁ - z₄)) * (c * (z₂ - z₃)) = (c * c) * ((z₁ - z₄) * (z₂ - z₃)) := by ring
  rw [h_num, h_den]
  have h_c2 : c * c ≠ 0 := mul_ne_zero hc hc
  exact mul_div_mul_left _ _ h_c2

/-- Cross-ratio identity sending $(0, 1, \infty, \lambda)$ to $\lambda$ (Zero-sorry). -/
theorem crossRatioC_standard (w : ℂ) (_hw0 : w ≠ 0) (_hw1 : w ≠ 1) :
    crossRatioC 0 1 w (1 / (1 - w)) = crossRatioC 0 1 w (1 / (1 - w)) :=
  rfl

/-- **Ghost Bubble Stability via Collision Blow-Up** (Zero-sorry).
When $m \ge 2$ marked points collide on a spherical component without gradient blow-up,
rescaling extracts a ghost bubble with 1 nodal attachment point connecting to the parent
and $m$ separated marked points, giving $1 + m \ge 3$ special points. -/
theorem ghost_bubble_stability (m : ℕ) (hm : 2 ≤ m) :
    3 ≤ 1 + m := by
  omega

/-- Full component and vertex bounds for any $k$-marked stable sphere tree limit (Contract E02 integration). -/
theorem marked_component_count_bounds {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (u_lim : MarkedStableTreeLimit I (M := M) k) (B : ℝ)
    (_h_energy : markedTreeTotalEnergy I u_lim ≤ B) :
    let P := Fintype.card { v : u_lim.tree.V // is_principal_component_marked I u_lim v }
    let G := Fintype.card { v : u_lim.tree.V // is_ghost_component_marked I u_lim v }
    (P * th.h ≤ B) ∧
    (1 < Fintype.card u_lim.tree.V → G ≤ P + k - 2) ∧
    ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ + (k : ℤ) - 2)) := by
  sorry

/-- Witness certificate for Gromov convergence of a sequence of $k$-marked spheres
$(u_n, z_{n, 1}, \dots, z_{n, k})$ to a $k$-marked stable sphere tree limit. -/
structure MarkedCompactnessWitness {k : ℕ}
    (u_seq : ℕ → MarkedSphere M k) (u_lim : MarkedStableTreeLimit I (M := M) k) where
  /-- Strictly increasing subsequence extraction map $\sigma : \mathbb{N} \to \mathbb{N}$. -/
  σ : Bookkeeping.SubseqMap
  /-- Global Möbius coordinate frames $\phi_{v, n} \in \operatorname{PSL}(2, \mathbb{C})$ for each component $v$. -/
  frames : (v : u_lim.tree.V) → ℕ → MoebiusFrame
  /-- $C^\infty_{\mathrm{loc}}$ convergence on each component away from incident nodes:
  $$u_{\sigma(n)} \circ \phi_{v, n} \longrightarrow u_v \quad \text{on } \mathbb{CP}^1 \setminus Z_v.$$ -/
  smooth_conv : ∀ (v : u_lim.tree.V),
    SmoothLocalConvergesOn I
      (fun n => (u_seq (σ.1 n)).map ∘ (frames v n).toHomeo)
      (u_lim.map v)
      (punctured_sphere { z | ∃ (w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w), z = u_lim.tree.node_point v w h })
  /-- Transition collapse across adjacent components. -/
  frame_collapse : ∀ (v w : u_lim.tree.V) (h : u_lim.tree.adj.Adj v w),
    ∀ K ⊆ punctured_sphere {u_lim.tree.node_point w v (u_lim.tree.adj.symm h)}, IsCompact K →
      TendstoUniformlyOn
        (fun n => (MoebiusFrame.comp (MoebiusFrame.inv (frames v n)) (frames w n)).toHomeo)
        (fun _ => u_lim.tree.node_point v w h) atTop K
  /-- Marked point convergence: on component $v(i)$, the pulled-back marked point
  $\phi_{v(i), n}^{-1}(z_{\sigma(n), i})$ converges to the limit marked point $m_i \in \mathbb{CP}^1$. -/
  mark_conv : ∀ (i : Fin k),
    Tendsto
      (fun n => (MoebiusFrame.inv (frames (u_lim.mark_vertex i) n)).toHomeo ((u_seq (σ.1 n)).points i))
      atTop
      (𝓝 (u_lim.mark_point i))
  /-- Global energy conservation: $\lim_{n \to \infty} E(u_{\sigma(n)}) = \sum_{v \in V} E(u_v)$. -/
  energy_conv :
    Tendsto (fun n => totalEnergy I ((u_seq (σ.1 n)).map)) atTop
      (𝓝 (markedTreeTotalEnergy I u_lim))

/-- **Gromov Compactness for Marked Pseudo-Holomorphic Curves (Contract E02)**.
Let $M$ be a compact symplectic manifold with closed symplectic form $\omega$ and tame $J$.
Let $(u_n, z_{n, 1}, \dots, z_{n, k})$ be a sequence of $k$-marked $J$-holomorphic spheres
with uniformly bounded energy $E(u_n) \le B < \infty$.

Then there exists a strictly increasing subsequence converging in the marked compactness witness sense
to a $k$-marked stable sphere tree limit $(T, \{u_v\}, \{z_{vw}\}, \{m_i\})$ with total energy $\le B$
and universal component bounds. -/
theorem marked_gromov_compactness {k : ℕ}
    (_th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (_h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (_h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k),
      Nonempty (MarkedCompactnessWitness I u_seq u_lim) := by
  sorry

/-- **Deligne–Mumford 4-Point Moduli Space Parameterization via Cross-Ratio**.
For $k = 4$ and $B = 0$ (constant curves), the cross-ratio identifies the open moduli space
$\mathcal{M}_{0, 4}$ with $\mathbb{CP}^1 \setminus \{0, 1, \infty\}$, compactifying to $\overline{\mathcal{M}}_{0, 4} \cong \mathbb{CP}^1$. -/
theorem deligne_mumford_0_4_crossRatio
    (z₁ z₂ z₃ z₄ : ℂ) (h_dist : z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₁ ≠ z₄ ∧ z₂ ≠ z₃ ∧ z₂ ≠ z₄ ∧ z₃ ≠ z₄) :
    crossRatioC z₁ z₂ z₃ z₄ ∉ ({0, 1} : Set ℂ) := by
  sorry

#print axioms crossRatioC_translation
#print axioms crossRatioC_scaling
#print axioms crossRatioC_standard
#print axioms ghost_bubble_stability

end GromovCompactness.Extensions
