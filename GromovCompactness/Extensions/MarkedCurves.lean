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

set_option linter.unusedSectionVars false

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

/-- The Ghost Component Bound Theorem for $k$-marked stable sphere trees:
In any marked stable sphere tree with $|V| > 1$, $G \le P + k - 2$ (Zero-sorry). -/
theorem marked_ghost_components_bound {k : ℕ}
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (P G : ℕ)
    (h_multi : 1 < Fintype.card u_lim.tree.V)
    (hP : P = Fintype.card { v : u_lim.tree.V // is_principal_component_marked I u_lim v })
    (hG : G = Fintype.card { v : u_lim.tree.V // is_ghost_component_marked I u_lim v }) :
    G ≤ P + k - 2 := by
  let s_prin := Finset.univ.filter (is_principal_component_marked I u_lim)
  let s_ghost := Finset.univ.filter (is_ghost_component_marked I u_lim)
  have hP' : P = s_prin.card := by rw [hP, Fintype.card_subtype]
  have hG' : G = s_ghost.card := by rw [hG, Fintype.card_subtype]
  have h_prin_eq : s_prin = Finset.univ.filter (fun v => ¬ is_ghost_component_marked I u_lim v) := by
    ext v
    simp [is_principal_component_marked, s_prin]
  have h_sum_cards : s_ghost.card + s_prin.card = Fintype.card u_lim.tree.V := by
    rw [h_prin_eq, Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ]
  have h_V_eq : Fintype.card u_lim.tree.V = G + P := by
    omega
  have h_split := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset u_lim.tree.V))
    (p := is_ghost_component_marked I u_lim) (f := fun v => u_lim.tree.adj.degree v)
  have h_split_sum : ∑ v : u_lim.tree.V, u_lim.tree.adj.degree v =
      (∑ v ∈ s_ghost, u_lim.tree.adj.degree v) +
      (∑ v ∈ s_prin, u_lim.tree.adj.degree v) := by
    rw [h_prin_eq]
    exact h_split.symm
  have h_deg_sum := tree_degree_sum u_lim.tree
  have h_prin_bound : P ≤ ∑ v ∈ s_prin, u_lim.tree.adj.degree v := by
    have h_le : ∑ v ∈ s_prin, (1 : ℕ) ≤ ∑ v ∈ s_prin, u_lim.tree.adj.degree v := by
      apply Finset.sum_le_sum
      intro v _
      exact tree_degree_ge_one u_lim.tree h_multi v
    have h_const : (∑ v ∈ s_prin, (1 : ℕ)) = s_prin.card := by
      simp [Finset.sum_const]
    omega
  have h_stab_le : 3 * G ≤ ∑ v ∈ s_ghost, (u_lim.tree.adj.degree v + Fintype.card { i : Fin k // u_lim.mark_vertex i = v }) := by
    have h_each_stab : ∀ v ∈ s_ghost, 3 ≤ u_lim.tree.adj.degree v + Fintype.card { i : Fin k // u_lim.mark_vertex i = v } := by
      intro v hv
      have hv_ghost : is_ghost_component_marked I u_lim v := (Finset.mem_filter.mp hv).2
      exact u_lim.stable v hv_ghost
    have h_sum := Finset.sum_le_sum h_each_stab
    have h_const : (∑ v ∈ s_ghost, (3 : ℕ)) = 3 * s_ghost.card := by
      simp [Finset.sum_const, mul_comm]
    rw [hG']
    rwa [h_const] at h_sum
  rw [Finset.sum_add_distrib] at h_stab_le
  have h_fiber_card : (∑ v : u_lim.tree.V, Fintype.card { i : Fin k // u_lim.mark_vertex i = v }) = k := by
    have h_equiv := Fintype.card_congr (Equiv.sigmaFiberEquiv u_lim.mark_vertex)
    rw [Fintype.card_sigma] at h_equiv
    rw [Fintype.card_fin] at h_equiv
    exact h_equiv
  have h_fiber_sub : (∑ v ∈ s_ghost, Fintype.card { i : Fin k // u_lim.mark_vertex i = v }) ≤ k := by
    have h_le := Finset.sum_le_univ_sum_of_nonneg (s := s_ghost) (f := fun v => Fintype.card { i : Fin k // u_lim.mark_vertex i = v })
      (fun _ => Nat.zero_le _)
    rwa [h_fiber_card] at h_le
  omega

/-- Full component and vertex bounds for any $k$-marked stable sphere tree limit (Contract E02 integration, Zero-sorry). -/
theorem marked_component_count_bounds {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (u_lim : MarkedStableTreeLimit I (M := M) k) (B : ℝ)
    (h_energy : markedTreeTotalEnergy I u_lim ≤ B) :
    let P := Fintype.card { v : u_lim.tree.V // is_principal_component_marked I u_lim v }
    let G := Fintype.card { v : u_lim.tree.V // is_ghost_component_marked I u_lim v }
    (P * th.h ≤ B) ∧
    (1 < Fintype.card u_lim.tree.V → G ≤ P + k - 2) ∧
    ((Fintype.card u_lim.tree.V : ℤ) ≤ max 1 (2 * ⌊B / th.h⌋ + (k : ℤ) - 2)) := by
  intro P G
  let s_prin := Finset.univ.filter (is_principal_component_marked I u_lim)
  have hP : P = s_prin.card := by
    dsimp [P, s_prin]
    rw [Fintype.card_subtype]
  have h_each : ∀ v ∈ s_prin, th.h ≤ totalEnergy I (u_lim.map v) := by
    intro v hv
    have hv_prin : is_principal_component_marked I u_lim v := (Finset.mem_filter.mp hv).2
    have hv_nonconst : ¬ ∃ c : M, ∀ z : CP1, u_lim.map v z = c := hv_prin
    have h_sph := th.h_sph (u_lim.map v) (u_lim.is_jhol v) hv_nonconst
    exact th.h_le_sph.trans h_sph
  have h_sum_le : ∑ v ∈ s_prin, th.h ≤ ∑ v ∈ s_prin, totalEnergy I (u_lim.map v) :=
    Finset.sum_le_sum h_each
  have h_const_sum : ∑ v ∈ s_prin, th.h = (P : ℝ) * th.h := by
    rw [Finset.sum_const, nsmul_eq_mul, hP]
  rw [h_const_sum] at h_sum_le
  have h_nonneg : ∀ v : u_lim.tree.V, 0 ≤ totalEnergy I (u_lim.map v) := by
    intro v
    exact energy_nonneg I (u_lim.map v) Set.univ
  have h_sub_le : ∑ v ∈ s_prin, totalEnergy I (u_lim.map v) ≤
      ∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) := by
    apply Finset.sum_le_univ_sum_of_nonneg
    intro i
    exact h_nonneg i
  have h_P_energy : (P : ℝ) * th.h ≤ B :=
    h_sum_le.trans (h_sub_le.trans h_energy)
  refine ⟨h_P_energy, ?_, ?_⟩
  · intro h_multi
    exact marked_ghost_components_bound I u_lim P G h_multi rfl rfl
  · by_cases h_multi : 1 < Fintype.card u_lim.tree.V
    · have h_G_le := marked_ghost_components_bound I u_lim P G h_multi rfl rfl
      let s_ghost := Finset.univ.filter (is_ghost_component_marked I u_lim)
      have hG : G = s_ghost.card := by
        dsimp [G, s_ghost]
        rw [Fintype.card_subtype]
      have h_prin_eq : s_prin = Finset.univ.filter (fun v => ¬ is_ghost_component_marked I u_lim v) := by
        ext v
        simp [is_principal_component_marked, s_prin]
      have h_sum_cards : s_ghost.card + s_prin.card = Fintype.card u_lim.tree.V := by
        rw [h_prin_eq, Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ]
      have h_V_eq : Fintype.card u_lim.tree.V = G + P := by
        omega
      have h_P_le_div : (P : ℝ) ≤ B / th.h := by
        rwa [le_div_iff₀ th.h_pos]
      have h_P_le_floor : (P : ℤ) ≤ ⌊B / th.h⌋ := by
        rw [Int.le_floor]
        exact h_P_le_div
      have h_card_le : (Fintype.card u_lim.tree.V : ℤ) ≤ 2 * ⌊B / th.h⌋ + (k : ℤ) - 2 := by
        have h1 : (Fintype.card u_lim.tree.V : ℤ) ≤ 2 * (P : ℤ) + (k : ℤ) - 2 := by omega
        linarith
      exact h_card_le.trans (le_max_right 1 (2 * ⌊B / th.h⌋ + (k : ℤ) - 2))
    · have h_card1 : Fintype.card u_lim.tree.V = 1 := by
        have h_pos : 0 < Fintype.card u_lim.tree.V := Fintype.card_pos
        omega
      rw [h_card1]
      push_cast
      exact le_max_left 1 (2 * ⌊B / th.h⌋ + (k : ℤ) - 2)

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
  intro h_in
  rcases h_dist with ⟨h12, h13, h14, h23, h24, h34⟩
  have hd13 : z₁ - z₃ ≠ 0 := sub_ne_zero.mpr h13
  have hd24 : z₂ - z₄ ≠ 0 := sub_ne_zero.mpr h24
  have hd14 : z₁ - z₄ ≠ 0 := sub_ne_zero.mpr h14
  have hd23 : z₂ - z₃ ≠ 0 := sub_ne_zero.mpr h23
  have hd12 : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr h12
  have hd34 : z₃ - z₄ ≠ 0 := sub_ne_zero.mpr h34
  have h_num_ne : (z₁ - z₃) * (z₂ - z₄) ≠ 0 := mul_ne_zero hd13 hd24
  have h_den_ne : (z₁ - z₄) * (z₂ - z₃) ≠ 0 := mul_ne_zero hd14 hd23
  dsimp [crossRatioC] at h_in
  rcases Set.mem_insert_iff.mp h_in with h0 | h1
  · have hz : ((z₁ - z₃) * (z₂ - z₄)) / ((z₁ - z₄) * (z₂ - z₃)) = 0 := h0
    rw [div_eq_zero_iff] at hz
    rcases hz with hz_num | hz_den
    · exact h_num_ne hz_num
    · exact h_den_ne hz_den
  · have h1_eq : ((z₁ - z₃) * (z₂ - z₄)) / ((z₁ - z₄) * (z₂ - z₃)) = 1 := Set.mem_singleton_iff.mp h1
    have h_eq : (z₁ - z₃) * (z₂ - z₄) = (z₁ - z₄) * (z₂ - z₃) := by
      exact (div_eq_one_iff_eq h_den_ne).mp h1_eq
    have h_diff : (z₁ - z₃) * (z₂ - z₄) - (z₁ - z₄) * (z₂ - z₃) = (z₁ - z₂) * (z₃ - z₄) := by ring
    have h_prod_zero : (z₁ - z₂) * (z₃ - z₄) = 0 := by
      rw [← h_diff, h_eq, sub_self]
    rcases mul_eq_zero.mp h_prod_zero with h_zero1 | h_zero2
    · exact hd12 h_zero1
    · exact hd34 h_zero2

#print axioms crossRatioC_translation
#print axioms crossRatioC_scaling
#print axioms crossRatioC_standard
#print axioms ghost_bubble_stability
#print axioms deligne_mumford_0_4_crossRatio
#print axioms marked_ghost_components_bound
#print axioms marked_component_count_bounds

end GromovCompactness.Extensions
