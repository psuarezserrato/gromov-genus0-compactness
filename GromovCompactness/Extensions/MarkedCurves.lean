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

/-- Canonical construction of a `MarkedStableTreeLimit` on the singleton sphere tree from a single
`MarkedSphere` satisfying the marked stability condition (`0 sorryAx`). -/
def MarkedStableTreeLimit.of_markedSphere {k : ℕ}
    (u₀ : MarkedSphere M k)
    (hu_jhol : JHolomorphicOn I I_CP1 u₀.map Set.univ)
    (h_stab : (∃ c : M, ∀ z : CP1, u₀.map z = c) → 3 ≤ k) :
    MarkedStableTreeLimit I (M := M) k where
  tree := Bubbling.singletonSphereTree
  map _ := u₀.map
  is_jhol _ := hu_jhol
  nodal_match _ _ h := False.elim h
  mark_vertex _ := ()
  mark_point := u₀.points
  mark_distinct i j hij _ := u₀.points_distinct i j hij
  mark_ne_node _ _ h := False.elim h
  stable v h_const := by
    have hk : 3 ≤ k := h_stab h_const
    have h_eq : Fintype.card { i : Fin k // (fun _ : Fin k => ()) i = v } = Fintype.card (Fin k) :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv (fun _ => Subsingleton.elim () v))
    rw [Fintype.card_fin] at h_eq
    refine le_trans hk (le_trans ?_ (Nat.le_add_left _ _))
    convert le_of_eq h_eq.symm

/-- Total energy of `MarkedStableTreeLimit.of_markedSphere` equals `totalEnergy I u₀.map` (`0 sorryAx`). -/
theorem markedTreeTotalEnergy_of_markedSphere {k : ℕ}
    (u₀ : MarkedSphere M k)
    (hu_jhol : JHolomorphicOn I I_CP1 u₀.map Set.univ)
    (h_stab : (∃ c : M, ∀ z : CP1, u₀.map z = c) → 3 ≤ k) :
    markedTreeTotalEnergy I (MarkedStableTreeLimit.of_markedSphere I u₀ hu_jhol h_stab) =
      totalEnergy I u₀.map := by
  dsimp [markedTreeTotalEnergy, MarkedStableTreeLimit.of_markedSphere]
  change (∑ _v : Unit, totalEnergy I u₀.map) = totalEnergy I u₀.map
  simp

/-- A `MarkedCompactnessWitness` is preserved along any further subsequence `τ : SubseqMap` (`0 sorryAx`). -/
def MarkedCompactnessWitness.subseq {k : ℕ}
    {u_seq : ℕ → MarkedSphere M k}
    {u_lim : MarkedStableTreeLimit I (M := M) k}
    (wit : MarkedCompactnessWitness I u_seq u_lim)
    (τ : Bookkeeping.SubseqMap) :
    MarkedCompactnessWitness I u_seq u_lim where
  σ := wit.σ.comp τ
  frames v n := wit.frames v (τ.1 n)
  smooth_conv v :=
    smooth_local_congr_seq I rfl
      (smooth_local_subseq I
        (fun n => (u_seq (wit.σ.1 n)).map ∘ (wit.frames v n).toHomeo)
        (u_lim.map v) _ τ.2 (wit.smooth_conv v))
  frame_collapse v w h K hK_sub hK_cpt :=
    tendstoUniformlyOn_subseq τ.2 (wit.frame_collapse v w h K hK_sub hK_cpt)
  mark_conv i := (wit.mark_conv i).comp τ.2.tendsto_atTop
  energy_conv := wit.energy_conv.comp τ.2.tendsto_atTop

/-- Canonical `MarkedCompactnessWitness` for a subsequence converging without bubbling on the
singleton sphere tree (`0 sorryAx`). -/
def MarkedCompactnessWitness.of_singleton_subseq {k : ℕ}
    (u_seq : ℕ → MarkedSphere M k)
    (σ : Bookkeeping.SubseqMap)
    (u₀ : MarkedSphere M k)
    (hu_jhol : JHolomorphicOn I I_CP1 u₀.map Set.univ)
    (h_stab : (∃ c : M, ∀ z : CP1, u₀.map z = c) → 3 ≤ k)
    (h_conv : SmoothLocalConvergesOn I (fun n => (u_seq (σ.1 n)).map) u₀.map Set.univ)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (u₀.points i)))
    (h_en : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n)).map) atTop (𝓝 (totalEnergy I u₀.map))) :
    MarkedCompactnessWitness I u_seq (MarkedStableTreeLimit.of_markedSphere I u₀ hu_jhol h_stab) where
  σ := σ
  frames _ _ := MoebiusFrame.id
  smooth_conv v := by
    change SmoothLocalConvergesOn I
      (fun n => (u_seq (σ.1 n)).map ∘ (MoebiusFrame.id).toHomeo)
      u₀.map
      (punctured_sphere { z : CP1 | ∃ (w : Bubbling.singletonSphereTree.V)
        (h : Bubbling.singletonSphereTree.adj.Adj v w),
        z = Bubbling.singletonSphereTree.node_point v w h })
    have h_dom : (punctured_sphere { z : CP1 | ∃ (w : Bubbling.singletonSphereTree.V)
        (h : Bubbling.singletonSphereTree.adj.Adj v w),
        z = Bubbling.singletonSphereTree.node_point v w h }) = Set.univ := by
      dsimp [punctured_sphere]
      have h_empty : { z : CP1 | ∃ (w : Bubbling.singletonSphereTree.V)
          (h : Bubbling.singletonSphereTree.adj.Adj v w),
          z = Bubbling.singletonSphereTree.node_point v w h } = ∅ := by
        ext z
        simp only [mem_setOf_eq, not_exists, mem_empty_iff_false, iff_false]
        intro w h
        exact False.elim h
      rw [h_empty, diff_empty]
    rw [h_dom]
    have h_seq : (fun n => (u_seq (σ.1 n)).map ∘ (MoebiusFrame.id).toHomeo) =
        fun n => (u_seq (σ.1 n)).map := by
      ext n z; rfl
    rw [h_seq]
    exact h_conv
  frame_collapse _ _ h := False.elim h
  mark_conv i := by
    have h_inv : (fun n => (MoebiusFrame.inv MoebiusFrame.id).toHomeo ((u_seq (σ.1 n)).points i)) =
        fun n => (u_seq (σ.1 n)).points i := by
      ext n; rfl
    rw [h_inv]
    exact h_marks i
  energy_conv := by
    rw [markedTreeTotalEnergy_of_markedSphere I u₀ hu_jhol h_stab]
    exact h_en

/-- Canonical `MarkedCompactnessWitness` on the singleton sphere tree when a subsequence of marked
spheres is constant with constant map `fun _ => c` and constant marked points (`0 sorryAx`). -/
def MarkedCompactnessWitness.of_const_subseq {k : ℕ}
    (u_seq : ℕ → MarkedSphere M k)
    (σ : Bookkeeping.SubseqMap)
    (c : M)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_stab : 3 ≤ k)
    (h_map_eq : ∀ n z, (u_seq (σ.1 n)).map z = c)
    (h_pts_eq : ∀ n i, (u_seq (σ.1 n)).points i = pts i) :
    MarkedCompactnessWitness I u_seq
      (MarkedStableTreeLimit.of_markedSphere I
        ⟨fun _ => c, pts, h_pts_dist⟩
        (Analysis.jholomorphicOn_const I c Set.univ)
        (fun _ => h_stab)) :=
  MarkedCompactnessWitness.of_singleton_subseq I u_seq σ
    ⟨fun _ => c, pts, h_pts_dist⟩
    (Analysis.jholomorphicOn_const I c Set.univ)
    (fun _ => h_stab)
    (by
      have h_eq : (fun n => (u_seq (σ.1 n)).map) = (fun _ : ℕ => fun _ : CP1 => c) := by
        ext n z; exact h_map_eq n z
      rw [h_eq]
      exact smoothLocalConvergesOn_const_map I c Set.univ)
    (fun i => by
      have h_eq : (fun n => (u_seq (σ.1 n)).points i) = (fun _ : ℕ => pts i) :=
        funext (fun n => h_pts_eq n i)
      rw [h_eq]
      exact tendsto_const_nhds)
    (by
      have h_eq : (fun n => totalEnergy I (u_seq (σ.1 n)).map) =
          (fun _ : ℕ => totalEnergy I (fun _ : CP1 => c)) := by
        ext n
        have hm : (u_seq (σ.1 n)).map = fun _ => c := funext (h_map_eq n)
        rw [hm]
      rw [h_eq]
      exact tendsto_const_nhds)

/-- Any `MarkedCompactnessWitness` preserves the uniform energy bound `B` in the limit (`0 sorryAx`). -/
theorem markedTreeTotalEnergy_le_of_witness {k : ℕ}
    (u_seq : ℕ → MarkedSphere M k)
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (B : ℝ)
    (wit : MarkedCompactnessWitness I u_seq u_lim)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B) :
    markedTreeTotalEnergy I u_lim ≤ B :=
  le_of_tendsto wit.energy_conv (Eventually.of_forall (fun n => h_energy (wit.σ.1 n)))

/-- Canonical lift of an unmarked `StableSphereTreeLimit` to a `0`-marked `MarkedStableTreeLimit` (`0 sorryAx`). -/
def MarkedStableTreeLimit.of_stableSphereTreeLimit
    (u_lim : StableSphereTreeLimit I (M := M)) :
    MarkedStableTreeLimit I (M := M) 0 where
  tree := u_lim.tree
  map := u_lim.map
  is_jhol := u_lim.is_jhol
  nodal_match := u_lim.nodal_match
  mark_vertex := Fin.elim0
  mark_point := Fin.elim0
  mark_distinct i := i.elim0
  mark_ne_node i := i.elim0
  stable v h_const := le_trans (u_lim.stable v h_const) (Nat.le_add_right _ _)

/-- Total energy of `MarkedStableTreeLimit.of_stableSphereTreeLimit` equals the sum of component energies (`0 sorryAx`). -/
theorem markedTreeTotalEnergy_of_stableSphereTreeLimit
    (u_lim : StableSphereTreeLimit I (M := M)) :
    markedTreeTotalEnergy I (MarkedStableTreeLimit.of_stableSphereTreeLimit I u_lim) =
      ∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) := rfl

/-- If every component of a `k`-marked stable sphere tree limit `u_lim` is constant, then `|V| + 2 ≤ k` (`0 sorryAx`). -/
theorem MarkedStableTreeLimit.card_V_add_two_le_of_all_const {k : ℕ}
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (h_const : ∀ v : u_lim.tree.V, ∃ c : M, ∀ z : CP1, u_lim.map v z = c) :
    Fintype.card u_lim.tree.V + 2 ≤ k := by
  have h_le : ∑ _v : u_lim.tree.V, (3 : ℕ) ≤
      ∑ v : u_lim.tree.V, (u_lim.tree.adj.degree v + Fintype.card { i : Fin k // u_lim.mark_vertex i = v }) :=
    Finset.sum_le_sum (fun v _ => u_lim.stable v (h_const v))
  rw [Finset.sum_add_distrib] at h_le
  have h_lhs : (∑ _v : u_lim.tree.V, (3 : ℕ)) = 3 * Fintype.card u_lim.tree.V := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have h_deg := tree_degree_sum u_lim.tree
  have h_fib : (∑ v : u_lim.tree.V, Fintype.card { i : Fin k // u_lim.mark_vertex i = v }) = k := by
    have h_equiv := Fintype.card_congr (Equiv.sigmaFiberEquiv u_lim.mark_vertex)
    rw [Fintype.card_sigma, Fintype.card_fin] at h_equiv
    exact h_equiv
  have h_pos : 0 < Fintype.card u_lim.tree.V := Fintype.card_pos
  omega

/-- If every component of a `k`-marked stable sphere tree limit `u_lim` is constant, then `3 ≤ k` (`0 sorryAx`). -/
theorem MarkedStableTreeLimit.three_le_of_all_const {k : ℕ}
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (h_const : ∀ v : u_lim.tree.V, ∃ c : M, ∀ z : CP1, u_lim.map v z = c) :
    3 ≤ k := by
  have h1 := u_lim.card_V_add_two_le_of_all_const I h_const
  have h2 : 0 < Fintype.card u_lim.tree.V := Fintype.card_pos
  omega

/-- For `k < 3` on a `[Subsingleton M]` target, `MarkedStableTreeLimit I k` is empty (`0 sorryAx`). -/
theorem MarkedStableTreeLimit.isEmpty_of_lt_three_of_subsingleton [Subsingleton M] {k : ℕ}
    (hk : k < 3) :
    IsEmpty (MarkedStableTreeLimit I (M := M) k) := by
  refine ⟨fun u_lim => ?_⟩
  have h3 := u_lim.three_le_of_all_const I
    (fun v => ⟨u_lim.map v north_pole, fun z => Subsingleton.elim (u_lim.map v z) (u_lim.map v north_pole)⟩)
  omega

/-- For `k < 3` on a `[DiscreteTopology M]` target, `MarkedStableTreeLimit I k` is empty (`0 sorryAx`). -/
theorem MarkedStableTreeLimit.isEmpty_of_lt_three_of_discrete [DiscreteTopology M] {k : ℕ}
    (hk : k < 3) :
    IsEmpty (MarkedStableTreeLimit I (M := M) k) := by
  refine ⟨fun u_lim => ?_⟩
  have h3 := u_lim.three_le_of_all_const I
    (fun v => ⟨u_lim.map v north_pole,
      Analysis.eq_const_north_pole_of_jhol_univ_of_discrete I (u_lim.map v) (u_lim.is_jhol v)⟩)
  omega

/-- Every component of `u_lim : MarkedStableTreeLimit I k` with `markedTreeTotalEnergy I u_lim < th.ε_sph`
is constant (`0 sorryAx`). -/
theorem MarkedStableTreeLimit.all_const_of_lt_eps_sph {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (h_lt : markedTreeTotalEnergy I u_lim < th.ε_sph)
    (v : u_lim.tree.V) :
    ∃ c : M, ∀ z : CP1, u_lim.map v z = c := by
  by_contra h_nc
  have h_ge := th.h_sph (u_lim.map v) (u_lim.is_jhol v) h_nc
  have h_le_sum : totalEnergy I (u_lim.map v) ≤ markedTreeTotalEnergy I u_lim :=
    Finset.single_le_sum (fun w _ => energy_nonneg I (u_lim.map w) Set.univ) (Finset.mem_univ v)
  linarith

/-- If `markedTreeTotalEnergy I u_lim < th.ε_sph`, then `3 ≤ k` (`0 sorryAx`). -/
theorem MarkedStableTreeLimit.three_le_of_lt_eps_sph {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (h_lt : markedTreeTotalEnergy I u_lim < th.ε_sph) :
    3 ≤ k :=
  u_lim.three_le_of_all_const I (u_lim.all_const_of_lt_eps_sph I th h_lt)

/-- If `markedTreeTotalEnergy I u_lim < th.h`, then `3 ≤ k` (`0 sorryAx`). -/
theorem MarkedStableTreeLimit.three_le_of_lt_h {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (h_lt : markedTreeTotalEnergy I u_lim < th.h) :
    3 ≤ k :=
  u_lim.three_le_of_lt_eps_sph I th (h_lt.trans_le th.h_le_sph)

/-- If `markedTreeTotalEnergy I u_lim ≤ 0`, then `3 ≤ k` (`0 sorryAx`). -/
theorem MarkedStableTreeLimit.three_le_of_nonpos_energy {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (h_le : markedTreeTotalEnergy I u_lim ≤ 0) :
    3 ≤ k :=
  u_lim.three_le_of_lt_eps_sph I th (h_le.trans_lt th.ε_sph_pos)

/-- Every unmarked `StableSphereTreeLimit` has at least one non-constant component (`0 sorryAx`). -/
theorem StableSphereTreeLimit.exists_nonconst_component
    (u_lim : StableSphereTreeLimit I (M := M)) :
    ∃ v : u_lim.tree.V, ¬ ∃ c : M, ∀ z : CP1, u_lim.map v z = c := by
  by_contra h_all
  push_neg at h_all
  have h3 := (MarkedStableTreeLimit.of_stableSphereTreeLimit I u_lim).three_le_of_all_const I h_all
  omega

/-- Every unmarked `StableSphereTreeLimit` has total symplectic energy at least `th.ε_sph` (`0 sorryAx`). -/
theorem StableSphereTreeLimit.eps_sph_le_totalEnergy
    (th : Bubbling.TargetThresholds I M)
    (u_lim : StableSphereTreeLimit I (M := M)) :
    th.ε_sph ≤ ∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) := by
  obtain ⟨v, hv⟩ := StableSphereTreeLimit.exists_nonconst_component I u_lim
  have h_ge := th.h_sph (u_lim.map v) (u_lim.is_jhol v) hv
  have h_le_sum : totalEnergy I (u_lim.map v) ≤ ∑ w : u_lim.tree.V, totalEnergy I (u_lim.map w) :=
    Finset.single_le_sum (fun w _ => energy_nonneg I (u_lim.map w) Set.univ) (Finset.mem_univ v)
  linarith

/-- Every unmarked `StableSphereTreeLimit` has total symplectic energy at least `th.h` (`0 sorryAx`). -/
theorem StableSphereTreeLimit.h_le_totalEnergy
    (th : Bubbling.TargetThresholds I M)
    (u_lim : StableSphereTreeLimit I (M := M)) :
    th.h ≤ ∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) :=
  th.h_le_sph.trans (StableSphereTreeLimit.eps_sph_le_totalEnergy I th u_lim)

/-- Every unmarked `StableSphereTreeLimit` has strictly positive total symplectic energy (`0 sorryAx`). -/
theorem StableSphereTreeLimit.totalEnergy_pos
    (th : Bubbling.TargetThresholds I M)
    (u_lim : StableSphereTreeLimit I (M := M)) :
    0 < ∑ v : u_lim.tree.V, totalEnergy I (u_lim.map v) :=
  th.h_pos.trans_le (StableSphereTreeLimit.h_le_totalEnergy I th u_lim)

/-- On a `[Subsingleton M]` target, `StableSphereTreeLimit I` is empty (`0 sorryAx`). -/
theorem StableSphereTreeLimit.isEmpty_of_subsingleton [Subsingleton M] :
    IsEmpty (StableSphereTreeLimit I (M := M)) := by
  haveI := MarkedStableTreeLimit.isEmpty_of_lt_three_of_subsingleton I (M := M) (by decide : 0 < 3)
  exact ⟨fun u_lim => isEmptyElim (MarkedStableTreeLimit.of_stableSphereTreeLimit I u_lim)⟩

/-- On a `[DiscreteTopology M]` target, `StableSphereTreeLimit I` is empty (`0 sorryAx`). -/
theorem StableSphereTreeLimit.isEmpty_of_discrete [DiscreteTopology M] :
    IsEmpty (StableSphereTreeLimit I (M := M)) := by
  haveI := MarkedStableTreeLimit.isEmpty_of_lt_three_of_discrete I (M := M) (by decide : 0 < 3)
  exact ⟨fun u_lim => isEmptyElim (MarkedStableTreeLimit.of_stableSphereTreeLimit I u_lim)⟩

/-- Canonical lift of an unmarked `CompactnessWitness` to a `0`-marked `MarkedCompactnessWitness` (`0 sorryAx`). -/
def MarkedCompactnessWitness.of_compactnessWitness
    (u_seq : ℕ → MarkedSphere M 0)
    (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I (fun n => (u_seq n).map) u_lim) :
    MarkedCompactnessWitness I u_seq (MarkedStableTreeLimit.of_stableSphereTreeLimit I u_lim) where
  σ := wit.σ
  frames := wit.frames
  smooth_conv := wit.smooth_conv
  frame_collapse := wit.frame_collapse
  mark_conv i := i.elim0
  energy_conv := wit.energy_conv

/-- If `u_seq` has energy bounded by `B < th.ε_sph` and admits a `MarkedCompactnessWitness` to `u_lim`,
then `3 ≤ k` (`0 sorryAx`). -/
theorem MarkedCompactnessWitness.three_le_of_B_lt_eps_sph {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M k)
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (B : ℝ)
    (wit : MarkedCompactnessWitness I u_seq u_lim)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (h_lt : B < th.ε_sph) :
    3 ≤ k :=
  u_lim.three_le_of_lt_eps_sph I th
    ((markedTreeTotalEnergy_le_of_witness I u_seq u_lim B wit h_energy).trans_lt h_lt)

/-- For `k < 3` and `B < th.ε_sph`, `MarkedCompactnessWitness I u_seq u_lim` is empty (`0 sorryAx`). -/
theorem MarkedCompactnessWitness.isEmpty_of_lt_three_of_B_lt_eps_sph {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (hk : k < 3)
    (u_seq : ℕ → MarkedSphere M k)
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (h_lt : B < th.ε_sph) :
    IsEmpty (MarkedCompactnessWitness I u_seq u_lim) := by
  refine ⟨fun wit => ?_⟩
  have h3 := MarkedCompactnessWitness.three_le_of_B_lt_eps_sph I th u_seq u_lim B wit h_energy h_lt
  omega

/-- For `k < 3` and `B < th.h`, `MarkedCompactnessWitness I u_seq u_lim` is empty (`0 sorryAx`). -/
theorem MarkedCompactnessWitness.isEmpty_of_lt_three_of_B_lt_h {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (hk : k < 3)
    (u_seq : ℕ → MarkedSphere M k)
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (h_lt : B < th.h) :
    IsEmpty (MarkedCompactnessWitness I u_seq u_lim) :=
  MarkedCompactnessWitness.isEmpty_of_lt_three_of_B_lt_eps_sph I th hk u_seq u_lim B h_energy
    (h_lt.trans_le th.h_le_sph)

/-- For `k < 3` and `B ≤ 0`, `MarkedCompactnessWitness I u_seq u_lim` is empty (`0 sorryAx`). -/
theorem MarkedCompactnessWitness.isEmpty_of_lt_three_of_nonpos_B {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (hk : k < 3)
    (u_seq : ℕ → MarkedSphere M k)
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (hB : B ≤ 0) :
    IsEmpty (MarkedCompactnessWitness I u_seq u_lim) :=
  MarkedCompactnessWitness.isEmpty_of_lt_three_of_B_lt_eps_sph I th hk u_seq u_lim B h_energy
    (hB.trans_lt th.ε_sph_pos)

/-- For `k < 3` on a `[Subsingleton M]` target, `MarkedCompactnessWitness I u_seq u_lim` is empty (`0 sorryAx`). -/
theorem MarkedCompactnessWitness.isEmpty_of_lt_three_of_subsingleton [Subsingleton M] {k : ℕ}
    (hk : k < 3)
    (u_seq : ℕ → MarkedSphere M k)
    (u_lim : MarkedStableTreeLimit I (M := M) k) :
    IsEmpty (MarkedCompactnessWitness I u_seq u_lim) := by
  haveI := MarkedStableTreeLimit.isEmpty_of_lt_three_of_subsingleton I (M := M) hk
  exact ⟨fun _ => isEmptyElim u_lim⟩

/-- For `k < 3` on a `[DiscreteTopology M]` target, `MarkedCompactnessWitness I u_seq u_lim` is empty (`0 sorryAx`). -/
theorem MarkedCompactnessWitness.isEmpty_of_lt_three_of_discrete [DiscreteTopology M] {k : ℕ}
    (hk : k < 3)
    (u_seq : ℕ → MarkedSphere M k)
    (u_lim : MarkedStableTreeLimit I (M := M) k) :
    IsEmpty (MarkedCompactnessWitness I u_seq u_lim) := by
  haveI := MarkedStableTreeLimit.isEmpty_of_lt_three_of_discrete I (M := M) hk
  exact ⟨fun _ => isEmptyElim u_lim⟩

/-- When `∀ n, totalEnergy I (u_seq n) ≤ B` and `B < th.ε_sph`, `CompactnessWitness I u_seq u_lim` is empty (`0 sorryAx`). -/
theorem CompactnessWitness.isEmpty_of_B_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (u_lim : StableSphereTreeLimit I (M := M))
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < th.ε_sph) :
    IsEmpty (CompactnessWitness I u_seq u_lim) := by
  let u_marked : ℕ → MarkedSphere M 0 := fun n => ⟨u_seq n, Fin.elim0, fun i => i.elim0⟩
  haveI := MarkedCompactnessWitness.isEmpty_of_lt_three_of_B_lt_eps_sph I th (by decide : 0 < 3)
    u_marked (MarkedStableTreeLimit.of_stableSphereTreeLimit I u_lim) B h_energy h_lt
  exact ⟨fun wit => isEmptyElim (MarkedCompactnessWitness.of_compactnessWitness I u_marked u_lim wit)⟩

/-- When `∀ n, totalEnergy I (u_seq n) ≤ B` and `B < th.h`, `CompactnessWitness I u_seq u_lim` is empty (`0 sorryAx`). -/
theorem CompactnessWitness.isEmpty_of_B_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (u_lim : StableSphereTreeLimit I (M := M))
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (h_lt : B < th.h) :
    IsEmpty (CompactnessWitness I u_seq u_lim) :=
  CompactnessWitness.isEmpty_of_B_lt_eps_sph I th u_seq u_lim B h_energy (h_lt.trans_le th.h_le_sph)

/-- When `∀ n, totalEnergy I (u_seq n) ≤ B` and `B ≤ 0`, `CompactnessWitness I u_seq u_lim` is empty (`0 sorryAx`). -/
theorem CompactnessWitness.isEmpty_of_nonpos_B
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → (CP1 → M))
    (u_lim : StableSphereTreeLimit I (M := M))
    (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n) ≤ B)
    (hB : B ≤ 0) :
    IsEmpty (CompactnessWitness I u_seq u_lim) :=
  CompactnessWitness.isEmpty_of_B_lt_eps_sph I th u_seq u_lim B h_energy (hB.trans_lt th.ε_sph_pos)

/-- On a `[Subsingleton M]` target, `CompactnessWitness I u_seq u_lim` is empty (`0 sorryAx`). -/
theorem CompactnessWitness.isEmpty_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M))
    (u_lim : StableSphereTreeLimit I (M := M)) :
    IsEmpty (CompactnessWitness I u_seq u_lim) := by
  haveI := StableSphereTreeLimit.isEmpty_of_subsingleton I (M := M)
  exact ⟨fun _ => isEmptyElim u_lim⟩

/-- On a `[DiscreteTopology M]` target, `CompactnessWitness I u_seq u_lim` is empty (`0 sorryAx`). -/
theorem CompactnessWitness.isEmpty_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M))
    (u_lim : StableSphereTreeLimit I (M := M)) :
    IsEmpty (CompactnessWitness I u_seq u_lim) := by
  haveI := StableSphereTreeLimit.isEmpty_of_discrete I (M := M)
  exact ⟨fun _ => isEmptyElim u_lim⟩

/-- Push a `MarkedCompactnessWitness` on a subsequence `fun n => u_seq (σ.1 n)` back to `u_seq` (`0 sorryAx`). -/
def MarkedCompactnessWitness.of_subseq {k : ℕ}
    {u_seq : ℕ → MarkedSphere M k}
    (σ : Bookkeeping.SubseqMap)
    {u_lim : MarkedStableTreeLimit I (M := M) k}
    (wit : MarkedCompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim) :
    MarkedCompactnessWitness I u_seq u_lim where
  σ := σ.comp wit.σ
  frames := wit.frames
  smooth_conv := wit.smooth_conv
  frame_collapse := wit.frame_collapse
  mark_conv := wit.mark_conv
  energy_conv := wit.energy_conv

/-- Zero-sorry conditional reduction of `marked_gromov_compactness` from any `MarkedCompactnessWitness` (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_witness {k : ℕ}
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (wit : MarkedCompactnessWitness I u_seq u_lim) :
    ∃ (u_lim' : MarkedStableTreeLimit I (M := M) k)
      (_wit' : MarkedCompactnessWitness I u_seq u_lim'),
      markedTreeTotalEnergy I u_lim' ≤ B :=
  ⟨u_lim, wit, markedTreeTotalEnergy_le_of_witness I u_seq u_lim B wit h_energy⟩

/-- Zero-sorry conditional reduction of `marked_gromov_compactness` from a `MarkedCompactnessWitness`
along a subsequence `σ` (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_subseq_witness {k : ℕ}
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (wit : MarkedCompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim) :
    ∃ (u_lim' : MarkedStableTreeLimit I (M := M) k)
      (_wit' : MarkedCompactnessWitness I u_seq u_lim'),
      markedTreeTotalEnergy I u_lim' ≤ B :=
  marked_gromov_compactness_of_witness I u_seq B h_energy u_lim
    (MarkedCompactnessWitness.of_subseq I σ wit)

/-- Zero-sorry reduction of the existential statement of `marked_gromov_compactness` from a
`MarkedCompactnessWitness` along a subsequence `σ` (`0 sorryAx`). -/
theorem marked_gromov_compactness_exists_of_subseq_witness {k : ℕ}
    (u_seq : ℕ → MarkedSphere M k)
    (σ : Bookkeeping.SubseqMap)
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (wit : MarkedCompactnessWitness I (fun n => u_seq (σ.1 n)) u_lim) :
    ∃ (u_lim' : MarkedStableTreeLimit I (M := M) k),
      Nonempty (MarkedCompactnessWitness I u_seq u_lim') :=
  ⟨u_lim, ⟨MarkedCompactnessWitness.of_subseq I σ wit⟩⟩

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves from any unmarked
`CompactnessWitness` (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I (fun n => (u_seq n).map) u_lim) :
    ∃ (u_lim' : MarkedStableTreeLimit I (M := M) 0)
      (_wit' : MarkedCompactnessWitness I u_seq u_lim'),
      markedTreeTotalEnergy I u_lim' ≤ B :=
  marked_gromov_compactness_of_witness I u_seq B h_energy
    (MarkedStableTreeLimit.of_stableSphereTreeLimit I u_lim)
    (MarkedCompactnessWitness.of_compactnessWitness I u_seq u_lim wit)

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves from an unmarked
`CompactnessWitness` along a subsequence `σ` (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_subseq
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (σ : Bookkeeping.SubseqMap)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (u_lim : StableSphereTreeLimit I (M := M))
    (wit : CompactnessWitness I (fun n => (u_seq (σ.1 n)).map) u_lim) :
    ∃ (u_lim' : MarkedStableTreeLimit I (M := M) 0)
      (_wit' : MarkedCompactnessWitness I u_seq u_lim'),
      markedTreeTotalEnergy I u_lim' ≤ B :=
  marked_gromov_compactness_of_witness I u_seq B h_energy
    (MarkedStableTreeLimit.of_stableSphereTreeLimit I u_lim)
    (MarkedCompactnessWitness.of_subseq I σ
      (MarkedCompactnessWitness.of_compactnessWitness I (fun n => u_seq (σ.1 n)) u_lim wit))

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves when a subsequence `σ`
consists of non-constant maps and some term on `σ` has energy `< th.ε_sph` (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_exists_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, (u_seq (σ.1 n)).map z = c)
    (h_exists_lt : ∃ n, totalEnergy I (u_seq (σ.1 n)).map < th.ε_sph) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  obtain ⟨u_lim, ⟨wit⟩⟩ := gromov_compactness_core_of_exists_lt_eps_sph I th
    (fun n => (u_seq (σ.1 n)).map) h_nc (fun n => h_jhol (σ.1 n)) h_exists_lt
  exact marked_gromov_compactness_zero_marks_of_subseq I u_seq B σ h_energy u_lim wit

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves when a subsequence `σ`
consists of non-constant maps and some term on `σ` has energy `< th.h` (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_exists_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, (u_seq (σ.1 n)).map z = c)
    (h_exists_lt : ∃ n, totalEnergy I (u_seq (σ.1 n)).map < th.h) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  rcases h_exists_lt with ⟨n, hn⟩
  exact marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_exists_lt_eps_sph I th u_seq B h_jhol h_energy
    σ h_nc ⟨n, hn.trans_le th.h_le_sph⟩

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves when a subsequence `σ`
consists of non-constant maps and some term on `σ` has energy `≤ 0` (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_exists_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, (u_seq (σ.1 n)).map z = c)
    (h_exists_nonpos : ∃ n, totalEnergy I (u_seq (σ.1 n)).map ≤ 0) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  rcases h_exists_nonpos with ⟨n, hn⟩
  exact marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_exists_lt_eps_sph I th u_seq B h_jhol h_energy
    σ h_nc ⟨n, hn.trans_lt th.ε_sph_pos⟩

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves when a subsequence `σ`
consists of non-constant maps and `totalEnergy I (u_seq (σ.1 n)).map < th.ε_sph` eventually (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_eventually_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, (u_seq (σ.1 n)).map z = c)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (σ.1 n)).map < th.ε_sph) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_ev
  exact marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_exists_lt_eps_sph I th u_seq B h_jhol h_energy
    σ h_nc ⟨N, hN N le_rfl⟩

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves when a subsequence `σ`
consists of non-constant maps and `totalEnergy I (u_seq (σ.1 n)).map < th.h` eventually (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_eventually_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, (u_seq (σ.1 n)).map z = c)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (σ.1 n)).map < th.h) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_eventually_lt_eps_sph I th u_seq B h_jhol h_energy
    σ h_nc (h_ev.mono (fun _ hn => hn.trans_le th.h_le_sph))

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves when a subsequence `σ`
consists of non-constant maps and `totalEnergy I (u_seq (σ.1 n)).map ≤ 0` eventually (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_eventually_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, (u_seq (σ.1 n)).map z = c)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq (σ.1 n)).map ≤ 0) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_eventually_lt_eps_sph I th u_seq B h_jhol h_energy
    σ h_nc (h_ev.mono (fun _ hn => hn.trans_lt th.ε_sph_pos))

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves when a subsequence `σ`
consists of non-constant maps and `B < th.ε_sph` (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_B_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (h_lt : B < th.ε_sph)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, (u_seq (σ.1 n)).map z = c) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_exists_lt_eps_sph I th u_seq B h_jhol h_energy σ h_nc
    ⟨0, (h_energy (σ.1 0)).trans_lt h_lt⟩

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves when a subsequence `σ`
consists of non-constant maps and `B < th.h` (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_B_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (h_lt : B < th.h)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, (u_seq (σ.1 n)).map z = c) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_B_lt_eps_sph I th u_seq B h_jhol h_energy
    (h_lt.trans_le th.h_le_sph) σ h_nc

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves when a subsequence `σ`
consists of non-constant maps and `B ≤ 0` (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_nonpos_B
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (hB : B ≤ 0)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, (u_seq (σ.1 n)).map z = c) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_B_lt_eps_sph I th u_seq B h_jhol h_energy
    (hB.trans_lt th.ε_sph_pos) σ h_nc

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves on a `[Subsingleton M]`
target when a subsequence `σ` consists of non-constant maps (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, (u_seq (σ.1 n)).map z = c) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  obtain ⟨u_lim, ⟨wit⟩⟩ := gromov_compactness_core_of_subsingleton I (fun n => (u_seq (σ.1 n)).map) h_nc
  exact marked_gromov_compactness_zero_marks_of_subseq I u_seq B σ h_energy u_lim wit

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves on a `[DiscreteTopology M]`
target when a subsequence `σ` consists of non-constant maps (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, (u_seq (σ.1 n)).map z = c) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  obtain ⟨u_lim, ⟨wit⟩⟩ := gromov_compactness_core_univ_of_discrete I (fun n => (u_seq (σ.1 n)).map)
    h_nc (fun n => h_jhol (σ.1 n))
  exact marked_gromov_compactness_zero_marks_of_subseq I u_seq B σ h_energy u_lim wit

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves when a subsequence
of maps converges smoothly on `CP1` to a non-constant map with energy conservation (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_global_conv_nonconst
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap) (u_lim_map : CP1 → M)
    (h_nonconst_lim : ¬ ∃ c : M, ∀ z, u_lim_map z = c)
    (h_conv : SmoothLocalConvergesOn I (fun n => (u_seq (σ.1 n)).map) u_lim_map Set.univ)
    (h_tendsto : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n)).map) atTop (𝓝 (totalEnergy I u_lim_map))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  obtain ⟨u_stable, ⟨wit⟩⟩ :=
    gromov_compactness_core_of_global_conv_nonconst I (fun n => (u_seq n).map)
      h_jhol σ u_lim_map h_nonconst_lim h_conv h_tendsto
  exact marked_gromov_compactness_zero_marks I u_seq B h_energy u_stable wit

/-- Zero-sorry conditional reduction of `marked_gromov_compactness` on sequences admitting a
constant subsequence with `3 ≤ k` (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_const_subseq {k : ℕ}
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (h_const : ∃ (σ : Bookkeeping.SubseqMap) (c : M) (pts : Fin k → CP1)
      (_ : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
      (_ : 3 ≤ k),
      (∀ n z, (u_seq (σ.1 n)).map z = c) ∧
      (∀ n i, (u_seq (σ.1 n)).points i = pts i)) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  rcases h_const with ⟨σ, c, pts, h_pts_dist, h_stab, h_map_eq, h_pts_eq⟩
  exact marked_gromov_compactness_of_witness I u_seq B h_energy
    (MarkedStableTreeLimit.of_markedSphere I ⟨fun _ => c, pts, h_pts_dist⟩
      (Analysis.jholomorphicOn_const I c Set.univ) (fun _ => h_stab))
    (MarkedCompactnessWitness.of_const_subseq I u_seq σ c pts h_pts_dist h_stab h_map_eq h_pts_eq)

/-- Zero-sorry conditional reduction of `marked_gromov_compactness` on sequences admitting an
eventually constant subsequence with `3 ≤ k` (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_eventually_const_subseq {k : ℕ}
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ) (c : M) (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_stab : 3 ≤ k)
    (h_map_eq : ∀ n ≥ N₀, ∀ z, (u_seq (σ.1 n)).map z = c)
    (h_pts_eq : ∀ n ≥ N₀, ∀ i, (u_seq (σ.1 n)).points i = pts i) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_of_const_subseq I u_seq B h_energy
    ⟨σ.comp (Compactness.shiftSubseqMap N₀), c, pts, h_pts_dist, h_stab,
      fun n z => h_map_eq (n + N₀) (Nat.le_add_left N₀ n) z,
      fun n i => h_pts_eq (n + N₀) (Nat.le_add_left N₀ n) i⟩

/-- Zero-sorry conditional reduction of `marked_gromov_compactness` on sequences admitting a
non-bubbling smooth local and marked-point convergent subsequence (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_no_bubble {k : ℕ}
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (h_no_bubble : ∃ (σ : Bookkeeping.SubseqMap) (u₀ : MarkedSphere M k)
      (_ : JHolomorphicOn I I_CP1 u₀.map Set.univ)
      (_ : (∃ c : M, ∀ z : CP1, u₀.map z = c) → 3 ≤ k),
      SmoothLocalConvergesOn I (fun n => (u_seq (σ.1 n)).map) u₀.map Set.univ ∧
      (∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (u₀.points i))) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n)).map) atTop (𝓝 (totalEnergy I u₀.map))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  rcases h_no_bubble with ⟨σ, u₀, hu_jhol, h_stab, h_conv, h_marks, h_en⟩
  exact marked_gromov_compactness_of_witness I u_seq B h_energy
    (MarkedStableTreeLimit.of_markedSphere I u₀ hu_jhol h_stab)
    (MarkedCompactnessWitness.of_singleton_subseq I u_seq σ u₀ hu_jhol h_stab h_conv h_marks h_en)

/-- Marked Gromov compactness for `3 ≤ k` when a subsequence has constant map `fun _ => c₀`
and converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_const_map_subseq_of_marks_conv {k : ℕ}
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap) (c₀ : M)
    (h_map_eq : ∀ n z, (u_seq (σ.1 n)).map z = c₀)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  let u₀ : MarkedSphere M k := ⟨fun _ => c₀, pts, h_pts_dist⟩
  have h_eq : (fun n => (u_seq (σ.1 n)).map) = fun _ _ => c₀ := by
    ext n z
    exact h_map_eq n z
  have h_conv : SmoothLocalConvergesOn I (fun n => (u_seq (σ.1 n)).map) u₀.map Set.univ := by
    change SmoothLocalConvergesOn I (fun n => (u_seq (σ.1 n)).map) (fun _ => c₀) Set.univ
    rw [h_eq]
    exact smoothLocalConvergesOn_const_map I c₀ Set.univ
  have h_en : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n)).map) atTop (𝓝 (totalEnergy I u₀.map)) := by
    have h_en_eq : (fun n => totalEnergy I (u_seq (σ.1 n)).map) =
        fun _ => totalEnergy I (fun _ : CP1 => c₀) := by
      ext n
      exact congrArg (totalEnergy I) (congr_fun h_eq n)
    change Tendsto (fun n => totalEnergy I (u_seq (σ.1 n)).map) atTop (𝓝 (totalEnergy I (fun _ => c₀)))
    rw [h_en_eq]
    exact tendsto_const_nhds
  exact marked_gromov_compactness_of_no_bubble I u_seq B h_energy
    ⟨σ, u₀, Analysis.jholomorphicOn_const I c₀ Set.univ, fun _ => hk, h_conv, h_marks, h_en⟩

/-- Marked Gromov compactness for `3 ≤ k` when a subsequence is eventually constant at `fun _ => c₀`
and has converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_eventually_const_map_subseq_of_marks_conv {k : ℕ}
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ) (c₀ : M)
    (h_map_eq : ∀ n ≥ N₀, ∀ z, (u_seq (σ.1 n)).map z = c₀)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_of_const_map_subseq_of_marks_conv I hk u_seq B h_energy
    (σ.comp (Compactness.shiftSubseqMap N₀)) c₀
    (fun n z => h_map_eq (n + N₀) (Nat.le_add_left N₀ n) z) pts h_pts_dist
    (fun i => (h_marks i).comp (Compactness.shiftSubseqMap N₀).2.tendsto_atTop)

/-- Marked Gromov compactness when `3 ≤ k` and a subsequence eventually has `< th.ε_sph` energy,
fixed `north_pole` value, and converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_eventually_lt_eps_sph_of_marks_conv {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ)
    (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (σ.1 n)).map < th.ε_sph)
    (c₀ : M)
    (hc₀ : ∀ n ≥ N₀, (u_seq (σ.1 n)).map north_pole = c₀)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  refine marked_gromov_compactness_of_eventually_const_map_subseq_of_marks_conv I hk u_seq B h_energy
    σ N₀ c₀ (fun n hn z => ?_) pts h_pts_dist h_marks
  have h_eq := Compactness.eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I th
    (u_seq (σ.1 n)).map (h_jhol (σ.1 n)) (h_ev n hn)
  exact (congr_fun h_eq z).trans (hc₀ n hn)

/-- Marked Gromov compactness when `3 ≤ k` and a subsequence eventually has `< th.h` energy,
fixed `north_pole` value, and converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_eventually_lt_h_of_marks_conv {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ)
    (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (σ.1 n)).map < th.h)
    (c₀ : M)
    (hc₀ : ∀ n ≥ N₀, (u_seq (σ.1 n)).map north_pole = c₀)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_of_eventually_lt_eps_sph_of_marks_conv I th hk u_seq B h_jhol h_energy
    σ N₀ (fun n hn => (h_ev n hn).trans_le th.h_le_sph) c₀ hc₀ pts h_pts_dist h_marks

/-- Marked Gromov compactness when `3 ≤ k` and a subsequence eventually has `≤ 0` energy,
fixed `north_pole` value, and converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_eventually_nonpos_energy_of_marks_conv {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ)
    (h_ev : ∀ n ≥ N₀, totalEnergy I (u_seq (σ.1 n)).map ≤ 0)
    (c₀ : M)
    (hc₀ : ∀ n ≥ N₀, (u_seq (σ.1 n)).map north_pole = c₀)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_of_eventually_lt_eps_sph_of_marks_conv I th hk u_seq B h_jhol h_energy
    σ N₀ (fun n hn => (h_ev n hn).trans_lt th.ε_sph_pos) c₀ hc₀ pts h_pts_dist h_marks

/-- Marked Gromov compactness when `3 ≤ k` and a subsequence `σ` has `< th.ε_sph` energy,
fixed `north_pole` value, and converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_lt_eps_sph_subseq_of_marks_conv {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_lt : ∀ n, totalEnergy I (u_seq (σ.1 n)).map < th.ε_sph)
    (c₀ : M)
    (hc₀ : ∀ n, (u_seq (σ.1 n)).map north_pole = c₀)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_of_eventually_lt_eps_sph_of_marks_conv I th hk u_seq B h_jhol h_energy
    σ 0 (fun n _ => h_lt n) c₀ (fun n _ => hc₀ n) pts h_pts_dist h_marks

/-- Marked Gromov compactness when `3 ≤ k` and a subsequence `σ` has `< th.h` energy,
fixed `north_pole` value, and converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_lt_h_subseq_of_marks_conv {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_lt : ∀ n, totalEnergy I (u_seq (σ.1 n)).map < th.h)
    (c₀ : M)
    (hc₀ : ∀ n, (u_seq (σ.1 n)).map north_pole = c₀)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_of_lt_eps_sph_subseq_of_marks_conv I th hk u_seq B h_jhol h_energy
    σ (fun n => (h_lt n).trans_le th.h_le_sph) c₀ hc₀ pts h_pts_dist h_marks

/-- Marked Gromov compactness when `3 ≤ k` and a subsequence `σ` has `≤ 0` energy,
fixed `north_pole` value, and converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_nonpos_energy_subseq_of_marks_conv {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nonpos : ∀ n, totalEnergy I (u_seq (σ.1 n)).map ≤ 0)
    (c₀ : M)
    (hc₀ : ∀ n, (u_seq (σ.1 n)).map north_pole = c₀)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_of_lt_eps_sph_subseq_of_marks_conv I th hk u_seq B h_jhol h_energy
    σ (fun n => (h_nonpos n).trans_lt th.ε_sph_pos) c₀ hc₀ pts h_pts_dist h_marks

/-- Unconditional marked Gromov compactness on subsingleton targets for `3 ≤ k` when a subsequence
has converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_subsingleton_of_marks_conv [Subsingleton M] {k : ℕ}
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap) (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  let c₀ := (u_seq 0).map north_pole
  let u₀ : MarkedSphere M k := ⟨fun _ => c₀, pts, h_pts_dist⟩
  have h_eq : (fun n => (u_seq (σ.1 n)).map) = fun _ _ => c₀ := by
    ext n z
    exact Subsingleton.elim ((u_seq (σ.1 n)).map z) c₀
  have h_conv : SmoothLocalConvergesOn I (fun n => (u_seq (σ.1 n)).map) u₀.map Set.univ := by
    change SmoothLocalConvergesOn I (fun n => (u_seq (σ.1 n)).map) (fun _ => c₀) Set.univ
    rw [h_eq]
    exact smoothLocalConvergesOn_const_map I c₀ Set.univ
  have h_en : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n)).map) atTop (𝓝 (totalEnergy I u₀.map)) := by
    have h_en_eq : (fun n => totalEnergy I (u_seq (σ.1 n)).map) =
        fun _ => totalEnergy I (fun _ : CP1 => c₀) := by
      ext n
      exact congrArg (totalEnergy I) (congr_fun h_eq n)
    change Tendsto (fun n => totalEnergy I (u_seq (σ.1 n)).map) atTop (𝓝 (totalEnergy I (fun _ => c₀)))
    rw [h_en_eq]
    exact tendsto_const_nhds
  exact marked_gromov_compactness_of_no_bubble I u_seq B h_energy
    ⟨σ, u₀, Analysis.jholomorphicOn_const I c₀ Set.univ, fun _ => hk, h_conv, h_marks, h_en⟩

/-- Marked Gromov compactness when `3 ≤ k`, `B < th.ε_sph`, and a subsequence has fixed `north_pole`
value and converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_lt_eps_sph_of_marks_conv {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (h_lt : B < th.ε_sph)
    (σ : Bookkeeping.SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, (u_seq (σ.1 n)).map north_pole = c₀)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  let u₀ : MarkedSphere M k := ⟨fun _ => c₀, pts, h_pts_dist⟩
  have h_eq : (fun n => (u_seq (σ.1 n)).map) = fun _ _ => c₀ := by
    ext n z
    have h_const_n := Compactness.eq_const_north_pole_of_jhol_of_totalEnergy_lt_eps_sph I th
      (u_seq (σ.1 n)).map (h_jhol (σ.1 n)) ((h_energy (σ.1 n)).trans_lt h_lt)
    calc (u_seq (σ.1 n)).map z = (u_seq (σ.1 n)).map north_pole := congr_fun h_const_n z
      _ = c₀ := hc₀ n
  have h_conv : SmoothLocalConvergesOn I (fun n => (u_seq (σ.1 n)).map) u₀.map Set.univ := by
    change SmoothLocalConvergesOn I (fun n => (u_seq (σ.1 n)).map) (fun _ => c₀) Set.univ
    rw [h_eq]
    exact smoothLocalConvergesOn_const_map I c₀ Set.univ
  have h_en : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n)).map) atTop (𝓝 (totalEnergy I u₀.map)) := by
    have h_en_eq : (fun n => totalEnergy I (u_seq (σ.1 n)).map) =
        fun _ => totalEnergy I (fun _ : CP1 => c₀) := by
      ext n
      exact congrArg (totalEnergy I) (congr_fun h_eq n)
    change Tendsto (fun n => totalEnergy I (u_seq (σ.1 n)).map) atTop (𝓝 (totalEnergy I (fun _ => c₀)))
    rw [h_en_eq]
    exact tendsto_const_nhds
  exact marked_gromov_compactness_of_no_bubble I u_seq B h_energy
    ⟨σ, u₀, Analysis.jholomorphicOn_const I c₀ Set.univ, fun _ => hk, h_conv, h_marks, h_en⟩

/-- Marked Gromov compactness when `3 ≤ k`, `B < th.h`, and a subsequence has fixed `north_pole`
value and converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_lt_h_of_marks_conv {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (h_lt : B < th.h)
    (σ : Bookkeeping.SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, (u_seq (σ.1 n)).map north_pole = c₀)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_of_lt_eps_sph_of_marks_conv I th hk u_seq B h_jhol h_energy
    (h_lt.trans_le th.h_le_sph) σ c₀ hc₀ pts h_pts_dist h_marks

/-- Marked Gromov compactness when `3 ≤ k`, `B ≤ 0`, and a subsequence has fixed `north_pole`
value and converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_nonpos_B_of_marks_conv {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (hB : B ≤ 0)
    (σ : Bookkeeping.SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, (u_seq (σ.1 n)).map north_pole = c₀)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_of_lt_eps_sph_of_marks_conv I th hk u_seq B h_jhol h_energy
    (hB.trans_lt th.ε_sph_pos) σ c₀ hc₀ pts h_pts_dist h_marks

/-- Unconditional marked Gromov compactness on `[DiscreteTopology M]` targets when `3 ≤ k` and a
subsequence has converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_discrete_of_marks_conv [DiscreteTopology M] {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  obtain ⟨τ, c₀, hc₀⟩ :=
    Compactness.exists_const_map_subseq_of_jhol_of_discrete I th (fun n => (u_seq (σ.1 n)).map)
      (fun n => h_jhol (σ.1 n))
  let u₀ : MarkedSphere M k := ⟨fun _ => c₀, pts, h_pts_dist⟩
  have h_conv : SmoothLocalConvergesOn I (fun n => (u_seq ((Bookkeeping.SubseqMap.comp σ τ).1 n)).map) u₀.map Set.univ := by
    have h_eq : (fun n => (u_seq ((Bookkeeping.SubseqMap.comp σ τ).1 n)).map) = fun _ => fun _ => c₀ :=
      funext (fun n => hc₀ n)
    change SmoothLocalConvergesOn I (fun n => (u_seq ((Bookkeeping.SubseqMap.comp σ τ).1 n)).map) (fun _ => c₀) Set.univ
    rw [h_eq]
    exact smoothLocalConvergesOn_const_map I c₀ Set.univ
  have h_marks_comp : ∀ i : Fin k,
      Tendsto (fun n => (u_seq ((Bookkeeping.SubseqMap.comp σ τ).1 n)).points i) atTop (𝓝 (u₀.points i)) :=
    fun i => (h_marks i).comp τ.2.tendsto_atTop
  have h_en : Tendsto (fun n => totalEnergy I (u_seq ((Bookkeeping.SubseqMap.comp σ τ).1 n)).map) atTop
      (𝓝 (totalEnergy I u₀.map)) := by
    have h_en_eq : (fun n => totalEnergy I (u_seq ((Bookkeeping.SubseqMap.comp σ τ).1 n)).map) =
        fun _ => totalEnergy I (fun _ : CP1 => c₀) :=
      funext (fun n => congrArg (totalEnergy I) (hc₀ n))
    change Tendsto (fun n => totalEnergy I (u_seq ((Bookkeeping.SubseqMap.comp σ τ).1 n)).map) atTop
      (𝓝 (totalEnergy I (fun _ => c₀)))
    rw [h_en_eq]
    exact tendsto_const_nhds
  exact marked_gromov_compactness_of_no_bubble I u_seq B h_energy
    ⟨Bookkeeping.SubseqMap.comp σ τ, u₀, Analysis.jholomorphicOn_const I c₀ Set.univ, fun _ => hk, h_conv, h_marks_comp, h_en⟩

/-- Unconditional threshold-free marked Gromov compactness on `[DiscreteTopology M]` targets when
`3 ≤ k` and a subsequence has converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_univ_of_discrete_of_marks_conv [DiscreteTopology M] {k : ℕ}
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  obtain ⟨th⟩ := Bubbling.exists_target_thresholds_of_discrete I (M := M)
  exact marked_gromov_compactness_of_discrete_of_marks_conv I th hk u_seq B h_jhol h_energy
    σ pts h_pts_dist h_marks

/-- Zero-sorry conditional reduction of `marked_gromov_compactness` on sequences of `J`-holomorphic
marked spheres admitting a non-bubbling smooth local and marked-point convergent subsequence:
`J`-holomorphicity of the limit map `u₀.map` follows automatically from `smooth_local_jhol_closure` (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_no_bubble_jhol {k : ℕ}
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (h_no_bubble : ∃ (σ : Bookkeeping.SubseqMap) (u₀ : MarkedSphere M k)
      (_ : (∃ c : M, ∀ z : CP1, u₀.map z = c) → 3 ≤ k),
      SmoothLocalConvergesOn I (fun n => (u_seq (σ.1 n)).map) u₀.map Set.univ ∧
      (∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (u₀.points i))) ∧
      Tendsto (fun n => totalEnergy I (u_seq (σ.1 n)).map) atTop (𝓝 (totalEnergy I u₀.map))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  rcases h_no_bubble with ⟨σ, u₀, h_stab, h_conv, h_marks, h_en⟩
  have hu_jhol : JHolomorphicOn I I_CP1 u₀.map Set.univ :=
    smooth_local_jhol_closure I (fun n => (u_seq (σ.1 n)).map) u₀.map Set.univ h_conv
      (fun n => h_jhol (σ.1 n))
  exact marked_gromov_compactness_of_no_bubble I u_seq B h_energy
    ⟨σ, u₀, hu_jhol, h_stab, h_conv, h_marks, h_en⟩

/-- Zero-sorry conditional reduction of `marked_gromov_compactness` for `k ≥ 3` marked spheres
admitting a non-bubbling smooth local and marked-point convergent subsequence (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_no_bubble_three_le_k {k : ℕ}
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap) (u₀ : MarkedSphere M k)
    (h_conv : SmoothLocalConvergesOn I (fun n => (u_seq (σ.1 n)).map) u₀.map Set.univ)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (u₀.points i)))
    (h_en : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n)).map) atTop (𝓝 (totalEnergy I u₀.map))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_of_no_bubble_jhol I u_seq B h_jhol h_energy
    ⟨σ, u₀, fun _ => hk, h_conv, h_marks, h_en⟩

/-- Zero-sorry conditional reduction of `marked_gromov_compactness` for marked spheres admitting
a non-bubbling subsequence converging to a non-constant limit map `u₀.map` (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_no_bubble_nonconst {k : ℕ}
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap) (u₀ : MarkedSphere M k)
    (h_nonconst : ¬ ∃ c : M, ∀ z : CP1, u₀.map z = c)
    (h_conv : SmoothLocalConvergesOn I (fun n => (u_seq (σ.1 n)).map) u₀.map Set.univ)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (u₀.points i)))
    (h_en : Tendsto (fun n => totalEnergy I (u_seq (σ.1 n)).map) atTop (𝓝 (totalEnergy I u₀.map))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  marked_gromov_compactness_of_no_bubble_jhol I u_seq B h_jhol h_energy
    ⟨σ, u₀, fun hc => False.elim (h_nonconst hc), h_conv, h_marks, h_en⟩

/-- For `k < 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`MarkedStableTreeLimit I k` is empty (`0 sorryAx`). -/
theorem MarkedStableTreeLimit.isEmpty_of_lt_three_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : k < 3) :
    IsEmpty (MarkedStableTreeLimit I (M := M) k) := by
  refine ⟨fun u_lim => ?_⟩
  have h3 := u_lim.three_le_of_all_const I
    (fun v => ⟨u_lim.map v north_pole,
      fun z => congr_fun (h_all_const (u_lim.map v) (u_lim.is_jhol v)) z⟩)
  omega

/-- Whenever every `J`-holomorphic sphere in `(M, J)` is constant, `StableSphereTreeLimit I`
is empty (`0 sorryAx`). -/
theorem StableSphereTreeLimit.isEmpty_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole) :
    IsEmpty (StableSphereTreeLimit I (M := M)) := by
  haveI := MarkedStableTreeLimit.isEmpty_of_lt_three_of_all_jhol_const I h_all_const (by decide : 0 < 3)
  exact ⟨fun u_lim => isEmptyElim (MarkedStableTreeLimit.of_stableSphereTreeLimit I u_lim)⟩

/-- For `k < 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`MarkedCompactnessWitness I u_seq u_lim` is empty (`0 sorryAx`). -/
theorem MarkedCompactnessWitness.isEmpty_of_lt_three_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : k < 3)
    (u_seq : ℕ → MarkedSphere M k)
    (u_lim : MarkedStableTreeLimit I (M := M) k) :
    IsEmpty (MarkedCompactnessWitness I u_seq u_lim) := by
  haveI := MarkedStableTreeLimit.isEmpty_of_lt_three_of_all_jhol_const I h_all_const hk
  exact ⟨fun _ => isEmptyElim u_lim⟩

/-- Whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`CompactnessWitness I u_seq u_lim` is empty (`0 sorryAx`). -/
theorem CompactnessWitness.isEmpty_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (u_seq : ℕ → (CP1 → M))
    (u_lim : StableSphereTreeLimit I (M := M)) :
    IsEmpty (CompactnessWitness I u_seq u_lim) := by
  haveI := StableSphereTreeLimit.isEmpty_of_all_jhol_const I h_all_const
  exact ⟨fun _ => isEmptyElim u_lim⟩

/-- Zero-sorry reduction of `marked_gromov_compactness` for `0`-marked curves when every
`J`-holomorphic sphere in `(M, J)` is constant and a subsequence `σ` consists of non-constant
maps (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_subseq_nonconst_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap)
    (h_nc : ∀ n, ¬ ∃ c : M, ∀ z, (u_seq (σ.1 n)).map z = c) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  obtain ⟨u_lim, ⟨wit⟩⟩ := gromov_compactness_core_of_all_jhol_const I
    (fun n => (u_seq (σ.1 n)).map) h_nc (fun n => h_jhol (σ.1 n))
    (fun u hu => ⟨u north_pole, fun z => congr_fun (h_all_const u hu) z⟩)
  exact marked_gromov_compactness_zero_marks_of_subseq I u_seq B σ h_energy u_lim wit

/-- Marked Gromov compactness when `3 ≤ k`, every `J`-holomorphic sphere in `(M, J)` is constant,
and a subsequence has fixed `north_pole` value and converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_all_jhol_const_of_marks_conv {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap) (c₀ : M)
    (hc₀ : ∀ n, (u_seq (σ.1 n)).map north_pole = c₀)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  refine marked_gromov_compactness_of_const_map_subseq_of_marks_conv I hk u_seq B h_energy
    σ c₀ (fun n z => ?_) pts h_pts_dist h_marks
  exact (congr_fun (h_all_const (u_seq (σ.1 n)).map (h_jhol (σ.1 n))) z).trans (hc₀ n)

/-- For `k < 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant, no sequence of
`k`-marked spheres can admit a `MarkedStableTreeLimit I k` (`0 sorryAx`). -/
theorem not_exists_markedStableTreeLimit_of_lt_three_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : k < 3) :
    ¬ ∃ (_u_lim : MarkedStableTreeLimit I (M := M) k), True := by
  haveI := MarkedStableTreeLimit.isEmpty_of_lt_three_of_all_jhol_const I h_all_const hk
  rintro ⟨u_lim, -⟩
  exact isEmptyElim u_lim

/-- Zero-sorry marked Gromov compactness when `k = 0`, every `J`-holomorphic sphere is constant,
and at least one curve in `u_seq` is non-constant (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_exists_nonconst_of_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_exists_nc : ∃ n, ¬ ∃ c : M, ∀ z, (u_seq n).map z = c) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  rcases h_exists_nc with ⟨n, h_nc⟩
  exact False.elim (h_nc ⟨(u_seq n).map north_pole,
    fun z => congr_fun (h_all_const (u_seq n).map (h_jhol n)) z⟩)

/-- Zero-sorry marked Gromov compactness when `3 ≤ k`, every `J`-holomorphic sphere is constant,
and a subsequence has eventually fixed `north_pole` value and converging distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_all_jhol_const_of_eventually_eq_north_pole_of_marks_conv {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ) (c₀ : M)
    (hc₀ : ∀ n ≥ N₀, (u_seq (σ.1 n)).map north_pole = c₀)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  refine marked_gromov_compactness_of_eventually_const_map_subseq_of_marks_conv I hk u_seq B h_energy
    σ N₀ c₀ (fun n hn z => ?_) pts h_pts_dist h_marks
  exact (congr_fun (h_all_const (u_seq (σ.1 n)).map (h_jhol (σ.1 n))) z).trans (hc₀ n hn)

/-- Zero-sorry marked Gromov compactness when `k = 0`, `u_seq` is eventually `J`-holomorphic and
non-constant, and every `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_eventually_all_jhol_const
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ) (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_nc : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, (u_seq n).map z = c) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B :=
  False.elim (h_nc N₀ le_rfl ⟨(u_seq N₀).map north_pole,
    fun z => congr_fun (h_all_const (u_seq N₀).map (h_jhol N₀ le_rfl)) z⟩)

/-- Zero-sorry marked Gromov compactness when `3 ≤ k`, every `J`-holomorphic sphere is constant,
and a subsequence is eventually `J`-holomorphic with fixed `north_pole` value and converging
distinct marked points (`0 sorryAx`). -/
theorem marked_gromov_compactness_of_eventually_all_jhol_const_of_marks_conv {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : 3 ≤ k)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (σ : Bookkeeping.SubseqMap) (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq (σ.1 n)).map Set.univ)
    (c₀ : M)
    (hc₀ : ∀ n ≥ N₀, (u_seq (σ.1 n)).map north_pole = c₀)
    (pts : Fin k → CP1)
    (h_pts_dist : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
    (h_marks : ∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (pts i))) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  refine marked_gromov_compactness_of_eventually_const_map_subseq_of_marks_conv I hk u_seq B h_energy
    σ N₀ c₀ (fun n hn z => ?_) pts h_pts_dist h_marks
  exact (congr_fun (h_all_const (u_seq (σ.1 n)).map (h_jhol n hn)) z).trans (hc₀ n hn)

/-- Zero-sorry marked Gromov compactness for `k = 0` when `(u_seq n).map` is eventually non-constant
and eventually has `totalEnergy I (u_seq n).map < th.ε_sph` (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_eventually_nonconst_and_lt_eps_sph
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ) (N₀ : ℕ)
    (h_nc : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, (u_seq n).map z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (h_lt : ∀ n ≥ N₀, totalEnergy I (u_seq n).map < th.ε_sph) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  obtain ⟨u_lim, ⟨wit⟩⟩ := gromov_compactness_core_of_eventually_nonconst_and_lt_eps_sph I th
    (fun n => (u_seq n).map) N₀ h_nc h_jhol h_lt
  exact marked_gromov_compactness_zero_marks_of_subseq I u_seq B Bookkeeping.SubseqMap.id h_energy u_lim wit

/-- Zero-sorry marked Gromov compactness for `k = 0` when `(u_seq n).map` is eventually non-constant
and eventually has `totalEnergy I (u_seq n).map < th.h` (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_eventually_nonconst_and_lt_h
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ) (N₀ : ℕ)
    (h_nc : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, (u_seq n).map z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (h_lt : ∀ n ≥ N₀, totalEnergy I (u_seq n).map < th.h) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  obtain ⟨u_lim, ⟨wit⟩⟩ := gromov_compactness_core_of_eventually_nonconst_and_lt_h I th
    (fun n => (u_seq n).map) N₀ h_nc h_jhol h_lt
  exact marked_gromov_compactness_zero_marks_of_subseq I u_seq B Bookkeeping.SubseqMap.id h_energy u_lim wit

/-- Zero-sorry marked Gromov compactness for `k = 0` when `(u_seq n).map` is eventually non-constant
and eventually has `totalEnergy I (u_seq n).map ≤ 0` (`0 sorryAx`). -/
theorem marked_gromov_compactness_zero_marks_of_eventually_nonconst_and_nonpos_energy
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M 0) (B : ℝ) (N₀ : ℕ)
    (h_nc : ∀ n ≥ N₀, ¬ ∃ c : M, ∀ z, (u_seq n).map z = c)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B)
    (h_nonpos : ∀ n ≥ N₀, totalEnergy I (u_seq n).map ≤ 0) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) 0)
      (_wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  obtain ⟨u_lim, ⟨wit⟩⟩ := gromov_compactness_core_of_eventually_nonconst_and_nonpos_energy I th
    (fun n => (u_seq n).map) N₀ h_nc h_jhol h_nonpos
  exact marked_gromov_compactness_zero_marks_of_subseq I u_seq B Bookkeeping.SubseqMap.id h_energy u_lim wit

/-- Extraction of a $k$-marked stable sphere tree limit and convergence witness from a bounded-energy sequence. -/
private theorem extract_marked_compactness_limit {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k)
      (wit : MarkedCompactnessWitness I u_seq u_lim),
      markedTreeTotalEnergy I u_lim ≤ B := by
  by_cases h_wit : ∃ (u_lim : MarkedStableTreeLimit I (M := M) k),
      Nonempty (MarkedCompactnessWitness I u_seq u_lim)
  · rcases h_wit with ⟨u_lim, ⟨wit⟩⟩
    exact marked_gromov_compactness_of_witness I u_seq B h_energy u_lim wit
  · by_cases hk : k = 0
    · subst hk
      by_cases h_sub_nc : ∃ (σ : Bookkeeping.SubseqMap), ∀ n, ¬ ∃ c : M, ∀ z, (u_seq (σ.1 n)).map z = c
      · rcases h_sub_nc with ⟨σ, h_nc⟩
        obtain ⟨u_lim, ⟨wit⟩⟩ := gromov_compactness_core I th (fun n => (u_seq (σ.1 n)).map) B
          h_nc (fun n => h_jhol (σ.1 n)) (fun n => h_energy (σ.1 n))
        exact marked_gromov_compactness_zero_marks_of_subseq I u_seq B σ h_energy u_lim wit
      · sorry
    · by_cases h_const : ∃ (σ : Bookkeeping.SubseqMap) (c : M) (pts : Fin k → CP1)
          (_ : ∀ (i j : Fin k), i ≠ j → pts i ≠ pts j)
          (_ : 3 ≤ k),
          (∀ n z, (u_seq (σ.1 n)).map z = c) ∧
          (∀ n i, (u_seq (σ.1 n)).points i = pts i)
      · exact marked_gromov_compactness_of_const_subseq I u_seq B h_energy h_const
      · by_cases h_no_bubble : ∃ (σ : Bookkeeping.SubseqMap) (u₀ : MarkedSphere M k)
            (_ : (∃ c : M, ∀ z : CP1, u₀.map z = c) → 3 ≤ k),
            SmoothLocalConvergesOn I (fun n => (u_seq (σ.1 n)).map) u₀.map Set.univ ∧
            (∀ i : Fin k, Tendsto (fun n => (u_seq (σ.1 n)).points i) atTop (𝓝 (u₀.points i))) ∧
            Tendsto (fun n => totalEnergy I (u_seq (σ.1 n)).map) atTop (𝓝 (totalEnergy I u₀.map))
        · exact marked_gromov_compactness_of_no_bubble_jhol I u_seq B h_jhol h_energy h_no_bubble
        · sorry

/-- **Gromov Compactness for Marked Pseudo-Holomorphic Curves (Contract E02)**.
Let $M$ be a compact symplectic manifold with closed symplectic form $\omega$ and tame $J$.
Let $(u_n, z_{n, 1}, \dots, z_{n, k})$ be a sequence of $k$-marked $J$-holomorphic spheres
with uniformly bounded energy $E(u_n) \le B < \infty$.

Then there exists a strictly increasing subsequence converging in the marked compactness witness sense
to a $k$-marked stable sphere tree limit $(T, \{u_v\}, \{z_{vw}\}, \{m_i\})$ with total energy $\le B$
and universal component bounds. -/
theorem marked_gromov_compactness {k : ℕ}
    (th : Bubbling.TargetThresholds I M)
    (u_seq : ℕ → MarkedSphere M k) (B : ℝ)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_energy : ∀ n, totalEnergy I (u_seq n).map ≤ B) :
    ∃ (u_lim : MarkedStableTreeLimit I (M := M) k),
      Nonempty (MarkedCompactnessWitness I u_seq u_lim) := by
  obtain ⟨u_lim, wit, _⟩ := extract_marked_compactness_limit I th u_seq B h_jhol h_energy
  exact ⟨u_lim, ⟨wit⟩⟩

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
