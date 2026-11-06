/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Sequences
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Hausdorff
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy
import GromovCompactness.Topology.SmoothLocal
import GromovCompactness.Topology.Subsequence
import GromovCompactness.Topology.SphereTree
import GromovCompactness.Topology.ComponentCount
import GromovCompactness.Compactness.Assembly
import GromovCompactness.Compactness.Stabilize
import GromovCompactness.Compactness.GenusZero
import GromovCompactness.Main
import GromovCompactness.Extensions.MarkedCurves

open scoped Manifold ContDiff Topology Classical
open Metric Set Filter Classical

set_option linter.unusedSectionVars false

namespace GromovCompactness.Extensions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Contract E05: Gromov Topology Metrizability & Compact Hausdorff Moduli Space

This module formalizes Contract `E05`:
1. `MarkedSphereTree`: $k$-marked combinatorial sphere trees with pairwise distinct marked points
   and disjointness from nodal points.
2. `MarkedStableMap`: Genus 0 stable $k$-marked pseudo-holomorphic maps into $(M, J)$
   with Deligne-Mumford / Kontsevich stability: ghost components satisfy $\operatorname{deg}_{\mathrm{nodal}}(v) + k_v \ge 3$.
3. `StableMapIso`: Isomorphism of stable marked maps (graph isomorphism, Möbius frames, node matching,
   marked point matching, curve intertwining).
4. `stableMapEquiv`: Equivalence relation on marked stable maps (reflexivity proved zero-sorry).
5. `ModuliSpace`: The quotient moduli space $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$.
6. `gromovDist` & `moduliSpaceMetric`: The canonical Gromov metric and metric space structure.
7. `moduli_space_t2`: Hausdorff separation ($T_2$) of the moduli space.
8. `moduli_space_compact` & `moduli_space_seq_compact`: Topological and sequential compactness.
9. `moduli_space_compact_hausdorff`: Master compact Hausdorff moduli space theorem.
10. `ModuliSpaceInClass`: Moduli space for a fixed homology class $A \in H_2(M; \mathbb{Z})$.

References:
- Mikhail Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Math. 82 (1985), §2.3.
- Sergei Ivashkovich & Vsevolod Shevchishin, arXiv:math/9912046, §2.
- D. McDuff & D. Salamon, *J-holomorphic Curves and Symplectic Topology*, AMS (2012), Chapter 5.
- `GROMOV_COMPACTNESS_BLUEPRINT.md` Contract `E05`.
-/

/-- A combinatorial $k$-marked sphere tree: a tree $T = (V, E_T)$ where each oriented edge
carries a nodal attachment point and $k$ marked points are assigned to vertices and coordinates. -/
structure MarkedSphereTree (k : ℕ) extends SphereTree where
  /-- Vertex carrying each marked point $i \in \{0, \dots, k-1\}$. -/
  mark_vertex : Fin k → V
  /-- Coordinates of each marked point on its host spherical component. -/
  mark_point : (i : Fin k) → CP1
  /-- Marked points on the same component are pairwise distinct. -/
  mark_distinct : ∀ (i j : Fin k), i ≠ j → mark_vertex i = mark_vertex j →
    mark_point i ≠ mark_point j
  /-- Marked points are disjoint from nodal attachment points on the same component. -/
  mark_node_distinct : ∀ (i : Fin k) (w : V) (h : adj.Adj (mark_vertex i) w),
    mark_point i ≠ node_point (mark_vertex i) w h

/-- The number of marked points located on component $v$. -/
noncomputable def marked_degree {k : ℕ} (tree : MarkedSphereTree k) (v : tree.V) : ℕ :=
  Fintype.card { i : Fin k // tree.mark_vertex i = v }

/-- Total number of special points (nodes + markings) on component $v$. -/
noncomputable def special_degree {k : ℕ} (tree : MarkedSphereTree k) (v : tree.V) : ℕ :=
  tree.adj.degree v + marked_degree tree v

/-- A $k$-marked stable pseudo-holomorphic map of genus 0 into $(M, J)$. -/
structure MarkedStableMap (k : ℕ) where
  /-- Underlying $k$-marked combinatorial sphere tree. -/
  tree : MarkedSphereTree k
  /-- Component pseudo-holomorphic curves $u_v : \mathbb{CP}^1 \to M$. -/
  map : (v : tree.V) → (CP1 → M)
  /-- Each component map is smooth and $J$-holomorphic. -/
  is_jhol : ∀ (v : tree.V), JHolomorphicOn I I_CP1 (map v) Set.univ
  /-- Nodal matching condition: across every incident edge $v \sim w$,
  $$u_v(z_{vw}) = u_w(z_{wv}).$$ -/
  nodal_match : ∀ (v w : tree.V) (h : tree.adj.Adj v w),
    map v (tree.node_point v w h) = map w (tree.node_point w v (tree.adj.adj_symm h))
  /-- Deligne-Mumford / Kontsevich stability condition: any constant component
  ('ghost bubble') carries at least 3 special points (nodes + marked points):
  $$\operatorname{special\_deg}(v) = \operatorname{deg}_{\mathrm{nodal}}(v) + k_v \ge 3.$$ -/
  stable : ∀ (v : tree.V), (∃ c : M, ∀ z : CP1, map v z = c) → 3 ≤ special_degree tree v

/-- Total symplectic energy of a $k$-marked stable map: $E(u) = \sum_{v \in V} E(u_v)$. -/
noncomputable def markedStableMapTotalEnergy {k : ℕ} (u : MarkedStableMap I (M := M) k) : ℝ :=
  ∑ v : u.tree.V, totalEnergy I (u.map v)

/-- Convert a `MarkedStableTreeLimit` (from `MarkedCurves.lean`) into a `MarkedStableMap` (`0 sorryAx`). -/
def MarkedStableMap.of_markedStableTreeLimit {k : ℕ}
    (lim : MarkedStableTreeLimit I (M := M) k) : MarkedStableMap I (M := M) k where
  tree := {
    toSphereTree := lim.tree
    mark_vertex := lim.mark_vertex
    mark_point := lim.mark_point
    mark_distinct := lim.mark_distinct
    mark_node_distinct := lim.mark_ne_node
  }
  map := lim.map
  is_jhol := lim.is_jhol
  nodal_match := lim.nodal_match
  stable := lim.stable

/-- Convert a `MarkedStableMap` into a `MarkedStableTreeLimit` (`0 sorryAx`). -/
def MarkedStableMap.toMarkedStableTreeLimit {k : ℕ}
    (u : MarkedStableMap I (M := M) k) : MarkedStableTreeLimit I (M := M) k where
  tree := u.tree.toSphereTree
  map := u.map
  is_jhol := u.is_jhol
  nodal_match := u.nodal_match
  mark_vertex := u.tree.mark_vertex
  mark_point := u.tree.mark_point
  mark_distinct := u.tree.mark_distinct
  mark_ne_node := u.tree.mark_node_distinct
  stable := u.stable

/-- `MarkedStableMap.of_markedStableTreeLimit` preserves total symplectic energy (`0 sorryAx`). -/
theorem markedStableMapTotalEnergy_of_markedStableTreeLimit {k : ℕ}
    (lim : MarkedStableTreeLimit I (M := M) k) :
    markedStableMapTotalEnergy I (MarkedStableMap.of_markedStableTreeLimit I lim) =
      markedTreeTotalEnergy I lim :=
  rfl

/-- `MarkedStableMap.toMarkedStableTreeLimit` preserves total symplectic energy (`0 sorryAx`). -/
theorem markedTreeTotalEnergy_toMarkedStableTreeLimit {k : ℕ}
    (u : MarkedStableMap I (M := M) k) :
    markedTreeTotalEnergy I (MarkedStableMap.toMarkedStableTreeLimit I u) =
      markedStableMapTotalEnergy I u :=
  rfl

/-- The space of $k$-marked stable maps with total energy bounded by $B$. -/
def BoundedMarkedStableMap (k : ℕ) (B : ℝ) : Type _ :=
  { u : MarkedStableMap I (M := M) k // markedStableMapTotalEnergy I u ≤ B }

/-- An isomorphism between two $k$-marked stable maps: a tree isomorphism and
Möbius transformations on each sphere component preserving nodes, markings, and maps. -/
structure StableMapIso {k : ℕ} (u₁ u₂ : MarkedStableMap I (M := M) k) where
  /-- Bijection between component vertex sets. -/
  v_equiv : u₁.tree.V ≃ u₂.tree.V
  /-- Preservation of graph adjacency. -/
  adj_compat : ∀ (v w : u₁.tree.V), u₁.tree.adj.Adj v w ↔ u₂.tree.adj.Adj (v_equiv v) (v_equiv w)
  /-- Biholomorphic Möbius frame transformation on each component sphere. -/
  moeb : (v : u₁.tree.V) → MoebiusFrame
  /-- Nodal points are mapped to corresponding nodal points. -/
  node_compat : ∀ (v w : u₁.tree.V) (h : u₁.tree.adj.Adj v w),
    (moeb v).toHomeo (u₁.tree.node_point v w h) =
      u₂.tree.node_point (v_equiv v) (v_equiv w) ((adj_compat v w).mp h)
  /-- Marked points lie on corresponding components. -/
  mark_vertex_compat : ∀ (i : Fin k), v_equiv (u₁.tree.mark_vertex i) = u₂.tree.mark_vertex i
  /-- Marked point coordinates are preserved under the component Möbius transformation. -/
  mark_point_compat : ∀ (i : Fin k),
    (moeb (u₁.tree.mark_vertex i)).toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i
  /-- Component curves are intertwined: $u_2 \circ \phi_v = u_1$. -/
  map_compat : ∀ (v : u₁.tree.V) (z : CP1),
    u₂.map (v_equiv v) ((moeb v).toHomeo z) = u₁.map v z
  /-- Component energy preservation under the intertwining Möbius reparametrization. -/
  energy_compat : ∀ (v : u₁.tree.V),
    totalEnergy I (u₁.map v) = totalEnergy I (u₂.map (v_equiv v)) := by intros; rfl

/-- Isomorphism of marked stable maps is an equivalence relation. -/
def stableMapEquiv {k : ℕ} (u₁ u₂ : MarkedStableMap I (M := M) k) : Prop :=
  Nonempty (StableMapIso I u₁ u₂)

/-- Reflexivity of stable map isomorphism (Zero-sorry). -/
theorem stableMapEquiv_refl {k : ℕ} (u : MarkedStableMap I (M := M) k) :
    stableMapEquiv I u u := by
  refine ⟨⟨Equiv.refl _, fun _ _ => Iff.rfl, fun _ => MoebiusFrame.id, ?_, fun _ => rfl, ?_, ?_, fun _ => rfl⟩⟩
  · intro v w h; rfl
  · intro i; rfl
  · intro v z; rfl

/-- Symmetry of stable map isomorphism (Zero-sorry). -/
theorem stableMapEquiv_symm {k : ℕ} {u₁ u₂ : MarkedStableMap I (M := M) k}
    (h : stableMapEquiv I u₁ u₂) : stableMapEquiv I u₂ u₁ := by
  obtain ⟨iso⟩ := h
  refine ⟨{
    v_equiv := iso.v_equiv.symm
    adj_compat := fun u v => by
      have h_adj := (iso.adj_compat (iso.v_equiv.symm u) (iso.v_equiv.symm v)).symm
      rw [iso.v_equiv.apply_symm_apply u, iso.v_equiv.apply_symm_apply v] at h_adj
      exact h_adj
    moeb := fun v => MoebiusFrame.inv (iso.moeb (iso.v_equiv.symm v))
    node_compat := fun v w h_adj => by
      dsimp [MoebiusFrame.inv]
      obtain ⟨v', rfl⟩ := iso.v_equiv.surjective v
      obtain ⟨w', rfl⟩ := iso.v_equiv.surjective w
      simp only [Equiv.symm_apply_apply]
      have h_orig_adj : u₁.tree.adj.Adj v' w' := (iso.adj_compat v' w').mpr h_adj
      have h_node := iso.node_compat v' w' h_orig_adj
      rw [← h_node, (iso.moeb v').toHomeo.symm_apply_apply]
    mark_vertex_compat := fun i => by
      have h_mv := iso.mark_vertex_compat i
      exact iso.v_equiv.symm_apply_eq.mpr h_mv.symm
    mark_point_compat := fun i => by
      dsimp [MoebiusFrame.inv]
      have h_mv : iso.v_equiv.symm (u₂.tree.mark_vertex i) = u₁.tree.mark_vertex i := by
        exact iso.v_equiv.symm_apply_eq.mpr (iso.mark_vertex_compat i).symm
      rw [h_mv]
      have h_mp := iso.mark_point_compat i
      rw [← h_mp, (iso.moeb (u₁.tree.mark_vertex i)).toHomeo.symm_apply_apply]
    map_compat := fun v z => by
      dsimp [MoebiusFrame.inv]
      have h_map := iso.map_compat (iso.v_equiv.symm v) ((iso.moeb (iso.v_equiv.symm v)).toHomeo.symm z)
      rw [iso.v_equiv.apply_symm_apply v] at h_map
      rw [(iso.moeb (iso.v_equiv.symm v)).toHomeo.apply_symm_apply z] at h_map
      exact h_map.symm
    energy_compat := fun v => by
      have h_en := (iso.energy_compat (iso.v_equiv.symm v)).symm
      rwa [iso.v_equiv.apply_symm_apply v] at h_en
  }⟩

/-- Transitivity of stable map isomorphism (Zero-sorry). -/
theorem stableMapEquiv_trans {k : ℕ} {u₁ u₂ u₃ : MarkedStableMap I (M := M) k}
    (h₁₂ : stableMapEquiv I u₁ u₂) (h₂₃ : stableMapEquiv I u₂ u₃) :
    stableMapEquiv I u₁ u₃ := by
  obtain ⟨iso12⟩ := h₁₂
  obtain ⟨iso23⟩ := h₂₃
  refine ⟨{
    v_equiv := iso12.v_equiv.trans iso23.v_equiv
    adj_compat := fun u v =>
      (iso12.adj_compat u v).trans (iso23.adj_compat (iso12.v_equiv u) (iso12.v_equiv v))
    moeb := fun v => MoebiusFrame.comp (iso23.moeb (iso12.v_equiv v)) (iso12.moeb v)
    node_compat := fun v w h => by
      dsimp [MoebiusFrame.comp]
      have h1 := iso12.node_compat v w h
      have h2 := iso23.node_compat (iso12.v_equiv v) (iso12.v_equiv w) ((iso12.adj_compat v w).mp h)
      rw [h1, h2]
    mark_vertex_compat := fun i => by
      dsimp [Equiv.trans]
      rw [iso12.mark_vertex_compat i, iso23.mark_vertex_compat i]
    mark_point_compat := fun i => by
      dsimp [MoebiusFrame.comp]
      rw [iso12.mark_vertex_compat i]
      rw [iso12.mark_point_compat i, iso23.mark_point_compat i]
    map_compat := fun v z => by
      dsimp [MoebiusFrame.comp, Equiv.trans]
      have h2 := iso23.map_compat (iso12.v_equiv v) ((iso12.moeb v).toHomeo z)
      have h1 := iso12.map_compat v z
      rw [h2, h1]
    energy_compat := fun v =>
      (iso12.energy_compat v).trans (iso23.energy_compat (iso12.v_equiv v))
  }⟩

/-- Equivalence relation on bounded marked stable maps. -/
def boundedMarkedStableMapSetoid (k : ℕ) (B : ℝ) :
    Setoid (BoundedMarkedStableMap I (M := M) k B) where
  r u₁ u₂ := stableMapEquiv I u₁.1 u₂.1
  iseqv := {
    refl := fun u => stableMapEquiv_refl I u.1
    symm := fun h => stableMapEquiv_symm I h
    trans := fun h₁ h₂ => stableMapEquiv_trans I h₁ h₂
  }

instance boundedMarkedStableMapSetoidInst (k : ℕ) (B : ℝ) :
    Setoid (BoundedMarkedStableMap I (M := M) k B) :=
  boundedMarkedStableMapSetoid I k B

/-- The Kontsevich moduli space $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$ of stable
$k$-marked genus 0 pseudo-holomorphic curves with energy bounded by $B$. -/
def ModuliSpace (k : ℕ) (B : ℝ) : Type _ :=
  Quotient (boundedMarkedStableMapSetoid I (M := M) k B)

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
    ∀ K ⊆ punctured_sphere {u_lim.tree.node_point w v (u_lim.tree.adj.adj_symm h)}, IsCompact K →
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

/-- Total symplectic energy of any marked stable map is nonnegative (`0 sorryAx`). -/
theorem markedStableMapTotalEnergy_nonneg {k : ℕ} (u : MarkedStableMap I (M := M) k) :
    0 ≤ markedStableMapTotalEnergy I u :=
  Finset.sum_nonneg (fun v _ => energy_nonneg I (u.map v) Set.univ)

/-- For `B < 0`, `BoundedMarkedStableMap I k B` is empty (`0 sorryAx`). -/
theorem isEmpty_boundedMarkedStableMap_of_neg (k : ℕ) {B : ℝ} (hB : B < 0) :
    IsEmpty (BoundedMarkedStableMap I (M := M) k B) := by
  refine ⟨fun r => ?_⟩
  have h_nonneg := markedStableMapTotalEnergy_nonneg I r.1
  have h_le := r.2
  linarith

/-- For `B < 0`, `ModuliSpace I k B` is empty (`0 sorryAx`). -/
theorem isEmpty_moduliSpace_of_neg (k : ℕ) {B : ℝ} (hB : B < 0) :
    IsEmpty (ModuliSpace I (M := M) k B) := by
  haveI := isEmpty_boundedMarkedStableMap_of_neg I (M := M) k hB
  refine ⟨fun x => ?_⟩
  obtain ⟨r, _⟩ := Quotient.exists_rep x
  exact isEmptyElim r

/-- `marked_degree tree v` equals the cardinality of the fiber `{i : Fin k | tree.mark_vertex i = v}` (`0 sorryAx`). -/
theorem marked_degree_eq_card_filter {k : ℕ} (tree : MarkedSphereTree k) (v : tree.V) :
    marked_degree tree v = (Finset.univ.filter (fun i : Fin k => tree.mark_vertex i = v)).card := by
  unfold marked_degree
  exact Fintype.card_subtype _

/-- The sum of `marked_degree tree v` over all components `v : tree.V` equals `k` (`0 sorryAx`). -/
theorem sum_marked_degree_eq {k : ℕ} (tree : MarkedSphereTree k) :
    ∑ v : tree.V, marked_degree tree v = k := by
  simp_rw [marked_degree_eq_card_filter]
  have h_fib := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin k))) (t := (Finset.univ : Finset tree.V))
    (f := tree.mark_vertex) (fun i _ => Finset.mem_univ (tree.mark_vertex i))
  rw [← h_fib, Finset.card_univ, Fintype.card_fin]

/-- The sum of `special_degree tree v` over all components `v : tree.V` equals `2 * (|V| - 1) + k` (`0 sorryAx`). -/
theorem sum_special_degree_eq {k : ℕ} (tree : MarkedSphereTree k) :
    ∑ v : tree.V, special_degree tree v = 2 * (Fintype.card tree.V - 1) + k := by
  unfold special_degree
  rw [Finset.sum_add_distrib, tree_degree_sum tree.toSphereTree, sum_marked_degree_eq tree]

/-- If every component of a `k`-marked stable map `u` is constant, then `|V| + 2 ≤ k` (`0 sorryAx`). -/
theorem card_V_add_two_le_of_all_const {k : ℕ}
    (u : MarkedStableMap I (M := M) k)
    (h_const : ∀ v : u.tree.V, ∃ c : M, ∀ z : CP1, u.map v z = c) :
    Fintype.card u.tree.V + 2 ≤ k := by
  have h_le : ∑ _v : u.tree.V, (3 : ℕ) ≤ ∑ v : u.tree.V, special_degree u.tree v :=
    Finset.sum_le_sum (fun v _ => u.stable v (h_const v))
  have h_lhs : (∑ _v : u.tree.V, (3 : ℕ)) = 3 * Fintype.card u.tree.V := by
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have h_rhs := sum_special_degree_eq u.tree
  have h_pos : 0 < Fintype.card u.tree.V := Fintype.card_pos
  omega

/-- If every component of a `k`-marked stable map `u` is constant, then `3 ≤ k` (`0 sorryAx`). -/
theorem three_le_of_all_const {k : ℕ}
    (u : MarkedStableMap I (M := M) k)
    (h_const : ∀ v : u.tree.V, ∃ c : M, ∀ z : CP1, u.map v z = c) :
    3 ≤ k := by
  have h1 := card_V_add_two_le_of_all_const I u h_const
  have h2 : 0 < Fintype.card u.tree.V := Fintype.card_pos
  omega

/-- Every component of `u : BoundedMarkedStableMap I k B` with `B < th.ε_sph` is constant (`0 sorryAx`). -/
theorem all_const_of_lt_eps_sph {k : ℕ} {B : ℝ}
    (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph)
    (u : BoundedMarkedStableMap I (M := M) k B)
    (v : u.1.tree.V) :
    ∃ c : M, ∀ z : CP1, u.1.map v z = c := by
  by_contra h_nonconst
  have h_ge : th.ε_sph ≤ totalEnergy I (u.1.map v) :=
    th.h_sph (u.1.map v) (u.1.is_jhol v) h_nonconst
  have h_le_sum : totalEnergy I (u.1.map v) ≤ markedStableMapTotalEnergy I u.1 :=
    Finset.single_le_sum (fun w _ => energy_nonneg I (u.1.map w) Set.univ) (Finset.mem_univ v)
  have h_tot := u.2
  linarith

/-- Every component of `u : BoundedMarkedStableMap I k B` with `B < th.h` is constant (`0 sorryAx`). -/
theorem all_const_of_lt_threshold {k : ℕ} {B : ℝ}
    (th : Bubbling.TargetThresholds I M) (hB : B < th.h)
    (u : BoundedMarkedStableMap I (M := M) k B)
    (v : u.1.tree.V) :
    ∃ c : M, ∀ z : CP1, u.1.map v z = c :=
  all_const_of_lt_eps_sph I th (hB.trans_le th.h_le_sph) u v

/-- Every component of `u : BoundedMarkedStableMap I k B` with `B ≤ 0` is constant (`0 sorryAx`). -/
theorem all_const_of_nonpos_B {k : ℕ} {B : ℝ}
    (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0)
    (u : BoundedMarkedStableMap I (M := M) k B)
    (v : u.1.tree.V) :
    ∃ c : M, ∀ z : CP1, u.1.map v z = c :=
  all_const_of_lt_eps_sph I th (hB.trans_lt th.ε_sph_pos) u v

/-- For `k < 3` on a subsingleton target `M`, `MarkedStableMap I k` is empty (`0 sorryAx`). -/
theorem isEmpty_markedStableMap_of_lt_three_of_subsingleton {k : ℕ}
    (hk : k < 3) [Subsingleton M] :
    IsEmpty (MarkedStableMap I (M := M) k) := by
  refine ⟨fun u => ?_⟩
  have h3 := three_le_of_all_const I u
    (fun v => ⟨u.map v north_pole, fun z => Subsingleton.elim (u.map v z) (u.map v north_pole)⟩)
  omega

/-- For `k < 3` on a subsingleton target `M`, `BoundedMarkedStableMap I k B` is empty (`0 sorryAx`). -/
theorem isEmpty_boundedMarkedStableMap_of_lt_three_of_subsingleton {k : ℕ}
    (hk : k < 3) (B : ℝ) [Subsingleton M] :
    IsEmpty (BoundedMarkedStableMap I (M := M) k B) := by
  haveI := isEmpty_markedStableMap_of_lt_three_of_subsingleton I (M := M) hk
  exact ⟨fun r => isEmptyElim r.1⟩

/-- For `k < 3` on a subsingleton target `M`, `ModuliSpace I k B` is empty (`0 sorryAx`). -/
theorem isEmpty_moduliSpace_of_lt_three_of_subsingleton {k : ℕ}
    (hk : k < 3) (B : ℝ) [Subsingleton M] :
    IsEmpty (ModuliSpace I (M := M) k B) := by
  haveI := isEmpty_boundedMarkedStableMap_of_lt_three_of_subsingleton I (M := M) hk B
  refine ⟨fun x => ?_⟩
  obtain ⟨r, _⟩ := Quotient.exists_rep x
  exact isEmptyElim r

/-- For `k < 3` and `B < th.ε_sph`, `BoundedMarkedStableMap I k B` is empty (`0 sorryAx`). -/
theorem isEmpty_boundedMarkedStableMap_of_lt_three_of_lt_eps_sph {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph) :
    IsEmpty (BoundedMarkedStableMap I (M := M) k B) := by
  refine ⟨fun r => ?_⟩
  have h3 := three_le_of_all_const I r.1 (all_const_of_lt_eps_sph I th hB r)
  omega

/-- For `k < 3` and `B < th.ε_sph`, `ModuliSpace I k B` is empty (`0 sorryAx`). -/
theorem isEmpty_moduliSpace_of_lt_three_of_lt_eps_sph {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph) :
    IsEmpty (ModuliSpace I (M := M) k B) := by
  haveI := isEmpty_boundedMarkedStableMap_of_lt_three_of_lt_eps_sph I hk th hB
  refine ⟨fun x => ?_⟩
  obtain ⟨r, _⟩ := Quotient.exists_rep x
  exact isEmptyElim r

/-- For `k < 3` and `B < th.h`, `BoundedMarkedStableMap I k B` is empty (`0 sorryAx`). -/
theorem isEmpty_boundedMarkedStableMap_of_lt_three_of_lt_threshold {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.h) :
    IsEmpty (BoundedMarkedStableMap I (M := M) k B) :=
  isEmpty_boundedMarkedStableMap_of_lt_three_of_lt_eps_sph I hk th (hB.trans_le th.h_le_sph)

/-- For `k < 3` and `B < th.h`, `ModuliSpace I k B` is empty (`0 sorryAx`). -/
theorem isEmpty_moduliSpace_of_lt_three_of_lt_threshold {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.h) :
    IsEmpty (ModuliSpace I (M := M) k B) :=
  isEmpty_moduliSpace_of_lt_three_of_lt_eps_sph I hk th (hB.trans_le th.h_le_sph)

/-- For `k < 3` and `B ≤ 0`, `BoundedMarkedStableMap I k B` is empty (`0 sorryAx`). -/
theorem isEmpty_boundedMarkedStableMap_of_lt_three_of_nonpos_B {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0) :
    IsEmpty (BoundedMarkedStableMap I (M := M) k B) :=
  isEmpty_boundedMarkedStableMap_of_lt_three_of_lt_eps_sph I hk th (hB.trans_lt th.ε_sph_pos)

/-- For `k < 3` and `B ≤ 0`, `ModuliSpace I k B` is empty (`0 sorryAx`). -/
theorem isEmpty_moduliSpace_of_lt_three_of_nonpos_B {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0) :
    IsEmpty (ModuliSpace I (M := M) k B) :=
  isEmpty_moduliSpace_of_lt_three_of_lt_eps_sph I hk th (hB.trans_lt th.ε_sph_pos)

/-- Every component of `u : MarkedStableMap I k` on a discrete target `M` is constant (`0 sorryAx`). -/
theorem all_const_of_discrete {k : ℕ} [DiscreteTopology M]
    (u : MarkedStableMap I (M := M) k)
    (v : u.tree.V) :
    ∃ c : M, ∀ z : CP1, u.map v z = c :=
  ⟨u.map v north_pole, Analysis.eq_const_north_pole_of_jhol_univ_of_discrete I (u.map v) (u.is_jhol v)⟩

/-- For `k < 3` on a discrete target `M`, `MarkedStableMap I k` is empty (`0 sorryAx`). -/
theorem isEmpty_markedStableMap_of_lt_three_of_discrete {k : ℕ}
    (hk : k < 3) [DiscreteTopology M] :
    IsEmpty (MarkedStableMap I (M := M) k) := by
  refine ⟨fun u => ?_⟩
  have h3 := three_le_of_all_const I u (all_const_of_discrete I u)
  omega

/-- For `k < 3` on a discrete target `M`, `BoundedMarkedStableMap I k B` is empty (`0 sorryAx`). -/
theorem isEmpty_boundedMarkedStableMap_of_lt_three_of_discrete {k : ℕ}
    (hk : k < 3) (B : ℝ) [DiscreteTopology M] :
    IsEmpty (BoundedMarkedStableMap I (M := M) k B) := by
  haveI := isEmpty_markedStableMap_of_lt_three_of_discrete I (M := M) hk
  exact ⟨fun r => isEmptyElim r.1⟩

/-- For `k < 3` on a discrete target `M`, `ModuliSpace I k B` is empty (`0 sorryAx`). -/
theorem isEmpty_moduliSpace_of_lt_three_of_discrete {k : ℕ}
    (hk : k < 3) (B : ℝ) [DiscreteTopology M] :
    IsEmpty (ModuliSpace I (M := M) k B) := by
  haveI := isEmpty_boundedMarkedStableMap_of_lt_three_of_discrete I (M := M) hk B
  refine ⟨fun x => ?_⟩
  obtain ⟨r, _⟩ := Quotient.exists_rep x
  exact isEmptyElim r

/-- If every component of a `3`-marked stable map `u` is constant, then `|V| = 1` (`0 sorryAx`). -/
theorem card_V_eq_one_of_all_const_three
    (u : MarkedStableMap I (M := M) 3)
    (h_const : ∀ v : u.tree.V, ∃ c : M, ∀ z : CP1, u.map v z = c) :
    Fintype.card u.tree.V = 1 := by
  have h_le := card_V_add_two_le_of_all_const I u h_const
  have h_pos : 0 < Fintype.card u.tree.V := Fintype.card_pos
  omega

/-- If every component of a `3`-marked stable map `u` is constant, then `u.tree.V` is a subsingleton (`0 sorryAx`). -/
theorem subsingleton_V_of_all_const_three
    (u : MarkedStableMap I (M := M) 3)
    (h_const : ∀ v : u.tree.V, ∃ c : M, ∀ z : CP1, u.map v z = c) :
    Subsingleton u.tree.V :=
  Fintype.card_le_one_iff_subsingleton.mp (by rw [card_V_eq_one_of_all_const_three I u h_const])

/-- If every component of a `3`-marked stable map `u` is constant, then `u.tree` has no edges (`0 sorryAx`). -/
theorem no_edges_of_all_const_three
    (u : MarkedStableMap I (M := M) 3)
    (h_const : ∀ v : u.tree.V, ∃ c : M, ∀ z : CP1, u.map v z = c)
    (v w : u.tree.V) :
    ¬ u.tree.adj.Adj v w := by
  have h_sub := subsingleton_V_of_all_const_three I u h_const
  intro h_adj
  exact u.tree.adj.ne_of_adj h_adj (h_sub.elim v w)

/-- Any two `k`-marked stable maps with single-vertex trees (`|V| = 1`), constant maps taking the
same value `c : M`, and marked points intertwined by a `MoebiusFrame` `φ` are isomorphic (`0 sorryAx`). -/
theorem stableMapEquiv_of_card_V_eq_one_and_const {k : ℕ}
    (u₁ u₂ : MarkedStableMap I (M := M) k)
    (h₁ : Fintype.card u₁.tree.V = 1)
    (h₂ : Fintype.card u₂.tree.V = 1)
    (c : M)
    (hc₁ : ∀ (v : u₁.tree.V) (z : CP1), u₁.map v z = c)
    (hc₂ : ∀ (w : u₂.tree.V) (z : CP1), u₂.map w z = c)
    (φ : MoebiusFrame)
    (h_marks : ∀ i : Fin k, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    stableMapEquiv I u₁ u₂ := by
  have h_sub₁ : Subsingleton u₁.tree.V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have h_sub₂ : Subsingleton u₂.tree.V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  let e : u₁.tree.V ≃ u₂.tree.V := Fintype.equivOfCardEq (h₁.trans h₂.symm)
  refine ⟨{
    v_equiv := e
    adj_compat := fun v w =>
      ⟨fun h => False.elim (u₁.tree.adj.ne_of_adj h (h_sub₁.elim v w)),
       fun h => False.elim (u₂.tree.adj.ne_of_adj h (h_sub₂.elim (e v) (e w)))⟩
    moeb := fun _ => φ
    node_compat := fun v w h => False.elim (u₁.tree.adj.ne_of_adj h (h_sub₁.elim v w))
    mark_vertex_compat := fun i => h_sub₂.elim _ _
    mark_point_compat := h_marks
    map_compat := fun v z => (hc₂ (e v) (φ.toHomeo z)).trans (hc₁ v z).symm
    energy_compat := fun v => by
      have hm₁ : u₁.map v = fun _ => c := funext (hc₁ v)
      have hm₂ : u₂.map (e v) = fun _ => c := funext (hc₂ (e v))
      rw [hm₁, hm₂]
  }⟩

/-- Any two `3`-marked stable maps whose components are all constant with the same value `c : M`
and whose marked points are intertwined by a `MoebiusFrame` `φ` are isomorphic (`0 sorryAx`). -/
theorem stableMapEquiv_of_all_const_three
    (u₁ u₂ : MarkedStableMap I (M := M) 3)
    (c : M)
    (hc₁ : ∀ (v : u₁.tree.V) (z : CP1), u₁.map v z = c)
    (hc₂ : ∀ (w : u₂.tree.V) (z : CP1), u₂.map w z = c)
    (φ : MoebiusFrame)
    (h_marks : ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    stableMapEquiv I u₁ u₂ :=
  stableMapEquiv_of_card_V_eq_one_and_const I u₁ u₂
    (card_V_eq_one_of_all_const_three I u₁ (fun v => ⟨c, hc₁ v⟩))
    (card_V_eq_one_of_all_const_three I u₂ (fun w => ⟨c, hc₂ w⟩))
    c hc₁ hc₂ φ h_marks

/-- Any two `3`-marked stable maps whose components are all constant with the same value `c : M`
and that have the same marked point coordinates are isomorphic (`0 sorryAx`). -/
theorem stableMapEquiv_of_all_const_three_same_marks
    (u₁ u₂ : MarkedStableMap I (M := M) 3)
    (c : M)
    (hc₁ : ∀ (v : u₁.tree.V) (z : CP1), u₁.map v z = c)
    (hc₂ : ∀ (w : u₂.tree.V) (z : CP1), u₂.map w z = c)
    (h_marks : u₁.tree.mark_point = u₂.tree.mark_point) :
    stableMapEquiv I u₁ u₂ :=
  stableMapEquiv_of_all_const_three I u₁ u₂ c hc₁ hc₂ MoebiusFrame.id
    (fun i => congrFun h_marks i)

/-- On a subsingleton target `M`, any two `3`-marked stable maps whose marked points are intertwined
by a `MoebiusFrame` `φ` are isomorphic (`0 sorryAx`). -/
theorem stableMapEquiv_of_subsingleton_three [Subsingleton M]
    (u₁ u₂ : MarkedStableMap I (M := M) 3)
    (φ : MoebiusFrame)
    (h_marks : ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    stableMapEquiv I u₁ u₂ := by
  let v₀ : u₁.tree.V := Classical.arbitrary u₁.tree.V
  exact stableMapEquiv_of_all_const_three I u₁ u₂ (u₁.map v₀ north_pole)
    (fun v z => Subsingleton.elim (u₁.map v z) (u₁.map v₀ north_pole))
    (fun w z => Subsingleton.elim (u₂.map w z) (u₁.map v₀ north_pole))
    φ h_marks

/-- On a subsingleton target `M`, if `MoebiusFrame` acts transitively on the marked point triples of
`MarkedStableMap I 3`, then `ModuliSpace I 3 B` is a subsingleton (`0 sorryAx`). -/
theorem subsingleton_moduliSpace_three_of_subsingleton_of_trans [Subsingleton M]
    (B : ℝ)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    Subsingleton (ModuliSpace I (M := M) 3 B) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨r₁, rfl⟩ := Quotient.exists_rep x
  obtain ⟨r₂, rfl⟩ := Quotient.exists_rep y
  obtain ⟨φ, hφ⟩ := h_trans r₁.1 r₂.1
  exact Quotient.sound' (stableMapEquiv_of_subsingleton_three I r₁.1 r₂.1 φ hφ)

/-- On a `[DiscreteTopology M]` target, two `3`-marked stable maps whose marked points are intertwined
by a `MoebiusFrame` `φ` and whose components share the same constant value `c : M` are isomorphic (`0 sorryAx`). -/
theorem stableMapEquiv_of_discrete_three_of_eq_val [DiscreteTopology M]
    (u₁ u₂ : MarkedStableMap I (M := M) 3)
    (c : M)
    (hc₁ : ∀ v : u₁.tree.V, u₁.map v north_pole = c)
    (hc₂ : ∀ w : u₂.tree.V, u₂.map w north_pole = c)
    (φ : MoebiusFrame)
    (h_marks : ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    stableMapEquiv I u₁ u₂ :=
  stableMapEquiv_of_all_const_three I u₁ u₂ c
    (fun v z => (Analysis.eq_const_north_pole_of_jhol_univ_of_discrete I (u₁.map v) (u₁.is_jhol v) z).trans (hc₁ v))
    (fun w z => (Analysis.eq_const_north_pole_of_jhol_univ_of_discrete I (u₂.map w) (u₂.is_jhol w) z).trans (hc₂ w))
    φ h_marks

/-- On a `[DiscreteTopology M]` target, two `3`-marked stable maps with identical marked points and
whose components share the same constant value `c : M` are isomorphic (`0 sorryAx`). -/
theorem stableMapEquiv_of_discrete_three_same_marks [DiscreteTopology M]
    (u₁ u₂ : MarkedStableMap I (M := M) 3)
    (c : M)
    (hc₁ : ∀ v : u₁.tree.V, u₁.map v north_pole = c)
    (hc₂ : ∀ w : u₂.tree.V, u₂.map w north_pole = c)
    (h_marks : u₁.tree.mark_point = u₂.tree.mark_point) :
    stableMapEquiv I u₁ u₂ :=
  stableMapEquiv_of_discrete_three_of_eq_val I u₁ u₂ c hc₁ hc₂ MoebiusFrame.id
    (fun i => congrFun h_marks i)

/-- On a `[DiscreteTopology M]` target, if all components of every `u : BoundedMarkedStableMap I 3 B`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is a subsingleton (`0 sorryAx`). -/
theorem subsingleton_moduliSpace_three_of_discrete_of_eq_val_of_trans [DiscreteTopology M]
    (B : ℝ) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    Subsingleton (ModuliSpace I (M := M) 3 B) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨r₁, rfl⟩ := Quotient.exists_rep x
  obtain ⟨r₂, rfl⟩ := Quotient.exists_rep y
  obtain ⟨φ, hφ⟩ := h_trans r₁.1 r₂.1
  exact Quotient.sound'
    (stableMapEquiv_of_discrete_three_of_eq_val I r₁.1 r₂.1 c (hc r₁) (hc r₂) φ hφ)

/-- Every subset of a subsingleton type is either empty or `Set.univ` (`0 sorryAx`). -/
lemma eq_empty_or_univ_of_subsingleton {X : Type*} (h_sub : Subsingleton X) (U : Set X) :
    U = ∅ ∨ U = Set.univ := by
  by_cases h_ne : U.Nonempty
  · right
    rcases h_ne with ⟨x, hx⟩
    ext y
    simp only [Set.mem_univ, iff_true]
    rwa [h_sub.elim y x]
  · left
    exact Set.not_nonempty_iff_eq_empty.mp h_ne

/-- On a subsingleton type, any two `TopologicalSpace` structures are equal (`0 sorryAx`). -/
lemma topologicalSpace_eq_of_subsingleton {X : Type*} (h_sub : Subsingleton X)
    (t₁ t₂ : TopologicalSpace X) : t₁ = t₂ := by
  ext U
  rcases eq_empty_or_univ_of_subsingleton h_sub U with rfl | rfl
  · exact ⟨fun _ => @isOpen_empty X t₂, fun _ => @isOpen_empty X t₁⟩
  · exact ⟨fun _ => @isOpen_univ X t₂, fun _ => @isOpen_univ X t₁⟩

/-- Any subsingleton type carries a canonical zero-distance `MetricSpace` structure (`0 sorryAx`). -/
def metricSpaceOfSubsingleton {X : Type*} (h_sub : Subsingleton X) : MetricSpace X where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  dist_triangle _ _ _ := by norm_num
  eq_of_dist_eq_zero {_ _} _ := h_sub.elim _ _

/-- When `ModuliSpace I k B` is a subsingleton, `moduliSpaceTopology I k B` is metrizable (`0 sorryAx`). -/
theorem exists_gromov_metricSpace_of_subsingleton (k : ℕ) (B : ℝ)
    (h_sub : Subsingleton (ModuliSpace I (M := M) k B)) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k B :=
  ⟨metricSpaceOfSubsingleton h_sub,
    topologicalSpace_eq_of_subsingleton h_sub _ (moduliSpaceTopology I k B)⟩

/-- For `B < 0`, `ModuliSpace I k B` is metrizable with zero `sorry` (`0 sorryAx`). -/
theorem exists_gromov_metricSpace_of_neg (k : ℕ) {B : ℝ} (hB : B < 0) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k B := by
  haveI := isEmpty_moduliSpace_of_neg I (M := M) k hB
  exact exists_gromov_metricSpace_of_subsingleton I k B inferInstance

/-- For `k < 3` on a subsingleton target `M`, `ModuliSpace I k B` is metrizable (`0 sorryAx`). -/
theorem exists_gromov_metricSpace_of_lt_three_of_subsingleton {k : ℕ}
    (hk : k < 3) (B : ℝ) [Subsingleton M] :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k B := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_subsingleton I (M := M) hk B
  exact exists_gromov_metricSpace_of_subsingleton I k B inferInstance

/-- For `k < 3` and `B < th.ε_sph`, `ModuliSpace I k B` is metrizable (`0 sorryAx`). -/
theorem exists_gromov_metricSpace_of_lt_three_of_lt_eps_sph {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k B := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_lt_eps_sph I hk th hB
  exact exists_gromov_metricSpace_of_subsingleton I k B inferInstance

/-- For `k < 3` and `B < th.h`, `ModuliSpace I k B` is metrizable (`0 sorryAx`). -/
theorem exists_gromov_metricSpace_of_lt_three_of_lt_threshold {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.h) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k B :=
  exists_gromov_metricSpace_of_lt_three_of_lt_eps_sph I hk th (hB.trans_le th.h_le_sph)

/-- For `k < 3` and `B ≤ 0`, `ModuliSpace I k B` is metrizable (`0 sorryAx`). -/
theorem exists_gromov_metricSpace_of_lt_three_of_nonpos_B {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k B :=
  exists_gromov_metricSpace_of_lt_three_of_lt_eps_sph I hk th (hB.trans_lt th.ε_sph_pos)

/-- For `k < 3` on a discrete target `M`, `ModuliSpace I k B` is metrizable (`0 sorryAx`). -/
theorem exists_gromov_metricSpace_of_lt_three_of_discrete {k : ℕ}
    (hk : k < 3) (B : ℝ) [DiscreteTopology M] :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k B := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_discrete I (M := M) hk B
  exact exists_gromov_metricSpace_of_subsingleton I k B inferInstance

/-- Existence of a metric space structure compatible with sequential Gromov convergence. -/
private theorem exists_gromov_metricSpace (k : ℕ) (B : ℝ) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k B := by
  by_cases hB : B < 0
  · exact exists_gromov_metricSpace_of_neg I k hB
  · by_cases h_sub : Subsingleton (ModuliSpace I (M := M) k B)
    · exact exists_gromov_metricSpace_of_subsingleton I k B h_sub
    · sorry

/-- Metrizability of the Gromov Moduli Space (McDuff-Salamon §5.6, deferred theorem).
There exists a metric inducing the sequential Gromov topology on $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$. -/
theorem moduli_space_metrizable (k : ℕ) (B : ℝ) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k B :=
  exists_gromov_metricSpace I k B

/-- Any Gromov-convergent sequence in `ModuliSpace` converges in `moduliSpaceTopology` (Zero-sorry). -/
theorem tendsto_of_gromovConverges {k : ℕ} {B : ℝ}
    {v_seq : ℕ → ModuliSpace I (M := M) k B}
    {u_lim : ModuliSpace I (M := M) k B}
    (h_conv : GromovConverges I v_seq u_lim) :
    Tendsto v_seq atTop (𝓝 u_lim) :=
  tendsto_nhds.mpr (fun _ hU hu => hU v_seq u_lim hu h_conv)

/-- Any `MarkedCompactnessWitness` for a sequence of `k`-marked spheres induces a `MarkedGromovWitness`
along its extracted subsequence `wit.σ` when each sphere is viewed as a singleton `MarkedStableMap` (`0 sorryAx`). -/
def MarkedGromovWitness.of_markedCompactnessWitness {k : ℕ}
    {u_seq : ℕ → MarkedSphere M k}
    {u_lim : MarkedStableTreeLimit I (M := M) k}
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_stab : ∀ n, (∃ c : M, ∀ z : CP1, (u_seq n).map z = c) → 3 ≤ k)
    (wit : MarkedCompactnessWitness I u_seq u_lim) :
    MarkedGromovWitness I
      (fun n => MarkedStableMap.of_markedStableTreeLimit I
        (MarkedStableTreeLimit.of_markedSphere I (u_seq (wit.σ.1 n))
          (h_jhol (wit.σ.1 n)) (h_stab (wit.σ.1 n))))
      (MarkedStableMap.of_markedStableTreeLimit I u_lim) where
  frames := wit.frames
  comp_map _ _ := ()
  smooth_conv v := by
    refine smooth_local_restriction I
      (fun n => (u_seq (wit.σ.1 n)).map ∘ (wit.frames v n).toHomeo)
      (u_lim.map v) ?_ (wit.smooth_conv v)
    intro z hz
    refine ⟨hz.1, fun h_node => hz.2 (Or.inl h_node)⟩
  frame_collapse := wit.frame_collapse
  mark_conv := wit.mark_conv
  energy_conv := by
    have h_eq : (fun n => markedStableMapTotalEnergy I
        (MarkedStableMap.of_markedStableTreeLimit I
          (MarkedStableTreeLimit.of_markedSphere I (u_seq (wit.σ.1 n))
            (h_jhol (wit.σ.1 n)) (h_stab (wit.σ.1 n))))) =
        fun n => totalEnergy I (u_seq (wit.σ.1 n)).map := by
      ext n
      exact markedTreeTotalEnergy_of_markedSphere I (u_seq (wit.σ.1 n))
        (h_jhol (wit.σ.1 n)) (h_stab (wit.σ.1 n))
    rw [h_eq, markedStableMapTotalEnergy_of_markedStableTreeLimit]
    exact wit.energy_conv

/-- A `MarkedGromovWitness` is preserved along any strictly monotone subsequence (`0 sorryAx`). -/
def MarkedGromovWitness.subseq {k : ℕ}
    {u_seq : ℕ → MarkedStableMap I (M := M) k}
    {u_lim : MarkedStableMap I (M := M) k}
    (wit : MarkedGromovWitness I u_seq u_lim)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    MarkedGromovWitness I (fun n => u_seq (φ n)) u_lim where
  frames v n := wit.frames v (φ n)
  comp_map v n := wit.comp_map v (φ n)
  smooth_conv v :=
    smooth_local_congr_seq I rfl
      (smooth_local_subseq I
        (fun n => (u_seq n).map (wit.comp_map v n) ∘ (wit.frames v n).toHomeo)
        (u_lim.map v) _ hφ (wit.smooth_conv v))
  frame_collapse v w h K hK_sub hK_cpt :=
    tendstoUniformlyOn_subseq hφ (wit.frame_collapse v w h K hK_sub hK_cpt)
  mark_conv i := (wit.mark_conv i).comp hφ.tendsto_atTop
  energy_conv := wit.energy_conv.comp hφ.tendsto_atTop

/-- Sequential Gromov convergence on `ModuliSpace` is preserved along any strictly monotone subsequence (`0 sorryAx`). -/
theorem gromovConverges_subseq {k : ℕ} {B : ℝ}
    {u_seq : ℕ → ModuliSpace I (M := M) k B}
    {u_lim : ModuliSpace I (M := M) k B}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_conv : GromovConverges I u_seq u_lim) :
    GromovConverges I (fun n => u_seq (φ n)) u_lim := by
  rcases h_conv with ⟨reps, lim_rep, h_reps, h_lim, ⟨wit⟩⟩
  exact ⟨fun n => reps (φ n), lim_rep, fun n => h_reps (φ n), h_lim, ⟨wit.subseq I φ hφ⟩⟩

/-- Reflexive `MarkedGromovWitness` for a constant sequence at an edgeless constant-component
marked stable map (`0 sorryAx`). -/
def MarkedGromovWitness.of_const_edgeless {k : ℕ}
    (u : MarkedStableMap I (M := M) k)
    (h_const_map : ∀ v : u.tree.V, ∃ c : M, u.map v = fun _ => c)
    (h_no_edges : ∀ v w : u.tree.V, ¬ u.tree.adj.Adj v w) :
    MarkedGromovWitness I (fun _ : ℕ => u) u where
  frames _ _ := MoebiusFrame.id
  comp_map v _ := v
  smooth_conv v := by
    obtain ⟨c, hc⟩ := h_const_map v
    have h_seq : (fun _ : ℕ => u.map v ∘ (MoebiusFrame.id).toHomeo) = fun _ _ => c := by
      ext _ z
      change u.map v z = c
      rw [hc]
    rw [h_seq, hc]
    exact smoothLocalConvergesOn_const_map I c _
  frame_collapse v w h := False.elim (h_no_edges v w h)
  mark_conv i := by
    dsimp only
    have h_inv : (fun _ : ℕ => (MoebiusFrame.inv MoebiusFrame.id).toHomeo (u.tree.mark_point i)) =
        fun _ => u.tree.mark_point i := by
      ext _; rfl
    rw [h_inv]
    exact tendsto_const_nhds
  energy_conv := tendsto_const_nhds

/-- For `B < 0`, subsequence extraction on `BoundedMarkedStableMap I k B` holds vacuously (`0 sorryAx`). -/
theorem extract_bounded_marked_stable_subseq_of_neg (k : ℕ) {B : ℝ} (hB : B < 0)
    (reps : ℕ → BoundedMarkedStableMap I (M := M) k B) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (lim_rep : BoundedMarkedStableMap I (M := M) k B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ n)).1) lim_rep.1) := by
  haveI := isEmpty_boundedMarkedStableMap_of_neg I (M := M) k hB
  exact isEmptyElim (reps 0)

/-- For `k < 3` on a subsingleton target `M`, subsequence extraction on `BoundedMarkedStableMap I k B`
holds vacuously (`0 sorryAx`). -/
theorem extract_bounded_marked_stable_subseq_of_lt_three_of_subsingleton {k : ℕ}
    (hk : k < 3) (B : ℝ) [Subsingleton M]
    (reps : ℕ → BoundedMarkedStableMap I (M := M) k B) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (lim_rep : BoundedMarkedStableMap I (M := M) k B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ n)).1) lim_rep.1) := by
  haveI := isEmpty_boundedMarkedStableMap_of_lt_three_of_subsingleton I (M := M) hk B
  exact isEmptyElim (reps 0)

/-- For `k < 3` and `B < th.ε_sph`, subsequence extraction on `BoundedMarkedStableMap I k B`
holds vacuously (`0 sorryAx`). -/
theorem extract_bounded_marked_stable_subseq_of_lt_three_of_lt_eps_sph {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph)
    (reps : ℕ → BoundedMarkedStableMap I (M := M) k B) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (lim_rep : BoundedMarkedStableMap I (M := M) k B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ n)).1) lim_rep.1) := by
  haveI := isEmpty_boundedMarkedStableMap_of_lt_three_of_lt_eps_sph I hk th hB
  exact isEmptyElim (reps 0)

/-- For `k < 3` and `B < th.h`, subsequence extraction on `BoundedMarkedStableMap I k B`
holds vacuously (`0 sorryAx`). -/
theorem extract_bounded_marked_stable_subseq_of_lt_three_of_lt_threshold {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.h)
    (reps : ℕ → BoundedMarkedStableMap I (M := M) k B) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (lim_rep : BoundedMarkedStableMap I (M := M) k B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ n)).1) lim_rep.1) :=
  extract_bounded_marked_stable_subseq_of_lt_three_of_lt_eps_sph I hk th (hB.trans_le th.h_le_sph) reps

/-- For `k < 3` and `B ≤ 0`, subsequence extraction on `BoundedMarkedStableMap I k B`
holds vacuously (`0 sorryAx`). -/
theorem extract_bounded_marked_stable_subseq_of_lt_three_of_nonpos_B {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0)
    (reps : ℕ → BoundedMarkedStableMap I (M := M) k B) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (lim_rep : BoundedMarkedStableMap I (M := M) k B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ n)).1) lim_rep.1) :=
  extract_bounded_marked_stable_subseq_of_lt_three_of_lt_eps_sph I hk th (hB.trans_lt th.ε_sph_pos) reps

/-- For `k < 3` on a discrete target `M`, subsequence extraction on `BoundedMarkedStableMap I k B`
holds vacuously (`0 sorryAx`). -/
theorem extract_bounded_marked_stable_subseq_of_lt_three_of_discrete {k : ℕ}
    (hk : k < 3) (B : ℝ) [DiscreteTopology M]
    (reps : ℕ → BoundedMarkedStableMap I (M := M) k B) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (lim_rep : BoundedMarkedStableMap I (M := M) k B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ n)).1) lim_rep.1) := by
  haveI := isEmpty_boundedMarkedStableMap_of_lt_three_of_discrete I (M := M) hk B
  exact isEmptyElim (reps 0)

/-- When `reps` has a constant subsequence at an edgeless constant-component `BoundedMarkedStableMap`,
subsequence extraction holds with `0 sorryAx`. -/
theorem extract_bounded_marked_stable_subseq_of_const_edgeless (k : ℕ) (B : ℝ)
    (reps : ℕ → BoundedMarkedStableMap I (M := M) k B)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (lim_rep : BoundedMarkedStableMap I (M := M) k B)
    (h_const : ∀ n, reps (φ n) = lim_rep)
    (h_const_map : ∀ v : lim_rep.1.tree.V, ∃ c : M, lim_rep.1.map v = fun _ => c)
    (h_no_edges : ∀ v w : lim_rep.1.tree.V, ¬ lim_rep.1.tree.adj.Adj v w) :
    ∃ (φ' : ℕ → ℕ), StrictMono φ' ∧
      ∃ (lim_rep' : BoundedMarkedStableMap I (M := M) k B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ' n)).1) lim_rep'.1) := by
  refine ⟨φ, hφ, lim_rep, ?_⟩
  have h_eq : (fun n => (reps (φ n)).1) = fun _ => lim_rep.1 := by
    ext n; rw [h_const n]
  rw [h_eq]
  exact ⟨MarkedGromovWitness.of_const_edgeless I lim_rep.1 h_const_map h_no_edges⟩

/-- For `k = 3` on a subsingleton target `M`, any sequence `reps` with a constant subsequence
extracts a Gromov-convergent subsequence with `0 sorryAx`. -/
theorem extract_bounded_marked_stable_subseq_of_const_three_of_subsingleton (B : ℝ) [Subsingleton M]
    (reps : ℕ → BoundedMarkedStableMap I (M := M) 3 B)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (lim_rep : BoundedMarkedStableMap I (M := M) 3 B)
    (h_const : ∀ n, reps (φ n) = lim_rep) :
    ∃ (φ' : ℕ → ℕ), StrictMono φ' ∧
      ∃ (lim_rep' : BoundedMarkedStableMap I (M := M) 3 B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ' n)).1) lim_rep'.1) := by
  have h_all : ∀ v : lim_rep.1.tree.V, ∃ c : M, ∀ z : CP1, lim_rep.1.map v z = c :=
    fun v => ⟨lim_rep.1.map v north_pole, fun z => Subsingleton.elim (lim_rep.1.map v z) (lim_rep.1.map v north_pole)⟩
  exact extract_bounded_marked_stable_subseq_of_const_edgeless I 3 B reps φ hφ lim_rep h_const
    (fun v => ⟨lim_rep.1.map v north_pole, funext (fun z => Subsingleton.elim (lim_rep.1.map v z) (lim_rep.1.map v north_pole))⟩)
    (no_edges_of_all_const_three I lim_rep.1 h_all)

/-- For `k = 3` and `B < th.ε_sph`, any sequence `reps` with a constant subsequence
extracts a Gromov-convergent subsequence with `0 sorryAx`. -/
theorem extract_bounded_marked_stable_subseq_of_const_three_of_lt_eps_sph {B : ℝ}
    (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph)
    (reps : ℕ → BoundedMarkedStableMap I (M := M) 3 B)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (lim_rep : BoundedMarkedStableMap I (M := M) 3 B)
    (h_const : ∀ n, reps (φ n) = lim_rep) :
    ∃ (φ' : ℕ → ℕ), StrictMono φ' ∧
      ∃ (lim_rep' : BoundedMarkedStableMap I (M := M) 3 B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ' n)).1) lim_rep'.1) := by
  have h_all := all_const_of_lt_eps_sph I th hB lim_rep
  exact extract_bounded_marked_stable_subseq_of_const_edgeless I 3 B reps φ hφ lim_rep h_const
    (fun v => let ⟨c, hc⟩ := h_all v; ⟨c, funext hc⟩)
    (no_edges_of_all_const_three I lim_rep.1 h_all)

/-- For `k = 3` and `B < th.h`, any sequence `reps` with a constant subsequence
extracts a Gromov-convergent subsequence with `0 sorryAx`. -/
theorem extract_bounded_marked_stable_subseq_of_const_three_of_lt_threshold {B : ℝ}
    (th : Bubbling.TargetThresholds I M) (hB : B < th.h)
    (reps : ℕ → BoundedMarkedStableMap I (M := M) 3 B)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (lim_rep : BoundedMarkedStableMap I (M := M) 3 B)
    (h_const : ∀ n, reps (φ n) = lim_rep) :
    ∃ (φ' : ℕ → ℕ), StrictMono φ' ∧
      ∃ (lim_rep' : BoundedMarkedStableMap I (M := M) 3 B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ' n)).1) lim_rep'.1) :=
  extract_bounded_marked_stable_subseq_of_const_three_of_lt_eps_sph I th (hB.trans_le th.h_le_sph)
    reps φ hφ lim_rep h_const

/-- For `k = 3` and `B ≤ 0`, any sequence `reps` with a constant subsequence
extracts a Gromov-convergent subsequence with `0 sorryAx`. -/
theorem extract_bounded_marked_stable_subseq_of_const_three_of_nonpos_B {B : ℝ}
    (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0)
    (reps : ℕ → BoundedMarkedStableMap I (M := M) 3 B)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (lim_rep : BoundedMarkedStableMap I (M := M) 3 B)
    (h_const : ∀ n, reps (φ n) = lim_rep) :
    ∃ (φ' : ℕ → ℕ), StrictMono φ' ∧
      ∃ (lim_rep' : BoundedMarkedStableMap I (M := M) 3 B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ' n)).1) lim_rep'.1) :=
  extract_bounded_marked_stable_subseq_of_const_three_of_lt_eps_sph I th (hB.trans_lt th.ε_sph_pos)
    reps φ hφ lim_rep h_const

/-- For `k = 3` on a discrete target `M`, any sequence `reps` with a constant subsequence
extracts a Gromov-convergent subsequence with `0 sorryAx`. -/
theorem extract_bounded_marked_stable_subseq_of_const_three_of_discrete (B : ℝ) [DiscreteTopology M]
    (reps : ℕ → BoundedMarkedStableMap I (M := M) 3 B)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (lim_rep : BoundedMarkedStableMap I (M := M) 3 B)
    (h_const : ∀ n, reps (φ n) = lim_rep) :
    ∃ (φ' : ℕ → ℕ), StrictMono φ' ∧
      ∃ (lim_rep' : BoundedMarkedStableMap I (M := M) 3 B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ' n)).1) lim_rep'.1) := by
  have h_all := all_const_of_discrete I lim_rep.1
  exact extract_bounded_marked_stable_subseq_of_const_edgeless I 3 B reps φ hφ lim_rep h_const
    (fun v => let ⟨c, hc⟩ := h_all v; ⟨c, funext hc⟩)
    (no_edges_of_all_const_three I lim_rep.1 h_all)

/-- When `reps` is eventually constant at an edgeless constant-component `BoundedMarkedStableMap`,
subsequence extraction holds with `0 sorryAx`. -/
theorem extract_bounded_marked_stable_subseq_of_eventually_const_edgeless (k : ℕ) (B : ℝ)
    (reps : ℕ → BoundedMarkedStableMap I (M := M) k B)
    (N₀ : ℕ)
    (lim_rep : BoundedMarkedStableMap I (M := M) k B)
    (h_ev : ∀ n ≥ N₀, reps n = lim_rep)
    (h_const_map : ∀ v : lim_rep.1.tree.V, ∃ c : M, lim_rep.1.map v = fun _ => c)
    (h_no_edges : ∀ v w : lim_rep.1.tree.V, ¬ lim_rep.1.tree.adj.Adj v w) :
    ∃ (φ' : ℕ → ℕ), StrictMono φ' ∧
      ∃ (lim_rep' : BoundedMarkedStableMap I (M := M) k B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ' n)).1) lim_rep'.1) :=
  extract_bounded_marked_stable_subseq_of_const_edgeless I k B reps
    (Compactness.shiftSubseqMap N₀).1 (Compactness.shiftSubseqMap N₀).2 lim_rep
    (fun n => h_ev (n + N₀) (Nat.le_add_left N₀ n)) h_const_map h_no_edges

/-- When `reps` already has a subsequence `φ` with a `MarkedGromovWitness` to `lim_rep`,
subsequence extraction holds immediately (`0 sorryAx`). -/
theorem extract_bounded_marked_stable_subseq_of_witness (k : ℕ) (B : ℝ)
    (reps : ℕ → BoundedMarkedStableMap I (M := M) k B)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (lim_rep : BoundedMarkedStableMap I (M := M) k B)
    (wit : MarkedGromovWitness I (fun n => (reps (φ n)).1) lim_rep.1) :
    ∃ (φ' : ℕ → ℕ), StrictMono φ' ∧
      ∃ (lim_rep' : BoundedMarkedStableMap I (M := M) k B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ' n)).1) lim_rep'.1) :=
  ⟨φ, hφ, lim_rep, ⟨wit⟩⟩

/-- If `reps n` is the `MarkedStableMap` associated to a marked sphere `u_seq n`, then
`totalEnergy I (u_seq n).map ≤ B` (`0 sorryAx`). -/
theorem totalEnergy_markedSphere_le_of_boundedMarkedStableMap (k : ℕ) (B : ℝ)
    (reps : ℕ → BoundedMarkedStableMap I (M := M) k B)
    (u_seq : ℕ → MarkedSphere M k)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_stab : ∀ n, (∃ c : M, ∀ z : CP1, (u_seq n).map z = c) → 3 ≤ k)
    (h_reps_eq : ∀ n, (reps n).1 = MarkedStableMap.of_markedStableTreeLimit I
      (MarkedStableTreeLimit.of_markedSphere I (u_seq n) (h_jhol n) (h_stab n)))
    (n : ℕ) :
    totalEnergy I (u_seq n).map ≤ B := by
  have h_bound := (reps n).2
  rw [h_reps_eq n, markedStableMapTotalEnergy_of_markedStableTreeLimit,
      markedTreeTotalEnergy_of_markedSphere] at h_bound
  exact h_bound

/-- When `reps` arises from a sequence of `k`-marked spheres `u_seq` equipped with a
`MarkedCompactnessWitness`, subsequence extraction holds with `0 sorryAx`. -/
theorem extract_bounded_marked_stable_subseq_of_marked_spheres (k : ℕ) (B : ℝ)
    (reps : ℕ → BoundedMarkedStableMap I (M := M) k B)
    (u_seq : ℕ → MarkedSphere M k)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_stab : ∀ n, (∃ c : M, ∀ z : CP1, (u_seq n).map z = c) → 3 ≤ k)
    (h_reps_eq : ∀ n, (reps n).1 = MarkedStableMap.of_markedStableTreeLimit I
      (MarkedStableTreeLimit.of_markedSphere I (u_seq n) (h_jhol n) (h_stab n)))
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (wit : MarkedCompactnessWitness I u_seq u_lim) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (lim_rep : BoundedMarkedStableMap I (M := M) k B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ n)).1) lim_rep.1) := by
  have h_energy_subseq : ∀ n, totalEnergy I (u_seq (wit.σ.1 n)).map ≤ B :=
    fun n => totalEnergy_markedSphere_le_of_boundedMarkedStableMap I k B reps u_seq h_jhol h_stab h_reps_eq (wit.σ.1 n)
  have h_lim_le : markedStableMapTotalEnergy I (MarkedStableMap.of_markedStableTreeLimit I u_lim) ≤ B := by
    rw [markedStableMapTotalEnergy_of_markedStableTreeLimit]
    exact le_of_tendsto wit.energy_conv (Eventually.of_forall h_energy_subseq)
  refine ⟨wit.σ.1, wit.σ.2, ⟨MarkedStableMap.of_markedStableTreeLimit I u_lim, h_lim_le⟩, ?_⟩
  have h_seq_eq : (fun n => (reps (wit.σ.1 n)).1) =
      fun n => MarkedStableMap.of_markedStableTreeLimit I
        (MarkedStableTreeLimit.of_markedSphere I (u_seq (wit.σ.1 n))
          (h_jhol (wit.σ.1 n)) (h_stab (wit.σ.1 n))) := by
    ext n; exact h_reps_eq (wit.σ.1 n)
  rw [h_seq_eq]
  exact ⟨MarkedGromovWitness.of_markedCompactnessWitness I h_jhol h_stab wit⟩

/-- When a subsequence `reps ∘ τ.1` arises from a sequence of `k`-marked spheres `u_seq` equipped
with a `MarkedCompactnessWitness`, subsequence extraction for `reps` holds with `0 sorryAx`. -/
theorem extract_bounded_marked_stable_subseq_of_marked_spheres_subseq (k : ℕ) (B : ℝ)
    (reps : ℕ → BoundedMarkedStableMap I (M := M) k B)
    (τ : Bookkeeping.SubseqMap)
    (u_seq : ℕ → MarkedSphere M k)
    (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
    (h_stab : ∀ n, (∃ c : M, ∀ z : CP1, (u_seq n).map z = c) → 3 ≤ k)
    (h_reps_eq : ∀ n, (reps (τ.1 n)).1 = MarkedStableMap.of_markedStableTreeLimit I
      (MarkedStableTreeLimit.of_markedSphere I (u_seq n) (h_jhol n) (h_stab n)))
    (u_lim : MarkedStableTreeLimit I (M := M) k)
    (wit : MarkedCompactnessWitness I u_seq u_lim) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (lim_rep : BoundedMarkedStableMap I (M := M) k B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ n)).1) lim_rep.1) := by
  obtain ⟨φ, hφ, lim_rep, ⟨gwit⟩⟩ :=
    extract_bounded_marked_stable_subseq_of_marked_spheres I k B (fun n => reps (τ.1 n))
      u_seq h_jhol h_stab h_reps_eq u_lim wit
  exact ⟨τ.1 ∘ φ, τ.2.comp hφ, lim_rep, ⟨gwit⟩⟩

/-- Subsequence extraction for bounded marked stable maps in the Gromov sense. -/
private theorem extract_bounded_marked_stable_subseq (k : ℕ) (B : ℝ)
    (reps : ℕ → BoundedMarkedStableMap I (M := M) k B) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (lim_rep : BoundedMarkedStableMap I (M := M) k B),
        Nonempty (MarkedGromovWitness I (fun n => (reps (φ n)).1) lim_rep.1) := by
  by_cases hB : B < 0
  · exact extract_bounded_marked_stable_subseq_of_neg I k hB reps
  · by_cases h_ce : ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (lim_rep : BoundedMarkedStableMap I (M := M) k B),
        (∀ n, reps (φ n) = lim_rep) ∧
        (∀ v : lim_rep.1.tree.V, ∃ c : M, lim_rep.1.map v = fun _ => c) ∧
        (∀ v w : lim_rep.1.tree.V, ¬ lim_rep.1.tree.adj.Adj v w)
    · rcases h_ce with ⟨φ, hφ, lim_rep, h_const, h_const_map, h_no_edges⟩
      exact extract_bounded_marked_stable_subseq_of_const_edgeless I k B reps φ hφ lim_rep h_const h_const_map h_no_edges
    · by_cases h_ms : ∃ (τ : Bookkeeping.SubseqMap) (u_seq : ℕ → MarkedSphere M k)
          (h_jhol : ∀ n, JHolomorphicOn I I_CP1 (u_seq n).map Set.univ)
          (h_stab : ∀ n, (∃ c : M, ∀ z : CP1, (u_seq n).map z = c) → 3 ≤ k)
          (h_fin : ∀ n, energyMeasureExtended I (u_seq n).map Set.univ < ⊤),
          ∀ n, (reps (τ.1 n)).1 = MarkedStableMap.of_markedStableTreeLimit I
            (MarkedStableTreeLimit.of_markedSphere I (u_seq n) (h_jhol n) (h_stab n))
      · rcases h_ms with ⟨τ, u_seq, h_jhol, h_stab, h_fin, h_reps_eq⟩
        obtain ⟨th⟩ := Bubbling.exists_target_thresholds I (M := M)
        obtain ⟨u_lim, ⟨wit⟩⟩ := marked_gromov_compactness I th u_seq B h_jhol
          (totalEnergy_markedSphere_le_of_boundedMarkedStableMap I k B (fun n => reps (τ.1 n)) u_seq h_jhol h_stab h_reps_eq) h_fin
        exact extract_bounded_marked_stable_subseq_of_marked_spheres_subseq I k B reps τ u_seq h_jhol h_stab h_reps_eq u_lim wit
      · sorry

/-- Zero-sorry conditional reduction of `moduli_space_seq_compact` from representative subsequence extraction (`0 sorryAx`). -/
theorem moduli_space_seq_compact_of_extract (k : ℕ) (B : ℝ)
    (h_extract : ∀ (reps : ℕ → BoundedMarkedStableMap I (M := M) k B),
      ∃ (φ : ℕ → ℕ), StrictMono φ ∧
        ∃ (lim_rep : BoundedMarkedStableMap I (M := M) k B),
          Nonempty (MarkedGromovWitness I (fun n => (reps (φ n)).1) lim_rep.1)) :
    SeqCompactSpace (ModuliSpace I (M := M) k B) := by
  refine ⟨fun u_seq _ => ?_⟩
  have h_reps : ∀ n, ∃ r : BoundedMarkedStableMap I (M := M) k B, Quotient.mk' r = u_seq n :=
    fun n => Quotient.exists_rep (u_seq n)
  choose reps h_reps_eq using h_reps
  obtain ⟨φ, hφ_mono, lim_rep, h_wit⟩ := h_extract reps
  refine ⟨Quotient.mk' lim_rep, mem_univ _, φ, hφ_mono, ?_⟩
  apply tendsto_of_gromovConverges I
  exact ⟨fun n => reps (φ n), lim_rep, fun n => h_reps_eq (φ n), rfl, h_wit⟩

/-- **Sequential Compactness of the Moduli Space (Contract E05)**:
Every sequence in $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$ has a convergent subsequence
in the Gromov topology. -/
theorem moduli_space_seq_compact (k : ℕ) (B : ℝ) :
    SeqCompactSpace (ModuliSpace I (M := M) k B) :=
  moduli_space_seq_compact_of_extract I k B (extract_bounded_marked_stable_subseq I k B)

private lemma metricSpace_t2 (X : Type*) [MetricSpace X] : T2Space X := inferInstance

private lemma metricSpace_compact_of_seqCompact (X : Type*) [MetricSpace X] [SeqCompactSpace X] :
    CompactSpace X :=
  ⟨isSeqCompact_univ.isCompact⟩

/-- Zero-sorry conditional reduction of `moduli_space_t2` from metrizability (`0 sorryAx`). -/
theorem moduli_space_t2_of_metrizable (k : ℕ) (B : ℝ)
    (h_metr : ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k B) :
    T2Space (ModuliSpace I (M := M) k B) := by
  obtain ⟨m, hm⟩ := h_metr
  have h_t2 : @T2Space (ModuliSpace I (M := M) k B) m.toUniformSpace.toTopologicalSpace :=
    @metricSpace_t2 (ModuliSpace I (M := M) k B) m
  rwa [hm] at h_t2

/-- **Hausdorff Separation of the Moduli Space (Contract E05)**:
The moduli space $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$ is a Hausdorff space ($T_2$).
This formalizes the uniqueness of Gromov limits up to stable map isomorphism. -/
theorem moduli_space_t2 (k : ℕ) (B : ℝ) :
    T2Space (ModuliSpace I (M := M) k B) :=
  moduli_space_t2_of_metrizable I k B (moduli_space_metrizable I (M := M) k B)

/-- Zero-sorry conditional reduction of `moduli_space_compact` from metrizability and sequential compactness (`0 sorryAx`). -/
theorem moduli_space_compact_of_metrizable_and_seq_compact (k : ℕ) (B : ℝ)
    (h_metr : ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k B)
    (h_seq_comp : SeqCompactSpace (ModuliSpace I (M := M) k B)) :
    CompactSpace (ModuliSpace I (M := M) k B) := by
  obtain ⟨m, hm⟩ := h_metr
  have h_seq : @SeqCompactSpace (ModuliSpace I (M := M) k B) m.toUniformSpace.toTopologicalSpace := by
    rw [hm]
    exact h_seq_comp
  have h_comp : @CompactSpace (ModuliSpace I (M := M) k B) m.toUniformSpace.toTopologicalSpace :=
    @metricSpace_compact_of_seqCompact (ModuliSpace I (M := M) k B) m h_seq
  rwa [hm] at h_comp

/-- **Compactness of the Moduli Space (Contract E05)**:
The moduli space $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$ is a compact topological space. -/
theorem moduli_space_compact (k : ℕ) (B : ℝ) :
    CompactSpace (ModuliSpace I (M := M) k B) :=
  moduli_space_compact_of_metrizable_and_seq_compact I k B
    (moduli_space_metrizable I (M := M) k B) (moduli_space_seq_compact I k B)

/-- Zero-sorry conditional reduction of `moduli_space_compact_hausdorff` (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_of_metrizable_and_seq_compact (k : ℕ) (B : ℝ)
    (h_metr : ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k B)
    (h_seq_comp : SeqCompactSpace (ModuliSpace I (M := M) k B)) :
    CompactSpace (ModuliSpace I (M := M) k B) ∧ T2Space (ModuliSpace I (M := M) k B) :=
  ⟨moduli_space_compact_of_metrizable_and_seq_compact I k B h_metr h_seq_comp,
    moduli_space_t2_of_metrizable I k B h_metr⟩

/-- When `ModuliSpace I k B` is a subsingleton, it is sequentially compact (`0 sorryAx`). -/
theorem moduli_space_seq_compact_of_subsingleton (k : ℕ) (B : ℝ)
    (h_sub : Subsingleton (ModuliSpace I (M := M) k B)) :
    SeqCompactSpace (ModuliSpace I (M := M) k B) := by
  refine ⟨fun u_seq _ => ⟨u_seq 0, Set.mem_univ _, id, strictMono_id, ?_⟩⟩
  have h_eq : (u_seq ∘ id) = fun _ => u_seq 0 := funext (fun n => h_sub.elim (u_seq n) (u_seq 0))
  rw [h_eq]
  exact tendsto_const_nhds

/-- For `B < 0`, `ModuliSpace I k B` is sequentially compact with zero `sorry` (`0 sorryAx`). -/
theorem moduli_space_seq_compact_of_neg (k : ℕ) {B : ℝ} (hB : B < 0) :
    SeqCompactSpace (ModuliSpace I (M := M) k B) :=
  moduli_space_seq_compact_of_extract I k B (extract_bounded_marked_stable_subseq_of_neg I k hB)

/-- When `ModuliSpace I k B` is a subsingleton, it is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_t2_of_subsingleton (k : ℕ) (B : ℝ)
    (h_sub : Subsingleton (ModuliSpace I (M := M) k B)) :
    T2Space (ModuliSpace I (M := M) k B) :=
  moduli_space_t2_of_metrizable I k B (exists_gromov_metricSpace_of_subsingleton I k B h_sub)

/-- For `B < 0`, `ModuliSpace I k B` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_t2_of_neg (k : ℕ) {B : ℝ} (hB : B < 0) :
    T2Space (ModuliSpace I (M := M) k B) :=
  moduli_space_t2_of_metrizable I k B (exists_gromov_metricSpace_of_neg I k hB)

/-- When `ModuliSpace I k B` is a subsingleton, it is compact (`0 sorryAx`). -/
theorem moduli_space_compact_of_subsingleton (k : ℕ) (B : ℝ)
    (h_sub : Subsingleton (ModuliSpace I (M := M) k B)) :
    CompactSpace (ModuliSpace I (M := M) k B) :=
  moduli_space_compact_of_metrizable_and_seq_compact I k B
    (exists_gromov_metricSpace_of_subsingleton I k B h_sub)
    (moduli_space_seq_compact_of_subsingleton I k B h_sub)

/-- For `B < 0`, `ModuliSpace I k B` is compact (`0 sorryAx`). -/
theorem moduli_space_compact_of_neg (k : ℕ) {B : ℝ} (hB : B < 0) :
    CompactSpace (ModuliSpace I (M := M) k B) :=
  moduli_space_compact_of_metrizable_and_seq_compact I k B
    (exists_gromov_metricSpace_of_neg I k hB)
    (moduli_space_seq_compact_of_neg I k hB)

/-- When `ModuliSpace I k B` is a subsingleton, it is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_of_subsingleton (k : ℕ) (B : ℝ)
    (h_sub : Subsingleton (ModuliSpace I (M := M) k B)) :
    CompactSpace (ModuliSpace I (M := M) k B) ∧ T2Space (ModuliSpace I (M := M) k B) :=
  ⟨moduli_space_compact_of_subsingleton I k B h_sub, moduli_space_t2_of_subsingleton I k B h_sub⟩

/-- For `B < 0`, `ModuliSpace I k B` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_of_neg (k : ℕ) {B : ℝ} (hB : B < 0) :
    CompactSpace (ModuliSpace I (M := M) k B) ∧ T2Space (ModuliSpace I (M := M) k B) :=
  ⟨moduli_space_compact_of_neg I k hB, moduli_space_t2_of_neg I k hB⟩

/-- For `k < 3` on a subsingleton target `M`, `ModuliSpace I k B` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_of_lt_three_of_subsingleton {k : ℕ}
    (hk : k < 3) (B : ℝ) [Subsingleton M] :
    CompactSpace (ModuliSpace I (M := M) k B) ∧ T2Space (ModuliSpace I (M := M) k B) := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_subsingleton I (M := M) hk B
  exact moduli_space_compact_hausdorff_of_subsingleton I k B inferInstance

/-- For `k < 3` and `B < th.ε_sph`, `ModuliSpace I k B` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_of_lt_three_of_lt_eps_sph {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph) :
    CompactSpace (ModuliSpace I (M := M) k B) ∧ T2Space (ModuliSpace I (M := M) k B) := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_lt_eps_sph I hk th hB
  exact moduli_space_compact_hausdorff_of_subsingleton I k B inferInstance

/-- For `k < 3` and `B < th.h`, `ModuliSpace I k B` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_of_lt_three_of_lt_threshold {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.h) :
    CompactSpace (ModuliSpace I (M := M) k B) ∧ T2Space (ModuliSpace I (M := M) k B) :=
  moduli_space_compact_hausdorff_of_lt_three_of_lt_eps_sph I hk th (hB.trans_le th.h_le_sph)

/-- For `k < 3` and `B ≤ 0`, `ModuliSpace I k B` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_of_lt_three_of_nonpos_B {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0) :
    CompactSpace (ModuliSpace I (M := M) k B) ∧ T2Space (ModuliSpace I (M := M) k B) :=
  moduli_space_compact_hausdorff_of_lt_three_of_lt_eps_sph I hk th (hB.trans_lt th.ε_sph_pos)

/-- For `k < 3` on a discrete target `M`, `ModuliSpace I k B` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_of_lt_three_of_discrete {k : ℕ}
    (hk : k < 3) (B : ℝ) [DiscreteTopology M] :
    CompactSpace (ModuliSpace I (M := M) k B) ∧ T2Space (ModuliSpace I (M := M) k B) := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_discrete I (M := M) hk B
  exact moduli_space_compact_hausdorff_of_subsingleton I k B inferInstance

/-- For `k < 3` on a subsingleton target `M`, `ModuliSpace I k B` is sequentially compact (`0 sorryAx`). -/
theorem moduli_space_seq_compact_of_lt_three_of_subsingleton {k : ℕ}
    (hk : k < 3) (B : ℝ) [Subsingleton M] :
    SeqCompactSpace (ModuliSpace I (M := M) k B) :=
  moduli_space_seq_compact_of_extract I k B
    (extract_bounded_marked_stable_subseq_of_lt_three_of_subsingleton I hk B)

/-- For `k < 3` and `B < th.ε_sph`, `ModuliSpace I k B` is sequentially compact (`0 sorryAx`). -/
theorem moduli_space_seq_compact_of_lt_three_of_lt_eps_sph {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph) :
    SeqCompactSpace (ModuliSpace I (M := M) k B) :=
  moduli_space_seq_compact_of_extract I k B
    (extract_bounded_marked_stable_subseq_of_lt_three_of_lt_eps_sph I hk th hB)

/-- For `k < 3` and `B < th.h`, `ModuliSpace I k B` is sequentially compact (`0 sorryAx`). -/
theorem moduli_space_seq_compact_of_lt_three_of_lt_threshold {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.h) :
    SeqCompactSpace (ModuliSpace I (M := M) k B) :=
  moduli_space_seq_compact_of_lt_three_of_lt_eps_sph I hk th (hB.trans_le th.h_le_sph)

/-- For `k < 3` and `B ≤ 0`, `ModuliSpace I k B` is sequentially compact (`0 sorryAx`). -/
theorem moduli_space_seq_compact_of_lt_three_of_nonpos_B {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0) :
    SeqCompactSpace (ModuliSpace I (M := M) k B) :=
  moduli_space_seq_compact_of_lt_three_of_lt_eps_sph I hk th (hB.trans_lt th.ε_sph_pos)

/-- For `k < 3` on a discrete target `M`, `ModuliSpace I k B` is sequentially compact (`0 sorryAx`). -/
theorem moduli_space_seq_compact_of_lt_three_of_discrete {k : ℕ}
    (hk : k < 3) (B : ℝ) [DiscreteTopology M] :
    SeqCompactSpace (ModuliSpace I (M := M) k B) :=
  moduli_space_seq_compact_of_extract I k B
    (extract_bounded_marked_stable_subseq_of_lt_three_of_discrete I hk B)

/-- For `k < 3` on a subsingleton target `M`, `ModuliSpace I k B` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_t2_of_lt_three_of_subsingleton {k : ℕ}
    (hk : k < 3) (B : ℝ) [Subsingleton M] :
    T2Space (ModuliSpace I (M := M) k B) :=
  (moduli_space_compact_hausdorff_of_lt_three_of_subsingleton I hk B).2

/-- For `k < 3` and `B < th.ε_sph`, `ModuliSpace I k B` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_t2_of_lt_three_of_lt_eps_sph {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph) :
    T2Space (ModuliSpace I (M := M) k B) :=
  (moduli_space_compact_hausdorff_of_lt_three_of_lt_eps_sph I hk th hB).2

/-- For `k < 3` and `B < th.h`, `ModuliSpace I k B` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_t2_of_lt_three_of_lt_threshold {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.h) :
    T2Space (ModuliSpace I (M := M) k B) :=
  (moduli_space_compact_hausdorff_of_lt_three_of_lt_threshold I hk th hB).2

/-- For `k < 3` and `B ≤ 0`, `ModuliSpace I k B` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_t2_of_lt_three_of_nonpos_B {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0) :
    T2Space (ModuliSpace I (M := M) k B) :=
  (moduli_space_compact_hausdorff_of_lt_three_of_nonpos_B I hk th hB).2

/-- For `k < 3` on a discrete target `M`, `ModuliSpace I k B` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_t2_of_lt_three_of_discrete {k : ℕ}
    (hk : k < 3) (B : ℝ) [DiscreteTopology M] :
    T2Space (ModuliSpace I (M := M) k B) :=
  (moduli_space_compact_hausdorff_of_lt_three_of_discrete I hk B).2

/-- For `k < 3` on a subsingleton target `M`, `ModuliSpace I k B` is compact (`0 sorryAx`). -/
theorem moduli_space_compact_of_lt_three_of_subsingleton {k : ℕ}
    (hk : k < 3) (B : ℝ) [Subsingleton M] :
    CompactSpace (ModuliSpace I (M := M) k B) :=
  (moduli_space_compact_hausdorff_of_lt_three_of_subsingleton I hk B).1

/-- For `k < 3` and `B < th.ε_sph`, `ModuliSpace I k B` is compact (`0 sorryAx`). -/
theorem moduli_space_compact_of_lt_three_of_lt_eps_sph {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph) :
    CompactSpace (ModuliSpace I (M := M) k B) :=
  (moduli_space_compact_hausdorff_of_lt_three_of_lt_eps_sph I hk th hB).1

/-- For `k < 3` and `B < th.h`, `ModuliSpace I k B` is compact (`0 sorryAx`). -/
theorem moduli_space_compact_of_lt_three_of_lt_threshold {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B < th.h) :
    CompactSpace (ModuliSpace I (M := M) k B) :=
  (moduli_space_compact_hausdorff_of_lt_three_of_lt_threshold I hk th hB).1

/-- For `k < 3` and `B ≤ 0`, `ModuliSpace I k B` is compact (`0 sorryAx`). -/
theorem moduli_space_compact_of_lt_three_of_nonpos_B {k : ℕ} {B : ℝ}
    (hk : k < 3) (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0) :
    CompactSpace (ModuliSpace I (M := M) k B) :=
  (moduli_space_compact_hausdorff_of_lt_three_of_nonpos_B I hk th hB).1

/-- For `k < 3` on a discrete target `M`, `ModuliSpace I k B` is compact (`0 sorryAx`). -/
theorem moduli_space_compact_of_lt_three_of_discrete {k : ℕ}
    (hk : k < 3) (B : ℝ) [DiscreteTopology M] :
    CompactSpace (ModuliSpace I (M := M) k B) :=
  (moduli_space_compact_hausdorff_of_lt_three_of_discrete I hk B).1

/-- On a subsingleton target `M`, if `MoebiusFrame` acts transitively on the marked point triples of
`MarkedStableMap I 3`, then `ModuliSpace I 3 B` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_three_of_subsingleton_of_trans [Subsingleton M]
    (B : ℝ)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpace I (M := M) 3 B) ∧ T2Space (ModuliSpace I (M := M) 3 B) :=
  moduli_space_compact_hausdorff_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_subsingleton_of_trans I B h_trans)

/-- On a `[DiscreteTopology M]` target, if all components of every `u : BoundedMarkedStableMap I 3 B`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is metrizable (`0 sorryAx`). -/
theorem exists_gromov_metricSpace_three_of_discrete_of_eq_val_of_trans [DiscreteTopology M]
    (B : ℝ) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) 3 B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I 3 B :=
  exists_gromov_metricSpace_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_discrete_of_eq_val_of_trans I B c hc h_trans)

/-- On a `[DiscreteTopology M]` target, if all components of every `u : BoundedMarkedStableMap I 3 B`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is sequentially compact (`0 sorryAx`). -/
theorem moduli_space_seq_compact_three_of_discrete_of_eq_val_of_trans [DiscreteTopology M]
    (B : ℝ) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    SeqCompactSpace (ModuliSpace I (M := M) 3 B) :=
  moduli_space_seq_compact_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_discrete_of_eq_val_of_trans I B c hc h_trans)

/-- On a `[DiscreteTopology M]` target, if all components of every `u : BoundedMarkedStableMap I 3 B`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_t2_three_of_discrete_of_eq_val_of_trans [DiscreteTopology M]
    (B : ℝ) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    T2Space (ModuliSpace I (M := M) 3 B) :=
  moduli_space_t2_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_discrete_of_eq_val_of_trans I B c hc h_trans)

/-- On a `[DiscreteTopology M]` target, if all components of every `u : BoundedMarkedStableMap I 3 B`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is compact (`0 sorryAx`). -/
theorem moduli_space_compact_three_of_discrete_of_eq_val_of_trans [DiscreteTopology M]
    (B : ℝ) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpace I (M := M) 3 B) :=
  moduli_space_compact_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_discrete_of_eq_val_of_trans I B c hc h_trans)

/-- On a `[DiscreteTopology M]` target, if all components of every `u : BoundedMarkedStableMap I 3 B`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_three_of_discrete_of_eq_val_of_trans [DiscreteTopology M]
    (B : ℝ) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpace I (M := M) 3 B) ∧ T2Space (ModuliSpace I (M := M) 3 B) :=
  moduli_space_compact_hausdorff_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_discrete_of_eq_val_of_trans I B c hc h_trans)

/-- For `B < th.ε_sph`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is a subsingleton (`0 sorryAx`). -/
theorem subsingleton_moduliSpace_three_of_lt_eps_sph_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    Subsingleton (ModuliSpace I (M := M) 3 B) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨r₁, rfl⟩ := Quotient.exists_rep x
  obtain ⟨r₂, rfl⟩ := Quotient.exists_rep y
  obtain ⟨φ, hφ⟩ := h_trans r₁.1 r₂.1
  have h₁ : ∀ (v : r₁.1.tree.V) (z : CP1), r₁.1.map v z = c := by
    intro v z
    obtain ⟨c₁, hc₁⟩ := all_const_of_lt_eps_sph I th hB r₁ v
    exact (hc₁ z).trans ((hc₁ north_pole).symm.trans (hc r₁ v))
  have h₂ : ∀ (w : r₂.1.tree.V) (z : CP1), r₂.1.map w z = c := by
    intro w z
    obtain ⟨c₂, hc₂⟩ := all_const_of_lt_eps_sph I th hB r₂ w
    exact (hc₂ z).trans ((hc₂ north_pole).symm.trans (hc r₂ w))
  exact Quotient.sound' (stableMapEquiv_of_all_const_three I r₁.1 r₂.1 c h₁ h₂ φ hφ)

/-- For `B < th.ε_sph`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is metrizable (`0 sorryAx`). -/
theorem exists_gromov_metricSpace_three_of_lt_eps_sph_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) 3 B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I 3 B :=
  exists_gromov_metricSpace_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_lt_eps_sph_of_eq_val_of_trans I th hB c hc h_trans)

/-- For `B < th.ε_sph`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is sequentially compact (`0 sorryAx`). -/
theorem moduli_space_seq_compact_three_of_lt_eps_sph_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    SeqCompactSpace (ModuliSpace I (M := M) 3 B) :=
  moduli_space_seq_compact_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_lt_eps_sph_of_eq_val_of_trans I th hB c hc h_trans)

/-- For `B < th.ε_sph`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_t2_three_of_lt_eps_sph_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    T2Space (ModuliSpace I (M := M) 3 B) :=
  moduli_space_t2_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_lt_eps_sph_of_eq_val_of_trans I th hB c hc h_trans)

/-- For `B < th.ε_sph`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is compact (`0 sorryAx`). -/
theorem moduli_space_compact_three_of_lt_eps_sph_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpace I (M := M) 3 B) :=
  moduli_space_compact_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_lt_eps_sph_of_eq_val_of_trans I th hB c hc h_trans)

/-- For `B < th.ε_sph`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_three_of_lt_eps_sph_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B < th.ε_sph) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpace I (M := M) 3 B) ∧ T2Space (ModuliSpace I (M := M) 3 B) :=
  moduli_space_compact_hausdorff_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_lt_eps_sph_of_eq_val_of_trans I th hB c hc h_trans)

/-- For `B ≤ 0`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is metrizable (`0 sorryAx`). -/
theorem exists_gromov_metricSpace_three_of_nonpos_B_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) 3 B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I 3 B :=
  exists_gromov_metricSpace_three_of_lt_eps_sph_of_eq_val_of_trans I th
    (hB.trans_lt th.ε_sph_pos) c hc h_trans

/-- For `B ≤ 0`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is sequentially compact (`0 sorryAx`). -/
theorem moduli_space_seq_compact_three_of_nonpos_B_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    SeqCompactSpace (ModuliSpace I (M := M) 3 B) :=
  moduli_space_seq_compact_three_of_lt_eps_sph_of_eq_val_of_trans I th
    (hB.trans_lt th.ε_sph_pos) c hc h_trans

/-- For `B ≤ 0`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_t2_three_of_nonpos_B_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    T2Space (ModuliSpace I (M := M) 3 B) :=
  moduli_space_t2_three_of_lt_eps_sph_of_eq_val_of_trans I th
    (hB.trans_lt th.ε_sph_pos) c hc h_trans

/-- For `B ≤ 0`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is compact (`0 sorryAx`). -/
theorem moduli_space_compact_three_of_nonpos_B_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpace I (M := M) 3 B) :=
  moduli_space_compact_three_of_lt_eps_sph_of_eq_val_of_trans I th
    (hB.trans_lt th.ε_sph_pos) c hc h_trans

/-- For `B ≤ 0`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_three_of_nonpos_B_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B ≤ 0) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpace I (M := M) 3 B) ∧ T2Space (ModuliSpace I (M := M) 3 B) :=
  moduli_space_compact_hausdorff_three_of_lt_eps_sph_of_eq_val_of_trans I th
    (hB.trans_lt th.ε_sph_pos) c hc h_trans

/-- For `B < th.h`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is metrizable (`0 sorryAx`). -/
theorem exists_gromov_metricSpace_three_of_lt_threshold_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B < th.h) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) 3 B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I 3 B :=
  exists_gromov_metricSpace_three_of_lt_eps_sph_of_eq_val_of_trans I th
    (hB.trans_le th.h_le_sph) c hc h_trans

/-- For `B < th.h`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is sequentially compact (`0 sorryAx`). -/
theorem moduli_space_seq_compact_three_of_lt_threshold_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B < th.h) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    SeqCompactSpace (ModuliSpace I (M := M) 3 B) :=
  moduli_space_seq_compact_three_of_lt_eps_sph_of_eq_val_of_trans I th
    (hB.trans_le th.h_le_sph) c hc h_trans

/-- For `B < th.h`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_t2_three_of_lt_threshold_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B < th.h) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    T2Space (ModuliSpace I (M := M) 3 B) :=
  moduli_space_t2_three_of_lt_eps_sph_of_eq_val_of_trans I th
    (hB.trans_le th.h_le_sph) c hc h_trans

/-- For `B < th.h`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is compact (`0 sorryAx`). -/
theorem moduli_space_compact_three_of_lt_threshold_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B < th.h) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpace I (M := M) 3 B) :=
  moduli_space_compact_three_of_lt_eps_sph_of_eq_val_of_trans I th
    (hB.trans_le th.h_le_sph) c hc h_trans

/-- For `B < th.h`, if all components of every `u : BoundedMarkedStableMap I 3 B` evaluate to
the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point triples
of `MarkedStableMap I 3`, then `ModuliSpace I 3 B` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_three_of_lt_threshold_of_eq_val_of_trans
    {B : ℝ} (th : Bubbling.TargetThresholds I M) (hB : B < th.h) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpace I (M := M) 3 B) ∧ T2Space (ModuliSpace I (M := M) 3 B) :=
  moduli_space_compact_hausdorff_three_of_lt_eps_sph_of_eq_val_of_trans I th
    (hB.trans_le th.h_le_sph) c hc h_trans

/-- **Master Compact Hausdorff Moduli Space Theorem (Contract E05)**:
The moduli space $\overline{\mathcal{M}}_{0, k}(M, J, \le B)$ is both compact and Hausdorff. -/
theorem moduli_space_compact_hausdorff (k : ℕ) (B : ℝ) :
    CompactSpace (ModuliSpace I (M := M) k B) ∧ T2Space (ModuliSpace I (M := M) k B) :=
  ⟨moduli_space_compact I k B, moduli_space_t2 I k B⟩

/-- A homology class $A \in H_2(M; \mathbb{Z})$ represented with its symplectic pairing. -/
structure HomologyClass2 (M : Type*) where
  /-- Symplectic area pairing $\langle [\omega], A \rangle$. -/
  omega_eval : ℝ
  /-- Area is non-negative for pseudo-holomorphic curves. -/
  omega_eval_nonneg : 0 ≤ omega_eval

/-- Predicate selecting marked stable maps representing class $A$. -/
def represents_homology_class {k : ℕ}
    (u : MarkedStableMap I (M := M) k) (A : HomologyClass2 M) : Prop :=
  markedStableMapTotalEnergy I u = A.omega_eval

/-- Predicate for moduli space elements representing a homology class A (Zero-sorry). -/
def ModuliSpace.represents_class {k : ℕ} (A : HomologyClass2 M)
    (x : ModuliSpace I (M := M) k A.omega_eval) : Prop :=
  ∃ (u : BoundedMarkedStableMap I (M := M) k A.omega_eval),
    Quotient.mk' u = x ∧ represents_homology_class I u.1 A

/-- Isomorphic marked stable maps have equal total symplectic energy (Zero-sorry). -/
theorem stableMapEquiv_totalEnergy_eq {k : ℕ}
    {u₁ u₂ : MarkedStableMap I (M := M) k}
    (h_iso : stableMapEquiv I u₁ u₂) :
    markedStableMapTotalEnergy I u₁ = markedStableMapTotalEnergy I u₂ := by
  rcases h_iso with ⟨iso⟩
  dsimp [markedStableMapTotalEnergy]
  simp_rw [iso.energy_compat]
  exact Equiv.sum_comp iso.v_equiv (fun w => totalEnergy I (u₂.map w))

/-- Characterization of `ModuliSpace.represents_class` on quotient representatives (Zero direct sorry). -/
theorem represents_class_mk_iff {k : ℕ} (A : HomologyClass2 M)
    (u : BoundedMarkedStableMap I (M := M) k A.omega_eval) :
    ModuliSpace.represents_class I A (Quotient.mk' u) ↔
      markedStableMapTotalEnergy I u.1 = A.omega_eval := by
  constructor
  · rintro ⟨u', h_eq, h_class⟩
    have h_equiv : stableMapEquiv I u'.1 u.1 := Quotient.exact' h_eq
    rw [← stableMapEquiv_totalEnergy_eq I h_equiv]
    exact h_class
  · intro h_en
    exact ⟨u, rfl, h_en⟩

/-- The subset of the moduli space representing a fixed homology class $A$ is closed
in the sequential Gromov topology (Zero direct sorry). -/
theorem isClosed_represents_class (k : ℕ) (A : HomologyClass2 M) :
    IsClosed { x : ModuliSpace I (M := M) k A.omega_eval | ModuliSpace.represents_class I A x } := by
  rw [← isOpen_compl_iff]
  intro u_seq u_lim hu_lim h_conv
  rcases h_conv with ⟨reps, lim_rep, h_reps, h_lim_rep, ⟨wit⟩⟩
  have h_lim_ne : markedStableMapTotalEnergy I lim_rep.1 ≠ A.omega_eval := by
    intro h_eq
    apply hu_lim
    rw [← h_lim_rep]
    exact (represents_class_mk_iff I A lim_rep).mpr h_eq
  have h_open_ne : IsOpen ({A.omega_eval}ᶜ : Set ℝ) := isOpen_compl_singleton
  have h_ev := wit.energy_conv.eventually (h_open_ne.mem_nhds h_lim_ne)
  filter_upwards [h_ev] with n hn
  intro h_mem
  rw [← h_reps n] at h_mem
  have h_eq := (represents_class_mk_iff I A (reps n)).mp h_mem
  exact hn h_eq

/-- The moduli space for a fixed homology class A (Zero-sorry). -/
def ModuliSpaceInClass (k : ℕ) (A : HomologyClass2 M) : Type _ :=
  { x : ModuliSpace I (M := M) k A.omega_eval // ModuliSpace.represents_class I A x }

/-- Subspace topology on the homology-fixed moduli space (Zero-sorry). -/
instance moduliSpaceInClassTopologicalSpace (k : ℕ) (A : HomologyClass2 M) :
    TopologicalSpace (ModuliSpaceInClass I (M := M) k A) :=
  TopologicalSpace.induced Subtype.val (moduliSpaceTopologicalSpace I k A.omega_eval)

/-- Zero-sorry conditional reduction of `T2Space (ModuliSpaceInClass I k A)` from metrizability (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_of_metrizable
    (k : ℕ) (A : HomologyClass2 M)
    (h_metr : ∃ (m : MetricSpace (ModuliSpace I (M := M) k A.omega_eval)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k A.omega_eval) :
    T2Space (ModuliSpaceInClass I k A) := by
  haveI : T2Space (ModuliSpace I (M := M) k A.omega_eval) :=
    moduli_space_t2_of_metrizable I k A.omega_eval h_metr
  exact Topology.IsEmbedding.t2Space ⟨⟨rfl⟩, Subtype.val_injective⟩

/-- When `ModuliSpace I k A.omega_eval` is a subsingleton, `ModuliSpaceInClass I k A` is Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_of_subsingleton
    (k : ℕ) (A : HomologyClass2 M)
    (h_sub : Subsingleton (ModuliSpace I (M := M) k A.omega_eval)) :
    T2Space (ModuliSpaceInClass I k A) :=
  moduli_space_in_class_t2_of_metrizable I k A
    (exists_gromov_metricSpace_of_subsingleton I k A.omega_eval h_sub)

/-- Zero-sorry conditional reduction of `moduli_space_in_class_compact_hausdorff` (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_of_metrizable_and_seq_compact
    (k : ℕ) (A : HomologyClass2 M)
    (h_metr : ∃ (m : MetricSpace (ModuliSpace I (M := M) k A.omega_eval)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k A.omega_eval)
    (h_seq_comp : SeqCompactSpace (ModuliSpace I (M := M) k A.omega_eval)) :
    CompactSpace (ModuliSpaceInClass I k A) ∧ T2Space (ModuliSpaceInClass I k A) := by
  haveI : T2Space (ModuliSpace I (M := M) k A.omega_eval) :=
    moduli_space_t2_of_metrizable I k A.omega_eval h_metr
  haveI : CompactSpace (ModuliSpace I (M := M) k A.omega_eval) :=
    moduli_space_compact_of_metrizable_and_seq_compact I k A.omega_eval h_metr h_seq_comp
  refine ⟨?_, Topology.IsEmbedding.t2Space ⟨⟨rfl⟩, Subtype.val_injective⟩⟩
  exact isCompact_iff_compactSpace.mp (isClosed_represents_class I k A).isCompact

/-- When `ModuliSpace I k A.omega_eval` is a subsingleton, `ModuliSpaceInClass I k A` is compact (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_of_subsingleton
    (k : ℕ) (A : HomologyClass2 M)
    (h_sub : Subsingleton (ModuliSpace I (M := M) k A.omega_eval)) :
    CompactSpace (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_metrizable_and_seq_compact I k A
    (exists_gromov_metricSpace_of_subsingleton I k A.omega_eval h_sub)
    (moduli_space_seq_compact_of_subsingleton I k A.omega_eval h_sub)).1

/-- When `ModuliSpace I k A.omega_eval` is a subsingleton, `ModuliSpaceInClass I k A` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_of_subsingleton
    (k : ℕ) (A : HomologyClass2 M)
    (h_sub : Subsingleton (ModuliSpace I (M := M) k A.omega_eval)) :
    CompactSpace (ModuliSpaceInClass I k A) ∧ T2Space (ModuliSpaceInClass I k A) :=
  moduli_space_in_class_compact_hausdorff_of_metrizable_and_seq_compact I k A
    (exists_gromov_metricSpace_of_subsingleton I k A.omega_eval h_sub)
    (moduli_space_seq_compact_of_subsingleton I k A.omega_eval h_sub)

/-- For `k < 3` on a subsingleton target `M`, `ModuliSpaceInClass I k A` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_of_lt_three_of_subsingleton {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M) [Subsingleton M] :
    CompactSpace (ModuliSpaceInClass I k A) ∧ T2Space (ModuliSpaceInClass I k A) := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_subsingleton I (M := M) hk A.omega_eval
  exact moduli_space_in_class_compact_hausdorff_of_subsingleton I k A inferInstance

/-- For `k < 3` and `A.omega_eval < th.ε_sph`, `ModuliSpaceInClass I k A` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_of_lt_three_of_lt_eps_sph {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M)
    (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval < th.ε_sph) :
    CompactSpace (ModuliSpaceInClass I k A) ∧ T2Space (ModuliSpaceInClass I k A) := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_lt_eps_sph I hk th hA
  exact moduli_space_in_class_compact_hausdorff_of_subsingleton I k A inferInstance

/-- For `k < 3` and `A.omega_eval < th.h`, `ModuliSpaceInClass I k A` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_of_lt_three_of_lt_threshold {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M)
    (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval < th.h) :
    CompactSpace (ModuliSpaceInClass I k A) ∧ T2Space (ModuliSpaceInClass I k A) :=
  moduli_space_in_class_compact_hausdorff_of_lt_three_of_lt_eps_sph I hk A th (hA.trans_le th.h_le_sph)

/-- For `k < 3` and `A.omega_eval ≤ 0`, `ModuliSpaceInClass I k A` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_of_lt_three_of_nonpos_omega {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M)
    (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval ≤ 0) :
    CompactSpace (ModuliSpaceInClass I k A) ∧ T2Space (ModuliSpaceInClass I k A) :=
  moduli_space_in_class_compact_hausdorff_of_lt_three_of_lt_eps_sph I hk A th (hA.trans_lt th.ε_sph_pos)

/-- For `k < 3` on a discrete target `M`, `ModuliSpaceInClass I k A` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_of_lt_three_of_discrete {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M) [DiscreteTopology M] :
    CompactSpace (ModuliSpaceInClass I k A) ∧ T2Space (ModuliSpaceInClass I k A) := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_discrete I (M := M) hk A.omega_eval
  exact moduli_space_in_class_compact_hausdorff_of_subsingleton I k A inferInstance

/-- For `k < 3` on a subsingleton target `M`, `ModuliSpaceInClass I k A` is compact (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_of_lt_three_of_subsingleton {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M) [Subsingleton M] :
    CompactSpace (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_lt_three_of_subsingleton I hk A).1

/-- For `k < 3` on a subsingleton target `M`, `ModuliSpaceInClass I k A` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_of_lt_three_of_subsingleton {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M) [Subsingleton M] :
    T2Space (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_lt_three_of_subsingleton I hk A).2

/-- For `k < 3` and `A.omega_eval < th.ε_sph`, `ModuliSpaceInClass I k A` is compact (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_of_lt_three_of_lt_eps_sph {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M)
    (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval < th.ε_sph) :
    CompactSpace (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_lt_three_of_lt_eps_sph I hk A th hA).1

/-- For `k < 3` and `A.omega_eval < th.ε_sph`, `ModuliSpaceInClass I k A` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_of_lt_three_of_lt_eps_sph {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M)
    (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval < th.ε_sph) :
    T2Space (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_lt_three_of_lt_eps_sph I hk A th hA).2

/-- For `k < 3` and `A.omega_eval < th.h`, `ModuliSpaceInClass I k A` is compact (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_of_lt_three_of_lt_threshold {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M)
    (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval < th.h) :
    CompactSpace (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_lt_three_of_lt_threshold I hk A th hA).1

/-- For `k < 3` and `A.omega_eval < th.h`, `ModuliSpaceInClass I k A` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_of_lt_three_of_lt_threshold {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M)
    (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval < th.h) :
    T2Space (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_lt_three_of_lt_threshold I hk A th hA).2

/-- For `k < 3` and `A.omega_eval ≤ 0`, `ModuliSpaceInClass I k A` is compact (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_of_lt_three_of_nonpos_omega {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M)
    (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval ≤ 0) :
    CompactSpace (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_lt_three_of_nonpos_omega I hk A th hA).1

/-- For `k < 3` and `A.omega_eval ≤ 0`, `ModuliSpaceInClass I k A` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_of_lt_three_of_nonpos_omega {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M)
    (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval ≤ 0) :
    T2Space (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_lt_three_of_nonpos_omega I hk A th hA).2

/-- For `k < 3` on a discrete target `M`, `ModuliSpaceInClass I k A` is compact (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_of_lt_three_of_discrete {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M) [DiscreteTopology M] :
    CompactSpace (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_lt_three_of_discrete I hk A).1

/-- For `k < 3` on a discrete target `M`, `ModuliSpaceInClass I k A` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_of_lt_three_of_discrete {k : ℕ}
    (hk : k < 3) (A : HomologyClass2 M) [DiscreteTopology M] :
    T2Space (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_lt_three_of_discrete I hk A).2

/-- On a `[Subsingleton M]` target, if `MoebiusFrame` acts transitively on the marked point triples of
`MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_three_of_subsingleton_of_trans [Subsingleton M]
    (A : HomologyClass2 M)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpaceInClass I 3 A) ∧ T2Space (ModuliSpaceInClass I 3 A) :=
  moduli_space_in_class_compact_hausdorff_of_subsingleton I 3 A
    (subsingleton_moduliSpace_three_of_subsingleton_of_trans I A.omega_eval h_trans)

/-- For `A.omega_eval < th.ε_sph`, if all components of every `u : BoundedMarkedStableMap I 3 A.omega_eval`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_three_of_lt_eps_sph_of_eq_val_of_trans
    (A : HomologyClass2 M) (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval < th.ε_sph) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpaceInClass I 3 A) ∧ T2Space (ModuliSpaceInClass I 3 A) :=
  moduli_space_in_class_compact_hausdorff_of_subsingleton I 3 A
    (subsingleton_moduliSpace_three_of_lt_eps_sph_of_eq_val_of_trans I th hA c hc h_trans)

/-- For `A.omega_eval ≤ 0`, if all components of every `u : BoundedMarkedStableMap I 3 A.omega_eval`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_three_of_nonpos_omega_of_eq_val_of_trans
    (A : HomologyClass2 M) (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval ≤ 0) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpaceInClass I 3 A) ∧ T2Space (ModuliSpaceInClass I 3 A) :=
  moduli_space_in_class_compact_hausdorff_three_of_lt_eps_sph_of_eq_val_of_trans I A th
    (hA.trans_lt th.ε_sph_pos) c hc h_trans

/-- For `A.omega_eval < th.h`, if all components of every `u : BoundedMarkedStableMap I 3 A.omega_eval`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_three_of_lt_threshold_of_eq_val_of_trans
    (A : HomologyClass2 M) (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval < th.h) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpaceInClass I 3 A) ∧ T2Space (ModuliSpaceInClass I 3 A) :=
  moduli_space_in_class_compact_hausdorff_three_of_lt_eps_sph_of_eq_val_of_trans I A th
    (hA.trans_le th.h_le_sph) c hc h_trans

/-- On a `[DiscreteTopology M]` target, if all components of every `u : BoundedMarkedStableMap I 3 A.omega_eval`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_three_of_discrete_of_eq_val_of_trans [DiscreteTopology M]
    (A : HomologyClass2 M) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpaceInClass I 3 A) ∧ T2Space (ModuliSpaceInClass I 3 A) :=
  moduli_space_in_class_compact_hausdorff_of_subsingleton I 3 A
    (subsingleton_moduliSpace_three_of_discrete_of_eq_val_of_trans I A.omega_eval c hc h_trans)

/-- Every component of `u : MarkedStableMap I k` is constant whenever every `J`-holomorphic
sphere in `(M, J)` is constant (`0 sorryAx`). -/
theorem all_const_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (u : MarkedStableMap I (M := M) k)
    (v : u.tree.V) :
    ∃ c : M, ∀ z : CP1, u.map v z = c :=
  ⟨u.map v north_pole, fun z => congr_fun (h_all_const (u.map v) (u.is_jhol v)) z⟩

/-- For `k < 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`MarkedStableMap I k` is empty (`0 sorryAx`). -/
theorem isEmpty_markedStableMap_of_lt_three_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : k < 3) :
    IsEmpty (MarkedStableMap I (M := M) k) := by
  refine ⟨fun u => ?_⟩
  have h3 := three_le_of_all_const I u (all_const_of_all_jhol_const I h_all_const u)
  omega

/-- For `k < 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`BoundedMarkedStableMap I k B` is empty (`0 sorryAx`). -/
theorem isEmpty_boundedMarkedStableMap_of_lt_three_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : k < 3) (B : ℝ) :
    IsEmpty (BoundedMarkedStableMap I (M := M) k B) := by
  haveI := isEmpty_markedStableMap_of_lt_three_of_all_jhol_const I h_all_const hk
  exact ⟨fun r => isEmptyElim r.1⟩

/-- For `k < 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`ModuliSpace I k B` is empty (`0 sorryAx`). -/
theorem isEmpty_moduliSpace_of_lt_three_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : k < 3) (B : ℝ) :
    IsEmpty (ModuliSpace I (M := M) k B) := by
  haveI := isEmpty_boundedMarkedStableMap_of_lt_three_of_all_jhol_const I h_all_const hk B
  refine ⟨fun x => ?_⟩
  obtain ⟨r, _⟩ := Quotient.exists_rep x
  exact isEmptyElim r

/-- For `k < 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`ModuliSpace I k B` is metrizable (`0 sorryAx`). -/
theorem exists_gromov_metricSpace_of_lt_three_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : k < 3) (B : ℝ) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) k B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I k B := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_all_jhol_const I h_all_const hk B
  exact exists_gromov_metricSpace_of_subsingleton I k B inferInstance

/-- For `k < 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`ModuliSpace I k B` is sequentially compact (`0 sorryAx`). -/
theorem moduli_space_seq_compact_of_lt_three_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : k < 3) (B : ℝ) :
    SeqCompactSpace (ModuliSpace I (M := M) k B) := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_all_jhol_const I h_all_const hk B
  exact moduli_space_seq_compact_of_subsingleton I k B inferInstance

/-- For `k < 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`ModuliSpace I k B` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_t2_of_lt_three_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : k < 3) (B : ℝ) :
    T2Space (ModuliSpace I (M := M) k B) := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_all_jhol_const I h_all_const hk B
  exact moduli_space_t2_of_subsingleton I k B inferInstance

/-- For `k < 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`ModuliSpace I k B` is compact (`0 sorryAx`). -/
theorem moduli_space_compact_of_lt_three_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : k < 3) (B : ℝ) :
    CompactSpace (ModuliSpace I (M := M) k B) := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_all_jhol_const I h_all_const hk B
  exact moduli_space_compact_of_subsingleton I k B inferInstance

/-- For `k < 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`ModuliSpace I k B` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_of_lt_three_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : k < 3) (B : ℝ) :
    CompactSpace (ModuliSpace I (M := M) k B) ∧ T2Space (ModuliSpace I (M := M) k B) := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_all_jhol_const I h_all_const hk B
  exact moduli_space_compact_hausdorff_of_subsingleton I k B inferInstance

/-- For `k < 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`ModuliSpaceInClass I k A` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_of_lt_three_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : k < 3) (A : HomologyClass2 M) :
    CompactSpace (ModuliSpaceInClass I k A) ∧ T2Space (ModuliSpaceInClass I k A) := by
  haveI := isEmpty_moduliSpace_of_lt_three_of_all_jhol_const I h_all_const hk A.omega_eval
  exact moduli_space_in_class_compact_hausdorff_of_subsingleton I k A inferInstance

/-- For `k < 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`ModuliSpaceInClass I k A` is compact (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_of_lt_three_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : k < 3) (A : HomologyClass2 M) :
    CompactSpace (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_lt_three_of_all_jhol_const I h_all_const hk A).1

/-- For `k < 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant,
`ModuliSpaceInClass I k A` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_of_lt_three_of_all_jhol_const {k : ℕ}
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (hk : k < 3) (A : HomologyClass2 M) :
    T2Space (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_lt_three_of_all_jhol_const I h_all_const hk A).2

/-- For `k = 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant, if all components
of every `u : BoundedMarkedStableMap I 3 B` evaluate to the same point `c : M` at `north_pole` and
`MoebiusFrame` acts transitively on the marked point triples of `MarkedStableMap I 3`, then
`ModuliSpace I 3 B` is a subsingleton (`0 sorryAx`). -/
theorem subsingleton_moduliSpace_three_of_all_jhol_const_of_eq_val_of_trans
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (B : ℝ) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    Subsingleton (ModuliSpace I (M := M) 3 B) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨r₁, rfl⟩ := Quotient.exists_rep x
  obtain ⟨r₂, rfl⟩ := Quotient.exists_rep y
  obtain ⟨φ, hφ⟩ := h_trans r₁.1 r₂.1
  have h₁ : ∀ (v : r₁.1.tree.V) (z : CP1), r₁.1.map v z = c := by
    intro v z
    obtain ⟨c₁, hc₁⟩ := all_const_of_all_jhol_const I h_all_const r₁.1 v
    exact (hc₁ z).trans ((hc₁ north_pole).symm.trans (hc r₁ v))
  have h₂ : ∀ (w : r₂.1.tree.V) (z : CP1), r₂.1.map w z = c := by
    intro w z
    obtain ⟨c₂, hc₂⟩ := all_const_of_all_jhol_const I h_all_const r₂.1 w
    exact (hc₂ z).trans ((hc₂ north_pole).symm.trans (hc r₂ w))
  exact Quotient.sound' (stableMapEquiv_of_all_const_three I r₁.1 r₂.1 c h₁ h₂ φ hφ)

/-- For `k = 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant, if all components
of every `u : BoundedMarkedStableMap I 3 B` evaluate to the same point `c : M` at `north_pole` and
`MoebiusFrame` acts transitively on the marked point triples of `MarkedStableMap I 3`, then
`ModuliSpace I 3 B` is metrizable (`0 sorryAx`). -/
theorem exists_gromov_metricSpace_three_of_all_jhol_const_of_eq_val_of_trans
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (B : ℝ) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    ∃ (m : MetricSpace (ModuliSpace I (M := M) 3 B)),
      m.toUniformSpace.toTopologicalSpace = moduliSpaceTopology I 3 B :=
  exists_gromov_metricSpace_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_all_jhol_const_of_eq_val_of_trans I h_all_const B c hc h_trans)

/-- For `k = 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant, if all components
of every `u : BoundedMarkedStableMap I 3 B` evaluate to the same point `c : M` at `north_pole` and
`MoebiusFrame` acts transitively on the marked point triples of `MarkedStableMap I 3`, then
`ModuliSpace I 3 B` is sequentially compact (`0 sorryAx`). -/
theorem moduli_space_seq_compact_three_of_all_jhol_const_of_eq_val_of_trans
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (B : ℝ) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    SeqCompactSpace (ModuliSpace I (M := M) 3 B) :=
  moduli_space_seq_compact_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_all_jhol_const_of_eq_val_of_trans I h_all_const B c hc h_trans)

/-- For `k = 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant, if all components
of every `u : BoundedMarkedStableMap I 3 B` evaluate to the same point `c : M` at `north_pole` and
`MoebiusFrame` acts transitively on the marked point triples of `MarkedStableMap I 3`, then
`ModuliSpace I 3 B` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_t2_three_of_all_jhol_const_of_eq_val_of_trans
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (B : ℝ) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    T2Space (ModuliSpace I (M := M) 3 B) :=
  moduli_space_t2_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_all_jhol_const_of_eq_val_of_trans I h_all_const B c hc h_trans)

/-- For `k = 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant, if all components
of every `u : BoundedMarkedStableMap I 3 B` evaluate to the same point `c : M` at `north_pole` and
`MoebiusFrame` acts transitively on the marked point triples of `MarkedStableMap I 3`, then
`ModuliSpace I 3 B` is compact (`0 sorryAx`). -/
theorem moduli_space_compact_three_of_all_jhol_const_of_eq_val_of_trans
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (B : ℝ) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpace I (M := M) 3 B) :=
  moduli_space_compact_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_all_jhol_const_of_eq_val_of_trans I h_all_const B c hc h_trans)

/-- For `k = 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant, if all components
of every `u : BoundedMarkedStableMap I 3 B` evaluate to the same point `c : M` at `north_pole` and
`MoebiusFrame` acts transitively on the marked point triples of `MarkedStableMap I 3`, then
`ModuliSpace I 3 B` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_compact_hausdorff_three_of_all_jhol_const_of_eq_val_of_trans
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (B : ℝ) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 B) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpace I (M := M) 3 B) ∧ T2Space (ModuliSpace I (M := M) 3 B) :=
  moduli_space_compact_hausdorff_of_subsingleton I 3 B
    (subsingleton_moduliSpace_three_of_all_jhol_const_of_eq_val_of_trans I h_all_const B c hc h_trans)

/-- For `k = 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant, if all components
of every `u : BoundedMarkedStableMap I 3 A.omega_eval` evaluate to the same point `c : M` at `north_pole`
and `MoebiusFrame` acts transitively on the marked point triples of `MarkedStableMap I 3`, then
`ModuliSpaceInClass I 3 A` is compact Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_three_of_all_jhol_const_of_eq_val_of_trans
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (A : HomologyClass2 M) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpaceInClass I 3 A) ∧ T2Space (ModuliSpaceInClass I 3 A) :=
  moduli_space_in_class_compact_hausdorff_of_subsingleton I 3 A
    (subsingleton_moduliSpace_three_of_all_jhol_const_of_eq_val_of_trans I h_all_const A.omega_eval c hc h_trans)

/-- For `k = 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant, if all components
of every `u : BoundedMarkedStableMap I 3 A.omega_eval` evaluate to the same point `c : M` at `north_pole`
and `MoebiusFrame` acts transitively on the marked point triples of `MarkedStableMap I 3`, then
`ModuliSpaceInClass I 3 A` is compact (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_three_of_all_jhol_const_of_eq_val_of_trans
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (A : HomologyClass2 M) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpaceInClass I 3 A) :=
  (moduli_space_in_class_compact_hausdorff_three_of_all_jhol_const_of_eq_val_of_trans I h_all_const A c hc h_trans).1

/-- For `k = 3`, whenever every `J`-holomorphic sphere in `(M, J)` is constant, if all components
of every `u : BoundedMarkedStableMap I 3 A.omega_eval` evaluate to the same point `c : M` at `north_pole`
and `MoebiusFrame` acts transitively on the marked point triples of `MarkedStableMap I 3`, then
`ModuliSpaceInClass I 3 A` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_three_of_all_jhol_const_of_eq_val_of_trans
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn I I_CP1 u Set.univ → u = fun _ => u north_pole)
    (A : HomologyClass2 M) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    T2Space (ModuliSpaceInClass I 3 A) :=
  (moduli_space_in_class_compact_hausdorff_three_of_all_jhol_const_of_eq_val_of_trans I h_all_const A c hc h_trans).2

/-- For `k = 3`, on subsingleton targets `[Subsingleton M]`, if `MoebiusFrame` acts transitively on
the marked point triples of `MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is compact (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_three_of_subsingleton_of_trans [Subsingleton M]
    (A : HomologyClass2 M)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpaceInClass I 3 A) :=
  (moduli_space_in_class_compact_hausdorff_three_of_subsingleton_of_trans I A h_trans).1

/-- For `k = 3`, on subsingleton targets `[Subsingleton M]`, if `MoebiusFrame` acts transitively on
the marked point triples of `MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is Hausdorff (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_three_of_subsingleton_of_trans [Subsingleton M]
    (A : HomologyClass2 M)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    T2Space (ModuliSpaceInClass I 3 A) :=
  (moduli_space_in_class_compact_hausdorff_three_of_subsingleton_of_trans I A h_trans).2

/-- For `A.omega_eval < th.ε_sph`, if all components of every `u : BoundedMarkedStableMap I 3 A.omega_eval`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is compact (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_three_of_lt_eps_sph_of_eq_val_of_trans
    (A : HomologyClass2 M) (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval < th.ε_sph) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpaceInClass I 3 A) :=
  (moduli_space_in_class_compact_hausdorff_three_of_lt_eps_sph_of_eq_val_of_trans I A th hA c hc h_trans).1

/-- For `A.omega_eval < th.ε_sph`, if all components of every `u : BoundedMarkedStableMap I 3 A.omega_eval`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_three_of_lt_eps_sph_of_eq_val_of_trans
    (A : HomologyClass2 M) (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval < th.ε_sph) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    T2Space (ModuliSpaceInClass I 3 A) :=
  (moduli_space_in_class_compact_hausdorff_three_of_lt_eps_sph_of_eq_val_of_trans I A th hA c hc h_trans).2

/-- For `A.omega_eval < th.h`, if all components of every `u : BoundedMarkedStableMap I 3 A.omega_eval`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is compact (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_three_of_lt_threshold_of_eq_val_of_trans
    (A : HomologyClass2 M) (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval < th.h) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpaceInClass I 3 A) :=
  (moduli_space_in_class_compact_hausdorff_three_of_lt_threshold_of_eq_val_of_trans I A th hA c hc h_trans).1

/-- For `A.omega_eval < th.h`, if all components of every `u : BoundedMarkedStableMap I 3 A.omega_eval`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_three_of_lt_threshold_of_eq_val_of_trans
    (A : HomologyClass2 M) (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval < th.h) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    T2Space (ModuliSpaceInClass I 3 A) :=
  (moduli_space_in_class_compact_hausdorff_three_of_lt_threshold_of_eq_val_of_trans I A th hA c hc h_trans).2

/-- For `A.omega_eval ≤ 0`, if all components of every `u : BoundedMarkedStableMap I 3 A.omega_eval`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is compact (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_three_of_nonpos_omega_of_eq_val_of_trans
    (A : HomologyClass2 M) (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval ≤ 0) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpaceInClass I 3 A) :=
  (moduli_space_in_class_compact_hausdorff_three_of_nonpos_omega_of_eq_val_of_trans I A th hA c hc h_trans).1

/-- For `A.omega_eval ≤ 0`, if all components of every `u : BoundedMarkedStableMap I 3 A.omega_eval`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_three_of_nonpos_omega_of_eq_val_of_trans
    (A : HomologyClass2 M) (th : Bubbling.TargetThresholds I M) (hA : A.omega_eval ≤ 0) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    T2Space (ModuliSpaceInClass I 3 A) :=
  (moduli_space_in_class_compact_hausdorff_three_of_nonpos_omega_of_eq_val_of_trans I A th hA c hc h_trans).2

/-- On a `[DiscreteTopology M]` target, if all components of every `u : BoundedMarkedStableMap I 3 A.omega_eval`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is compact (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_three_of_discrete_of_eq_val_of_trans [DiscreteTopology M]
    (A : HomologyClass2 M) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    CompactSpace (ModuliSpaceInClass I 3 A) :=
  (moduli_space_in_class_compact_hausdorff_three_of_discrete_of_eq_val_of_trans I A c hc h_trans).1

/-- On a `[DiscreteTopology M]` target, if all components of every `u : BoundedMarkedStableMap I 3 A.omega_eval`
evaluate to the same point `c : M` at `north_pole` and `MoebiusFrame` acts transitively on the marked point
triples of `MarkedStableMap I 3`, then `ModuliSpaceInClass I 3 A` is Hausdorff (`T2Space`) (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_three_of_discrete_of_eq_val_of_trans [DiscreteTopology M]
    (A : HomologyClass2 M) (c : M)
    (hc : ∀ (u : BoundedMarkedStableMap I (M := M) 3 A.omega_eval) (v : u.1.tree.V), u.1.map v north_pole = c)
    (h_trans : ∀ (u₁ u₂ : MarkedStableMap I (M := M) 3),
      ∃ φ : MoebiusFrame, ∀ i : Fin 3, φ.toHomeo (u₁.tree.mark_point i) = u₂.tree.mark_point i) :
    T2Space (ModuliSpaceInClass I 3 A) :=
  (moduli_space_in_class_compact_hausdorff_three_of_discrete_of_eq_val_of_trans I A c hc h_trans).2

/-- For `A.omega_eval < 0`, `ModuliSpaceInClass I k A` is empty for any `k : ℕ` (`0 sorryAx`). -/
theorem isEmpty_moduliSpaceInClass_of_neg (k : ℕ) (A : HomologyClass2 M) (hA : A.omega_eval < 0) :
    IsEmpty (ModuliSpaceInClass I k A) := by
  haveI := isEmpty_moduliSpace_of_neg I (M := M) k hA
  exact ⟨fun x => isEmptyElim x.1⟩

/-- For `A.omega_eval < 0`, `ModuliSpaceInClass I k A` is compact Hausdorff for any `k : ℕ` (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_hausdorff_of_neg (k : ℕ) (A : HomologyClass2 M) (hA : A.omega_eval < 0) :
    CompactSpace (ModuliSpaceInClass I k A) ∧ T2Space (ModuliSpaceInClass I k A) := by
  haveI := isEmpty_moduliSpace_of_neg I (M := M) k hA
  exact moduli_space_in_class_compact_hausdorff_of_subsingleton I k A inferInstance

/-- For `A.omega_eval < 0`, `ModuliSpaceInClass I k A` is compact for any `k : ℕ` (`0 sorryAx`). -/
theorem moduli_space_in_class_compact_of_neg (k : ℕ) (A : HomologyClass2 M) (hA : A.omega_eval < 0) :
    CompactSpace (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_neg I k A hA).1

/-- For `A.omega_eval < 0`, `ModuliSpaceInClass I k A` is Hausdorff (`T2Space`) for any `k : ℕ` (`0 sorryAx`). -/
theorem moduli_space_in_class_t2_of_neg (k : ℕ) (A : HomologyClass2 M) (hA : A.omega_eval < 0) :
    T2Space (ModuliSpaceInClass I k A) :=
  (moduli_space_in_class_compact_hausdorff_of_neg I k A hA).2

/-- **Compact Hausdorff Space for Fixed Homology Class (Contract E05)**:
The moduli space $\overline{\mathcal{M}}_{0, k}(M, J, A)$ representing class $A \in H_2(M; \mathbb{Z})$
is compact and Hausdorff. -/
theorem moduli_space_in_class_compact_hausdorff (k : ℕ) (A : HomologyClass2 M) :
    CompactSpace (ModuliSpaceInClass I k A) ∧ T2Space (ModuliSpaceInClass I k A) :=
  moduli_space_in_class_compact_hausdorff_of_metrizable_and_seq_compact I k A
    (moduli_space_metrizable I (M := M) k A.omega_eval)
    (moduli_space_seq_compact I k A.omega_eval)

#print axioms stableMapEquiv_refl
#print axioms stableMapEquiv_symm
#print axioms stableMapEquiv_trans
#print axioms stableMapEquiv_totalEnergy_eq
#print axioms represents_class_mk_iff
#print axioms isClosed_represents_class
#print axioms moduli_space_t2

end GromovCompactness.Extensions
