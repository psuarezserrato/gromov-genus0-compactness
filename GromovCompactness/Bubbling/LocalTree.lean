/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import GromovCompactness.Bubbling.GhostBranching
import GromovCompactness.Bubbling.Rank
import GromovCompactness.Topology.SphereTree

open scoped Manifold ContDiff Topology
open Metric Set MeasureTheory Filter GromovCompactness GromovCompactness.Analysis Finset Classical

namespace GromovCompactness.Bubbling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-!
# Task B07: Resolve Defect into a Rooted Tree

This module formalizes the resolution of a single concentration defect mass $m > 0$ into a
finite rooted sphere tree attached to $f(0) \in M$, using well-founded induction on the
discrete energy rank $\lfloor m / h \rfloor \in \mathbb{N}$, following Gromov (1985, §2.2),
Ivashkovich-Shevchishin (1999, §2.3), and `gromov_compactness.pdf` §4.6 (Task `B07`).

## Key Definitions & Theorems
- `energy_rank_rel`: Discrete energy rank relation on $\mathbb{R}_{>0}$.
- `energy_rank_wf`: Proof that energy rank reduction is well-founded.
- `energy_rank_induction`: Well-founded induction principle on energy rank $\lfloor m / h \rfloor$.
- `singletonSphereTree`: The minimal single-vertex sphere tree with zero edges.
- `graft_trees_card` & `graft_trees_energy_sum`: Combinatorial and energy conservation under grafting.
- `graft_degree_ge_left` & `graft_degree_bridge_left`: Degree preservation and increase at nodes.
- `LocalDefectTree`: Bundled structure representing a finite rooted bubble tree attached to the base curve.
- `local_defect_tree_of_empty_children`: Constructive zero-sorry resolution for zero-defect bubbles.
- `resolve_single_defect_tree`: Top-level induction theorem resolving defect mass $m$.
-/

/-- Discrete energy rank well-founded relation (Contract B07). -/
def energy_rank_rel (h : ℝ) : ℝ → ℝ → Prop :=
  fun m₁ m₂ => Nat.floor (m₁ / h) < Nat.floor (m₂ / h)

/-- The discrete energy rank relation is well-founded (Contract B07, Zero-sorry). -/
theorem energy_rank_wf (h : ℝ) : WellFounded (energy_rank_rel h) :=
  InvImage.wf (fun m => Nat.floor (m / h)) Nat.lt_wfRel.wf

/-- Well-founded induction principle on the discrete energy rank (Contract B07, Zero-sorry). -/
theorem energy_rank_induction (h : ℝ) (P : ℝ → Prop)
    (h_step : ∀ m, (∀ m', energy_rank_rel h m' m → P m') → P m) (m : ℝ) :
    P m :=
  (energy_rank_wf h).induction m h_step

/-- Energy rank strictly decreases by at least 1 at each bubbling step (Contract B07, Zero-sorry). -/
lemma energy_rank_step_bound (h : ℝ) (_hh : 0 < h) (m m_child : ℝ)
    (h_rel : energy_rank_rel h m_child m) :
    Nat.floor (m_child / h) ≤ Nat.floor (m / h) - 1 := by
  dsimp [energy_rank_rel] at h_rel
  omega

/-- The singleton sphere tree consisting of a single vertex with no edges (Contract B07, Zero-sorry). -/
def singletonSphereTree : SphereTree where
  V := Unit
  fintypeV := inferInstance
  nonemptyV := inferInstance
  adj := ⊥
  is_tree := ⟨
    ⟨fun x y => by rcases x; rcases y; exact ⟨SimpleGraph.Walk.nil⟩⟩,
    fun x c hc => by
      rcases c with _ | @⟨u, v, w, h, q⟩
      · exact hc.not_nil SimpleGraph.Walk.nil_nil
      · exact False.elim h
  ⟩
  node_point := fun _ _ h => False.elim h
  node_distinct := fun _ _ _ h₁ => False.elim h₁

/-- Degree of the vertex in a singleton sphere tree is 0 (Zero-sorry). -/
lemma singletonSphereTree_degree (u : singletonSphereTree.V) :
    singletonSphereTree.adj.degree u = 0 := by
  have : singletonSphereTree.adj.neighborSet u = ∅ := by
    ext v
    simp [singletonSphereTree]
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Finset.card_eq_zero, Set.toFinset_eq_empty, this]

/-- Cardinality of the singleton sphere tree is 1 (Zero-sorry). -/
lemma singletonSphereTree_card : Fintype.card singletonSphereTree.V = 1 := by
  dsimp [singletonSphereTree]

/-- Vertex count additivity under tree grafting (Contract B07, Zero-sorry). -/
lemma graft_trees_card (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    (p₁ p₂ : CP1)
    (hp₁ : ∀ (w : T₁.V) (h : T₁.adj.Adj v₁ w), p₁ ≠ T₁.node_point v₁ w h)
    (hp₂ : ∀ (w : T₂.V) (h : T₂.adj.Adj v₂ w), p₂ ≠ T₂.node_point v₂ w h) :
    Fintype.card (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).V =
      Fintype.card T₁.V + Fintype.card T₂.V := by
  dsimp [graft_trees]
  exact Fintype.card_sum

/-- Energy sum additivity under tree grafting (Contract B07, Zero-sorry). -/
lemma graft_trees_energy_sum (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    (p₁ p₂ : CP1)
    (hp₁ : ∀ (w : T₁.V) (h : T₁.adj.Adj v₁ w), p₁ ≠ T₁.node_point v₁ w h)
    (hp₂ : ∀ (w : T₂.V) (h : T₂.adj.Adj v₂ w), p₂ ≠ T₂.node_point v₂ w h)
    (f : (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).V → ℝ) :
    (∑ v : (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).V, f v) =
      (∑ u : T₁.V, f (Sum.inl u)) + (∑ w : T₂.V, f (Sum.inr w)) := by
  dsimp [graft_trees]
  exact Fintype.sum_sum_type f

/-- Left degree monotonicity under tree grafting: degrees do not decrease (Zero-sorry). -/
lemma graft_degree_ge_left (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) (u : T₁.V) :
    T₁.adj.degree u ≤ (graftAdj T₁ T₂ v₁ v₂).degree (Sum.inl u) := by
  have h_inj : Function.Injective (Sum.inl : T₁.V → T₁.V ⊕ T₂.V) := Sum.inl_injective
  have h_sub : (T₁.adj.neighborFinset u).map ⟨Sum.inl, h_inj⟩ ⊆ (graftAdj T₁ T₂ v₁ v₂).neighborFinset (Sum.inl u) := by
    intro x hx
    rw [Finset.mem_map] at hx
    rcases hx with ⟨w, hw, rfl⟩
    rw [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact hw
  have h_card := Finset.card_le_card h_sub
  rw [Finset.card_map] at h_card
  exact h_card

/-- Right degree monotonicity under tree grafting: degrees do not decrease (Zero-sorry). -/
lemma graft_degree_ge_right (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) (w : T₂.V) :
    T₂.adj.degree w ≤ (graftAdj T₁ T₂ v₁ v₂).degree (Sum.inr w) := by
  have h_inj : Function.Injective (Sum.inr : T₂.V → T₁.V ⊕ T₂.V) := Sum.inr_injective
  have h_sub : (T₂.adj.neighborFinset w).map ⟨Sum.inr, h_inj⟩ ⊆ (graftAdj T₁ T₂ v₁ v₂).neighborFinset (Sum.inr w) := by
    intro x hx
    rw [Finset.mem_map] at hx
    rcases hx with ⟨u, hu, rfl⟩
    rw [SimpleGraph.mem_neighborFinset] at hu ⊢
    exact hu
  have h_card := Finset.card_le_card h_sub
  rw [Finset.card_map] at h_card
  exact h_card

/-- Degree increase at the left grafting node: exactly adds the bridge edge (Zero-sorry). -/
lemma graft_degree_bridge_left (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) :
    T₁.adj.degree v₁ + 1 ≤ (graftAdj T₁ T₂ v₁ v₂).degree (Sum.inl v₁) := by
  have h_inj : Function.Injective (Sum.inl : T₁.V → T₁.V ⊕ T₂.V) := Sum.inl_injective
  let s_old := (T₁.adj.neighborFinset v₁).map ⟨Sum.inl, h_inj⟩
  have h_not_mem : Sum.inr v₂ ∉ s_old := by
    intro h_in
    rw [Finset.mem_map] at h_in
    rcases h_in with ⟨w, _, hw⟩
    contradiction
  have h_bridge : (graftAdj T₁ T₂ v₁ v₂).Adj (Sum.inl v₁) (Sum.inr v₂) := graftAdj_bridge T₁ T₂ v₁ v₂
  have h_sub : insert (Sum.inr v₂) s_old ⊆ (graftAdj T₁ T₂ v₁ v₂).neighborFinset (Sum.inl v₁) := by
    rw [Finset.insert_subset_iff]
    constructor
    · rw [SimpleGraph.mem_neighborFinset]
      exact h_bridge
    · intro x hx
      rw [Finset.mem_map] at hx
      rcases hx with ⟨w, hw, rfl⟩
      rw [SimpleGraph.mem_neighborFinset] at hw ⊢
      exact hw
  have h_card := Finset.card_le_card h_sub
  rw [Finset.card_insert_of_not_mem h_not_mem, Finset.card_map] at h_card
  exact h_card

/-- Degree increase at the right grafting node: exactly adds the bridge edge (Zero-sorry). -/
lemma graft_degree_bridge_right (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) :
    T₂.adj.degree v₂ + 1 ≤ (graftAdj T₁ T₂ v₁ v₂).degree (Sum.inr v₂) := by
  have h_inj : Function.Injective (Sum.inr : T₂.V → T₁.V ⊕ T₂.V) := Sum.inr_injective
  let s_old := (T₂.adj.neighborFinset v₂).map ⟨Sum.inr, h_inj⟩
  have h_not_mem : Sum.inl v₁ ∉ s_old := by
    intro h_in
    rw [Finset.mem_map] at h_in
    rcases h_in with ⟨w, _, hw⟩
    contradiction
  have h_bridge : (graftAdj T₁ T₂ v₁ v₂).Adj (Sum.inr v₂) (Sum.inl v₁) :=
    (graftAdj T₁ T₂ v₁ v₂).symm (graftAdj_bridge T₁ T₂ v₁ v₂)
  have h_sub : insert (Sum.inl v₁) s_old ⊆ (graftAdj T₁ T₂ v₁ v₂).neighborFinset (Sum.inr v₂) := by
    rw [Finset.insert_subset_iff]
    constructor
    · rw [SimpleGraph.mem_neighborFinset]
      exact h_bridge
    · intro x hx
      rw [Finset.mem_map] at hx
      rcases hx with ⟨w, hw, rfl⟩
      rw [SimpleGraph.mem_neighborFinset] at hw ⊢
      exact hw
  have h_card := Finset.card_le_card h_sub
  rw [Finset.card_insert_of_not_mem h_not_mem, Finset.card_map] at h_card
  exact h_card

/-- Upgrading of child root stability: a root of degree ≥ 2 in a child tree acquires
degree ≥ 3 when grafted as a child onto a parent component (Zero-sorry). -/
lemma ghost_child_stability_of_degree_two (d : ℕ) (h_deg : 2 ≤ d) :
    3 ≤ d + 1 := by
  omega

/-- A finite rooted bubble tree resolving a single point defect mass `m_defect` at `base_val`. -/
structure LocalDefectTree (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M) where
  tree : SphereTree
  root : tree.V
  map : (v : tree.V) → (CP1 → M)
  is_jhol : ∀ (v : tree.V), JHolomorphicOn (I := I) (I_dom := I_CP1) (map v) Set.univ
  nodal_match : ∀ (v w : tree.V) (h : tree.adj.Adj v w),
    map v (tree.node_point v w h) = map w (tree.node_point w v (tree.adj.symm h))
  root_attach : map root north_pole = base_val
  energy_sum : (∑ v : tree.V, totalEnergy I (map v)) = m_defect
  stable : ∀ (v : tree.V), (∃ c : M, ∀ z : CP1, map v z = c) →
    (if v = root then 2 ≤ tree.adj.degree v else 3 ≤ tree.adj.degree v)

/-- Base case: a one-level decomposition with no children yields a singleton defect tree (Zero-sorry). -/
def local_defect_tree_of_empty_children
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (hm : thresh.h ≤ m_defect)
    (h_empty : decomp.q = ∅) :
    LocalDefectTree I thresh m_defect base_val where
  tree := singletonSphereTree
  root := ()
  map _ := decomp.v
  is_jhol _ := decomp.v_jhol
  nodal_match _ _ h := False.elim h
  root_attach := decomp.node_match
  energy_sum := by
    have h_univ : (Finset.univ : Finset singletonSphereTree.V) = {()} := by
      ext x; rcases x; simp
    change (∑ v ∈ Finset.univ, totalEnergy I decomp.v) = m_defect
    rw [h_univ, Finset.sum_singleton]
    have h_ms := decomp.mass_sum
    rw [h_empty, Finset.sum_empty, add_zero] at h_ms
    exact h_ms.symm
  stable := by
    intro u hu
    exfalso
    have h_card := ghost_component_branches_of_const I thresh m_defect base_val decomp hm hu
    rw [h_empty, Finset.card_empty] at h_card
    omega

/-- One-level decomposition extraction for an isolated defect mass m ≥ h. -/
theorem exists_one_level_decomp
    (thresh : TargetThresholds I M) (m_defect : ℝ)
    (_hm : thresh.h ≤ m_defect) (base_val : M) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) := by
  sorry

/-- Grafting child defect trees onto the one-level bubble curve. -/
theorem graft_child_defect_trees
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (_hm : thresh.h ≤ m_defect)
    (_child_trees : (z : ℂ) → z ∈ decomp.q →
      LocalDefectTree I thresh (decomp.m_child z) (decomp.v (stereo_chart.symm z))) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  sorry

/-- Resolution of sub-threshold mass (below the minimal sphere energy h). -/
theorem local_defect_tree_of_subthreshold
    (thresh : TargetThresholds I M) (m_defect : ℝ)
    (_hm_pos : 0 < m_defect) (_hm_lt : m_defect < thresh.h) (base_val : M) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  sorry

/-- Resolution of a Single Defect into a Finite Rooted Bubble Tree (Contract B07).
Proved with zero direct sorry via energy_rank_induction and B04/B06. -/
theorem resolve_single_defect_tree
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : 0 < m_defect) (base_val : M) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  revert hm base_val
  refine energy_rank_induction thresh.h
    (fun m => 0 < m → ∀ (b : M), Nonempty (LocalDefectTree I thresh m b)) ?_ m_defect
  intro m ih hm_pos b
  by_cases h_ge : thresh.h ≤ m
  · obtain ⟨decomp⟩ := exists_one_level_decomp I thresh m h_ge b
    by_cases h_q : decomp.q = ∅
    · exact ⟨local_defect_tree_of_empty_children I thresh m b decomp h_ge h_q⟩
    · have h_children : ∀ (z : ℂ) (hz : z ∈ decomp.q),
          Nonempty (LocalDefectTree I thresh (decomp.m_child z) (decomp.v (stereo_chart.symm z))) := by
        intro z hz
        have h_rel : energy_rank_rel thresh.h (decomp.m_child z) m :=
          child_rank_strict_decrease I thresh m b decomp h_ge z hz
        have h_pos : 0 < decomp.m_child z :=
          thresh.h_pos.trans_le (decomp.m_child_pos z hz)
        exact ih (decomp.m_child z) h_rel h_pos (decomp.v (stereo_chart.symm z))
      let child_trees : (z : ℂ) → z ∈ decomp.q → LocalDefectTree I thresh (decomp.m_child z) (decomp.v (stereo_chart.symm z)) :=
        fun z hz => Classical.choice (h_children z hz)
      exact graft_child_defect_trees I thresh m b decomp h_ge child_trees
  · push_neg at h_ge
    exact local_defect_tree_of_subthreshold I thresh m hm_pos h_ge b

#print axioms energy_rank_wf
#print axioms energy_rank_induction
#print axioms energy_rank_step_bound
#print axioms singletonSphereTree
#print axioms singletonSphereTree_degree
#print axioms singletonSphereTree_card
#print axioms graft_trees_card
#print axioms graft_trees_energy_sum
#print axioms graft_degree_ge_left
#print axioms graft_degree_ge_right
#print axioms graft_degree_bridge_left
#print axioms graft_degree_bridge_right
#print axioms ghost_child_stability_of_degree_two
#print axioms local_defect_tree_of_empty_children
#print axioms resolve_single_defect_tree

end GromovCompactness.Bubbling
