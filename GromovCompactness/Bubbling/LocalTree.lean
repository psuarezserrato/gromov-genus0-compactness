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
    exact iff_of_false (fun h => h) (Set.notMem_empty v)
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Finset.card_eq_zero, Set.toFinset_eq_empty, this]

/-- Cardinality of the singleton sphere tree is 1 (Zero-sorry). -/
lemma singletonSphereTree_card : Fintype.card singletonSphereTree.V = 1 :=
  Fintype.card_unit

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
  rw [Finset.card_insert_of_notMem h_not_mem, Finset.card_map] at h_card
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
    (graftAdj T₁ T₂ v₁ v₂).adj_symm (graftAdj_bridge T₁ T₂ v₁ v₂)
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
  rw [Finset.card_insert_of_notMem h_not_mem, Finset.card_map] at h_card
  exact h_card

/-- Upgrading of child root stability: a root of degree ≥ 2 in a child tree acquires
degree ≥ 3 when grafted as a child onto a parent component (Zero-sorry). -/
lemma ghost_child_stability_of_degree_two (d : ℕ) (h_deg : 2 ≤ d) :
    3 ≤ d + 1 := by
  omega

lemma stereo_chart_symm_ne_north_pole (w : ℂ) : stereo_chart.symm w ≠ north_pole := by
  intro hw_eq
  have h_source := stereo_chart.map_target (show w ∈ stereo_chart.target by simp [stereo_chart])
  rw [hw_eq, stereo_chart_source] at h_source
  exact h_source rfl

/-- A finite rooted bubble tree resolving a single point defect mass `m_defect` at `base_val`. -/
structure LocalDefectTree (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M) where
  tree : SphereTree
  root : tree.V
  map : (v : tree.V) → (CP1 → M)
  is_jhol : ∀ (v : tree.V), JHolomorphicOn (I := I) (I_dom := I_CP1) (map v) Set.univ
  nodal_match : ∀ (v w : tree.V) (h : tree.adj.Adj v w),
    map v (tree.node_point v w h) = map w (tree.node_point w v (tree.adj.adj_symm h))
  root_attach : map root north_pole = base_val
  root_north_pole_free : ∀ (w : tree.V) (h : tree.adj.Adj root w),
    tree.node_point root w h ≠ north_pole
  energy_sum : thresh.h ≤ m_defect → (∑ v : tree.V, totalEnergy I (map v)) = m_defect
  stable : thresh.h ≤ m_defect → ∀ (v : tree.V), (∃ c : M, ∀ z : CP1, map v z = c) →
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
  root_north_pole_free _ h := False.elim h
  energy_sum _ := by
    have h_sum : (∑ _v : singletonSphereTree.V, totalEnergy I decomp.v) = totalEnergy I decomp.v :=
      Fintype.sum_unique (fun _ : Unit => totalEnergy I decomp.v)
    rw [h_sum]
    have h_ms := decomp.mass_sum
    rw [h_empty, Finset.sum_empty, add_zero] at h_ms
    exact h_ms.symm
  stable _ := by
    intro u hu
    exfalso
    have h_card := ghost_component_branches_of_const I thresh m_defect base_val decomp hm hu
    rw [h_empty, Finset.card_empty] at h_card
    omega

/-- One-level decomposition extraction for an isolated defect mass `m ≥ h` across leaf bubbles
(`q = ∅`), single-child bubbles (`q = {0}`), unit-disk child configurations, and general calibrated
child configurations (`0 sorryAx`). -/
theorem exists_one_level_decomp
    (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect) (base_val : M)
    (h_disk :
      (∃ v : CP1 → M,
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        m_defect = totalEnergy I v ∧
        v north_pole = base_val ∧
        energyMeasure I v (disk_at 0 1) = m_defect - thresh.h / 2) ∨
      (∃ v : CP1 → M,
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        totalEnergy I v ≤ m_defect - thresh.h ∧
        v north_pole = base_val ∧
        totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) ∨
      (∃ (v : CP1 → M) (q : Finset ℂ) (m_child : ℂ → ℝ),
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        (∀ z ∈ q, ‖z‖ < 1) ∧
        (∀ z ∈ q, thresh.h ≤ m_child z) ∧
        (∀ z ∉ q, m_child z = 0) ∧
        m_defect = totalEnergy I v + ∑ z ∈ q, m_child z ∧
        v north_pole = base_val ∧
        totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) ∨
      (∃ (v : CP1 → M) (q : Finset ℂ) (m_child : ℂ → ℝ),
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        (∀ z ∈ q, thresh.h ≤ m_child z) ∧
        (∀ z ∉ q, m_child z = 0) ∧
        m_defect = totalEnergy I v + ∑ z ∈ q, m_child z ∧
        v north_pole = base_val ∧
        energyMeasure I v (disk_at 0 1) + ∑ z ∈ q.filter (fun w => ‖w‖ < 1), m_child z =
          m_defect - thresh.h / 2)) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) :=
  extract_rescaled_bubble_and_children I thresh m_defect hm base_val h_disk

private theorem exists_one_level_decomp_aux
    (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : thresh.h ≤ m_defect) (base_val : M) :
    Nonempty (OneLevelDecomposition I thresh m_defect base_val) := by
  by_cases h_disk :
      (∃ v : CP1 → M,
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        m_defect = totalEnergy I v ∧
        v north_pole = base_val ∧
        energyMeasure I v (disk_at 0 1) = m_defect - thresh.h / 2) ∨
      (∃ v : CP1 → M,
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        totalEnergy I v ≤ m_defect - thresh.h ∧
        v north_pole = base_val ∧
        totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) ∨
      (∃ (v : CP1 → M) (q : Finset ℂ) (m_child : ℂ → ℝ),
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        (∀ z ∈ q, ‖z‖ < 1) ∧
        (∀ z ∈ q, thresh.h ≤ m_child z) ∧
        (∀ z ∉ q, m_child z = 0) ∧
        m_defect = totalEnergy I v + ∑ z ∈ q, m_child z ∧
        v north_pole = base_val ∧
        totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2) ∨
      (∃ (v : CP1 → M) (q : Finset ℂ) (m_child : ℂ → ℝ),
        JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
        (∀ z ∈ q, thresh.h ≤ m_child z) ∧
        (∀ z ∉ q, m_child z = 0) ∧
        m_defect = totalEnergy I v + ∑ z ∈ q, m_child z ∧
        v north_pole = base_val ∧
        energyMeasure I v (disk_at 0 1) + ∑ z ∈ q.filter (fun w => ‖w‖ < 1), m_child z =
          m_defect - thresh.h / 2)
  · exact exists_one_level_decomp I thresh m_defect hm base_val h_disk
  · have _ := neck_vanishing_quantified I (M := M)
    have _ := removal_of_singularities I (M := M)
    sorry

/-- Partial grafted sphere tree obtained by grafting a subset `s ⊆ decomp.q` of child defect trees
onto the parent bubble `decomp.v`. -/
structure PartialGraftedTree
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (s : Finset ℂ) where
  tree : SphereTree
  root : tree.V
  map : (v : tree.V) → (CP1 → M)
  is_jhol : ∀ (v : tree.V), JHolomorphicOn (I := I) (I_dom := I_CP1) (map v) Set.univ
  nodal_match : ∀ (v w : tree.V) (h : tree.adj.Adj v w),
    map v (tree.node_point v w h) = map w (tree.node_point w v (tree.adj.adj_symm h))
  root_map : map root = decomp.v
  root_nodal_points : ∀ (w : tree.V) (h : tree.adj.Adj root w),
    ∃ z ∈ s, tree.node_point root w h = stereo_chart.symm z
  root_degree_ge : s.card ≤ tree.adj.degree root
  energy_sum : (∑ v : tree.V, totalEnergy I (map v)) =
    totalEnergy I decomp.v + ∑ z ∈ s, decomp.m_child z
  stable_off_root : ∀ (v : tree.V), v ≠ root → (∃ c : M, ∀ z : CP1, map v z = c) →
    3 ≤ tree.adj.degree v

/-- Empty subset base case for `PartialGraftedTree`: the singleton sphere tree at `decomp.v` (Zero-sorry). -/
noncomputable def partialGraftedTree_empty
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val) :
    PartialGraftedTree I thresh m_defect base_val decomp ∅ where
  tree := singletonSphereTree
  root := ()
  map _ := decomp.v
  is_jhol _ := decomp.v_jhol
  nodal_match _ _ h := False.elim h
  root_map := rfl
  root_nodal_points _ h := False.elim h
  root_degree_ge := by simp
  energy_sum := by
    have h_sum : (∑ _v : singletonSphereTree.V, totalEnergy I decomp.v) = totalEnergy I decomp.v :=
      Fintype.sum_unique (fun _ : Unit => totalEnergy I decomp.v)
    rw [h_sum, Finset.sum_empty, add_zero]
  stable_off_root v hv := by
    rcases v
    exact False.elim (hv rfl)

/-- Inductive insertion step for `PartialGraftedTree`: grafting one additional child defect tree at `z₀ ∉ s` (Zero-sorry). -/
noncomputable def partialGraftedTree_insert
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (s : Finset ℂ) (z₀ : ℂ) (hz₀_not_s : z₀ ∉ s) (hz₀_q : z₀ ∈ decomp.q)
    (P : PartialGraftedTree I thresh m_defect base_val decomp s)
    (C : LocalDefectTree I thresh (decomp.m_child z₀) (decomp.v (stereo_chart.symm z₀))) :
    PartialGraftedTree I thresh m_defect base_val decomp (insert z₀ s) := by
  have hp₁ : ∀ (w : P.tree.V) (h : P.tree.adj.Adj P.root w),
      stereo_chart.symm z₀ ≠ P.tree.node_point P.root w h := by
    intro w h heq
    obtain ⟨z, hz_s, hz_eq⟩ := P.root_nodal_points w h
    rw [hz_eq] at heq
    have hz_eq' : z₀ = z := stereo_chart_symm_injective heq
    subst hz_eq'
    exact hz₀_not_s hz_s
  have hp₂ : ∀ (w : C.tree.V) (h : C.tree.adj.Adj C.root w),
      north_pole ≠ C.tree.node_point C.root w h :=
    fun w h => (C.root_north_pole_free w h).symm
  have hm_child : thresh.h ≤ decomp.m_child z₀ := decomp.m_child_pos z₀ hz₀_q
  let T' := graft_trees P.tree C.tree P.root C.root (stereo_chart.symm z₀) north_pole hp₁ hp₂
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
      · obtain ⟨z, hz_s, hz_eq⟩ := P.root_nodal_points w h
        exact ⟨z, Finset.mem_insert_of_mem hz_s, hz_eq⟩
      · exact ⟨z₀, Finset.mem_insert_self z₀ s, rfl⟩
    root_degree_ge := by
      rw [Finset.card_insert_of_notMem hz₀_not_s]
      have h_le1 : s.card + 1 ≤ P.tree.adj.degree P.root + 1 := Nat.add_le_add_right P.root_degree_ge 1
      have h_le2 := graft_degree_bridge_left P.tree C.tree P.root C.root
      exact h_le1.trans h_le2
    energy_sum := by
      have h_split := graft_trees_energy_sum P.tree C.tree P.root C.root
        (stereo_chart.symm z₀) north_pole hp₁ hp₂ (fun v => totalEnergy I (map' v))
      rw [h_split]
      change (∑ u : P.tree.V, totalEnergy I (P.map u)) + (∑ w : C.tree.V, totalEnergy I (C.map w)) =
        totalEnergy I decomp.v + ∑ z ∈ insert z₀ s, decomp.m_child z
      rw [P.energy_sum, C.energy_sum hm_child, Finset.sum_insert hz₀_not_s]
      ring
    stable_off_root := fun v hv h_const => by
      rcases v with u | w
      · have hu : u ≠ P.root := fun heq => hv (congrArg Sum.inl heq)
        have h_deg := P.stable_off_root u hu h_const
        exact h_deg.trans (graft_degree_ge_left P.tree C.tree P.root C.root u)
      · have h_stab := C.stable hm_child w h_const
        by_cases hw : w = C.root
        · subst hw
          simp only [↓reduceIte] at h_stab
          have h_add := ghost_child_stability_of_degree_two (C.tree.adj.degree C.root) h_stab
          exact h_add.trans (graft_degree_bridge_right P.tree C.tree P.root C.root)
        · simp only [hw, ↓reduceIte] at h_stab
          exact h_stab.trans (graft_degree_ge_right P.tree C.tree P.root C.root w)
  }

/-- Grafting child defect trees onto the one-level bubble curve (Proved with zero sorry). -/
theorem graft_child_defect_trees
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (hm : thresh.h ≤ m_defect)
    (child_trees : (z : ℂ) → z ∈ decomp.q →
      LocalDefectTree I thresh (decomp.m_child z) (decomp.v (stereo_chart.symm z))) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  have h_ind : ∀ (s : Finset ℂ), s ⊆ decomp.q →
      Nonempty (PartialGraftedTree I thresh m_defect base_val decomp s) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      exact ⟨partialGraftedTree_empty I thresh m_defect base_val decomp⟩
    · intro z₀ s' hz₀_not_s ih hs_sub
      have hz₀_q : z₀ ∈ decomp.q := hs_sub (Finset.mem_insert_self z₀ s')
      have hs'_sub : s' ⊆ decomp.q := (Finset.subset_insert z₀ s').trans hs_sub
      obtain ⟨P⟩ := ih hs'_sub
      exact ⟨partialGraftedTree_insert I thresh m_defect base_val decomp s' z₀ hz₀_not_s hz₀_q P (child_trees z₀ hz₀_q)⟩
  obtain ⟨P⟩ := h_ind decomp.q Finset.Subset.rfl
  refine ⟨{
    tree := P.tree
    root := P.root
    map := P.map
    is_jhol := P.is_jhol
    nodal_match := P.nodal_match
    root_attach := by rw [P.root_map]; exact decomp.node_match
    root_north_pole_free := fun w h => by
      obtain ⟨z, _, hz_eq⟩ := P.root_nodal_points w h
      rw [hz_eq]
      exact stereo_chart_symm_ne_north_pole z
    energy_sum := fun _ => by
      rw [P.energy_sum]
      exact decomp.mass_sum.symm
    stable := fun _ v h_const => by
      by_cases hv : v = P.root
      · subst hv
        simp only [↓reduceIte]
        rw [P.root_map] at h_const
        have h_card := ghost_component_branches_of_const I thresh m_defect base_val decomp hm h_const
        exact h_card.trans P.root_degree_ge
      · simp only [hv, ↓reduceIte]
        exact P.stable_off_root v hv h_const
  }⟩

/-- Resolution of sub-threshold mass (below the minimal sphere energy h) (Proved with zero sorry). -/
theorem local_defect_tree_of_subthreshold
    (thresh : TargetThresholds I M) (m_defect : ℝ)
    (_hm_pos : 0 < m_defect) (hm_lt : m_defect < thresh.h) (base_val : M) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  refine ⟨{
    tree := singletonSphereTree
    root := ()
    map := fun _ _ => base_val
    is_jhol := fun _ => by
      refine ⟨contMDiffOn_const, ?_⟩
      intro z _hz _v
      simp only [mfderiv_const]
      exact ((ClosedTameTarget.J (I := I) base_val).map_zero).symm
    nodal_match := fun _ _ h => False.elim h
    root_attach := rfl
    root_north_pole_free := fun _ h => False.elim h
    energy_sum := fun h_ge => absurd h_ge (not_le_of_gt hm_lt)
    stable := fun h_ge => absurd h_ge (not_le_of_gt hm_lt)
  }⟩

/-- Single-step resolution of a `OneLevelDecomposition` when `m_defect < 3 * thresh.h / 2` and
`energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v` (`0 sorryAx`). -/
theorem local_defect_tree_of_lt_three_halves_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (hm : thresh.h ≤ m_defect)
    (h_le : energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v)
    (h_lt : m_defect < 3 * thresh.h / 2) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  ⟨local_defect_tree_of_empty_children I thresh m_defect base_val decomp hm
    (OneLevelDecomposition.q_eq_empty_of_lt_three_halves_h I thresh m_defect base_val decomp h_le h_lt)⟩

/-- Single-step resolution of a `OneLevelDecomposition` when `m_defect < thresh.ε_sph + thresh.h` (`0 sorryAx`). -/
theorem local_defect_tree_of_lt_eps_sph_add_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (hm : thresh.h ≤ m_defect)
    (h_lt : m_defect < thresh.ε_sph + thresh.h) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  ⟨local_defect_tree_of_empty_children I thresh m_defect base_val decomp hm
    (OneLevelDecomposition.q_eq_empty_of_lt_eps_sph_add_h I thresh m_defect base_val decomp h_lt)⟩

/-- Single-step resolution of a `OneLevelDecomposition` when `m_defect < 2 * thresh.h` (`0 sorryAx`). -/
theorem local_defect_tree_of_lt_two_mul_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (hm : thresh.h ≤ m_defect)
    (h_lt : m_defect < 2 * thresh.h) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  ⟨local_defect_tree_of_empty_children I thresh m_defect base_val decomp hm
    (OneLevelDecomposition.q_eq_empty_of_lt_two_mul_h I thresh m_defect base_val decomp h_lt)⟩

/-- Every `LocalDefectTree` at defect mass `m_defect ≥ thresh.h` contains at least one non-constant
component (`0 sorryAx`). -/
theorem LocalDefectTree.exists_nonconst_component
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M)
    (T : LocalDefectTree I thresh m_defect base_val) :
    ∃ v : T.tree.V, ¬ ∃ c : M, ∀ z, T.map v z = c := by
  by_contra h_all_const
  push_neg at h_all_const
  have h_sum := T.energy_sum hm
  have h_zero : (∑ v : T.tree.V, totalEnergy I (T.map v)) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    rcases h_all_const v with ⟨c, hc⟩
    have hv_const : T.map v = fun _ => c := funext hc
    dsimp [totalEnergy]
    rw [hv_const]
    exact energyMeasure_const_eq_zero I c Set.univ
  have h_pos := thresh.h_pos
  linarith

/-- Every `LocalDefectTree` at defect mass `m_defect ≥ thresh.h` satisfies `thresh.ε_sph ≤ m_defect` (`0 sorryAx`). -/
theorem LocalDefectTree.eps_sph_le_of_ge_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M)
    (T : LocalDefectTree I thresh m_defect base_val) :
    thresh.ε_sph ≤ m_defect := by
  obtain ⟨v, hv_nc⟩ := T.exists_nonconst_component I thresh m_defect hm base_val
  have hv_ge : thresh.ε_sph ≤ totalEnergy I (T.map v) :=
    thresh.h_sph (T.map v) (T.is_jhol v) hv_nc
  have hv_le_sum : totalEnergy I (T.map v) ≤ ∑ u : T.tree.V, totalEnergy I (T.map u) :=
    Finset.single_le_sum (fun u _ => energy_nonneg I (T.map u) Set.univ) (Finset.mem_univ v)
  rw [T.energy_sum hm] at hv_le_sum
  exact hv_ge.trans hv_le_sum

/-- If `thresh.h ≤ m_defect` and `m_defect < thresh.ε_sph`, `LocalDefectTree I thresh m_defect base_val`
is empty (`0 sorryAx`). -/
theorem LocalDefectTree.isEmpty_of_ge_h_of_lt_eps_sph
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect)
    (h_lt : m_defect < thresh.ε_sph) (base_val : M) :
    IsEmpty (LocalDefectTree I thresh m_defect base_val) :=
  ⟨fun T => not_lt_of_ge (T.eps_sph_le_of_ge_h I thresh m_defect hm base_val) h_lt⟩

/-- Every `LocalDefectTree` at defect mass `m_defect ≥ thresh.h` satisfies
`thresh.h ≤ ∑ v : T.tree.V, totalEnergy I (T.map v)` (`0 sorryAx`). -/
theorem LocalDefectTree.h_le_of_ge_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M)
    (T : LocalDefectTree I thresh m_defect base_val) :
    thresh.h ≤ ∑ v : T.tree.V, totalEnergy I (T.map v) := by
  rw [T.energy_sum hm]
  exact hm

/-- Every `LocalDefectTree` at defect mass `m_defect ≥ thresh.h` contains a component vertex `v`
with `thresh.ε_sph ≤ totalEnergy I (T.map v)` (`0 sorryAx`). -/
theorem LocalDefectTree.exists_eps_sph_le_component
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M)
    (T : LocalDefectTree I thresh m_defect base_val) :
    ∃ v : T.tree.V, thresh.ε_sph ≤ totalEnergy I (T.map v) := by
  obtain ⟨v, hv_nc⟩ := T.exists_nonconst_component I thresh m_defect hm base_val
  exact ⟨v, thresh.h_sph (T.map v) (T.is_jhol v) hv_nc⟩

/-- Every `LocalDefectTree` at defect mass `m_defect ≥ thresh.h` contains a component vertex `v`
with `thresh.h ≤ totalEnergy I (T.map v)` (`0 sorryAx`). -/
theorem LocalDefectTree.exists_h_le_component
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M)
    (T : LocalDefectTree I thresh m_defect base_val) :
    ∃ v : T.tree.V, thresh.h ≤ totalEnergy I (T.map v) := by
  obtain ⟨v, hv_ge⟩ := T.exists_eps_sph_le_component I thresh m_defect hm base_val
  exact ⟨v, thresh.h_le_sph.trans hv_ge⟩

/-- Unconditional resolution of a single defect into a `LocalDefectTree` when `thresh.ε_sph = thresh.h`,
`0 < m_defect`, and `m_defect < thresh.ε_sph` (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_eq_h_of_lt_eps_sph
    (thresh : TargetThresholds I M) (h_eq : thresh.ε_sph = thresh.h)
    (m_defect : ℝ) (hm : 0 < m_defect) (h_lt : m_defect < thresh.ε_sph) (base_val : M) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  local_defect_tree_of_subthreshold I thresh m_defect hm (h_eq ▸ h_lt) base_val

/-- Single-step resolution of a `OneLevelDecomposition` when `m_defect < thresh.ε_sph + thresh.h`,
without requiring `thresh.h ≤ m_defect` as a separate hypothesis (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_decomp_lt_eps_sph_add_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_lt : m_defect < thresh.ε_sph + thresh.h) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  local_defect_tree_of_lt_eps_sph_add_h I thresh m_defect base_val decomp
    (OneLevelDecomposition.h_le_m_defect I thresh m_defect base_val decomp) h_lt

/-- Single-step resolution of a `OneLevelDecomposition` when `m_defect < 2 * thresh.h`,
without requiring `thresh.h ≤ m_defect` as a separate hypothesis (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_decomp_lt_two_mul_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_lt : m_defect < 2 * thresh.h) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  local_defect_tree_of_lt_two_mul_h I thresh m_defect base_val decomp
    (OneLevelDecomposition.h_le_m_defect I thresh m_defect base_val decomp) h_lt

/-- Single-step resolution of a `OneLevelDecomposition` when `m_defect < 3 * thresh.h / 2` and
`energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v`, without requiring `thresh.h ≤ m_defect`
as a separate hypothesis (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_decomp_lt_three_halves_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_le : energyMeasure I decomp.v (disk_at 0 1) ≤ totalEnergy I decomp.v)
    (h_lt : m_defect < 3 * thresh.h / 2) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  local_defect_tree_of_lt_three_halves_h I thresh m_defect base_val decomp
    (OneLevelDecomposition.h_le_m_defect I thresh m_defect base_val decomp) h_le h_lt

/-- Direct leaf-bubble resolution of `resolve_single_defect_tree` when a `J`-holomorphic leaf bubble
`v : CP1 → M` with `m_defect = totalEnergy I v` and `v north_pole = base_val` is given (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_leaf_bubble
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M)
    (v : CP1 → M)
    (hv_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ)
    (hv_tot : m_defect = totalEnergy I v)
    (hv_node : v north_pole = base_val)
    (hv_calib : energyMeasure I v (disk_at 0 1) = m_defect - thresh.h / 2) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  ⟨local_defect_tree_of_empty_children I thresh m_defect base_val
    (OneLevelDecomposition.of_leaf_bubble I thresh m_defect base_val v hv_jhol hv_tot hv_node hv_calib)
    hm rfl⟩

/-- Zero-sorry conditional reduction of `resolve_single_defect_tree` via `energy_rank_induction`
from one-level mass decomposition `h_one_level` (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_one_level
    (thresh : TargetThresholds I M)
    (h_one_level : ∀ (m : ℝ), thresh.h ≤ m → ∀ (b : M),
      Nonempty (OneLevelDecomposition I thresh m b))
    (m_defect : ℝ) (hm : 0 < m_defect) (base_val : M) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  revert hm base_val
  refine energy_rank_induction thresh.h
    (fun m => 0 < m → ∀ (b : M), Nonempty (LocalDefectTree I thresh m b)) ?_ m_defect
  intro m ih hm_pos b
  by_cases h_ge : thresh.h ≤ m
  · obtain ⟨decomp⟩ := h_one_level m h_ge b
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

/-- Zero-sorry conditional reduction of `resolve_single_defect_tree` across sub-threshold masses
(`m_defect < thresh.h`), leaf bubbles, and one-level decompositions (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_cases
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : 0 < m_defect) (base_val : M)
    (h_cases : m_defect < thresh.h ∨
      (thresh.h ≤ m_defect ∧
        ∃ v : CP1 → M,
          JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ ∧
          m_defect = totalEnergy I v ∧
          v north_pole = base_val ∧
          energyMeasure I v (disk_at 0 1) = m_defect - thresh.h / 2) ∨
      (thresh.h ≤ m_defect ∧
        ∃ decomp : OneLevelDecomposition I thresh m_defect base_val,
          decomp.q = ∅ ∨
          (∀ z ∈ decomp.q, Nonempty (LocalDefectTree I thresh (decomp.m_child z) (decomp.v (stereo_chart.symm z)))))) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  rcases h_cases with hm_lt | ⟨hm_ge, v, hv_jhol, hv_tot, hv_node, hv_calib⟩ | ⟨hm_ge, decomp, h_q | h_children⟩
  · exact local_defect_tree_of_subthreshold I thresh m_defect hm hm_lt base_val
  · exact resolve_single_defect_tree_of_leaf_bubble I thresh m_defect hm_ge base_val v hv_jhol hv_tot hv_node hv_calib
  · exact ⟨local_defect_tree_of_empty_children I thresh m_defect base_val decomp hm_ge h_q⟩
  · exact graft_child_defect_trees I thresh m_defect base_val decomp hm_ge
      (fun z hz => Classical.choice (h_children z hz))

/-- On a subsingleton target `M`, no `LocalDefectTree` exists for `m_defect ≥ thresh.h` (`0 sorryAx`),
since every component map has zero energy while `energy_sum` requires total energy `m_defect > 0`. -/
theorem LocalDefectTree.isEmpty_of_subsingleton_of_ge [Subsingleton M]
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M) :
    IsEmpty (LocalDefectTree I thresh m_defect base_val) := by
  refine ⟨fun T => ?_⟩
  have h_sum := T.energy_sum hm
  have h_zero : (∑ v : T.tree.V, totalEnergy I (T.map v)) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    have hv_const : T.map v = fun _ => T.map v north_pole :=
      funext (fun z => Subsingleton.elim (T.map v z) (T.map v north_pole))
    dsimp [totalEnergy]
    rw [hv_const]
    exact energyMeasure_const_eq_zero I (T.map v north_pole) Set.univ
  have h_pos := thresh.h_pos
  linarith

/-- On a subsingleton target `M`, for `0 < m_defect`, `LocalDefectTree I thresh m_defect base_val`
is nonempty if and only if `m_defect < thresh.h` (`0 sorryAx`). -/
theorem nonempty_localDefectTree_iff_lt_of_subsingleton [Subsingleton M]
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : 0 < m_defect) (base_val : M) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) ↔ m_defect < thresh.h := by
  constructor
  · rintro ⟨T⟩
    by_contra h_not_lt
    have hm_ge : thresh.h ≤ m_defect := le_of_not_gt h_not_lt
    haveI := LocalDefectTree.isEmpty_of_subsingleton_of_ge I thresh m_defect hm_ge base_val
    exact isEmptyElim T
  · intro hm_lt
    exact local_defect_tree_of_subthreshold I thresh m_defect hm hm_lt base_val

/-- On a discrete target `M`, no `LocalDefectTree` exists for `m_defect ≥ thresh.h` (`0 sorryAx`),
since every `J`-holomorphic component map on `CP1` is constant (`eq_const_north_pole_of_jhol_univ_of_discrete`)
and therefore has zero energy while `energy_sum` requires total energy `m_defect > 0`. -/
theorem LocalDefectTree.isEmpty_of_discrete_of_ge [DiscreteTopology M]
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M) :
    IsEmpty (LocalDefectTree I thresh m_defect base_val) := by
  refine ⟨fun T => ?_⟩
  have h_sum := T.energy_sum hm
  have h_zero : (∑ v : T.tree.V, totalEnergy I (T.map v)) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    have hv_const : T.map v = fun _ => T.map v north_pole :=
      funext (eq_const_north_pole_of_jhol_univ_of_discrete I (T.map v) (T.is_jhol v))
    dsimp [totalEnergy]
    rw [hv_const]
    exact energyMeasure_const_eq_zero I (T.map v north_pole) Set.univ
  have h_pos := thresh.h_pos
  linarith

/-- On a discrete target `M`, for `0 < m_defect`, `LocalDefectTree I thresh m_defect base_val`
is nonempty if and only if `m_defect < thresh.h` (`0 sorryAx`). -/
theorem nonempty_localDefectTree_iff_lt_of_discrete [DiscreteTopology M]
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : 0 < m_defect) (base_val : M) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) ↔ m_defect < thresh.h := by
  constructor
  · rintro ⟨T⟩
    by_contra h_not_lt
    have hm_ge : thresh.h ≤ m_defect := le_of_not_gt h_not_lt
    haveI := LocalDefectTree.isEmpty_of_discrete_of_ge I thresh m_defect hm_ge base_val
    exact isEmptyElim T
  · intro hm_lt
    exact local_defect_tree_of_subthreshold I thresh m_defect hm hm_lt base_val

/-- Unconditional resolution of a single defect into a `LocalDefectTree` when `u_seq` admits a
`CalibratedRescaling` at `m_defect` and has a constant term `u_seq n₀ = fun _ => c` (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_calibrated_of_const_term
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : 0 < m_defect) (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M) (n₀ : ℕ) (c : M) (hc : u_seq n₀ = fun _ => c) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  by_cases hm_lt : m_defect < thresh.h
  · exact local_defect_tree_of_subthreshold I thresh m_defect hm hm_lt base_val
  · exact False.elim (CalibratedRescaling.false_of_const_term I u_seq thresh m_defect
      (le_of_not_gt hm_lt) res n₀ c hc)

/-- Unconditional resolution of a single defect into a `LocalDefectTree` on `[Subsingleton M]`
when `u_seq` admits a `CalibratedRescaling` at `m_defect` (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_calibrated_of_subsingleton [Subsingleton M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : 0 < m_defect) (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  resolve_single_defect_tree_of_calibrated_of_const_term I u_seq thresh m_defect hm res base_val
    0 (u_seq 0 north_pole) (funext (fun z => Subsingleton.elim (u_seq 0 z) (u_seq 0 north_pole)))

/-- Unconditional resolution of a single defect into a `LocalDefectTree` on `[DiscreteTopology M]`
when `u_seq` admits a `CalibratedRescaling` at `m_defect` and has a continuous term `u_seq n₀` (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_calibrated_of_exists_continuous_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : 0 < m_defect) (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M) (n₀ : ℕ) (h_cont : Continuous (u_seq n₀)) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  resolve_single_defect_tree_of_calibrated_of_const_term I u_seq thresh m_defect hm res base_val
    n₀ (u_seq n₀ north_pole) (funext (eq_const_north_pole_of_continuous_of_discrete (u_seq n₀) h_cont))

/-- Unconditional resolution of a single defect into a `LocalDefectTree` on `[DiscreteTopology M]`
when `u_seq` admits a `CalibratedRescaling` at `m_defect` and each `u_seq n` is `J`-holomorphic (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_calibrated_of_jhol_of_discrete [DiscreteTopology M]
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : 0 < m_defect) (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M) (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  resolve_single_defect_tree_of_calibrated_of_exists_continuous_of_discrete I u_seq thresh m_defect hm res base_val
    0 (continuousOn_univ.mp (h_jhol 0).1.continuousOn)

/-- Unconditional resolution of a single defect into a `LocalDefectTree` when `u_seq` admits a
`CalibratedRescaling` at `m_defect` and some `J`-holomorphic term `u_seq n₀` has total energy
strictly below `thresh.ε_sph` (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_calibrated_of_exists_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : 0 < m_defect) (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M) (n₀ : ℕ) (hu₀ : JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.ε_sph) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  have h_const : ∃ c : M, ∀ z, u_seq n₀ z = c := by
    by_contra h_nc
    have h_ge := thresh.h_sph (u_seq n₀) hu₀ h_nc
    linarith
  rcases h_const with ⟨c, hc⟩
  exact resolve_single_defect_tree_of_calibrated_of_const_term I u_seq thresh m_defect hm res base_val
    n₀ c (funext hc)

/-- Unconditional resolution of a single defect into a `LocalDefectTree` when `u_seq` admits a
`CalibratedRescaling` at `m_defect` and some `J`-holomorphic term `u_seq n₀` has total energy
strictly below `thresh.h` (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_calibrated_of_exists_lt_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : 0 < m_defect) (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M) (n₀ : ℕ) (hu₀ : JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n₀) Set.univ)
    (h_lt : totalEnergy I (u_seq n₀) < thresh.h) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  resolve_single_defect_tree_of_calibrated_of_exists_lt_eps_sph I u_seq thresh m_defect hm res base_val
    n₀ hu₀ (h_lt.trans_le thresh.h_le_sph)

/-- Unconditional resolution of a single defect into a `LocalDefectTree` when `u_seq` admits a
`CalibratedRescaling` at `m_defect` and some `J`-holomorphic term `u_seq n₀` has nonpositive
total energy (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_calibrated_of_exists_nonpos_energy
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : 0 < m_defect) (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M) (n₀ : ℕ) (hu₀ : JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n₀) Set.univ)
    (h_le : totalEnergy I (u_seq n₀) ≤ 0) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  resolve_single_defect_tree_of_calibrated_of_exists_lt_eps_sph I u_seq thresh m_defect hm res base_val
    n₀ hu₀ (h_le.trans_lt thresh.ε_sph_pos)

/-- Every `LocalDefectTree` at defect mass `m_defect ≥ thresh.h` has strictly positive total energy (`0 sorryAx`). -/
theorem LocalDefectTree.pos_of_ge_h
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M)
    (T : LocalDefectTree I thresh m_defect base_val) :
    0 < ∑ v : T.tree.V, totalEnergy I (T.map v) :=
  thresh.h_pos.trans_le (T.h_le_of_ge_h I thresh m_defect hm base_val)

/-- Every `LocalDefectTree` at defect mass `m_defect ≥ thresh.h` contains a component vertex `v`
with strictly positive total energy (`0 sorryAx`). -/
theorem LocalDefectTree.exists_pos_energy_component
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M)
    (T : LocalDefectTree I thresh m_defect base_val) :
    ∃ v : T.tree.V, 0 < totalEnergy I (T.map v) := by
  obtain ⟨v, hv_ge⟩ := T.exists_h_le_component I thresh m_defect hm base_val
  exact ⟨v, thresh.h_pos.trans_le hv_ge⟩

/-- Unconditional resolution of a single defect into a `LocalDefectTree` when `u_seq` admits a
`CalibratedRescaling` at `m_defect` and consists of `J`-holomorphic spheres that eventually have
`totalEnergy < thresh.ε_sph` (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_calibrated_of_eventually_lt_eps_sph
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : 0 < m_defect) (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M) (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) < thresh.ε_sph) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_ev
  exact resolve_single_defect_tree_of_calibrated_of_exists_lt_eps_sph I u_seq thresh m_defect hm res base_val
    N (h_jhol N) (hN N le_rfl)

/-- Unconditional resolution of a single defect into a `LocalDefectTree` when `u_seq` admits a
`CalibratedRescaling` at `m_defect` and consists of `J`-holomorphic spheres that eventually have
`totalEnergy < thresh.h` (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_calibrated_of_eventually_lt_h
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : 0 < m_defect) (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M) (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) < thresh.h) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  resolve_single_defect_tree_of_calibrated_of_eventually_lt_eps_sph I u_seq thresh m_defect hm res base_val
    h_jhol (h_ev.mono (fun _ hn => hn.trans_le thresh.h_le_sph))

/-- Unconditional resolution of a single defect into a `LocalDefectTree` when `u_seq` admits a
`CalibratedRescaling` at `m_defect` and consists of `J`-holomorphic spheres that eventually have
`totalEnergy ≤ 0` (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_calibrated_of_eventually_nonpos_energy
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : 0 < m_defect) (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M) (h_jhol : ∀ n, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_ev : ∀ᶠ n in atTop, totalEnergy I (u_seq n) ≤ 0) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  resolve_single_defect_tree_of_calibrated_of_eventually_lt_eps_sph I u_seq thresh m_defect hm res base_val
    h_jhol (h_ev.mono (fun _ hn => hn.trans_lt thresh.ε_sph_pos))

/-- Unconditional resolution of a single defect into a `LocalDefectTree` when `u_seq` admits a
`CalibratedRescaling` at `m_defect` and is eventually constant (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_calibrated_of_eventually_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : 0 < m_defect) (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M)
    (h_ev : ∀ᶠ n in atTop, ∃ c : M, u_seq n = fun _ => c) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_ev
  obtain ⟨c, hc⟩ := hN N le_rfl
  exact resolve_single_defect_tree_of_calibrated_of_const_term I u_seq thresh m_defect hm res base_val
    N c hc

/-- Unconditional resolution of a single defect into a `LocalDefectTree` when `u_seq` admits a
`CalibratedRescaling` at `m_defect` and every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_calibrated_of_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : 0 < m_defect) (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M) (n₀ : ℕ) (hu₀ : JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n₀) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  obtain ⟨c, hc⟩ := h_all_const (u_seq n₀) hu₀
  exact resolve_single_defect_tree_of_calibrated_of_const_term I u_seq thresh m_defect hm res base_val
    n₀ c (funext hc)

/-- Whenever every globally `J`-holomorphic sphere is constant, no `LocalDefectTree` exists for
`m_defect ≥ thresh.h` (`0 sorryAx`). -/
theorem LocalDefectTree.isEmpty_of_all_jhol_const_of_ge
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c) :
    IsEmpty (LocalDefectTree I thresh m_defect base_val) := by
  refine ⟨fun T => ?_⟩
  obtain ⟨v, hv_nc⟩ := T.exists_nonconst_component I thresh m_defect hm base_val
  exact hv_nc (h_all_const (T.map v) (T.is_jhol v))

/-- Whenever every globally `J`-holomorphic sphere is constant, for `0 < m_defect`,
`LocalDefectTree I thresh m_defect base_val` is nonempty if and only if `m_defect < thresh.h` (`0 sorryAx`). -/
theorem nonempty_localDefectTree_iff_lt_of_all_jhol_const
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : 0 < m_defect) (base_val : M)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) ↔ m_defect < thresh.h := by
  constructor
  · rintro ⟨T⟩
    by_contra h_not_lt
    have hm_ge : thresh.h ≤ m_defect := le_of_not_gt h_not_lt
    haveI := LocalDefectTree.isEmpty_of_all_jhol_const_of_ge I thresh m_defect hm_ge base_val h_all_const
    exact isEmptyElim T
  · intro hm_lt
    exact local_defect_tree_of_subthreshold I thresh m_defect hm hm_lt base_val

/-- Whenever `0 < m_defect` and `m_defect < thresh.h`, every `LocalDefectTree` has total energy `0`
when every globally `J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem LocalDefectTree.energy_sum_eq_zero_of_all_jhol_const
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (T : LocalDefectTree I thresh m_defect base_val)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c) :
    (∑ v : T.tree.V, totalEnergy I (T.map v)) = 0 := by
  apply Finset.sum_eq_zero
  intro v _
  obtain ⟨c, hc⟩ := h_all_const (T.map v) (T.is_jhol v)
  dsimp [totalEnergy]
  rw [funext hc]
  exact energyMeasure_const_eq_zero I c Set.univ

/-- Zero-sorry resolution of `resolve_single_defect_tree` from a single-child bubble `v` at `0`
and a resolved child `LocalDefectTree` at `(m_defect - totalEnergy I v)` (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_single_child_at_zero
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M)
    (v : CP1 → M)
    (hv_jhol : JHolomorphicOn (I := I) (I_dom := I_CP1) v Set.univ)
    (hv_le : totalEnergy I v ≤ m_defect - thresh.h)
    (hv_node : v north_pole = base_val)
    (hv_ext : totalEnergy I v - energyMeasure I v (disk_at 0 1) = thresh.h / 2)
    (T_child : LocalDefectTree I thresh (m_defect - totalEnergy I v) (v (stereo_chart.symm 0))) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  let decomp := OneLevelDecomposition.of_single_child_at_zero I thresh m_defect base_val
    v hv_jhol hv_le hv_node hv_ext
  refine graft_child_defect_trees I thresh m_defect base_val decomp hm (fun z hz => ?_)
  have hz0 : z = 0 := Finset.mem_singleton.mp hz
  subst hz0
  simpa [decomp, OneLevelDecomposition.of_single_child_at_zero] using T_child

/-- Unconditional resolution of a single defect into a `LocalDefectTree` when `u_seq` admits a
`CalibratedRescaling` at `m_defect`, is eventually `J`-holomorphic, and every globally
`J`-holomorphic sphere is constant (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_calibrated_of_eventually_all_jhol_const
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : 0 < m_defect) (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M) (N₀ : ℕ)
    (h_jhol : ∀ n ≥ N₀, JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n) Set.univ)
    (h_all_const : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → ∃ c : M, ∀ z, u z = c) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  resolve_single_defect_tree_of_calibrated_of_all_jhol_const I u_seq thresh m_defect hm res base_val
    N₀ (h_jhol N₀ le_rfl) h_all_const

/-- Zero-sorry resolution of `resolve_single_defect_tree` when a `OneLevelDecomposition` has
`totalEnergy I decomp.v = m_defect` (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_decomp_totalEnergy_eq_m_defect
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (h_eq : totalEnergy I decomp.v = m_defect) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  ⟨local_defect_tree_of_empty_children I thresh m_defect base_val decomp hm
    (OneLevelDecomposition.q_eq_empty_of_totalEnergy_eq_m_defect I thresh m_defect base_val decomp h_eq)⟩

/-- Zero-sorry resolution of `resolve_single_defect_tree` when a `OneLevelDecomposition` has
`decomp.q = ∅` (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_decomp_q_empty
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M)
    (decomp : OneLevelDecomposition I thresh m_defect base_val)
    (hq : decomp.q = ∅) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  ⟨local_defect_tree_of_empty_children I thresh m_defect base_val decomp hm hq⟩

/-- On a `[Subsingleton M]` target, every `LocalDefectTree` has total energy `0` (`0 sorryAx`). -/
theorem LocalDefectTree.energy_sum_eq_zero_of_subsingleton [Subsingleton M]
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (T : LocalDefectTree I thresh m_defect base_val) :
    (∑ v : T.tree.V, totalEnergy I (T.map v)) = 0 :=
  T.energy_sum_eq_zero_of_all_jhol_const I thresh m_defect base_val
    (fun u _ => ⟨u north_pole, fun z => Subsingleton.elim (u z) (u north_pole)⟩)

/-- On a `[DiscreteTopology M]` target, every `LocalDefectTree` has total energy `0` (`0 sorryAx`). -/
theorem LocalDefectTree.energy_sum_eq_zero_of_discrete [DiscreteTopology M]
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (T : LocalDefectTree I thresh m_defect base_val) :
    (∑ v : T.tree.V, totalEnergy I (T.map v)) = 0 :=
  T.energy_sum_eq_zero_of_all_jhol_const I thresh m_defect base_val
    (fun u hu => ⟨u north_pole, eq_const_north_pole_of_jhol_univ_of_discrete I u hu⟩)

/-- Whenever every globally `J`-holomorphic sphere equals its `north_pole` value, no `LocalDefectTree`
exists for `m_defect ≥ thresh.h` (`0 sorryAx`). -/
theorem LocalDefectTree.isEmpty_of_all_jhol_eq_north_pole_of_ge
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : thresh.h ≤ m_defect) (base_val : M)
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → u = fun _ => u north_pole) :
    IsEmpty (LocalDefectTree I thresh m_defect base_val) :=
  LocalDefectTree.isEmpty_of_all_jhol_const_of_ge I thresh m_defect hm base_val
    (fun u hu => ⟨u north_pole, fun z => congr_fun (h_all_np u hu) z⟩)

/-- Whenever every globally `J`-holomorphic sphere equals its `north_pole` value, every
`LocalDefectTree` has total energy `0` (`0 sorryAx`). -/
theorem LocalDefectTree.energy_sum_eq_zero_of_all_jhol_eq_north_pole
    (thresh : TargetThresholds I M) (m_defect : ℝ) (base_val : M)
    (T : LocalDefectTree I thresh m_defect base_val)
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → u = fun _ => u north_pole) :
    (∑ v : T.tree.V, totalEnergy I (T.map v)) = 0 :=
  T.energy_sum_eq_zero_of_all_jhol_const I thresh m_defect base_val
    (fun u hu => ⟨u north_pole, fun z => congr_fun (h_all_np u hu) z⟩)

/-- Unconditional resolution of a single defect into a `LocalDefectTree` when `u_seq` admits a
`CalibratedRescaling` at `m_defect` and every globally `J`-holomorphic sphere equals its `north_pole` value (`0 sorryAx`). -/
theorem resolve_single_defect_tree_of_calibrated_of_all_jhol_eq_north_pole
    (u_seq : ℕ → (CP1 → M)) (thresh : TargetThresholds I M) (m_defect : ℝ)
    (hm : 0 < m_defect) (res : CalibratedRescaling I u_seq thresh m_defect)
    (base_val : M) (n₀ : ℕ) (hu₀ : JHolomorphicOn (I := I) (I_dom := I_CP1) (u_seq n₀) Set.univ)
    (h_all_np : ∀ u : CP1 → M, JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ → u = fun _ => u north_pole) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) :=
  resolve_single_defect_tree_of_calibrated_of_all_jhol_const I u_seq thresh m_defect hm res base_val n₀ hu₀
    (fun u hu => ⟨u north_pole, fun z => congr_fun (h_all_np u hu) z⟩)

/-- Resolution of a Single Defect into a Finite Rooted Bubble Tree (Contract B07).
Proved with zero direct sorry via energy_rank_induction and B04/B06. -/
theorem resolve_single_defect_tree
    (thresh : TargetThresholds I M) (m_defect : ℝ) (hm : 0 < m_defect) (base_val : M) :
    Nonempty (LocalDefectTree I thresh m_defect base_val) := by
  by_cases hm_lt : m_defect < thresh.h
  · exact local_defect_tree_of_subthreshold I thresh m_defect hm hm_lt base_val
  · exact resolve_single_defect_tree_of_one_level I thresh
      (fun m h_ge b => exists_one_level_decomp_aux I thresh m h_ge b) m_defect hm base_val

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
#print axioms graft_child_defect_trees
#print axioms local_defect_tree_of_subthreshold
#print axioms resolve_single_defect_tree

end GromovCompactness.Bubbling
