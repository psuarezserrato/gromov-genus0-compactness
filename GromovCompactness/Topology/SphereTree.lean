/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import GromovCompactness.Geometry.Target
import GromovCompactness.Geometry.Sphere
import GromovCompactness.Analysis.Energy

open scoped Manifold ContDiff Topology Classical
open Metric Set

/-!
# Task F06: Labelled Trees and Convergence Data

This module formalizes labelled sphere trees, nodal attachments, and ghost component stability
predicates for genus 0 Gromov limits, following Gromov (1985, §2.2), Ivashkovich-Shevchishin (1999, §2.3),
and `gromov_compactness.pdf` §2.2 & §5 (Task `F06`).

## Key Definitions
- `SphereTree`: A finite rooted combinatorial tree $T = (V, E_T)$ equipped with distinct nodal attachment
  points $z_{vw} \in \mathbb{CP}^1$ for each oriented incident edge $v \sim w$.
- `StableSphereTreeLimit`: A family of component curves $u_v : \mathbb{CP}^1 \to M$ attached along nodes
  satisfying the nodal matching condition $u_v(z_{vw}) = u_w(z_{wv})$ and the stability condition
  ($\operatorname{deg}(v) \ge 3$ whenever $u_v$ is constant).
- `ghost_components_bound`: Topological bound showing that for any multi-vertex stable tree,
  the number of ghost components $G$ satisfies $G \le P - 2$, where $P$ is the number of non-constant
  components, hence $|V| = P + G \le 2P - 2$.
- `graft_trees`: Tree grafting operation at nodal points with full proof of `IsTree`.
- `sphereTreeTotalEnergy`: Total symplectic energy of a sphere tree.
-/

namespace GromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- A combinatorial labelled sphere tree $T = (V, E_T)$ where each oriented edge
carries a nodal attachment point on the Riemann sphere $\mathbb{CP}^1$. -/
structure SphereTree where
  /-- Finite vertex type indexing the spherical components. -/
  V : Type
  [fintypeV : Fintype V]
  [nonemptyV : Nonempty V]
  /-- Simple graph representing the nodal tree incidence. -/
  adj : SimpleGraph V
  /-- Connectedness and acyclicity: $T$ is a tree ($b_1(T) = 0$). -/
  is_tree : adj.IsTree
  /-- Nodal attachment point $z_{vw} \in \mathbb{CP}^1$ on component $v$ facing component $w$. -/
  node_point : (v : V) → (w : V) → adj.Adj v w → CP1
  /-- Distinctness: incident nodal points on each component are pairwise distinct. -/
  node_distinct : ∀ (v : V) (w₁ w₂ : V) (h₁ : adj.Adj v w₁) (h₂ : adj.Adj v w₂),
    w₁ ≠ w₂ → node_point v w₁ h₁ ≠ node_point v w₂ h₂

attribute [instance] SphereTree.fintypeV SphereTree.nonemptyV

/-- A stable pseudo-holomorphic sphere tree limit curve $(T, \{u_v\}, \{z_{vw}\})$. -/
structure StableSphereTreeLimit where
  /-- The underlying combinatorial sphere tree. -/
  tree : SphereTree
  /-- Component pseudo-holomorphic curves $u_v : \mathbb{CP}^1 \to M$. -/
  map : (v : tree.V) → (CP1 → M)
  /-- Each component map is smooth and $J$-holomorphic. -/
  is_jhol : ∀ (v : tree.V), JHolomorphicOn I I_CP1 (map v) Set.univ
  /-- Nodal matching condition: across every edge $v \sim w$, the curve images coincide at the node:
  $$u_v(z_{vw}) = u_w(z_{wv}).$$ -/
  nodal_match : ∀ (v w : tree.V) (h : tree.adj.Adj v w),
    map v (tree.node_point v w h) = map w (tree.node_point w v (tree.adj.adj_symm h))
  /-- Stability condition for unmarked curves ($k = 0$): any component on which $u_v$ is constant
  ("ghost bubble") must have at least 3 special points (nodal attachments) $\operatorname{deg}(v) \ge 3$
  so that its biholomorphic automorphism group in $\operatorname{PSL}(2, \mathbb{C})$ fixing nodal points is finite.
  Note on unmarked vs marked curves:
  - For unmarked curves ($k = 0$, the primary track of this formalization), special points are strictly nodal points,
    so $\operatorname{deg}_{\text{nodal}}(v) \ge 3$.
  - For $k$-marked curves ($k > 0$, extension track E03/E04), marked points also stabilize ghost spheres;
    the general stability condition is $\operatorname{deg}_{\text{nodal}}(v) + k_v \ge 3$, where $k_v$ is the number
    of marked points on component $v$. Under that condition, a ghost component may have nodal degree 0, 1, or 2. -/
  stable : ∀ (v : tree.V), (∃ c : M, ∀ z : CP1, map v z = c) → 3 ≤ tree.adj.degree v

/-- Predicate characterizing ghost (constant) components of a sphere tree limit. -/
def is_ghost_component (lim : StableSphereTreeLimit I (M := M)) (v : lim.tree.V) : Prop :=
  ∃ c : M, ∀ z : CP1, lim.map v z = c

/-- Predicate characterizing non-constant (principal) components. -/
def is_principal_component (lim : StableSphereTreeLimit I (M := M)) (v : lim.tree.V) : Prop :=
  ¬ is_ghost_component I lim v

/-- Euler characteristic relation for trees: $|E| = |V| - 1$, hence $\sum_{v \in V} \operatorname{deg}(v) = 2(|V| - 1)$. -/
theorem tree_degree_sum (tree : SphereTree) :
    ∑ v : tree.V, tree.adj.degree v = 2 * (Fintype.card tree.V - 1) := by
  have h_edges := tree.is_tree.card_edgeFinset
  have h_sum := tree.adj.sum_degrees_eq_twice_card_edges
  rw [h_sum]
  congr 1
  omega

lemma tree_degree_ge_one (tree : SphereTree)
    (h_multivertex : 1 < Fintype.card tree.V)
    (v : tree.V) : 1 ≤ tree.adj.degree v := by
  by_contra h_zero
  push_neg at h_zero
  have h_deg0 : tree.adj.degree v = 0 := by omega
  have h_exists_ne : ∃ w : tree.V, w ≠ v := by
    by_contra h_all
    push_neg at h_all
    have h_le1 : Fintype.card tree.V ≤ 1 := by
      rw [Fintype.card_le_one_iff]
      intro a b
      rw [h_all a, h_all b]
    omega
  rcases h_exists_ne with ⟨w, hw⟩
  have h_reach : tree.adj.Reachable v w := tree.is_tree.connected.preconnected v w
  rcases h_reach with ⟨p⟩
  have hp_not_nil : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hw.symm
  rcases SimpleGraph.Walk.not_nil_iff.mp hp_not_nil with ⟨u, hvu, _⟩
  have h_pos : 0 < tree.adj.degree v := by
    rw [SimpleGraph.degree_pos_iff_exists_adj]
    exact ⟨u, hvu⟩
  omega

/-- The Ghost Component Bound Theorem (`gromov_compactness.pdf` Theorem 1 & Task `F06`):
In any stable sphere tree with $|V| > 1$, let $P$ be the number of non-constant components
and $G$ be the number of ghost components ($|V| = P + G$).
For unmarked curves ($k = 0$):
1. $G \le P - 2$
2. $|V| = P + G \le 2P - 2$.
In particular, the total number of components is linearly bounded by the number of non-constant components.
(For general $k$-marked curves, $G \le P + k - 2$ and $|V| \le \max(1, 2P + k - 2) \le \max(1, 2\lfloor B/h \rfloor + k - 2)$). -/
theorem ghost_components_bound
    (lim : StableSphereTreeLimit I (M := M))
    (P G : ℕ)
    (h_multivertex : 1 < Fintype.card lim.tree.V)
    (h_P : P = Fintype.card { v : lim.tree.V // is_principal_component I lim v })
    (h_G : G = Fintype.card { v : lim.tree.V // is_ghost_component I lim v }) :
    G ≤ P - 2 ∧ Fintype.card lim.tree.V ≤ 2 * P - 2 := by
  have h_card_G : G = (Finset.univ.filter (is_ghost_component I lim)).card := by
    rw [h_G, Fintype.card_subtype]
  have h_card_P : P = (Finset.univ.filter (is_principal_component I lim)).card := by
    rw [h_P, Fintype.card_subtype]
  have h_prin_eq : Finset.univ.filter (is_principal_component I lim) =
      Finset.univ.filter (fun v => ¬ is_ghost_component I lim v) := by
    ext v
    simp [is_principal_component]
  have h_sum_cards : (Finset.univ.filter (is_ghost_component I lim)).card +
      (Finset.univ.filter (is_principal_component I lim)).card = Fintype.card lim.tree.V := by
    rw [h_prin_eq, Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have h_V_eq : Fintype.card lim.tree.V = G + P := by
    rw [h_card_G, h_card_P, h_sum_cards]
  have h_split := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset lim.tree.V))
    (p := is_ghost_component I lim) (f := fun v => lim.tree.adj.degree v)
  have h_split_sum : ∑ v : lim.tree.V, lim.tree.adj.degree v =
      (∑ v ∈ Finset.univ.filter (is_ghost_component I lim), lim.tree.adj.degree v) +
      (∑ v ∈ Finset.univ.filter (is_principal_component I lim), lim.tree.adj.degree v) := by
    rw [h_prin_eq]
    exact h_split.symm
  have h_ghost_bound : 3 * G ≤ ∑ v ∈ Finset.univ.filter (is_ghost_component I lim), lim.tree.adj.degree v := by
    have h_le : ∑ v ∈ Finset.univ.filter (is_ghost_component I lim), (3 : ℕ) ≤
        ∑ v ∈ Finset.univ.filter (is_ghost_component I lim), lim.tree.adj.degree v := by
      apply Finset.sum_le_sum
      intro v hv
      have hv_ghost : is_ghost_component I lim v := (Finset.mem_filter.mp hv).2
      exact lim.stable v hv_ghost
    have h_const : (∑ v ∈ Finset.univ.filter (is_ghost_component I lim), (3 : ℕ)) =
        3 * (Finset.univ.filter (is_ghost_component I lim)).card := by
      simp [Finset.sum_const, mul_comm]
    omega
  have h_prin_bound : P ≤ ∑ v ∈ Finset.univ.filter (is_principal_component I lim), lim.tree.adj.degree v := by
    have h_le : ∑ v ∈ Finset.univ.filter (is_principal_component I lim), (1 : ℕ) ≤
        ∑ v ∈ Finset.univ.filter (is_principal_component I lim), lim.tree.adj.degree v := by
      apply Finset.sum_le_sum
      intro v _
      exact tree_degree_ge_one lim.tree h_multivertex v
    have h_const : (∑ v ∈ Finset.univ.filter (is_principal_component I lim), (1 : ℕ)) =
        (Finset.univ.filter (is_principal_component I lim)).card := by
      simp [Finset.sum_const]
    omega
  have h_deg_sum := tree_degree_sum lim.tree
  omega

/-- Adjacency relation for grafted sphere trees with a bridge edge connecting $v_1$ and $v_2$. -/
def graftAdj (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) : SimpleGraph (T₁.V ⊕ T₂.V) where
  Adj
    | Sum.inl u, Sum.inl v => T₁.adj.Adj u v
    | Sum.inr u, Sum.inr v => T₂.adj.Adj u v
    | Sum.inl u, Sum.inr v => u = v₁ ∧ v = v₂
    | Sum.inr u, Sum.inl v => u = v₂ ∧ v = v₁
  symm := ⟨fun a b h => by
    rcases a with u | u <;> rcases b with v | v
    · exact T₁.adj.adj_symm h
    · exact ⟨h.2, h.1⟩
    · exact ⟨h.2, h.1⟩
    · exact T₂.adj.adj_symm h⟩
  loopless := ⟨fun a h => by
    rcases a with u | u
    · exact T₁.adj.irrefl h
    · exact T₂.adj.irrefl h⟩

def graftHomInl (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) :
    T₁.adj →g graftAdj T₁ T₂ v₁ v₂ where
  toFun := Sum.inl
  map_rel' h := h

def graftHomInr (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) :
    T₂.adj →g graftAdj T₁ T₂ v₁ v₂ where
  toFun := Sum.inr
  map_rel' h := h

lemma graftAdj_bridge (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) :
    (graftAdj T₁ T₂ v₁ v₂).Adj (Sum.inl v₁) (Sum.inr v₂) :=
  ⟨rfl, rfl⟩

lemma graft_connected (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) :
    (graftAdj T₁ T₂ v₁ v₂).Connected := by
  refine ⟨fun x y => ?_⟩
  rcases x with x₁ | x₂ <;> rcases y with y₁ | y₂
  · rcases T₁.is_tree.connected.preconnected x₁ y₁ with ⟨p⟩
    exact ⟨p.map (graftHomInl T₁ T₂ v₁ v₂)⟩
  · rcases T₁.is_tree.connected.preconnected x₁ v₁ with ⟨p₁⟩
    rcases T₂.is_tree.connected.preconnected v₂ y₂ with ⟨p₂⟩
    let w_bridge : (graftAdj T₁ T₂ v₁ v₂).Walk (Sum.inl v₁) (Sum.inr v₂) :=
      SimpleGraph.Walk.cons (graftAdj_bridge T₁ T₂ v₁ v₂) SimpleGraph.Walk.nil
    let p₁' := p₁.map (graftHomInl T₁ T₂ v₁ v₂)
    let p₂' := p₂.map (graftHomInr T₁ T₂ v₁ v₂)
    exact ⟨p₁'.append (w_bridge.append p₂')⟩
  · rcases T₂.is_tree.connected.preconnected x₂ v₂ with ⟨p₂⟩
    rcases T₁.is_tree.connected.preconnected v₁ y₁ with ⟨p₁⟩
    let w_bridge : (graftAdj T₁ T₂ v₁ v₂).Walk (Sum.inr v₂) (Sum.inl v₁) :=
      SimpleGraph.Walk.cons ((graftAdj T₁ T₂ v₁ v₂).adj_symm (graftAdj_bridge T₁ T₂ v₁ v₂)) SimpleGraph.Walk.nil
    let p₂' := p₂.map (graftHomInr T₁ T₂ v₁ v₂)
    let p₁' := p₁.map (graftHomInl T₁ T₂ v₁ v₂)
    exact ⟨p₂'.append (w_bridge.append p₁')⟩
  · rcases T₂.is_tree.connected.preconnected x₂ y₂ with ⟨p⟩
    exact ⟨p.map (graftHomInr T₁ T₂ v₁ v₂)⟩

def isRight (T₁ T₂ : SphereTree) : T₁.V ⊕ T₂.V → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

lemma isRight_step (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    {x y : T₁.V ⊕ T₂.V} (h : (graftAdj T₁ T₂ v₁ v₂).Adj x y) :
    (isRight T₁ T₂ x ≠ isRight T₁ T₂ y) ↔
    (s(x, y) = s(Sum.inl v₁, Sum.inr v₂)) := by
  rcases x with x₁ | x₂ <;> rcases y with y₁ | y₂
  · simp [isRight, graftAdj] at h ⊢
  · simp [isRight, graftAdj] at h ⊢
    rcases h with ⟨rfl, rfl⟩
    simp
  · simp [isRight, graftAdj] at h ⊢
    rcases h with ⟨rfl, rfl⟩
    simp [Sym2.eq_swap]
  · simp [isRight, graftAdj] at h ⊢

lemma walk_bridge_count_parity (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    {x y : T₁.V ⊕ T₂.V} (p : (graftAdj T₁ T₂ v₁ v₂).Walk x y) :
    (p.edges.count s(Sum.inl v₁, Sum.inr v₂) : ZMod 2) =
    if isRight T₁ T₂ x = isRight T₁ T₂ y then 0 else 1 := by
  induction p with
  | nil =>
    simp
  | @cons u v w h q ih =>
    rw [SimpleGraph.Walk.edges_cons, List.count_cons]
    have h_step := isRight_step T₁ T₂ v₁ v₂ h
    push_cast
    rw [ih]
    by_cases he : s(u, v) = s(Sum.inl v₁, Sum.inr v₂)
    · simp only [he, beq_self_eq_true, ↓reduceIte]
      have h_diff : isRight T₁ T₂ u ≠ isRight T₁ T₂ v := h_step.mpr he
      rcases hu : isRight T₁ T₂ u <;> rcases hv : isRight T₁ T₂ v <;>
        rcases hw : isRight T₁ T₂ w <;>
        simp_all <;> try decide
    · have h_beq : (s(u, v) == s(Sum.inl v₁, Sum.inr v₂)) = false := by
        simp [beq_iff_eq, he]
      simp only [h_beq, Bool.false_eq_true, ↓reduceIte, add_zero]
      have h_same : isRight T₁ T₂ u = isRight T₁ T₂ v := by
        by_contra h_diff
        exact he (h_step.mp h_diff)
      rw [h_same]

lemma cycle_not_mem_bridge (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    {x : T₁.V ⊕ T₂.V} (p : (graftAdj T₁ T₂ v₁ v₂).Walk x x) (hp : p.IsCycle) :
    s(Sum.inl v₁, Sum.inr v₂) ∉ p.edges := by
  have h_parity := walk_bridge_count_parity T₁ T₂ v₁ v₂ p
  simp only [↓reduceIte] at h_parity
  have h_nodup : p.edges.Nodup := hp.isTrail.edges_nodup
  have h_le1 := (List.nodup_iff_count_le_one.mp h_nodup) s(Sum.inl v₁, Sum.inr v₂)
  have h_count : p.edges.count s(Sum.inl v₁, Sum.inr v₂) = 0 := by
    have h_mod : (p.edges.count s(Sum.inl v₁, Sum.inr v₂) : ZMod 2) = 0 := h_parity
    have h_dvd : 2 ∣ p.edges.count s(Sum.inl v₁, Sum.inr v₂) :=
      (ZMod.natCast_eq_zero_iff _ 2).mp h_mod
    obtain ⟨k, hk⟩ := h_dvd
    omega
  exact List.count_eq_zero.mp h_count

def walkOfInl (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) :
    ∀ {u v : T₁.V} (p : (graftAdj T₁ T₂ v₁ v₂).Walk (Sum.inl u) (Sum.inl v)),
    (s(Sum.inl v₁, Sum.inr v₂) ∉ p.edges) → T₁.adj.Walk u v
  | _, _, SimpleGraph.Walk.nil, _ => SimpleGraph.Walk.nil
  | u, _, SimpleGraph.Walk.cons (v := Sum.inl u') h q, hp =>
    have h_adj : T₁.adj.Adj u u' := h
    have hp' : s(Sum.inl v₁, Sum.inr v₂) ∉ q.edges := by
      intro h_in
      exact hp (List.mem_cons_of_mem _ h_in)
    SimpleGraph.Walk.cons h_adj (walkOfInl T₁ T₂ v₁ v₂ q hp')
  | u, _, SimpleGraph.Walk.cons (v := Sum.inr u') h q, hp => by
    have h_bridge : s(Sum.inl u, Sum.inr u') ∈ (SimpleGraph.Walk.cons h q).edges := by simp
    have h_eq : u = v₁ ∧ u' = v₂ := h
    have : s(Sum.inl u, Sum.inr u') = s(Sum.inl v₁, Sum.inr v₂) := by rw [h_eq.1, h_eq.2]
    exact False.elim (hp (this ▸ h_bridge))

lemma walkOfInl_map (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) :
    ∀ {u v : T₁.V} (p : (graftAdj T₁ T₂ v₁ v₂).Walk (Sum.inl u) (Sum.inl v))
    (hp : s(Sum.inl v₁, Sum.inr v₂) ∉ p.edges),
    (walkOfInl T₁ T₂ v₁ v₂ p hp).map (graftHomInl T₁ T₂ v₁ v₂) = p
  | _, _, SimpleGraph.Walk.nil, _ => by simp [walkOfInl]; try rfl
  | u, _, SimpleGraph.Walk.cons (v := Sum.inl u') h q, hp => by
    simp only [walkOfInl]
    have h' : T₁.adj.Adj u u' := h
    show SimpleGraph.Walk.map (graftHomInl T₁ T₂ v₁ v₂)
      (SimpleGraph.Walk.cons h' (walkOfInl T₁ T₂ v₁ v₂ q _)) = SimpleGraph.Walk.cons h q
    rw [SimpleGraph.Walk.map_cons]
    congr 1
    exact walkOfInl_map T₁ T₂ v₁ v₂ q _
  | u, _, SimpleGraph.Walk.cons (v := Sum.inr u') h q, hp => by
    have h_bridge : s(Sum.inl u, Sum.inr u') ∈ (SimpleGraph.Walk.cons h q).edges := by simp
    have h_eq : u = v₁ ∧ u' = v₂ := h
    have : s(Sum.inl u, Sum.inr u') = s(Sum.inl v₁, Sum.inr v₂) := by rw [h_eq.1, h_eq.2]
    exact False.elim (hp (this ▸ h_bridge))

def walkOfInr (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) :
    ∀ {u v : T₂.V} (p : (graftAdj T₁ T₂ v₁ v₂).Walk (Sum.inr u) (Sum.inr v)),
    (s(Sum.inl v₁, Sum.inr v₂) ∉ p.edges) → T₂.adj.Walk u v
  | _, _, SimpleGraph.Walk.nil, _ => SimpleGraph.Walk.nil
  | u, _, SimpleGraph.Walk.cons (v := Sum.inr u') h q, hp =>
    have h_adj : T₂.adj.Adj u u' := h
    have hp' : s(Sum.inl v₁, Sum.inr v₂) ∉ q.edges := by
      intro h_in
      exact hp (List.mem_cons_of_mem _ h_in)
    SimpleGraph.Walk.cons h_adj (walkOfInr T₁ T₂ v₁ v₂ q hp')
  | u, _, SimpleGraph.Walk.cons (v := Sum.inl u') h q, hp => by
    have h_bridge : s(Sum.inr u, Sum.inl u') ∈ (SimpleGraph.Walk.cons h q).edges := by simp
    have h_eq : u = v₂ ∧ u' = v₁ := h
    have : s(Sum.inr u, Sum.inl u') = s(Sum.inl v₁, Sum.inr v₂) := by
      rw [h_eq.1, h_eq.2, Sym2.eq_swap]
    exact False.elim (hp (this ▸ h_bridge))

lemma walkOfInr_map (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) :
    ∀ {u v : T₂.V} (p : (graftAdj T₁ T₂ v₁ v₂).Walk (Sum.inr u) (Sum.inr v))
    (hp : s(Sum.inl v₁, Sum.inr v₂) ∉ p.edges),
    (walkOfInr T₁ T₂ v₁ v₂ p hp).map (graftHomInr T₁ T₂ v₁ v₂) = p
  | _, _, SimpleGraph.Walk.nil, _ => by simp [walkOfInr]; try rfl
  | u, _, SimpleGraph.Walk.cons (v := Sum.inr u') h q, hp => by
    simp only [walkOfInr]
    have h' : T₂.adj.Adj u u' := h
    show SimpleGraph.Walk.map (graftHomInr T₁ T₂ v₁ v₂)
      (SimpleGraph.Walk.cons h' (walkOfInr T₁ T₂ v₁ v₂ q _)) = SimpleGraph.Walk.cons h q
    rw [SimpleGraph.Walk.map_cons]
    congr 1
    exact walkOfInr_map T₁ T₂ v₁ v₂ q _
  | u, _, SimpleGraph.Walk.cons (v := Sum.inl u') h q, hp => by
    have h_bridge : s(Sum.inr u, Sum.inl u') ∈ (SimpleGraph.Walk.cons h q).edges := by simp
    have h_eq : u = v₂ ∧ u' = v₁ := h
    have : s(Sum.inr u, Sum.inl u') = s(Sum.inl v₁, Sum.inr v₂) := by
      rw [h_eq.1, h_eq.2, Sym2.eq_swap]
    exact False.elim (hp (this ▸ h_bridge))

lemma graft_is_acyclic (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) :
    (graftAdj T₁ T₂ v₁ v₂).IsAcyclic := by
  intro x c hc
  have h_not_bridge := cycle_not_mem_bridge T₁ T₂ v₁ v₂ c hc
  rcases x with u | u
  · let c₁ := walkOfInl T₁ T₂ v₁ v₂ c h_not_bridge
    have h_map := walkOfInl_map T₁ T₂ v₁ v₂ c h_not_bridge
    have h_inj : Function.Injective (Sum.inl : T₁.V → T₁.V ⊕ T₂.V) := Sum.inl_injective
    have h_cyc : c₁.IsCycle := by
      have h_iff := SimpleGraph.Walk.isCycle_map_iff_of_injective (f := graftHomInl T₁ T₂ v₁ v₂) h_inj (p := c₁)
      rw [h_map] at h_iff
      exact h_iff.mp hc
    exact T₁.is_tree.isAcyclic c₁ h_cyc
  · let c₂ := walkOfInr T₁ T₂ v₁ v₂ c h_not_bridge
    have h_map := walkOfInr_map T₁ T₂ v₁ v₂ c h_not_bridge
    have h_inj : Function.Injective (Sum.inr : T₂.V → T₁.V ⊕ T₂.V) := Sum.inr_injective
    have h_cyc : c₂.IsCycle := by
      have h_iff := SimpleGraph.Walk.isCycle_map_iff_of_injective (f := graftHomInr T₁ T₂ v₁ v₂) h_inj (p := c₂)
      rw [h_map] at h_iff
      exact h_iff.mp hc
    exact T₂.is_tree.isAcyclic c₂ h_cyc

lemma graft_is_tree (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) :
    (graftAdj T₁ T₂ v₁ v₂).IsTree :=
  ⟨graft_connected T₁ T₂ v₁ v₂, graft_is_acyclic T₁ T₂ v₁ v₂⟩

def graftNodePoint (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) (p₁ p₂ : CP1)
    (x y : T₁.V ⊕ T₂.V) (h : (graftAdj T₁ T₂ v₁ v₂).Adj x y) : CP1 :=
  match x, y with
  | Sum.inl u, Sum.inl w => T₁.node_point u w h
  | Sum.inr u, Sum.inr w => T₂.node_point u w h
  | Sum.inl _, Sum.inr _ => p₁
  | Sum.inr _, Sum.inl _ => p₂

lemma graft_node_distinct (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V) (p₁ p₂ : CP1)
    (hp₁ : ∀ (w : T₁.V) (h : T₁.adj.Adj v₁ w), p₁ ≠ T₁.node_point v₁ w h)
    (hp₂ : ∀ (w : T₂.V) (h : T₂.adj.Adj v₂ w), p₂ ≠ T₂.node_point v₂ w h) :
    ∀ (x w₁ w₂ : T₁.V ⊕ T₂.V)
      (h₁ : (graftAdj T₁ T₂ v₁ v₂).Adj x w₁) (h₂ : (graftAdj T₁ T₂ v₁ v₂).Adj x w₂),
      w₁ ≠ w₂ →
      graftNodePoint T₁ T₂ v₁ v₂ p₁ p₂ x w₁ h₁ ≠ graftNodePoint T₁ T₂ v₁ v₂ p₁ p₂ x w₂ h₂ := by
  intro x w₁ w₂ h₁ h₂ h_ne
  rcases x with u | u <;> rcases w₁ with a₁ | a₂ <;> rcases w₂ with b₁ | b₂
  · have h_ne' : a₁ ≠ b₁ := by rintro rfl; exact h_ne rfl
    exact T₁.node_distinct u a₁ b₁ h₁ h₂ h_ne'
  · dsimp [graftNodePoint]
    have h₂' : u = v₁ := h₂.1
    subst h₂'
    exact (hp₁ a₁ h₁).symm
  · dsimp [graftNodePoint]
    have h₁' : u = v₁ := h₁.1
    subst h₁'
    exact hp₁ b₁ h₂
  · have ha : a₂ = v₂ := h₁.2
    have hb : b₂ = v₂ := h₂.2
    subst ha hb
    contradiction
  · have ha : a₁ = v₁ := h₁.2
    have hb : b₁ = v₁ := h₂.2
    subst ha hb
    contradiction
  · dsimp [graftNodePoint]
    have h₁' : u = v₂ := h₁.1
    subst h₁'
    exact hp₂ b₂ h₂
  · dsimp [graftNodePoint]
    have h₂' : u = v₂ := h₂.1
    subst h₂'
    exact (hp₂ a₂ h₁).symm
  · have h_ne' : a₂ ≠ b₂ := by rintro rfl; exact h_ne rfl
    exact T₂.node_distinct u a₂ b₂ h₁ h₂ h_ne'

/-- Tree grafting operation: attaching two stable sphere trees $T_1$ and $T_2$ by identifying
a designated smooth point on $T_1$ with a smooth point on $T_2$. -/
def graft_trees (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    (p₁ : CP1) (p₂ : CP1)
    (hp₁ : ∀ (w : T₁.V) (h : T₁.adj.Adj v₁ w), p₁ ≠ T₁.node_point v₁ w h)
    (hp₂ : ∀ (w : T₂.V) (h : T₂.adj.Adj v₂ w), p₂ ≠ T₂.node_point v₂ w h) : SphereTree where
  V := T₁.V ⊕ T₂.V
  fintypeV := inferInstance
  nonemptyV := inferInstance
  adj := graftAdj T₁ T₂ v₁ v₂
  is_tree := graft_is_tree T₁ T₂ v₁ v₂
  node_point := graftNodePoint T₁ T₂ v₁ v₂ p₁ p₂
  node_distinct := graft_node_distinct T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂

lemma graft_node_points_inr_nonroot (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    (p₁ p₂ : CP1) (hp₁ : ∀ w h, p₁ ≠ T₁.node_point v₁ w h) (hp₂ : ∀ w h, p₂ ≠ T₂.node_point v₂ w h)
    (w : T₂.V) (hw : w ≠ v₂) :
    { z | ∃ y h, z = (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).node_point (Sum.inr w) y h } =
    { z | ∃ w' h', z = T₂.node_point w w' h' } := by
  ext z
  constructor
  · rintro ⟨y, h, rfl⟩
    rcases y with u | w'
    · exfalso
      have heq : w = v₂ := h.1
      exact hw heq
    · exact ⟨w', h, rfl⟩
  · rintro ⟨w', h, rfl⟩
    exact ⟨Sum.inr w', h, rfl⟩

lemma graft_node_points_inr_root (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    (p₁ p₂ : CP1) (hp₁ : ∀ w h, p₁ ≠ T₁.node_point v₁ w h) (hp₂ : ∀ w h, p₂ ≠ T₂.node_point v₂ w h) :
    { z | ∃ y h, z = (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).node_point (Sum.inr v₂) y h } =
    insert p₂ { z | ∃ w' h', z = T₂.node_point v₂ w' h' } := by
  ext z
  constructor
  · rintro ⟨y, h, rfl⟩
    rcases y with u | w'
    · have hu : u = v₁ := h.2
      subst hu
      dsimp [graft_trees, graftNodePoint]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨w', h, rfl⟩
  · intro hz
    rcases Set.mem_insert_iff.mp hz with rfl | ⟨w', h, rfl⟩
    · refine ⟨Sum.inl v₁, ⟨rfl, rfl⟩, ?_⟩
      dsimp [graft_trees, graftNodePoint]
    · exact ⟨Sum.inr w', h, rfl⟩

lemma graft_node_points_inl_nonroot (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    (p₁ p₂ : CP1) (hp₁ : ∀ w h, p₁ ≠ T₁.node_point v₁ w h) (hp₂ : ∀ w h, p₂ ≠ T₂.node_point v₂ w h)
    (u : T₁.V) (hu : u ≠ v₁) :
    { z | ∃ y h, z = (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).node_point (Sum.inl u) y h } =
    { z | ∃ u' h', z = T₁.node_point u u' h' } := by
  ext z
  constructor
  · rintro ⟨y, h, rfl⟩
    rcases y with u' | w
    · exact ⟨u', h, rfl⟩
    · exfalso
      have heq : u = v₁ := h.1
      exact hu heq
  · rintro ⟨u', h, rfl⟩
    exact ⟨Sum.inl u', h, rfl⟩

/-- Total energy of a stable sphere tree is the sum of energies of its components. -/
noncomputable def sphereTreeTotalEnergy (lim : StableSphereTreeLimit I (M := M)) : ℝ :=
  ∑ v : lim.tree.V, totalEnergy I (lim.map v)

#print axioms tree_degree_sum
#print axioms ghost_components_bound
#print axioms graft_trees
#print axioms sphereTreeTotalEnergy

end GromovCompactness
