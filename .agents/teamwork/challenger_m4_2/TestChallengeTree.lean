/-
Copyright (c) 2026 Autoformalization Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Autoformalization Team (challenger_m4_2)
-/
import GromovCompactness.Topology.SphereTree

open scoped Manifold ContDiff Topology Classical
open Metric Set GromovCompactness

/-!
# Empirical and Adversarial Challenge Suite: SphereTree (Task F06)

This file performs rigorous adversarial testing of `GromovCompactness.Topology.SphereTree`:
1. `tree_degree_sum` on concrete trees:
   - Single-vertex tree ($|V| = 1$, degree sum = $0 = 2(1-1)$)
   - 2-vertex tree ($|V| = 2$, degree sum = $2 = 2(2-1)$)
   - 3-vertex path graph $P_3$ ($|V| = 3$, degree sum = $4 = 2(3-1)$)
   - 4-vertex star graph $K_{1,3}$ ($|V| = 4$, degree sum = $6 = 2(4-1)$)
2. `graft_trees` vertex counting, acyclicity, connectedness, and degree preservation:
   - $|V(T_1 \cup T_2)| = |V(T_1)| + |V(T_2)|$
   - $(T_1 \cup T_2)$ is acyclic (`IsAcyclic`)
   - $(T_1 \cup T_2)$ is connected (`Connected`)
   - $(T_1 \cup T_2)$ is a tree (`IsTree`)
   - Tree degree sum formula is preserved under grafting
3. `ghost_components_bound` edge configurations and adversarial stress-testing:
   - Edge configuration $P = 2, G = 0$ (sharp bound $G \le 0$, $|V| \le 2$, exact $|V| = 2$)
   - Edge configuration $P = 3, G = 1$ (sharp bound $G \le 1$, $|V| \le 4$, exact $|V| = 4$)
   - Refutation of invalid configuration $P = 2, G = 1$ (proves $G \le P - 2$ excludes impossible states)
   - Impossibility of multi-vertex stable trees with $P \le 1$ (proves $P \ge 2$)
   - Impossibility of purely ghost stable trees ($P = 0$)
4. Axiom audit: verifies standard axioms `[propext, Classical.choice, Quot.sound]` only.
-/

namespace ChallengeSphereTree

/-! ### Distinct Points on CP1 for Nodal Attachments -/

lemma north_ne_south : north_pole ≠ south_pole := by
  intro h
  have h2 := congr_arg (fun (p : CP1) => p.1 2) h
  dsimp [north_pole, south_pole] at h2
  revert h2
  norm_num

/-- Equatorial point $(1, 0, 0) \in S^2 \cong \mathbb{CP}^1$. -/
def east_pole : CP1 :=
  ⟨!₂[1, 0, 0], by
    simp only [mem_sphere_zero_iff_norm]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three]⟩

lemma east_ne_north : east_pole ≠ north_pole := by
  intro h
  have h2 := congr_arg (fun (p : CP1) => p.1 2) h
  dsimp [east_pole, north_pole] at h2
  revert h2
  norm_num

lemma east_ne_south : east_pole ≠ south_pole := by
  intro h
  have h2 := congr_arg (fun (p : CP1) => p.1 2) h
  dsimp [east_pole, south_pole] at h2
  revert h2
  norm_num

/-! ### Concrete Tree Constructions -/

/-- Single-vertex sphere tree ($V = \text{Unit}$, $E = \emptyset$). -/
def singleTree : SphereTree where
  V := Unit
  fintypeV := inferInstance
  nonemptyV := inferInstance
  adj := ⊥
  is_tree := by
    refine ⟨⟨fun x y => ?_⟩, ?_⟩
    · cases x; cases y; exact ⟨SimpleGraph.Walk.nil⟩
    · intro x c hc
      rcases SimpleGraph.Walk.not_nil_iff.mp hc.not_nil with ⟨u, hu, _⟩
      exact (SimpleGraph.bot_adj x u).mp hu
  node_point := fun _ _ h => False.elim ((SimpleGraph.bot_adj _ _).mp h)
  node_distinct := fun _ _ _ h => False.elim ((SimpleGraph.bot_adj _ _).mp h)

/-- Two-vertex sphere tree ($V = \text{Unit} \oplus \text{Unit}$, single edge). -/
def twoTree : SphereTree :=
  graft_trees singleTree singleTree () () north_pole south_pole
    (fun _ h => False.elim ((SimpleGraph.bot_adj _ _).mp h))
    (fun _ h => False.elim ((SimpleGraph.bot_adj _ _).mp h))

/-- Three-vertex path graph $P_3$ ($u_1 - u_2 - u_3$), constructed by attaching
a single-vertex tree to the second vertex of `twoTree`. -/
def threePathTree : SphereTree :=
  graft_trees twoTree singleTree (Sum.inr ()) () north_pole south_pole
    (by
      intro w h
      rcases w with w₁ | w₂
      · dsimp [twoTree, graft_trees, graftNodePoint]
        exact north_ne_south
      · exfalso
        exact (SimpleGraph.bot_adj () w₂).mp h)
    (fun _ h => False.elim ((SimpleGraph.bot_adj _ _).mp h))

/-- Three-vertex star graph $K_{1,2}$ (center $v_1$ attached to two leaves). -/
def threeStarTree : SphereTree :=
  graft_trees twoTree singleTree (Sum.inl ()) () south_pole north_pole
    (by
      intro w h
      rcases w with w₁ | w₂
      · exfalso
        exact (SimpleGraph.bot_adj () w₁).mp h
      · dsimp [twoTree, graft_trees, graftNodePoint]
        exact north_ne_south.symm)
    (fun _ h => False.elim ((SimpleGraph.bot_adj _ _).mp h))

/-- Four-vertex star graph $K_{1,3}$ (center attached to three leaves at distinct points:
`north_pole`, `south_pole`, and `east_pole`). -/
def fourStarTree : SphereTree :=
  graft_trees threeStarTree singleTree (Sum.inl (Sum.inl ())) () east_pole north_pole
    (by
      intro w h
      rcases w with w_three | w_single
      · rcases w_three with w₁ | w₂
        · exfalso
          exact (SimpleGraph.bot_adj () w₁).mp h
        · dsimp [threeStarTree, graft_trees, twoTree, graftNodePoint]
          exact east_ne_north
      · dsimp [threeStarTree, graft_trees, graftNodePoint]
        exact east_ne_south)
    (fun _ h => False.elim ((SimpleGraph.bot_adj _ _).mp h))

/-! ### Part 1: Empirical Verification of tree_degree_sum on Concrete Trees -/

theorem test_singleTree_card : Fintype.card singleTree.V = 1 :=
  rfl

theorem test_singleTree_degree_sum :
    ∑ v : singleTree.V, singleTree.adj.degree v = 0 := by
  have h := tree_degree_sum singleTree
  rw [test_singleTree_card] at h
  exact h

theorem test_twoTree_card : Fintype.card twoTree.V = 2 := by
  dsimp [twoTree, graft_trees, singleTree]
  rfl

theorem test_twoTree_degree_sum :
    ∑ v : twoTree.V, twoTree.adj.degree v = 2 := by
  have h := tree_degree_sum twoTree
  rw [test_twoTree_card] at h
  exact h

theorem test_threePathTree_card : Fintype.card threePathTree.V = 3 := by
  dsimp [threePathTree, graft_trees, twoTree, singleTree]
  rfl

theorem test_threePathTree_degree_sum :
    ∑ v : threePathTree.V, threePathTree.adj.degree v = 4 := by
  have h := tree_degree_sum threePathTree
  rw [test_threePathTree_card] at h
  exact h

theorem test_fourStarTree_card : Fintype.card fourStarTree.V = 4 := by
  dsimp [fourStarTree, threeStarTree, twoTree, singleTree, graft_trees]
  rfl

theorem test_fourStarTree_degree_sum :
    ∑ v : fourStarTree.V, fourStarTree.adj.degree v = 6 := by
  have h := tree_degree_sum fourStarTree
  rw [test_fourStarTree_card] at h
  exact h

/-! ### Part 2: Adversarial Testing of graft_trees -/

/-- Vertex count identity: $|V(T_1 \cup T_2)| = |V(T_1)| + |V(T_2)|$. -/
theorem test_graft_vertex_counting (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    (p₁ p₂ : CP1)
    (hp₁ : ∀ (w : T₁.V) (h : T₁.adj.Adj v₁ w), p₁ ≠ T₁.node_point v₁ w h)
    (hp₂ : ∀ (w : T₂.V) (h : T₂.adj.Adj v₂ w), p₂ ≠ T₂.node_point v₂ w h) :
    Fintype.card (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).V =
      Fintype.card T₁.V + Fintype.card T₂.V := by
  dsimp [graft_trees]
  exact Fintype.card_sum

/-- Acyclicity preservation: the grafted tree has no non-trivial simple cycles. -/
theorem test_graft_acyclicity (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    (p₁ p₂ : CP1)
    (hp₁ : ∀ (w : T₁.V) (h : T₁.adj.Adj v₁ w), p₁ ≠ T₁.node_point v₁ w h)
    (hp₂ : ∀ (w : T₂.V) (h : T₂.adj.Adj v₂ w), p₂ ≠ T₂.node_point v₂ w h) :
    (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).adj.IsAcyclic :=
  (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).is_tree.IsAcyclic

/-- Connectedness preservation: the grafted tree is connected. -/
theorem test_graft_connectedness (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    (p₁ p₂ : CP1)
    (hp₁ : ∀ (w : T₁.V) (h : T₁.adj.Adj v₁ w), p₁ ≠ T₁.node_point v₁ w h)
    (hp₂ : ∀ (w : T₂.V) (h : T₂.adj.Adj v₂ w), p₂ ≠ T₂.node_point v₂ w h) :
    (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).adj.Connected :=
  (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).is_tree.isConnected

/-- Full tree property: the grafted tree is a tree. -/
theorem test_graft_is_tree (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    (p₁ p₂ : CP1)
    (hp₁ : ∀ (w : T₁.V) (h : T₁.adj.Adj v₁ w), p₁ ≠ T₁.node_point v₁ w h)
    (hp₂ : ∀ (w : T₂.V) (h : T₂.adj.Adj v₂ w), p₂ ≠ T₂.node_point v₂ w h) :
    (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).adj.IsTree :=
  (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).is_tree

/-- Degree sum on grafted trees satisfies Euler characteristic formula. -/
theorem test_graft_degree_sum (T₁ T₂ : SphereTree) (v₁ : T₁.V) (v₂ : T₂.V)
    (p₁ p₂ : CP1)
    (hp₁ : ∀ (w : T₁.V) (h : T₁.adj.Adj v₁ w), p₁ ≠ T₁.node_point v₁ w h)
    (hp₂ : ∀ (w : T₂.V) (h : T₂.adj.Adj v₂ w), p₂ ≠ T₂.node_point v₂ w h) :
    ∑ v : (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).V,
      (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂).adj.degree v =
      2 * (Fintype.card T₁.V + Fintype.card T₂.V - 1) := by
  have h := tree_degree_sum (graft_trees T₁ T₂ v₁ v₂ p₁ p₂ hp₁ hp₂)
  rw [test_graft_vertex_counting] at h
  exact h

/-! ### Part 3: Ghost Component Bounds and Adversarial Stress-Testing -/

section GhostChallenge
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- Cardinality identity: $|V| = P + G$ from disjoint partition into principal and ghost components. -/
lemma card_V_eq_P_add_G
    (lim : StableSphereTreeLimit I (M := M))
    (P G : ℕ)
    (h_P : P = Fintype.card { v : lim.tree.V // is_principal_component I lim v })
    (h_G : G = Fintype.card { v : lim.tree.V // is_ghost_component I lim v }) :
    Fintype.card lim.tree.V = P + G := by
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
    rw [h_prin_eq, Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ]
  omega

/-- Edge configuration $P = 2, G = 0$: minimal non-trivial stable curve (two principal spheres).
Both bounds $G \le P - 2$ ($0 \le 0$) and $|V| \le 2P - 2$ ($2 \le 2$) are SHARP and exact. -/
theorem test_ghost_edge_P2_G0
    (lim : StableSphereTreeLimit I (M := M))
    (h_multivertex : 1 < Fintype.card lim.tree.V)
    (h_P : 2 = Fintype.card { v : lim.tree.V // is_principal_component I lim v })
    (h_G : 0 = Fintype.card { v : lim.tree.V // is_ghost_component I lim v }) :
    (0 ≤ (2 : ℕ) - 2 ∧ Fintype.card lim.tree.V ≤ 2 * 2 - 2) ∧
    Fintype.card lim.tree.V = 2 * 2 - 2 := by
  have h_bound := ghost_components_bound I lim 2 0 h_multivertex h_P h_G
  have h_exact : Fintype.card lim.tree.V = 2 := by
    have h_split := card_V_eq_P_add_G I lim 2 0 h_P h_G
    omega
  refine ⟨h_bound, ?_⟩
  omega

/-- Edge configuration $P = 3, G = 1$: one central ghost sphere of degree 3 attached to
three principal spheres. Both bounds $G \le P - 2$ ($1 \le 1$) and $|V| \le 2P - 2$ ($4 \le 4$)
are SHARP and exact. -/
theorem test_ghost_edge_P3_G1
    (lim : StableSphereTreeLimit I (M := M))
    (h_multivertex : 1 < Fintype.card lim.tree.V)
    (h_P : 3 = Fintype.card { v : lim.tree.V // is_principal_component I lim v })
    (h_G : 1 = Fintype.card { v : lim.tree.V // is_ghost_component I lim v }) :
    (1 ≤ (3 : ℕ) - 2 ∧ Fintype.card lim.tree.V ≤ 2 * 3 - 2) ∧
    Fintype.card lim.tree.V = 2 * 3 - 2 := by
  have h_bound := ghost_components_bound I lim 3 1 h_multivertex h_P h_G
  have h_exact : Fintype.card lim.tree.V = 4 := by
    have h_split := card_V_eq_P_add_G I lim 3 1 h_P h_G
    omega
  refine ⟨h_bound, ?_⟩
  omega

/-- Adversarial challenge: refute the impossible configuration $P = 2, G = 1$.
The theorem `ghost_components_bound` correctly eliminates this state. -/
theorem test_refute_ghost_P2_G1
    (lim : StableSphereTreeLimit I (M := M))
    (h_multivertex : 1 < Fintype.card lim.tree.V)
    (h_P : 2 = Fintype.card { v : lim.tree.V // is_principal_component I lim v })
    (h_G : 1 = Fintype.card { v : lim.tree.V // is_ghost_component I lim v }) :
    False := by
  have ⟨h_bound, _⟩ := ghost_components_bound I lim 2 1 h_multivertex h_P h_G
  omega

/-- Adversarial challenge: every multi-vertex stable sphere tree limit must have at least 2
principal components ($P \ge 2$). It is impossible to have $P \le 1$. -/
theorem test_principal_at_least_two
    (lim : StableSphereTreeLimit I (M := M))
    (P G : ℕ)
    (h_multivertex : 1 < Fintype.card lim.tree.V)
    (h_P : P = Fintype.card { v : lim.tree.V // is_principal_component I lim v })
    (h_G : G = Fintype.card { v : lim.tree.V // is_ghost_component I lim v }) :
    2 ≤ P := by
  have ⟨_, h_card⟩ := ghost_components_bound I lim P G h_multivertex h_P h_G
  have h_split := card_V_eq_P_add_G I lim P G h_P h_G
  omega

/-- Adversarial challenge: refute purely ghost stable trees ($P = 0$). -/
theorem test_refute_ghost_P0
    (lim : StableSphereTreeLimit I (M := M))
    (G : ℕ)
    (h_multivertex : 1 < Fintype.card lim.tree.V)
    (h_P : 0 = Fintype.card { v : lim.tree.V // is_principal_component I lim v })
    (h_G : G = Fintype.card { v : lim.tree.V // is_ghost_component I lim v }) :
    False := by
  have h_P_ge_2 := test_principal_at_least_two I lim 0 G h_multivertex h_P h_G
  omega

end GhostChallenge

/-! ### Part 4: Axiom Audit -/

#print axioms test_singleTree_degree_sum
#print axioms test_twoTree_degree_sum
#print axioms test_threePathTree_degree_sum
#print axioms test_fourStarTree_degree_sum
#print axioms test_graft_vertex_counting
#print axioms test_graft_acyclicity
#print axioms test_graft_connectedness
#print axioms test_graft_is_tree
#print axioms test_graft_degree_sum
#print axioms test_ghost_edge_P2_G0
#print axioms test_ghost_edge_P3_G1
#print axioms test_refute_ghost_P2_G1
#print axioms test_principal_at_least_two
#print axioms test_refute_ghost_P0

end ChallengeSphereTree
