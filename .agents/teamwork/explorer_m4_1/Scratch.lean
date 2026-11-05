import GromovCompactness.Extensions.Automorphisms

namespace GromovCompactness.Extensions

open scoped Manifold ContDiff Topology
open Metric Set GromovCompactness Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]

/-- **3-Point Möbius Rigidity (Projective PGL(2, ℂ))**:
Any Möbius transformation matrix fixing 3 distinct projective points in ℂ × ℂ
is projectively equivalent to the identity matrix.
Direct corollary of the proved `moebius_three_points_unique` / `exists_unique_moebius_three_points` (F02). -/
theorem moebius_three_point_rigidity_proj (M_mat : MoebiusMatrix) (v₁ v₂ v₃ : ℂ × ℂ)
    (h12 : ¬ ProjEquiv v₁ v₂) (h13 : ¬ ProjEquiv v₁ v₃) (h23 : ¬ ProjEquiv v₂ v₃)
    (hfix1 : ProjEquiv (M_mat.act v₁) v₁)
    (hfix2 : ProjEquiv (M_mat.act v₂) v₂)
    (hfix3 : ProjEquiv (M_mat.act v₃) v₃) :
    PglEquiv M_mat MoebiusMatrix.id := by
  have hid1 : ProjEquiv (MoebiusMatrix.id.act v₁) v₁ := by
    dsimp [MoebiusMatrix.id, MoebiusMatrix.act, ProjEquiv]; ring
  have hid2 : ProjEquiv (MoebiusMatrix.id.act v₂) v₂ := by
    dsimp [MoebiusMatrix.id, MoebiusMatrix.act, ProjEquiv]; ring
  have hid3 : ProjEquiv (MoebiusMatrix.id.act v₃) v₃ := by
    dsimp [MoebiusMatrix.id, MoebiusMatrix.act, ProjEquiv]; ring
  exact moebius_three_points_unique M_mat MoebiusMatrix.id v₁ v₂ v₃ v₁ v₂ v₃
    h12 h23 h13 h12 h23 h13 hfix1 hfix2 hfix3 hid1 hid2 hid3

#print axioms moebius_three_point_rigidity_proj

theorem pure_automorphism_fixes_nodes
    (lim : StableSphereTreeLimit I (M := M))
    (aut : PureComponentAutomorphism I lim)
    (v w : lim.tree.V) (h : lim.tree.adj.Adj v w) :
    (aut.1.frame v).toHomeo (lim.tree.node_point v w h) = lim.tree.node_point v w h := by
  rcases aut with ⟨⟨⟨toEquiv, map_adj'⟩, frame, curve_equiv, node_compat⟩, h_tree⟩
  dsimp at h_tree
  subst h_tree
  dsimp
  have h_node := node_compat v w h
  dsimp at h_node
  have h_edge_eq : (map_adj' v w).2 h = h := Subsingleton.elim _ _
  rw [h_edge_eq] at h_node
  exact h_node

theorem ghost_component_pure_automorphism_trivial_of_rigidity
    (h_rigidity : ∀ (ϕ : MoebiusFrame) (p₁ p₂ p₃ : CP1),
      p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ϕ.toHomeo p₁ = p₁ → ϕ.toHomeo p₂ = p₂ → ϕ.toHomeo p₃ = p₃ →
      ϕ.toHomeo = Homeomorph.refl CP1)
    (lim : StableSphereTreeLimit I (M := M))
    (v : lim.tree.V)
    (h_ghost : is_ghost_component I lim v)
    (aut : PureComponentAutomorphism I lim) :
    (aut.1.frame v).toHomeo = Homeomorph.refl CP1 := by
  have h_stab : 3 ≤ lim.tree.adj.degree v := lim.stable v h_ghost
  have h_card : 3 ≤ (lim.tree.adj.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact h_stab
  have h_nonempty : (lim.tree.adj.neighborFinset v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.card_empty] at h_card
    omega
  obtain ⟨w₁, hw1_mem⟩ := h_nonempty
  have h_card1 : 2 ≤ ((lim.tree.adj.neighborFinset v).erase w₁).card := by
    rw [Finset.card_erase_of_mem hw1_mem]
    omega
  have h_nonempty1 : ((lim.tree.adj.neighborFinset v).erase w₁).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.card_empty] at h_card1
    omega
  obtain ⟨w₂, hw2_mem'⟩ := h_nonempty1
  have hw2_mem := Finset.mem_of_mem_erase hw2_mem'
  have hw12_ne : w₁ ≠ w₂ := (Finset.ne_of_mem_erase hw2_mem').symm
  have h_card2 : 1 ≤ (((lim.tree.adj.neighborFinset v).erase w₁).erase w₂).card := by
    rw [Finset.card_erase_of_mem hw2_mem']
    omega
  have h_nonempty2 : (((lim.tree.adj.neighborFinset v).erase w₁).erase w₂).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.card_empty] at h_card2
    omega
  obtain ⟨w₃, hw3_mem''⟩ := h_nonempty2
  have hw3_mem' := Finset.mem_of_mem_erase hw3_mem''
  have hw23_ne : w₂ ≠ w₃ := (Finset.ne_of_mem_erase hw3_mem'').symm
  have hw3_mem := Finset.mem_of_mem_erase hw3_mem'
  have hw13_ne : w₁ ≠ w₃ := (Finset.ne_of_mem_erase hw3_mem').symm

  have h_adj1 : lim.tree.adj.Adj v w₁ := by rwa [lim.tree.adj.mem_neighborFinset] at hw1_mem
  have h_adj2 : lim.tree.adj.Adj v w₂ := by rwa [lim.tree.adj.mem_neighborFinset] at hw2_mem
  have h_adj3 : lim.tree.adj.Adj v w₃ := by rwa [lim.tree.adj.mem_neighborFinset] at hw3_mem

  let p₁ := lim.tree.node_point v w₁ h_adj1
  let p₂ := lim.tree.node_point v w₂ h_adj2
  let p₃ := lim.tree.node_point v w₃ h_adj3

  have hp12 : p₁ ≠ p₂ := lim.tree.node_distinct v w₁ w₂ h_adj1 h_adj2 hw12_ne
  have hp13 : p₁ ≠ p₃ := lim.tree.node_distinct v w₁ w₃ h_adj1 h_adj3 hw13_ne
  have hp23 : p₂ ≠ p₃ := lim.tree.node_distinct v w₂ w₃ h_adj2 h_adj3 hw23_ne

  have h_fix1 : (aut.1.frame v).toHomeo p₁ = p₁ := pure_automorphism_fixes_nodes I lim aut v w₁ h_adj1
  have h_fix2 : (aut.1.frame v).toHomeo p₂ = p₂ := pure_automorphism_fixes_nodes I lim aut v w₂ h_adj2
  have h_fix3 : (aut.1.frame v).toHomeo p₃ = p₃ := pure_automorphism_fixes_nodes I lim aut v w₃ h_adj3

  exact h_rigidity (aut.1.frame v) p₁ p₂ p₃ hp12 hp13 hp23 h_fix1 h_fix2 h_fix3

#print axioms ghost_component_pure_automorphism_trivial_of_rigidity

end GromovCompactness.Extensions
